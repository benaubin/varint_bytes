#![no_std]
#![forbid(unsafe_code)]

//! Helper library for reading/writing variable length integers
//!
//! ```
//! use varint_bytes::{GetVarInt, PutVarInt};
//! use bytes::{BytesMut};
//! 
//! let mut bytes = &[0b1010_1100, 0b0000_0010][..];
//! let num: u32 = bytes.get_varint();
//! assert_eq!(num, 300);
//!
//! let mut bytes = BytesMut::new();
//! bytes.put_varint(300 as u32);
//! assert_eq!(bytes[..], [0b1010_1100, 0b0000_0010][..]);
//!
//! ```
//!
//! ## Advantages:
//!
//! - Misuse resistant - won't read more than the maximum size of the output type or past the input
//! - Uses [tokio/bytes](https://github.com/tokio-rs/bytes)'s `Buf`
//! - `no_std` and `forbid(unsafe_code)`

use core::mem::size_of;

use bytes::{Buf, BufMut};

/// Allows reading variable length integers from `Buf`
pub trait GetVarInt<T> {
    /// Read variable-length integer.
    ///
    /// ```
    /// use varint_bytes::GetVarInt;
    ///
    /// let mut bytes = &[0b1010_1100, 0b0000_0010][..];
    /// let num: u32 = bytes.get_varint();
    /// assert_eq!(num, 300);
    /// ```
    fn get_varint(&mut self) -> T;
}

/// Allows writing variable length integers to `BufMut`
pub trait PutVarInt<T> {
    /// Write variable-length integer.
    ///
    /// ```
    /// use varint_bytes::PutVarInt;
    /// use bytes::{BytesMut};
    ///
    /// let mut bytes = BytesMut::new();
    /// bytes.put_varint(300 as u32);
    ///
    /// assert_eq!(bytes[..], [0b1010_1100, 0b0000_0010][..]);
    /// ```
    fn put_varint(&mut self, val: T);
}

macro_rules! varint {
    ($ty:ty) => {
        impl<T: Buf> GetVarInt<$ty> for T {
            /// Read variable-length unsigned integer
            #[inline(always)]
            fn get_varint(&mut self) -> $ty {
                let mut num: $ty = 0;

                static MAX_BYTES: usize = (size_of::<$ty>() * 8 / 7 + 1);

                for i in 0..MAX_BYTES.min(self.remaining()) {
                    let byte = self.get_u8();
                    
                    num = num | (((byte & 0b01111111) as $ty) << (i * 7));

                    let msb = byte & 0b10000000;
                    if msb == 0 { break }
                }

                num
            }
        }

        impl<T: BufMut> PutVarInt<$ty> for T {
            /// Write variable-length unsigned integer
            #[inline(always)]
            fn put_varint(&mut self, mut val: $ty) {
                loop {
                    let byte = ((val as u8) & 0b01111111);

                    val = val >> 7;

                    if val == 0 {
                        self.put_u8(byte);
                        return;
                    } else {
                        self.put_u8(byte | 0b10000000);
                    }
                }
            }
        }
    }
}

varint! ( u32 );
varint! ( u64 );

/// Handles zig-zag encoding
pub trait ZigZag {
    type Encoded;
    /// Encodes this integer with zigzag encoding
    fn zigzag(self) -> Self::Encoded;
    /// Decodes the zigzag encoded value
    fn decode_zigzag(val: Self::Encoded) -> Self;
}

macro_rules! zigzag {
    ($signed:ty => $unsigned:ty) => {
        impl ZigZag for $signed {
            type Encoded = $unsigned;

            #[inline(always)]
            fn zigzag(self) -> $unsigned {
                const SIZE: usize = (size_of::<$signed>() * 8 - 1);
                ((self << 1) ^ (self >> SIZE)) as $unsigned
            }
            #[inline(always)]
            fn decode_zigzag(val: $unsigned) -> $signed {
                ((val >> 1) as $signed) ^ -((val & 1) as $signed)
            }
        }

        impl<T: GetVarInt<$unsigned>> GetVarInt<$signed> for T {
            /// Reads a signed zigzag-encoded variable-length integer
            #[inline(always)]
            fn get_varint(&mut self) -> $signed {
                ZigZag::decode_zigzag(self.get_varint())
            }
        }

        impl<T: PutVarInt<$unsigned>> PutVarInt<$signed> for T {
            /// Writes a signed zigzag-encoded variable-length integer
            #[inline(always)]
            fn put_varint(&mut self, val: $signed) {
                self.put_varint(val.zigzag())
            }
        }
    };
}

zigzag!( i32 => u32 );
zigzag!( i64 => u64 );

#[cfg(test)]
mod test {
    use bytes::BytesMut;
    use core::fmt::Debug;

    use super::*;

    static VAR_INTS: &'static [u32] = &[
        1,
        300,
        555,
        u32::MAX
    ];

    static VAR_INT_BUF: &'static [u8] = &[
        0b0000_0001,
        0b1010_1100, 0b0000_0010,
        0b1010_1011, 0b0000_0100,
        0b1111_1111, 0b1111_1111, 0b1111_1111, 0b1111_1111, 0b0000_1111
    ];

    #[test]
    fn put_unsigned_ints() {
        let mut bytes = BytesMut::new();

        for num in VAR_INTS.iter().cloned() {
            bytes.put_varint(num)
        }

        assert_eq!(bytes[..], VAR_INT_BUF[..])
    }

    #[test]
    fn get_unsigned_ints() {
        let mut buf: &[u8] = VAR_INT_BUF;

        for expected in VAR_INTS.iter().cloned() {
            let act: u32 = buf.get_varint();
            assert_eq!(act, expected);
        }
    }

    struct InfiniteBuf { bytes: &'static [u8], bytes_read: usize }

    impl Buf for InfiniteBuf {
        fn remaining(&self) -> usize { self.bytes.len() }
        fn bytes(&self) -> &[u8] { self.bytes }
        fn advance(&mut self, cnt: usize) { self.bytes_read += cnt }
    }


    #[test]
    fn dos_resistant() {
        static BUF: [u8; 7] = [255, 255, 255, 255, 255, 200, 130];
        let mut buf: & [u8] = & BUF;

        // implies we should read more than 5 bytes
        let res: u32 = buf.get_varint();
        // should fail open at the maximum number of bytes for the type, leaving the remainder of the buffer alone
        assert_eq!(res, u32::MAX);
        assert_eq!(buf, &BUF[5..]);
        
        // asks to read more bytes than available.
        // would normally cause panic due to overflow with rust's regular behavior.
        // instead, we should just read as if the msb is set to zero when we run out of bytes to read
        let res: u32 = buf.get_varint();
        assert_eq!(res, 328)
    }

    #[test]
    fn reads_lazily() {
        let mut buf: & [u8] = & [15, 77];
        let res: u32 = buf.get_varint();
        assert_eq!(res, 15);
        assert_eq!(buf, & [ 77 ]);
    }
    
    #[test]
    fn zigzag() {
        fn case<Z: ZigZag + Debug + PartialEq + Copy>(n: Z, encoded: Z::Encoded) where Z::Encoded: Debug + PartialEq {
            assert_eq!(n.zigzag(), encoded);
            assert_eq!(n, ZigZag::decode_zigzag(encoded));
        }
        
        case::<i32>(0, 0);
        case::<i32>(-1, 1);
        case::<i32>(1, 2);
        case::<i32>(-2, 3);
        case::<i64>(-2, 3);
        case::<i64>(2147483647, 4294967294);
        case::<i64>(-2147483648, 4294967295);
    }
}