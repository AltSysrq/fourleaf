//-
// Copyright 2017, Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Low-level definitions for working with the wire format.
//!
//! External code generally should not use things from this module; instead,
//! prefer the `stream` module if you want to do lower-level streaming.

use std::borrow::Cow;
use std::io::{self, Read, Write};
use std::usize;

use num_traits::FromPrimitive;

/// Used for reading bytes from a stream.
///
/// This is similar to `io::Read`, but allows bulk reads to return references
/// into an underlying byte slice instead of requiring a copy to a heap
/// allocation.
pub trait Input<'a> {
    /// Read and return a single byte.
    fn read_byte(&mut self) -> io::Result<u8>;
    /// Read and return a single byte, or None if at EOF.
    fn read_byte_opt(&mut self) -> io::Result<Option<u8>>;
    /// Read the given number of bytes and return them in a slice. The slice
    /// may be a new allocation or be backed by the underlying value.
    fn read_bytes(&mut self, n: usize) -> io::Result<Cow<'a, [u8]>>;
    /// Discard up to the given number of bytes (as with Read::read but
    /// discarding the buffer).
    fn skip(&mut self, n: usize) -> io::Result<usize>;
}

impl<'a, T : Read> Input<'a> for T {
    fn read_byte(&mut self) -> io::Result<u8> {
        let mut buf = [0u8];
        self.read_exact(&mut buf)?;
        Ok(buf[0])
    }

    fn read_byte_opt(&mut self) -> io::Result<Option<u8>> {
        let mut buf = [0u8];
        let n = self.read(&mut buf)?;
        Ok(if 0 == n { None } else { Some(buf[0]) })
    }

    fn read_bytes(&mut self, n: usize) -> io::Result<Cow<'a, [u8]>> {
        let mut buf = vec![0u8;n];
        self.read_exact(&mut buf[..])?;
        Ok(Cow::Owned(buf))
    }

    fn skip(&mut self, n: usize) -> io::Result<usize> {
        io::copy(&mut self.take(n as u64), &mut io::sink()).map(|v| v as usize)
    }
}

/// Wraps byte-slice-like things to use an `Input` implementation which returns
/// slices into the referenced buffer instead of copying.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZeroCopy<T>(pub T);

impl<'a> Input<'a> for ZeroCopy<&'a [u8]> {
    fn read_byte(&mut self) -> io::Result<u8> {
        self.0.read_byte()
    }

    fn read_byte_opt(&mut self) -> io::Result<Option<u8>> {
        self.0.read_byte_opt()
    }

    fn read_bytes(&mut self, n: usize) -> io::Result<Cow<'a, [u8]>> {
        if n > self.0.len() {
            Err(io::Error::new(io::ErrorKind::UnexpectedEof,
                               "Not enough bytes in buffer"))
        } else {
            let ret = &self.0[..n];
            self.0 = &self.0[n..];
            Ok(Cow::Borrowed(ret))
        }
    }

    fn skip(&mut self, n: usize) -> io::Result<usize> {
        self.read_bytes(n).map(|b| b.len())
    }
}

/// A descriptor for an element in a struct, or a marker for the end of the
/// struct or other special functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Descriptor(#[allow(missing_docs)] pub u8);

enum_from_primitive! {
/// The type of the value (if any) following a normal `Descriptor`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
pub enum DescriptorType {
    Null = 0x00,
    Integer = 0x40,
    Blob = 0x80,
    Struct = 0xC0,
}
}

enum_from_primitive! {
/// The interpretation of a special `Descriptor`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
pub enum SpecialType {
    EndOfStruct = 0x00,
    EndOfDoc = 0x40,
    Exception = 0x80,
    Padding = 0xC0,
}
}

/// A `Descriptor` in a more structured format.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParsedDescriptor {
    /// A normal descriptor, indicating a field tag and the type which follows
    /// it (if any). The tag must always be in the range 1..63 (inclusive).
    Pair(DescriptorType, u8),
    /// A special descriptor.
    Special(SpecialType),
}

impl Descriptor {
    /// Convert this `Descriptor` to a `ParsedDescriptor`.
    pub fn parse(self) -> ParsedDescriptor {
        let ty = self.0 & 0xC0;
        let tag = self.0 & 0x3F;

        if 0 == tag {
            ParsedDescriptor::Special(SpecialType::from_u8(ty).unwrap())
        } else {
            ParsedDescriptor::Pair(DescriptorType::from_u8(ty).unwrap(), tag)
        }
    }
}

impl From<ParsedDescriptor> for Descriptor {
    fn from(d: ParsedDescriptor) -> Self {
        Descriptor(match d {
            ParsedDescriptor::Pair(ty, tag) => {
                debug_assert!(tag >= 1 && tag <= 63);
                tag | (ty as u8)
            },
            ParsedDescriptor::Special(ty) => ty as u8
        })
    }
}

/// Decode an unsigned integer from the given input, parsing up to 64 bits.
///
/// This fails if the encoded value overflows a u64.
pub fn decode_u64<'a, R : Input<'a>>(r: &mut R) -> io::Result<u64> {
    let mut accum = 0u64;
    let mut shift = 0;
    loop {
        let b = r.read_byte()?;
        let v = (b & 0x7F) as u64;
        if v << shift >> shift != v {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData, "Integer overflow"));
        }
        accum |= v << shift;
        shift += 7;

        if 0 == (b & 0x80) {
            break;
        }
    }

    Ok(accum)
}

/// Encode an unsigned 64-bit integer to the given output.
pub fn encode_u64<W : Write>(w: &mut W, mut i: u64) -> io::Result<()> {
    let mut bytes = [0u8;10];
    let mut n = 0;

    loop {
        bytes[n] = (i & 0x7F) as u8;
        i >>= 7;
        if i > 0 {
            bytes[n] |= 0x80;
        }
        n += 1;
        if 0 == i {
            break
        }
    }

    w.write_all(&mut bytes[..n])
}

/// Invert `zigzag`.
pub fn unzigzag(i: u64) -> i64 {
    let sign = if (i & 1) != 0 { !0u64 } else { 0 };
    ((i >> 1) ^ sign) as i64
}

/// Decode a 64-bit integer and then unZigZag it to a signed value.
pub fn decode_i64<'a, R : Input<'a>>(r: &mut R) -> io::Result<i64> {
    let i = decode_u64(r)?;
    Ok(unzigzag(i))
}

/// ZigZag the given signed 64-bit integer into the unsigned storage format.
pub fn zigzag(i: i64) -> u64 {
    ((i << 1) ^ (i >> 63)) as u64
}

/// ZigZag the given signed 64-bit integer to unsigned format, then write it to
/// the given output.
pub fn encode_i64<W : Write>(w: &mut W, i: i64) -> io::Result<()> {
    encode_u64(w, zigzag(i))
}

/// Encode the given byte slice as a blob on the given writer.
pub fn encode_blob<W : Write, D : AsRef<[u8]>>(w: &mut W, data: D)
                                               -> io::Result<()> {
    let data = data.as_ref();
    encode_u64(w, data.len() as u64)?;
    w.write_all(data)
}

/// Decode a blob from the given input, returning a cow to the data contained.
pub fn decode_blob<'a, R : Input<'a>>(r: &mut R)
                                      -> io::Result<Cow<'a, [u8]>> {
    let length = decode_u64(r)?;
    if length > (usize::MAX as u64) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Blob length longer than usize::MAX"));
    }

    r.read_bytes(length as usize)
}

/// Read a descriptor from the given input.
pub fn decode_descriptor<'a, R : Input<'a>>(r: &mut R)
                                            -> io::Result<Descriptor> {
    r.read_byte().map(Descriptor)
}

/// Write a descriptor to the given output.
pub fn encode_descriptor<W : Write>(w: &mut W, desc: Descriptor)
                                    -> io::Result<()> {
    w.write_all(&[desc.0])
}

#[cfg(test)]
mod test {
    use std::io;
    use std::{i64, u64};

    use super::*;

    #[test]
    fn integer_encoding_and_decoding() {
        macro_rules! test {
            ($enc:ident, $dec:ident, $v:expr, $vec:expr) => { {
                let mut output = Vec::new();
                $enc(&mut output, $v).unwrap();
                assert_eq!(&$vec[..], &output[..]);

                let mut input = &output[..];
                let decoded = $dec(&mut input).unwrap();
                let empty: &[u8] = &[];
                assert_eq!(empty, input);
                assert_eq!($v, decoded);
            } }
        }

        test!(encode_u64, decode_u64, 0, [0]);
        test!(encode_i64, decode_i64, 0, [0]);
        test!(encode_u64, decode_u64, 1, [1]);
        test!(encode_i64, decode_i64, 1, [2]);
        test!(encode_i64, decode_i64, -1, [1]);
        test!(encode_u64, decode_u64, 256, [128, 2]);
        test!(encode_i64, decode_i64, 256, [128, 4]);
        test!(encode_u64, decode_u64, u64::MAX,
              [255, 255, 255, 255, 255, 255, 255, 255, 255, 1]);
        test!(encode_i64, decode_i64, i64::MAX,
              [254, 255, 255, 255, 255, 255, 255, 255, 255, 1]);
        test!(encode_i64, decode_i64, i64::MIN,
              [255, 255, 255, 255, 255, 255, 255, 255, 255, 1]);
    }

    #[test]
    fn integer_decode_detects_overflow() {
        match decode_u64(&mut&[255, 255, 255, 255, 255,
                               255, 255, 255, 255, 2][..]) {
            Ok(i) => panic!("Unexpectedly decoded {}", i),
            Err(e) => assert_eq!(io::ErrorKind::InvalidData, e.kind()),
        }
    }

    #[test]
    fn blob_encoding_and_decoding() {
        macro_rules! test {
            ($v:expr) => { {
                let mut output = Vec::new();
                encode_blob(&mut output, $v).unwrap();

                let decoded = decode_blob(&mut&output[..]).unwrap();
                assert_eq!($v, &*decoded);

                let decoded = decode_blob(&mut ZeroCopy(&output[..])).unwrap();
                assert_eq!($v, &*decoded);
            } }
        }
        test!(b"");
        test!(b"hello world");
        test!(&[42u8;1024][..]);
    }

    #[test]
    fn descriptor_conversion() {
        macro_rules! test {
            ($n:expr, $v:expr) => { {
                let desc = Descriptor($n);
                let parsed = desc.parse();
                assert_eq!($v, parsed);
                let d2 = Descriptor::from(parsed);
                assert_eq!($n, d2.0);
            } }
        }

        test!(0x00, ParsedDescriptor::Special(SpecialType::EndOfStruct));
        test!(0x40, ParsedDescriptor::Special(SpecialType::EndOfDoc));
        test!(0x80, ParsedDescriptor::Special(SpecialType::Exception));
        test!(0xC0, ParsedDescriptor::Special(SpecialType::Padding));
        test!(0x01, ParsedDescriptor::Pair(DescriptorType::Null, 1));
        test!(0x41, ParsedDescriptor::Pair(DescriptorType::Integer, 1));
        test!(0x81, ParsedDescriptor::Pair(DescriptorType::Blob, 1));
        test!(0xC1, ParsedDescriptor::Pair(DescriptorType::Struct, 1));
        test!(0x3F, ParsedDescriptor::Pair(DescriptorType::Null, 63));
        test!(0x7F, ParsedDescriptor::Pair(DescriptorType::Integer, 63));
        test!(0xBF, ParsedDescriptor::Pair(DescriptorType::Blob, 63));
        test!(0xFF, ParsedDescriptor::Pair(DescriptorType::Struct, 63));
    }

    #[test]
    fn zero_copy_read_past_end() {
        let mut zc = ZeroCopy(&b"hello world"[..]);
        match zc.read_bytes(100) {
            Ok(v) => panic!("Unexpectedly succeeded with {:?}", v),
            Err(e) => assert_eq!(io::ErrorKind::UnexpectedEof, e.kind()),
        }
    }

    #[test]
    fn zero_copy_read_advance() {
        let mut zc = ZeroCopy(&b"hello world"[..]);
        assert_eq!(b'h', zc.read_byte().unwrap());
        assert_eq!(b"ell", &*zc.read_bytes(3).unwrap());
        assert_eq!(b'o', zc.read_byte().unwrap());
    }
}
