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

use std::io::{self, Read, Write};

fn read_byte<R : Read>(r: &mut R) -> io::Result<u8> {
    let mut buf = [0u8;1];
    r.read_exact(&mut buf)?;
    Ok(buf[0])
}

/// A descriptor for an element in a struct, or a marker for the end of the
/// struct or other special functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Descriptor(#[allow(missing_docs)] pub u8);

/// The type of the value (if any) following a normal `Descriptor`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
#[repr(u8)]
pub enum DescriptorType {
    Null = 0x00,
    Integer = 0x40,
    Blob = 0x80,
    Struct = 0xC0,
}

impl DescriptorType {
    #[inline]
    fn from_u8(ty: u8) -> Self {
        use self::DescriptorType::*;

        match ty {
            0x00 => Null,
            0x40 => Integer,
            0x80 => Blob,
            0xC0 => Struct,
            _ => unreachable!(),
        }
    }
}

/// The interpretation of a special `Descriptor`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
#[repr(u8)]
pub enum SpecialType {
    EndOfStruct = 0x00,
    EndOfDoc = 0x40,
    Exception = 0x80,
    Padding = 0xC0,
}

impl SpecialType {
    #[inline]
    fn from_u8(ty: u8) -> Self {
        use self::SpecialType::*;

        match ty {
            0x00 => EndOfStruct,
            0x40 => EndOfDoc,
            0x80 => Exception,
            0xC0 => Padding,
            _ => unreachable!(),
        }
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
            ParsedDescriptor::Special(SpecialType::from_u8(ty))
        } else {
            ParsedDescriptor::Pair(DescriptorType::from_u8(ty), tag)
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
pub fn decode_u64<R : Read>(r: &mut R) -> io::Result<u64> {
    let mut accum = 0u64;
    let mut shift = 0;
    loop {
        let b = read_byte(r)?;
        let v = (b & 0x7F) as u64;
        // Since we accept denormalised integers, we also should accept
        // denormalised integers wider than 64 bits for forwards compatibility,
        // but this means being a bit more careful around shifting.
        if 0 != v {
            if shift >= 64 || v << shift >> shift != v {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData, "integer overflow"));
            }
            accum |= v << shift;
        }
        shift += 7;

        if 0 == (b & 0x80) {
            break;
        }

        // For forwards-compatibility, accept denormalised integers up to a
        // maximum length (even wider than 64 bits), but ensure we give up
        // eventually.
        if shift > 256 * 7 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData, "denormalised integer too wide"));
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

    w.write_all(&bytes[..n])
}

/// Encodes an unsigned 64-bit integer to the given output.
///
/// The integer is "fixed-width" in that it always occupies the full 10 bytes
/// regardless of its value. This allows in-place updates of the value while
/// still allowing `decode_u64` to understand it.
pub fn encode_fixed_u64<W : Write>(w: &mut W, mut i: u64) -> io::Result<()> {
    let mut bytes = [0u8;10];
    for n in 0..bytes.len() {
        bytes[n] = (i & 0x7F) as u8;
        i >>= 7;
        if n + 1 < bytes.len() {
            bytes[n] |= 0x80;
        }
    }

    w.write_all(&bytes)
}

/// Invert `zigzag`.
pub fn unzigzag(i: u64) -> i64 {
    let sign = if (i & 1) != 0 { !0u64 } else { 0 };
    ((i >> 1) ^ sign) as i64
}

/// Decode a 64-bit integer and then unZigZag it to a signed value.
pub fn decode_i64<R : Read>(r: &mut R) -> io::Result<i64> {
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

/// Read a descriptor from the given input.
pub fn decode_descriptor<R : Read>(r: &mut R)
                                   -> io::Result<Descriptor> {
    read_byte(r).map(Descriptor)
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

        test!(encode_fixed_u64, decode_u64, 0,
              [128, 128, 128, 128, 128, 128, 128, 128, 128, 0]);
        test!(encode_fixed_u64, decode_u64, 1,
              [129, 128, 128, 128, 128, 128, 128, 128, 128, 0]);
        test!(encode_fixed_u64, decode_u64, 256,
              [128, 130, 128, 128, 128, 128, 128, 128, 128, 0]);
        test!(encode_fixed_u64, decode_u64, u64::MAX,
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
    fn integer_decode_detects_overflow_in_overshifted_byte() {
        match decode_u64(&mut&[128, 128, 128, 128, 128,
                               128, 128, 128, 128, 128,
                               128, 128, 128, 128, 1][..]) {
            Ok(i) => panic!("Unexpectedly decoded {}", i),
            Err(e) => assert_eq!(io::ErrorKind::InvalidData, e.kind()),
        }
    }

    #[test]
    fn integer_decode_eventually_gives_up_decoding_denorm() {
        match decode_u64(&mut&[128u8;4096][..]) {
            Ok(i) => panic!("Unexpectedly decoded {}", i),
            Err(e) => assert_eq!(io::ErrorKind::InvalidData, e.kind()),
        }
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
}

//  LocalWords:  denormalised
