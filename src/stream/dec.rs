//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functionality for decoding a fourleaf stream in terms of tag/value pairs.

use std::borrow::Cow;
use std::cmp::min;
use std::io::{self, Read};
use std::{i8, u8, i16, u16, i32, u32, i64, u64, isize, usize};

use wire::{self, Input, DescriptorType, ParsedDescriptor, SpecialType};

/// Streaming fourleaf parser.
///
/// The parser is built around pulling one tag/value pair at a time via
/// `next_field()`. While it automatically handles the format of tag/value
/// pairs and the special descriptors, it is unaware of the tree structure of
/// the document. For example, it will happily parse an infinite stream of
/// `EndOfStruct` values.
///
/// The reader used as input should be buffered if it is based on a heavyweight
/// resource like a file or socket handle, as many decoding operations will
/// read exactly one byte.
///
/// The position of the underlying reader is always immediately after the last
/// content read, unless any method call returns an `io::Error`, in which case
/// the exact position is unspecified and continued use of the decoder will not
/// result in well-defined results.
#[derive(Debug)]
pub struct Decoder<R> {
    input: R,
    /// The current offset in `R` from where this decoder started.
    pos: u64,
    /// Whether an `EndOfDoc` special descriptor was encountered.
    eof: bool,
    /// If there is a partially-consumed blob, the number of bytes remaining in
    /// that blob.
    in_blob: u64,
    /// Whether an EOF from the underlying input should be translated to an
    /// `EndOfDoc` descriptor.
    graceful_eof: bool,
}

/// A field decoded from a fourleaf stream.
#[derive(Debug)]
pub struct Field<D> {
    /// The tag of this field, in the range 1..63, inclusive.
    pub tag: u8,
    /// The offset of this field in the stream. This specifically points to the
    /// byte containing the tag.
    pub pos: u64,
    /// The value of this field.
    pub value: Value<D>,
}

/// A value of a decoded field.
#[derive(Debug)]
pub enum Value<D> {
    /// The null value.
    Null,
    /// General integer values. Conversion to things other than u64 can be
    /// achieved with the `to_<type>` methods.
    Integer(u64),
    /// A value which is a blob of bytes.
    ///
    /// The actual byte sequence has not been read in when the `Value`
    /// is returned. Instead, the `Blob` allows streaming the value out
    /// or obtaining the whole thing at once.
    Blob(Blob<D>),
    /// The start of a child struct.
    ///
    /// This should be handled by "recursing" into the appropriate code to
    /// handle the struct, and from there continuing to use `next_value` on the
    /// `Decoder` until it returns `None` to indicate the end of the child
    /// struct.
    Struct,
}

/// A handle to a blob within the fourleaf stream.
///
/// If the input to the decoder is `io::Read`, this is also `io::Read` and can
/// be used to read the content of the blob that way. Otherwise, `get()` must
/// be used to fetch the content.
///
/// If parsing untrusted input which is not already buffered into memory, you
/// will want to check `len()` first to make sure the blob has a reasonable
/// size before calling `get()`.
#[derive(Debug)]
pub struct Blob<D> {
    decoder: D,
    len: u64,
}

#[derive(Debug)]
struct DecoderInput<'d, R : 'd>(&'d mut Decoder<R>, bool);
impl<'d, 'a: 'd, R : Input<'a>> Input<'a> for DecoderInput<'d, R> {
    fn read_byte(&mut self) -> io::Result<u8> {
        if self.1 {
            self.read_byte_opt().map(|o| o.unwrap_or(
                wire::SpecialType::EndOfDoc as u8))
        } else {
            let byte = self.0.input.read_byte()?;
            self.0.pos += 1;
            Ok(byte)
        }
    }

    fn read_byte_opt(&mut self) -> io::Result<Option<u8>> {
        let r = self.0.input.read_byte_opt()?;
        if r.is_some() {
            self.0.pos += 1;
        }
        Ok(r)
    }

    fn read_bytes(&mut self, n: usize) -> io::Result<Cow<'a, [u8]>> {
        let bytes = self.0.input.read_bytes(n)?;
        self.0.pos += bytes.len() as u64;
        Ok(bytes)
    }

    fn skip(&mut self, n: usize) -> io::Result<usize> {
        let skipped = self.0.input.skip(n)?;
        self.0.pos += skipped as u64;
        Ok(skipped)
    }
}

impl<'a, R : Input<'a>> Decoder<R> {
    /// Create a new decoder starting from byte offset 0.
    pub fn new(input: R) -> Self {
        Self::new_at(input, 0)
    }

    /// Create a new decoder with the byte offset starting at the given value.
    ///
    /// Note that `offset` does not cause `input` to be seeked; rather, it
    /// simply sets the initial value for byte offset tracking.
    pub fn new_at(input: R, offset: u64) -> Self {
        Decoder {
            input: input,
            pos: offset,
            eof: false,
            in_blob: 0,
            graceful_eof: false,
        }
    }

    /// Consumes this `Decoder` and returns the underlying input.
    pub fn into_inner(self) -> R {
        self.input
    }

    /// Returns the current byte offset of the decoder.
    pub fn pos(&self) -> u64 {
        self.pos
    }

    /// Returns whether an `EndOfDoc` descriptor has been encountered.
    ///
    /// If this returns true, `next_field()` will always return `None`.
    pub fn eof(&self) -> bool {
        self.eof
    }

    /// Clears the EOF flag if it had been set by an `EndOfDoc` descriptor,
    /// allowing the decoder to continue with whatever follows.
    pub fn clear_eof(&mut self) {
        self.eof = false;
    }

    /// Returns whether graceful EOF handling is enabled.
    ///
    /// See `set_graceful_eof()` for an explanation.
    pub fn graceful_eof(&self) -> bool {
        self.graceful_eof
    }

    /// Sets whether an EOF where a descriptor is expected should be handled
    /// gracefully.
    ///
    /// If true, if an EOF is encountered when reading a descriptor (i.e., the
    /// start of a field), the decoder acts as if it had encountered an
    /// explicit `EndOfDoc` descriptor and returns `None` from `next_field()`
    /// and sets the EOF flag.
    ///
    /// If false, encountering an EOF when reading a descriptor results in an
    /// `UnexpectedEof` error.
    ///
    /// The default is false; i.e., inputs are expected to be explicitly
    /// terminated. Setting it to true is useful when working with append-only
    /// files which necessarily cannot have explicit termination.
    pub fn set_graceful_eof(&mut self, graceful_eof: bool) {
        self.graceful_eof = graceful_eof;
    }

    /// Decodes the next field.
    ///
    /// If the end of the current struct has been reached, returns `None`, but
    /// the next call will continue parsing the input. If the end of the
    /// document is reached, returns `None` without doing IO; this can be
    /// tested explicitly with the `eof()` method.
    ///
    /// Padding is implicitly skipped.
    ///
    /// If an error descriptor is encountered, up to 256 bytes of the message
    /// are read, converted to a string lossily, and returned as an error.
    /// Subsequent calls would continue in the stream immediately after the
    /// error message.
    ///
    /// If the field is a blob, it is not read in by this call. If the caller
    /// does not fully consume such a blob itself, the next call to
    /// `next_field` will do so.
    pub fn next_field(&mut self)
                      -> io::Result<Option<Field<&mut Self>>> {
        if self.eof {
            return Ok(None);
        }

        self.skip_blob()?;

        loop {
            let offset = self.pos;
            match wire::decode_descriptor(&mut self.input(true))?.parse() {
                ParsedDescriptor::Pair(ty, tag) =>
                    return Ok(Some(Field {
                        tag: tag,
                        pos: offset,
                        value: self.next_value(ty)?,
                    })),

                ParsedDescriptor::Special(SpecialType::EndOfStruct) =>
                    return Ok(None),

                ParsedDescriptor::Special(SpecialType::EndOfDoc) => {
                    self.eof = true;
                    return Ok(None);
                },

                ParsedDescriptor::Special(SpecialType::Error) => {
                    let message = self.next_blob()?.get_or_trunc(256)?;
                    return Err(io::Error::new(
                        io::ErrorKind::Other,
                        format!("Error message in stream: {}",
                                String::from_utf8_lossy(&message[..]))));
                },

                ParsedDescriptor::Special(SpecialType::Padding) => { },
            }
        }
    }

    fn next_value(&mut self, ty: DescriptorType)
                  -> io::Result<Value<&mut Self>> {
        Ok(match ty {
            DescriptorType::Null => Value::Null,
            DescriptorType::Integer => Value::Integer(
                wire::decode_u64(&mut self.input(false))?),
            DescriptorType::Blob => Value::Blob(self.next_blob()?),
            DescriptorType::Struct => Value::Struct,
        })
    }

    fn next_blob(&mut self) -> io::Result<Blob<&mut Self>> {
        let len = wire::decode_u64(&mut self.input(false))?;
        self.in_blob = len;
        Ok(Blob {
            decoder: self,
            len: len,
        })
    }

    fn input<'d>(&'d mut self, graceful_eof: bool) -> DecoderInput<'d, R> {
        let graceful_eof = graceful_eof && self.graceful_eof;
        DecoderInput(self, graceful_eof)
    }

    fn skip_blob(&mut self) -> io::Result<()> {
        while 0 != self.in_blob {
            let in_blob = self.in_blob;
            let skipped = self.input(false).skip(
                min(in_blob, usize::MAX as u64) as usize)? as u64;
            self.in_blob -= skipped;
        }
        Ok(())
    }
}

impl<'d, 'a : 'd, R : Input<'a>> Blob<&'d mut Decoder<R>> {
    /// Returns the size of this blob, in bytes.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns the number of unconsumed bytes in this blob.
    pub fn remaining(&self) -> u64 {
        self.decoder.in_blob
    }

    /// Returns the current byte offset of the decoder.
    pub fn decoder_pos(&self) -> u64 {
        self.decoder.pos
    }

    /// Returns the byte offset of the first byte in this blob (regardless of
    /// how much of the blob has been consumed).
    pub fn start_pos(&self) -> u64 {
        self.decoder.pos - (self.len - self.decoder.in_blob)
    }

    /// Returns the current byte offset into this blob; i.e., the number of
    /// bytes that have been consumed.
    pub fn inner_pos(&self) -> u64 {
        self.len - self.decoder.in_blob
    }

    /// Reads the full remaining value of this blob.
    ///
    /// If the underlying reader supports it, this simply returns a slice into
    /// the input buffer. Otherwise, the content of the blob is buffered into a
    /// `Vec<u8>` and that is returned.
    ///
    /// `max` indicates the maximum size of the blob to extract. If you fully
    /// trust the input or know that it is already fully buffered, one can
    /// simply use `usize::MAX`; for untrusted input, some value indicating the
    /// maximum reasonable allocation size should be given instead.
    ///
    /// If the length of this blob is larger than `max`, an error is returned.
    pub fn get(&mut self, max: usize) -> io::Result<Cow<'a, [u8]>> {
        if self.decoder.in_blob > (max as u64) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Blob length longer than maximum size"));
        }

        let ret = self.decoder.input(false).read_bytes(self.len as usize)?;
        self.decoder.in_blob -= ret.len() as u64;
        Ok(ret)
    }

    /// Reads up to `max` bytes of this blob.
    ///
    /// This mostly behaves like `get()`, except that if the blob is larger
    /// than `max`, it is implicitly truncated instead.
    ///
    /// If this does not read the full blob, it is still possible to read the
    /// remaining parts via further calls to methods on the blob.
    pub fn get_or_trunc(&mut self, max: usize) -> io::Result<Cow<'a, [u8]>> {
        let len = min(self.decoder.in_blob, max as u64) as usize;
        let ret = self.decoder.input(false).read_bytes(len)?;
        self.decoder.in_blob -= ret.len() as u64;
        Ok(ret)
    }
}

impl<'d, R : Read + 'd> Read for Blob<&'d mut Decoder<R>> {
    fn read(&mut self, mut buf: &mut [u8]) -> io::Result<usize> {
        if 0 == self.decoder.in_blob {
            return Ok(0);
        }

        let buf = if buf.len() as u64 > self.decoder.in_blob {
            &mut buf[..(self.decoder.in_blob as usize)]
        } else {
            buf
        };

        let n = self.decoder.input.read(buf)?;
        self.decoder.pos += n as u64;
        self.decoder.in_blob -= n as u64;
        Ok(n)
    }
}

macro_rules! to_int {
    ($meth:ident -> $t:ident, $zz:ident -> $long:ty) => {
        /// If this value is an integer, adjust it for signedness, check that
        /// it is in the valid range, and return it as the desired type.
        ///
        /// An error is returned if this value is not an integer, or is an
        /// integer but is out of range.
        pub fn $meth(&self) -> Result<$t, &'static str> {
            #[allow(unused_imports)]
            use wire::unzigzag;

            match *self {
                Value::Null => Err("Expected Integer, got Null"),
                Value::Blob(_) => Err("Expected Integer, got Blob"),
                Value::Struct => Err("Expected Integer, got Struct"),
                Value::Integer(v) => {
                    let v = $zz(v);
                    if v < ($t::MIN as $long) {
                        Err(concat!("Integer value is less than ",
                                    stringify!($t), "::MIN"))
                    } else if v > ($t::MAX as $long) {
                        Err(concat!("Integer value is greater than ",
                                    stringify!($t), "::MAX"))
                    } else {
                        Ok(v as $t)
                    }
                },
            }
        }
    }
}

fn id<T>(t: T) -> T { t }

impl<D> Value<D> {
    /// If this value is Null, return `()`. Otherwise, return an error message.
    pub fn to_null(&self) -> Result<(), &'static str> {
        match *self {
            Value::Null => Ok(()),
            Value::Integer(_) => Err("Expected Null, got Integer"),
            Value::Blob(_) => Err("Expected Null, got Blob"),
            Value::Struct => Err("Expected Null, got Struct"),
        }
    }

    /// If this value is a Struct, return `()`. Otherwise, return an error
    /// message.
    pub fn to_struct(&self) -> Result<(), &'static str> {
        match *self {
            Value::Struct => Ok(()),
            Value::Null => Err("Expected Struct, got Null"),
            Value::Integer(_) => Err("Expected Struct, got Integer"),
            Value::Blob(_) => Err("Expected Struct, got Blob"),
        }
    }

    to_int!(to_u8 -> u8, id -> u64);
    to_int!(to_i8 -> i8, unzigzag -> i64);
    to_int!(to_u16 -> u16, id -> u64);
    to_int!(to_i16 -> i16, unzigzag -> i64);
    to_int!(to_u32 -> u32, id -> u64);
    to_int!(to_i32 -> i32, unzigzag -> i64);
    to_int!(to_u64 -> u64, id -> u64);
    to_int!(to_i64 -> i64, unzigzag -> i64);
    to_int!(to_usize -> usize, id -> u64);
    to_int!(to_isize -> isize, unzigzag -> i64);

    /// If this value is an Integer, convert it to a bool.
    ///
    /// An error is returned if this value is not an integer, or if it is an
    /// integer not equal to 0 or 1.
    pub fn to_bool(&self) -> Result<bool, &'static str> {
        match self.to_u64()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err("Boolean value was neither 0 nor 1"),
        }
    }

    /// If this value is a Blob, return a reference to the blob.
    ///
    /// An error is returned if this value is not a blob.
    pub fn to_blob(&mut self) -> Result<&mut Blob<D>, &'static str> {
        match *self {
            Value::Blob(ref mut b) => Ok(b),
            Value::Null => Err("Expected Blob, got Null"),
            Value::Integer(_) => Err("Expected Blob, got Integer"),
            Value::Struct => Err("Expected Blob, got Struct"),
        }
    }
}

#[cfg(test)]
mod test {
    use std::io::{self, Read};
    use std::str;

    use super::*;

    fn decoder(text: &str) -> Decoder<io::Cursor<Vec<u8>>> {
        let mut data = Vec::new();

        fn decode_hexit(c: char) -> u8 {
            let n = c as u8;

            if c >= '0' && c <= '9' {
                (n - b'0')
            } else if c >= 'a' && c <= 'f' {
                (n - b'a' + 10) as u8
            } else if c >= 'A' && c <= 'F' {
                (n - b'A' + 10) as u8
            } else {
                panic!("Invalid hexit {}", c)
            }
        }

        let mut chars = text.chars();
        while let Some(first) = chars.next() {
            if ' ' == first {
                // ignore
            } else if '\'' == first {
                loop {
                    let c = chars.next().unwrap();
                    if '\'' == c {
                        break;
                    } else {
                        data.push(c as u8);
                    }
                }
            } else {
                data.push((decode_hexit(first) << 4) |
                          decode_hexit(chars.next().unwrap()));
            }
        }

        Decoder::new(io::Cursor::new(data))
    }

    #[test]
    fn simple() {
        let mut dec = decoder("01 00");
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(0, field.pos);
            field.value.to_null().unwrap();
        }

        assert!(dec.next_field().unwrap().is_none());

        match dec.next_field() {
            Ok(r) => panic!("next_field succeeded unexpectedly: {:?}", r),
            Err(e) => assert_eq!(io::ErrorKind::UnexpectedEof, e.kind()),
        }
    }

    #[test]
    fn decode_integers() {
        macro_rules! assert_all_ints_are {
            ($uv:expr, $iv:expr, $act:expr) => { {
                assert_eq!($uv, $act.value.to_u8().unwrap());
                assert_eq!($iv, $act.value.to_i8().unwrap());
                assert_eq!($uv, $act.value.to_u16().unwrap());
                assert_eq!($iv, $act.value.to_i16().unwrap());
                assert_eq!($uv, $act.value.to_u32().unwrap());
                assert_eq!($iv, $act.value.to_i32().unwrap());
                assert_eq!($uv, $act.value.to_u64().unwrap());
                assert_eq!($iv, $act.value.to_i64().unwrap());
                assert_eq!($uv, $act.value.to_usize().unwrap());
                assert_eq!($iv, $act.value.to_isize().unwrap());
            } }
        }

        let mut dec = decoder("41 00 42 01 43 80 01 00");
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(false, field.value.to_bool().unwrap());
            assert_all_ints_are!(0, 0, field);
        }
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(true, field.value.to_bool().unwrap());
            assert_all_ints_are!(1, -1, field);
        }
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(3, field.tag);
            assert!(field.value.to_bool().is_err());
            assert_all_ints_are!(128, 64, field);
        }

        assert!(dec.next_field().unwrap().is_none());
    }

    #[test]
    fn read_whole_blob() {
        let mut dec = decoder("81 0B 'hello world' 00");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);

            let blob = field.value.to_blob().unwrap();
            assert_eq!(11, blob.len());
            assert_eq!(11, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(2, blob.decoder_pos());
            assert_eq!(0, blob.inner_pos());

            let data = blob.get(65536).unwrap();
            assert_eq!(b"hello world", &data[..]);

            assert_eq!(11, blob.len());
            assert_eq!(0, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.decoder_pos());
            assert_eq!(11, blob.inner_pos());
        }

        assert!(dec.next_field().unwrap().is_none());
    }

    #[test]
    fn read_partial_blob() {
        let mut dec = decoder("81 0B 'hello world' 02 00");

        {
            let mut field = dec.next_field().unwrap().unwrap();
            let blob = field.value.to_blob().unwrap();

            let data4 = blob.get_or_trunc(4).unwrap();
            assert_eq!(b"hell", &data4[..]);

            assert_eq!(11, blob.len());
            assert_eq!(7, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(6, blob.decoder_pos());
            assert_eq!(4, blob.inner_pos());

            let mut buf = [0u8;5];
            assert_eq!(5, blob.read(&mut buf).unwrap());
            assert_eq!(b"o wor", &buf[..]);

            assert_eq!(11, blob.len());
            assert_eq!(2, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(11, blob.decoder_pos());
            assert_eq!(9, blob.inner_pos());

            // Drop the blob without fully consuming it
        }

        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(13, field.pos);
            field.value.to_null().unwrap();
        }

        assert!(dec.next_field().unwrap().is_none());
    }

    #[test]
    fn get_oversized_blob_fails() {
        let mut dec = decoder("81 FFFFFF00");

        {
            let mut field = dec.next_field().unwrap().unwrap();
            let blob = field.value.to_blob().unwrap();

            assert!(blob.get(256).is_err());
        }
    }

    #[test]
    fn read_nested_struct() {
        let mut dec = decoder("C1 C2 00 C3 00 00");

        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(0, field.pos);
            field.value.to_struct().unwrap();
        }
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(1, field.pos);
            field.value.to_struct().unwrap();
        }
        assert!(dec.next_field().unwrap().is_none());
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(3, field.tag);
            assert_eq!(3, field.pos);
            field.value.to_struct().unwrap();
        }
        assert!(dec.next_field().unwrap().is_none());
        assert!(dec.next_field().unwrap().is_none());
    }

    #[test]
    fn read_explicit_eof() {
        let mut dec = decoder("C1 40 02");

        {
            let field = dec.next_field().unwrap().unwrap();
            field.value.to_struct().unwrap();
        }
        assert!(dec.next_field().unwrap().is_none());
        assert!(dec.next_field().unwrap().is_none());
        assert!(dec.next_field().unwrap().is_none());
        assert_eq!(2, dec.pos());
        assert!(dec.eof());

        dec.clear_eof();
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(2, field.pos);
            field.value.to_null().unwrap();
        }
    }

    #[test]
    fn graceless_eof() {
        let mut dec = decoder("01");
        assert!(!dec.graceful_eof());
        {
            let field = dec.next_field().unwrap().unwrap();
            field.value.to_null().unwrap();
        }

        match dec.next_field() {
            Ok(f) => panic!("next_field succeeded unexpectedly: {:?}", f),
            Err(e) => assert_eq!(io::ErrorKind::UnexpectedEof, e.kind()),
        }
    }

    #[test]
    fn graceful_eof() {
        let mut dec = decoder("01");
        dec.set_graceful_eof(true);
        assert!(dec.graceful_eof());
        {
            let field = dec.next_field().unwrap().unwrap();
            field.value.to_null().unwrap();
        }

        assert!(dec.next_field().unwrap().is_none());
        assert!(dec.eof());
        assert_eq!(1, dec.pos());
    }

    #[test]
    fn padding_skipped() {
        let mut dec = decoder("01 C0 C0 C0 02");
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(0, field.pos);
            field.value.to_null().unwrap();
        }
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(4, field.pos);
            field.value.to_null().unwrap();
        }
    }

    #[test]
    fn read_inband_error() {
        let mut dec = decoder("80 05 'plugh' 01");

        match dec.next_field() {
            Ok(f) => panic!("next_field succeeded unexpectedly: {:?}", f),
            Err(e) => {
                let s = e.to_string();
                assert!(s.contains("plugh"));
            },
        }

        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(7, field.pos);
            field.value.to_null().unwrap();
        }
    }
}
