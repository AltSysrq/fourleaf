//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functionality for decoding a fourleaf stream in terms of tag/value pairs.

use std::io::{self, Read, Seek};
use std::{i8, u8, i16, u16, i32, u32, i64, u64, isize, usize};

use wire::{self, DescriptorType, ParsedDescriptor, SpecialType};

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
    /// If there is a partially-consumed blob, the byte offset where it ends.
    blob_end: u64,
    /// Whether an EOF from the underlying input should be translated to an
    /// `EndOfDoc` descriptor.
    graceful_eof: bool,
}

/// An element decoded from a fourleaf stream.
#[derive(Debug)]
pub enum Element<D> {
    /// A normal tag/value pair representing a field.
    Field(Field<D>),
    /// The end of the struct currently being decoded.
    EndOfStruct,
    /// An explicit end to the whole document, closing all structs being
    /// decoded.
    EndOfDoc,
    /// An exception inserted by the encoder. The blob is usually treated as an
    /// error message as sorts, but this could also be used for in-band
    /// signalling.
    Exception(Blob<D>),
    /// A byte of padding.
    Padding,
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
impl<'d, R : Read> Read for DecoderInput<'d, R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.is_empty() { return Ok(0); }

        let n = self.0.input.read(buf)?;
        self.0.pos += n as u64;

        if 0 == n && self.1 {
            buf[0] = wire::SpecialType::EndOfDoc as u8;
            Ok(1)
        } else {
            Ok(n)
        }
    }
}

impl<R : Read> Decoder<R> {
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
            blob_end: 0,
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
    /// If an exception descriptor is encountered, up to 256 bytes of the
    /// message are read, converted to a string lossily, and returned as an
    /// error. Subsequent calls would continue in the stream immediately after
    /// the error message.
    ///
    /// If the field is a blob, it is not read in by this call. If the caller
    /// does not fully consume such a blob itself, the next call to
    /// `next_field` will do so.
    ///
    /// If you want to use padding or exceptions as in-band signalling, see
    /// `next_element()` instead.
    pub fn next_field(&mut self)
                      -> io::Result<Option<Field<&mut Self>>> {
        match self.next_element_impl(true)? {
            Element::Padding => unreachable!(),
            Element::EndOfStruct | Element::EndOfDoc => return Ok(None),
            Element::Field(field) => return Ok(Some(field)),
            Element::Exception(blob) => {
                // XXX If we don't explicitly give `blob` a type here, rustc
                // seems to think that `'a` is a free lifetime.
                let mut blob: Blob<&mut Decoder<R>> = blob;
                let message = blob.read_or_trunc(256)?;
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("Error message in stream: {:?}",
                            String::from_utf8_lossy(&message[..]))));
            },
        }
    }

    /// Reads the next element from the stream.
    ///
    /// This is lower-level than `next_field()`, since will return padding,
    /// does not convert exceptions to errors, and distinguishes between
    /// end-of-struct and end-of-document conditions.
    ///
    /// If the `eof()` flag is set, this returns `Element::EndOfDoc` without
    /// reading anything.
    ///
    /// If this call returns `Element::EndOfDoc`, the `eof()` flag is
    /// implicitly set.
    pub fn next_element(&mut self)
                        -> io::Result<Element<&mut Self>> {
        self.next_element_impl(false)
    }

    /// `next_element`, except that it allows implicitly skipping padding.
    ///
    /// This workaround is due to the limitations of lexical lifetimes;
    /// `next_field()` cannot loop over padding itself as the fact that it
    /// sometimes returns in the loop extends the loop borrows to the end of
    /// the function.
    fn next_element_impl(&mut self, skip_padding: bool)
                         -> io::Result<Element<&mut Self>> {
        if self.eof {
            return Ok(Element::EndOfDoc);
        }

        self.skip_blob()?;

        loop {
            let offset = self.pos;
            match wire::decode_descriptor(&mut self.input(true))?.parse() {
                ParsedDescriptor::Pair(ty, tag) =>
                    return Ok(Element::Field(Field {
                        tag: tag,
                        pos: offset,
                        value: self.next_value(ty)?,
                    })),

                ParsedDescriptor::Special(SpecialType::EndOfStruct) =>
                    return Ok(Element::EndOfStruct),

                ParsedDescriptor::Special(SpecialType::EndOfDoc) => {
                    self.eof = true;
                    return Ok(Element::EndOfDoc);
                },

                ParsedDescriptor::Special(SpecialType::Exception) =>
                    return Ok(Element::Exception(self.next_blob()?)),

                ParsedDescriptor::Special(SpecialType::Padding) => {
                    if skip_padding {
                        continue;
                    } else {
                        return Ok(Element::Padding);
                    }
                },
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
        self.blob_end = self.pos + len;
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
        if self.blob_end > self.pos {
            let n = self.blob_end - self.pos;
            // TODO Optimise for `Seek` inputs.
            let skipped = io::copy(&mut self.input(false).take(n),
                                   &mut io::sink())?;
            if skipped < n {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "EOF reached before end of blob"));
            }
        }
        Ok(())
    }
}

impl<'d, R : 'd> Blob<&'d mut Decoder<R>> {
    /// Returns the size of this blob, in bytes.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns the number of unconsumed bytes in this blob.
    pub fn remaining(&self) -> u64 {
        self.decoder.blob_end - self.decoder.pos
    }

    /// Returns the current byte offset of the decoder.
    pub fn decoder_pos(&self) -> u64 {
        self.decoder.pos
    }

    /// Returns the byte offset of the first byte in this blob (regardless of
    /// how much of the blob has been consumed).
    pub fn start_pos(&self) -> u64 {
        self.decoder.blob_end - self.len
    }

    /// Returns the byte offset one past the last byte in this blob.
    pub fn end_pos(&self) -> u64 {
        self.decoder.blob_end
    }

    /// Returns the current byte offset into this blob; i.e., the number of
    /// bytes that have been consumed.
    pub fn inner_pos(&self) -> u64 {
        self.len - self.remaining()
    }
}

impl<'d, R : Read + 'd> Blob<&'d mut Decoder<R>> {
    /// Reads the full remaining value of this blob.
    ///
    /// The content of the blob is buffered into a `Vec<u8>` and that is
    /// returned. If you are decoding a byte slice, consider using `slice()`
    /// instead, which will not need to copy the blob.
    ///
    /// `max` indicates the maximum size of the blob to extract. If you fully
    /// trust the input or know that it is already fully buffered, one can
    /// simply use `usize::MAX`; for untrusted input, some value indicating the
    /// maximum reasonable allocation size should be given instead.
    ///
    /// If the length of this blob is larger than `max`, an error is returned.
    pub fn read_fully(&mut self, max: usize) -> io::Result<Vec<u8>> {
        if self.remaining() > (max as u64) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Blob length longer than maximum size"));
        }

        let mut ret = Vec::new();
        self.read_to_end(&mut ret)?;
        Ok(ret)
    }

    /// Reads up to `max` bytes of this blob.
    ///
    /// This mostly behaves like `read_fully()`, except that if the blob is
    /// larger than `max`, it is implicitly truncated instead.
    ///
    /// If this does not read the full blob, it is still possible to read the
    /// remaining parts via further calls to methods on the blob.
    pub fn read_or_trunc(&mut self, max: usize) -> io::Result<Vec<u8>> {
        let mut ret = Vec::new();
        self.take(max as u64).read_to_end(&mut ret)?;
        Ok(ret)
    }
}

impl<'d, R : AsRef<[u8]>> Blob<&'d mut Decoder<R>> {
    /// Returns a reference to the unconsumed bytes in this blob.
    ///
    /// This does not consume the blob.
    ///
    /// Returns `None` if the nominal length of the blob is larger than the
    /// underlying slice.
    pub fn slice(&self) -> Option<&[u8]> {
        let rem = self.remaining();
        let input = self.decoder.input.as_ref();
        if rem <= (input.len() as u64) {
            Some(&input[..(rem as usize)])
        } else {
            None
        }
    }
}

impl<'d, R : AsMut<[u8]>> Blob<&'d mut Decoder<R>> {
    /// Returns a mutable reference to the unconsumed bytes in this blob.
    ///
    /// This does not consume the blob.
    ///
    /// The caller is free to manipulate the content of the blob arbitrarily;
    /// this will not corrupt the underlying file.
    pub fn slice_mut(&mut self) -> Option<&mut [u8]> {
        let rem = self.remaining();
        let input = self.decoder.input.as_mut();
        if rem <= (input.len() as u64) {
            Some(&mut input[..(rem as usize)])
        } else {
            None
        }
    }
}

impl<'d, R : Read + 'd> Read for Blob<&'d mut Decoder<R>> {
    fn read(&mut self, mut buf: &mut [u8]) -> io::Result<usize> {
        let remaining = self.remaining();

        if 0 == remaining {
            return Ok(0);
        }

        let buf = if buf.len() as u64 > remaining {
            &mut buf[..(remaining as usize)]
        } else {
            buf
        };

        let n = self.decoder.input(false).read(buf)?;
        Ok(n)
    }
}

impl<'d, R : Seek + 'd> Seek for Blob<&'d mut Decoder<R>> {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        macro_rules! check {
            ($cond:expr) => { if !($cond) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "seek out of blob bounds"));
            } }
        }

        let pos = match pos {
            io::SeekFrom::Start(pos) => {
                check!(pos <= self.len());
                self.start_pos() + pos
            },
            io::SeekFrom::End(off) => {
                check!(off <= 0);
                let off = (-off) as u64;
                check!(off <= self.len);
                self.start_pos() + (self.len - off)
            },
            io::SeekFrom::Current(off) => {
                if off < 0 {
                    let off = (-off) as u64;
                    check!(off <= self.inner_pos());
                    self.decoder_pos() - off
                } else {
                    let off = off as u64;
                    check!(off <= self.remaining());
                    self.decoder_pos() + off
                }
            },
        };

        if pos < self.decoder_pos() {
            let displacement = self.decoder_pos() - pos;
            if pos > (i64::MAX as u64) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Cannot seek blob by >= 8 EB at a time"));
            }
            self.decoder.input.seek(
                io::SeekFrom::Current(-(displacement as i64)))?;
            self.decoder.pos -= displacement;
        } else {
            let displacement = pos - self.decoder_pos();
            if pos > (i64::MAX as u64) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Cannot seek blob by >= 8 EB at a time"));
            }
            self.decoder.input.seek(
                io::SeekFrom::Current(displacement as i64))?;
            self.decoder.pos += displacement;
        }

        Ok(self.inner_pos())
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

    fn parse(text: &str) -> Vec<u8> {
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

        data
    }

    fn decoder(text: &str) -> Decoder<io::Cursor<Vec<u8>>> {
        Decoder::new(io::Cursor::new(parse(text)))
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
            assert_eq!(13, blob.end_pos());
            assert_eq!(2, blob.decoder_pos());
            assert_eq!(0, blob.inner_pos());

            let data = blob.read_fully(65536).unwrap();
            assert_eq!(b"hello world", &data[..]);

            assert_eq!(11, blob.len());
            assert_eq!(0, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.end_pos());
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

            let data4 = blob.read_or_trunc(4).unwrap();
            assert_eq!(b"hell", &data4[..]);

            assert_eq!(11, blob.len());
            assert_eq!(7, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.end_pos());
            assert_eq!(6, blob.decoder_pos());
            assert_eq!(4, blob.inner_pos());

            let mut buf = [0u8;5];
            assert_eq!(5, blob.read(&mut buf).unwrap());
            assert_eq!(b"o wor", &buf[..]);

            assert_eq!(11, blob.len());
            assert_eq!(2, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.end_pos());
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

            assert!(blob.read_fully(256).is_err());
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
