//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functionality for encoding and decoding a fourleaf stream in terms of
//! tag/value pairs.

use std::cmp::min;
use std::fmt;
use std::io::{self, BufRead, Read, Seek, Write};
use std::{i8, u8, i16, u16, i32, u32, i64, u64, isize, usize};

use wire::{self, DescriptorType, ParsedDescriptor, SpecialType};

/// A simple wrapper around `io::Cursor` which exposes `AsRef<[u8]>` and
/// `AsMut<[u8]>` for use with `Blob::slice()` and `Blob::slice_mut()`.
///
/// Note that the `AsRef` and `AsMut` implementations return the *unconsumed*
/// portion of the slice rather than the whole thing.
#[derive(Debug, Clone)]
pub struct TransparentCursor<T>(#[allow(missing_docs)] pub io::Cursor<T>);
impl<T : AsRef<[u8]>> Read for TransparentCursor<T> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

impl<T : AsRef<[u8]>> BufRead for TransparentCursor<T> {
    #[inline]
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        self.0.fill_buf()
    }
    #[inline]
    fn consume(&mut self, amt: usize) {
        self.0.consume(amt)
    }
}

impl<T> Write for TransparentCursor<T> where io::Cursor<T> : Write {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }
    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

impl<T : AsRef<[u8]>> Seek for TransparentCursor<T> {
    fn seek(&mut self, whence: io::SeekFrom) -> io::Result<u64> {
        self.0.seek(whence)
    }
}

impl<T : AsRef<[u8]>> AsRef<[u8]> for TransparentCursor<T> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        let pos = self.0.position() as usize;
        &self.0.get_ref().as_ref()[pos..]
    }
}

impl<T : AsMut<[u8]>> AsMut<[u8]> for TransparentCursor<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        let pos = self.0.position() as usize;
        &mut self.0.get_mut().as_mut()[pos..]
    }
}

#[derive(Clone, Copy)]
struct Nd<T>(T);
impl<T> fmt::Debug for Nd<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<?>")
    }
}

/// Streaming fourleaf parser and encoder.
///
/// The parser is built around pulling one tag/value pair at a time via
/// `next_field()`. While it automatically handles the format of tag/value
/// pairs and the special descriptors, it is unaware of the tree structure of
/// the document. For example, it will happily parse an infinite byte stream of
/// `EndOfStruct` values.
///
/// The reader used as input should be buffered if it is based on a heavyweight
/// resource like a file or socket handle, as many decoding operations will
/// read exactly one byte.
///
/// The position of the underlying reader is always immediately after the last
/// content read, unless any method call returns an `io::Error`, in which case
/// the exact position is unspecified and continued use of the stream will not
/// result in well-defined results.
#[derive(Debug)]
pub struct Stream<R> {
    inner: R,
    /// The current offset in `R` from where this stream started.
    pos: u64,
    /// Whether an `EndOfDoc` special descriptor was encountered.
    eof: bool,
    /// If there is a partially-consumed blob, the byte offset where it ends.
    blob_end: u64,
    /// Whether an EOF from the underlying input should be translated to an
    /// `EndOfDoc` descriptor.
    graceful_eof: bool,
    /// Function to use to skip `n` bytes in `input`. Returns the actual number
    /// of bytes skipped.
    skip: Nd<fn (inner: &mut Stream<R>, n: u64) -> io::Result<u64>>,
}

/// An element decoded from a fourleaf stream.
#[derive(Debug)]
pub enum Element<'d, R : 'd> {
    /// A normal tag/value pair representing a field.
    Field(Field<'d, R>),
    /// The end of the struct currently being decoded.
    EndOfStruct,
    /// An explicit end to the whole document, closing all structs being
    /// decoded.
    EndOfDoc,
    /// An exception inserted by the encoder. The blob is usually treated as an
    /// error message as sorts, but this could also be used for in-band
    /// signalling.
    Exception(Blob<'d, R>),
    /// A byte of padding.
    Padding,
}

/// A field decoded from a fourleaf stream.
#[derive(Debug)]
pub struct Field<'d, R : 'd> {
    /// The tag of this field, in the range 1..63, inclusive.
    pub tag: u8,
    /// The offset of this field in the stream. This specifically points to the
    /// byte containing the tag.
    pub pos: u64,
    /// The value of this field.
    pub value: Value<'d, R>,
}

/// A value of a decoded field.
#[derive(Debug)]
pub enum Value<'d, R : 'd> {
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
    Blob(Blob<'d, R>),
    /// The start of a child struct.
    ///
    /// This should be handled by "recursing" into the appropriate code to
    /// handle the struct, and from there continuing to use `next_value` on the
    /// `Stream` until it returns `None` to indicate the end of the child
    /// struct.
    Struct,
}

/// A handle to a blob within the fourleaf stream.
///
/// A `Blob` forwards `Read`, `Seek`, and `Write` implementations to the
/// underlying input to the stream, adapted to treat the `Blob` essentially as
/// a "file" of its own. Note that while one can make in-place writes to the
/// `Blob`, you cannot do anything that would change its size, such as writing
/// or seeking past the end.
#[derive(Debug)]
pub struct Blob<'d, R : 'd> {
    stream: &'d mut Stream<R>,
    len: u64,
}

/// Check that advancing `pos` by `n` will not cause overflow.
///
/// Generally, the inherent method on `Stream` should be used, but in a few
/// cases the borrow checker cannot accept that, so this global function can
/// be called instead.
fn check_advance_pos(pos: u64, n: u64) -> io::Result<()> {
    if u64::MAX - pos < n {
        Err(io::Error::new(
            io::ErrorKind::Other,
            "new position would be greater than u64::MAX"))
    } else {
        Ok(())
    }
}

#[derive(Debug)]
struct StreamTracker<'d, R : 'd>(&'d mut Stream<R>, bool);
impl<'d, R : Read> Read for StreamTracker<'d, R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.is_empty() { return Ok(0); }
        self.0.check_advance_pos(buf.len() as u64)?;

        let n = self.0.inner.read(buf)?;
        self.0.pos += n as u64;

        if 0 == n && self.1 {
            buf[0] = wire::SpecialType::EndOfDoc as u8;
            Ok(1)
        } else {
            Ok(n)
        }
    }
}
impl<'d, R : BufRead> BufRead for StreamTracker<'d, R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        self.0.fill_buf_nb()
    }

    fn consume(&mut self, amt: usize) {
        self.0.inner.consume(amt);
        self.0.pos += amt as u64;
    }
}
impl<'d, W : Write> Write for StreamTracker<'d, W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() { return Ok(0); }
        self.0.check_advance_pos(buf.len() as u64)?;

        let n = self.0.inner.write(buf)?;
        self.0.pos += n as u64;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.inner.flush()
    }
}

impl<R> Stream<R> {
    fn track<'d>(&'d mut self, graceful_eof: bool) -> StreamTracker<'d, R> {
        let graceful_eof = graceful_eof && self.graceful_eof;
        StreamTracker(self, graceful_eof)
    }

    fn check_advance_pos(&self, n: u64) -> io::Result<()> {
        check_advance_pos(self.pos, n)
    }
}

impl<T : AsRef<[u8]>> Stream<TransparentCursor<T>> {
    /// Create a new stream which decodes the given slice.
    pub fn from_slice(t: T) -> Self {
        Self::new_seek(TransparentCursor(io::Cursor::new(t)))
    }
}

impl<R : Read> Stream<R> {
    /// Create a new stream starting from byte offset 0.
    pub fn new(inner: R) -> Self {
        Stream {
            inner: inner,
            pos: 0,
            eof: false,
            blob_end: 0,
            graceful_eof: false,
            skip: Nd(Self::skip_by_discard),
        }
    }

    /// Like `new()`, but if the stream needs to skip a blob, it will use
    /// `seek()` instead of reading and discarding data.
    ///
    /// Once specialisation becomes stable, this method will likely be
    /// deprecated as detecting to use `seek()` will be determined
    /// automatically.
    pub fn new_seek(inner: R) -> Self where R : Seek {
        Stream {
            inner: inner,
            pos: 0,
            eof: false,
            blob_end: 0,
            graceful_eof: false,
            skip: Nd(Self::skip_by_seek),
        }
    }

    fn skip_by_discard(&mut self, n: u64) -> io::Result<u64> {
        io::copy(&mut self.track(false).take(n), &mut io::sink())
    }

    fn skip_by_seek(&mut self, n: u64) -> io::Result<u64> where R : Seek {
        // If the amount is to large to be passed to `SeekOffset:Current`, split
        // into smaller pieces. This is fine since we're allowed to fail partially.
        if n > (i64::MAX as u64) {
            let first = self.skip_by_seek(i64::MAX as u64)?;
            if first < (i64::MAX as u64) {
                Ok(first)
            } else {
                let second = self.skip_by_seek(n - first)?;
                Ok(first + second)
            }
        } else {
            // Otherwise, try to seek directly.
            self.check_advance_pos(n)?;
            if self.inner.seek(io::SeekFrom::Current(n as i64)).is_ok() {
                self.pos += n;
                Ok(n)
            } else {
                // If seeking failed (maybe the underlying file descriptor isn't
                // actually seekable?), fall back to read+discard.
                self.skip_by_discard(n)
            }
        }
    }

    /// Consumes this `Stream` and returns the underlying byte stream.
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Returns the current byte offset of the stream.
    pub fn pos(&self) -> u64 {
        self.pos
    }

    /// Changes the stream's current conception of the position in the byte
    /// stream.
    ///
    /// This should only be used if some operation outside the stream's
    /// control caused the position of the byte stream to actually change, as
    /// the stream will assume that other positions it maintains are still
    /// valid. It may also be used immediately after construction to change the
    /// starting offset value.
    ///
    /// To change the _logical_ position in the byte stream, use `reset_pos()`
    /// instead.
    pub fn set_pos(&mut self, pos: u64) {
        self.pos = pos;
    }

    /// Alters what this stream considers to be the logical position in the
    /// byte stream.
    ///
    /// This will cause the stream to flush any operations depending on the
    /// current position, and so can encounter IO errors.
    pub fn reset_pos(&mut self, pos: u64) -> io::Result<()> {
        self.skip_blob()?;
        self.blob_end = 0;
        self.pos = pos;
        Ok(())
    }

    /// Returns whether an `EndOfDoc` descriptor has been encountered.
    ///
    /// If this returns true, `next_field()` will always return `None`.
    pub fn eof(&self) -> bool {
        self.eof
    }

    /// Clears the EOF flag if it had been set by an `EndOfDoc` descriptor,
    /// allowing the stream to continue with whatever follows.
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
    /// start of a field), the stream acts as if it had encountered an
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
    pub fn next_field(&mut self) -> io::Result<Option<Field<R>>> {
        match self.next_element_impl(true)? {
            Element::Padding => unreachable!(),
            Element::EndOfStruct | Element::EndOfDoc => return Ok(None),
            Element::Field(field) => return Ok(Some(field)),
            Element::Exception(mut blob) => {
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
    pub fn next_element(&mut self) -> io::Result<Element<R>> {
        self.next_element_impl(false)
    }

    /// `next_element`, except that it allows implicitly skipping padding.
    ///
    /// This workaround is due to the limitations of lexical lifetimes;
    /// `next_field()` cannot loop over padding itself as the fact that it
    /// sometimes returns in the loop extends the loop borrows to the end of
    /// the function.
    fn next_element_impl(&mut self, skip_padding: bool)
                         -> io::Result<Element<R>> {
        if self.eof {
            return Ok(Element::EndOfDoc);
        }

        self.skip_blob()?;

        loop {
            let offset = self.pos;
            match wire::decode_descriptor(&mut self.track(true))?.parse() {
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
                  -> io::Result<Value<R>> {
        Ok(match ty {
            DescriptorType::Null => Value::Null,
            DescriptorType::Integer => Value::Integer(
                wire::decode_u64(&mut self.track(false))?),
            DescriptorType::Blob => Value::Blob(self.next_blob()?),
            DescriptorType::Struct => Value::Struct,
        })
    }

    fn next_blob(&mut self) -> io::Result<Blob<R>> {
        let len = wire::decode_u64(&mut self.track(false))?;
        self.check_advance_pos(len)?;

        self.blob_end = self.pos + len;
        Ok(Blob {
            stream: self,
            len: len,
        })
    }

    fn skip_blob(&mut self) -> io::Result<()> {
        if self.blob_end > self.pos {
            let n = self.blob_end - self.pos;
            let skipped = (self.skip.0)(self, n)?;
            if skipped < n {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "EOF reached before end of blob"));
            }
        }
        Ok(())
    }
}

impl<R : BufRead> Stream<R> {
    /// Like `BufRead::fill_buf()`. Exists here so that `Blob` can get a slice
    /// with the appropriate lifetime.
    fn fill_buf_nb(&mut self) -> io::Result<&[u8]> {
        let ret = self.inner.fill_buf()?;
        check_advance_pos(self.pos, ret.len() as u64)?;
        Ok(ret)
    }
}

impl<'d, R : 'd> Blob<'d, R> {
    /// Returns the size of this blob, in bytes.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns the number of unconsumed bytes in this blob.
    pub fn remaining(&self) -> u64 {
        self.stream.blob_end - self.stream.pos
    }

    /// Returns the current byte offset of the stream.
    pub fn stream_pos(&self) -> u64 {
        self.stream.pos
    }

    /// Returns the byte offset of the first byte in this blob (regardless of
    /// how much of the blob has been consumed).
    pub fn start_pos(&self) -> u64 {
        self.stream.blob_end - self.len
    }

    /// Returns the byte offset one past the last byte in this blob.
    pub fn end_pos(&self) -> u64 {
        self.stream.blob_end
    }

    /// Returns the current byte offset into this blob; i.e., the number of
    /// bytes that have been consumed.
    pub fn inner_pos(&self) -> u64 {
        self.len - self.remaining()
    }
}

impl<'d, R : Read + 'd> Blob<'d, R> {
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

impl<'d, R : AsRef<[u8]> + 'd> Blob<'d, R> {
    /// Returns a reference to the unconsumed bytes in this blob.
    ///
    /// This does not consume the blob.
    ///
    /// Returns `None` if the nominal length of the blob is larger than the
    /// underlying slice.
    pub fn slice(&self) -> Option<&[u8]> {
        let rem = self.remaining();
        let inner = self.stream.inner.as_ref();
        if rem <= (inner.len() as u64) {
            Some(&inner[..(rem as usize)])
        } else {
            None
        }
    }
}

impl<'d, R : AsMut<[u8]> + 'd> Blob<'d, R> {
    /// Returns a mutable reference to the unconsumed bytes in this blob.
    ///
    /// This does not consume the blob.
    ///
    /// The caller is free to manipulate the content of the blob arbitrarily;
    /// this will not corrupt the underlying data (but will obviously modify
    /// it).
    pub fn slice_mut(&mut self) -> Option<&mut [u8]> {
        let rem = self.remaining();
        let inner = self.stream.inner.as_mut();
        if rem <= (inner.len() as u64) {
            Some(&mut inner[..(rem as usize)])
        } else {
            None
        }
    }
}

impl<'d, R : Read + 'd> Read for Blob<'d, R> {
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

        let n = self.stream.track(false).read(buf)?;
        Ok(n)
    }
}

impl<'d, R : BufRead + 'd> BufRead for Blob<'d, R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let avail = min(usize::MAX as u64, self.remaining()) as usize;
        let ret = self.stream.fill_buf_nb()?;
        Ok(&ret[..min(avail, ret.len())])
    }
    fn consume(&mut self, amt: usize) {
        debug_assert!((amt as u64) <= self.remaining());
        self.stream.track(false).consume(amt)
    }
}

impl<'d, W : Write + 'd> Write for Blob<'d, W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let avail = min(buf.len(),
                        min(self.remaining(), usize::MAX as u64) as usize);

        self.stream.track(false).write(&buf[..avail])
    }

    fn flush(&mut self) -> io::Result<()> {
        self.stream.track(false).flush()
    }
}

impl<'d, R : Seek + 'd> Seek for Blob<'d, R> {
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
                check!(pos <= self.len);
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
                    self.stream_pos() - off
                } else {
                    let off = off as u64;
                    check!(off <= self.remaining());
                    self.stream_pos() + off
                }
            },
        };

        if pos < self.stream_pos() {
            let displacement = self.stream_pos() - pos;
            if displacement > (i64::MAX as u64) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Cannot seek blob by >= 8 EB at a time"));
            }
            self.stream.inner.seek(
                io::SeekFrom::Current(-(displacement as i64)))?;
            self.stream.pos -= displacement;
        } else {
            let displacement = pos - self.stream_pos();
            if displacement > (i64::MAX as u64) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Cannot seek blob by >= 8 EB at a time"));
            }
            self.stream.inner.seek(
                io::SeekFrom::Current(displacement as i64))?;
            self.stream.pos += displacement;
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

impl<'d, R : 'd> Value<'d, R> {
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
    pub fn to_blob(&mut self) -> Result<&mut Blob<'d, R>, &'static str> {
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
    use std::io::{self, BufRead, Read, Seek, Write};
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

    fn stream(text: &str) -> Stream<io::Cursor<Vec<u8>>> {
        Stream::new(io::Cursor::new(parse(text)))
    }

    #[test]
    fn simple() {
        let mut dec = stream("01 00");
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

        let mut dec = stream("41 00 42 01 43 80 01 00");
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
        let mut dec = stream("81 0B 'hello world' 00");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);

            let blob = field.value.to_blob().unwrap();
            assert_eq!(11, blob.len());
            assert_eq!(11, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.end_pos());
            assert_eq!(2, blob.stream_pos());
            assert_eq!(0, blob.inner_pos());

            let data = blob.read_fully(65536).unwrap();
            assert_eq!(b"hello world", &data[..]);

            assert_eq!(11, blob.len());
            assert_eq!(0, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.end_pos());
            assert_eq!(13, blob.stream_pos());
            assert_eq!(11, blob.inner_pos());
        }

        assert!(dec.next_field().unwrap().is_none());
    }

    #[test]
    fn read_partial_blob() {
        let mut dec = stream("81 0B 'hello world' 02 00");

        {
            let mut field = dec.next_field().unwrap().unwrap();
            let blob = field.value.to_blob().unwrap();

            let data4 = blob.read_or_trunc(4).unwrap();
            assert_eq!(b"hell", &data4[..]);

            assert_eq!(11, blob.len());
            assert_eq!(7, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.end_pos());
            assert_eq!(6, blob.stream_pos());
            assert_eq!(4, blob.inner_pos());

            let mut buf = [0u8;5];
            assert_eq!(5, blob.read(&mut buf).unwrap());
            assert_eq!(b"o wor", &buf[..]);

            assert_eq!(11, blob.len());
            assert_eq!(2, blob.remaining());
            assert_eq!(2, blob.start_pos());
            assert_eq!(13, blob.end_pos());
            assert_eq!(11, blob.stream_pos());
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
        let mut dec = stream("81 FFFFFF00");

        {
            let mut field = dec.next_field().unwrap().unwrap();
            let blob = field.value.to_blob().unwrap();

            assert!(blob.read_fully(256).is_err());
        }
    }

    #[test]
    fn read_nested_struct() {
        let mut dec = stream("C1 C2 00 C3 00 00");

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
        let mut dec = stream("C1 40 02");

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
        let mut dec = stream("01");
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
        let mut dec = stream("01");
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
        let mut dec = stream("01 C0 C0 C0 02");
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
        let mut dec = stream("80 05 'plugh' 01");

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

    #[test]
    fn read_overflow_detected() {
        let mut dec = stream("41 ff ff ff ff ff 00 00");
        dec.reset_pos(0xFFFFFFFFFFFFFFFA).unwrap();
        assert!(dec.next_field().is_err());
    }

    #[test]
    fn blob_access_overflow_detected() {
        let mut dec = stream("81 05 'plugh' 00");
        dec.reset_pos(0xFFFFFFFFFFFFFFFA).unwrap();
        assert!(dec.next_field().is_err());
    }

    #[test]
    fn reset_pos_skips_unconsumed_blob() {
        let mut dec = stream("81 05 'plugh' 02 00");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            field.value.to_blob().unwrap();
        }

        dec.reset_pos(0).unwrap();
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            field.value.to_null().unwrap();
            assert_eq!(0, field.pos);
        }
    }

    #[test]
    fn blob_seek() {
        let mut dec = stream("81 0B 'hello world' 02");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            let blob = field.value.to_blob().unwrap();

            assert_eq!(11, blob.len());
            assert_eq!(11, blob.remaining());
            assert_eq!(0, blob.inner_pos());
            assert_eq!(2, blob.start_pos());
            assert_eq!(2, blob.stream_pos());

            blob.seek(io::SeekFrom::Current(3)).unwrap();
            assert_eq!(11, blob.len());
            assert_eq!(8, blob.remaining());
            assert_eq!(3, blob.inner_pos());
            assert_eq!(5, blob.stream_pos());
            assert_eq!(b"lo world", &blob.read_fully(256).unwrap()[..]);

            blob.seek(io::SeekFrom::Start(6)).unwrap();
            assert_eq!(11, blob.len());
            assert_eq!(5, blob.remaining());
            assert_eq!(6, blob.inner_pos());
            assert_eq!(8, blob.stream_pos());
            assert_eq!(b"world", &blob.read_fully(256).unwrap()[..]);

            blob.seek(io::SeekFrom::Current(-3)).unwrap();
            assert_eq!(11, blob.len());
            assert_eq!(3, blob.remaining());
            assert_eq!(8, blob.inner_pos());
            assert_eq!(10, blob.stream_pos());
            assert_eq!(b"rld", &blob.read_fully(256).unwrap()[..]);

            blob.seek(io::SeekFrom::Start(3)).unwrap();

            assert!(blob.seek(io::SeekFrom::Start(12)).is_err());
            assert!(blob.seek(io::SeekFrom::Current(-4)).is_err());
            assert!(blob.seek(io::SeekFrom::Current(9)).is_err());
            assert!(blob.seek(io::SeekFrom::End(-12)).is_err());
            assert!(blob.seek(io::SeekFrom::End(1)).is_err());

            blob.seek(io::SeekFrom::Start(0)).unwrap();
            assert_eq!(11, blob.remaining());
            blob.seek(io::SeekFrom::Start(11)).unwrap();
            assert_eq!(0, blob.remaining());
            blob.seek(io::SeekFrom::End(-11)).unwrap();
            assert_eq!(11, blob.remaining());
            blob.seek(io::SeekFrom::End(0)).unwrap();
            assert_eq!(0, blob.remaining());
            blob.seek(io::SeekFrom::Start(5)).unwrap();
            blob.seek(io::SeekFrom::Current(-5)).unwrap();
            assert_eq!(11, blob.remaining());
            blob.seek(io::SeekFrom::End(-5)).unwrap();
            blob.seek(io::SeekFrom::Current(5)).unwrap();
            assert_eq!(0, blob.remaining());

            blob.seek(io::SeekFrom::Start(5)).unwrap();
            // Don't consume
        }

        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(13, field.pos);
            field.value.to_null().unwrap();
        }
    }

    #[test]
    fn blob_rewrite() {
        let mut dec = stream("81 0B 'hello world' 02");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            let blob = field.value.to_blob().unwrap();

            blob.seek(io::SeekFrom::Start(6)).unwrap();
            assert_eq!(5, blob.write(b"minnasama").unwrap());

            blob.seek(io::SeekFrom::Start(0)).unwrap();
            assert_eq!(b"hello minna", &blob.read_fully(256).unwrap()[..]);
        }

        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(13, field.pos);
            field.value.to_null().unwrap();
        }
    }

    #[test]
    fn blob_slicing() {
        let mut data = parse("81 0B 'hello world' 02");
        {
            let mut dec = Stream::from_slice(&mut data[..]);

            {
                let mut field = dec.next_field().unwrap().unwrap();
                assert_eq!(1, field.tag);
                let blob = field.value.to_blob().unwrap();

                assert_eq!(b"hello world", blob.slice().unwrap());
                assert_eq!(b"hello world", blob.slice_mut().unwrap());

                assert_eq!(b"hello ", &blob.read_or_trunc(6).unwrap()[..]);
                assert_eq!(b"world", blob.slice().unwrap());
                blob.slice_mut().unwrap()[0] = b'W';
                assert_eq!(b"World", blob.slice().unwrap());
            }

            {
                let field = dec.next_field().unwrap().unwrap();
                assert_eq!(2, field.tag);
                assert_eq!(13, field.pos);
                field.value.to_null().unwrap();
            }
        }

        let data2 = parse("81 0B 'hello World' 02");
        assert_eq!(data, data2);
    }

    #[test]
    fn blob_slice_oob() {
        let mut data = parse("81 0B 'plugh'");
        let mut dec = Stream::from_slice(&mut data[..]);
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            let blob = field.value.to_blob().unwrap();
            assert_eq!(11, blob.len());
            assert!(blob.slice().is_none());
            assert!(blob.slice_mut().is_none());
        }
    }

    #[test]
    fn blob_bufread() {
        let mut dec = stream("81 0B 'hello world' 02");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            let blob = field.value.to_blob().unwrap();

            assert_eq!(b"hello world", blob.fill_buf().unwrap());
            blob.consume(6);
            assert_eq!(6, blob.inner_pos());
            assert_eq!(8, blob.stream_pos());
            assert_eq!(5, blob.remaining());

            assert_eq!(b"world", blob.fill_buf().unwrap());
        }
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(13, field.pos);
            field.value.to_null().unwrap();
        }
    }
}
