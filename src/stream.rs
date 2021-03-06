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

use io::{AsExtBytes, TransparentCursor};
use wire::{self, DescriptorType, ParsedDescriptor, SpecialType};

#[derive(Clone, Copy)]
struct Nd<T>(T);
impl<T> fmt::Debug for Nd<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<?>")
    }
}

quick_error! {
    /// Errors which may be encountered when operating on a `Stream`.
    #[derive(Debug)]
    pub enum Error {
        /// An IO error occurred on the underlying byte stream.
        Io(err: io::Error) {
            from()
            cause(err)
            description(err.description())
        }
        /// An integer was encountered that was larger than the maximum bit
        /// width supported by this implementation.
        IntegerOverflow {
            description("integer overflow")
        }
        /// An integer (possibly in denormalised form) was encountered which
        /// was rejected as being excessively wide, even though it did not
        /// overflow the implementation's maximum bit width in the prefix that
        /// was examined.
        OverwideInteger {
            description("encoded integer too wide")
        }
        /// An exception element was encountered in the stream and was handled
        /// by interpreting it as an error message.
        Exception(msg: String) {
            description("error message in stream")
            display("error message in stream: {}", msg)
        }
        /// A blob element was found upon reading to have a declared length
        /// larger than the rest of the stream.
        TruncatedBlob(bytes_remaining: u64) {
            description("blob extends beyond EOF")
            display("blob extends beyond EOF ({} bytes remaining)",
                    bytes_remaining)
        }
        /// A blob would be read or written that would result in an end
        /// position greater than `u64::MAX`.
        OverlongBlob {
            description("blob length too long")
        }
        /// When writing to a stream, the writer allocated a blob of a fixed
        /// length but did not fully write it.
        ///
        /// This error will also happen if the writer seeks the position in the
        /// blob to a location other than the end and then tries to continue
        /// using the `Stream`.
        IncompleteBlob(bytes_remaining: u64) {
            description("blob not fully written")
            display("blob not fully written ({} bytes remaining)",
                    bytes_remaining)
        }
        /// The writer started a dynamic blob, but then repositioned the stream
        /// to before the start of the blob.
        ///
        /// This should not ordinarily be possible without using methods like
        /// `stream_get_mut` and `set_stream_pos` on the blob to bypass the
        /// abstraction.
        PositionBeforeStartOfDynamicBlob {
            description("stream position moved before start of dynamic blob")
        }
        /// The writer created a dynamic blob and wrote more than `i64::MAX`
        /// bytes to it.
        OverlongDynamicBlob {
            description("dynamic blob length exceeds i64::MAX")
        }
        /// A reader requested to read a blob up to some maximum size, but the
        /// remaining size of the blob is greater than that.
        LargeBlob(max: usize, remaining: u64) {
            description("blob exceeds maximum requested size")
            display("blob (size {}) exceeds maximum requested size ({})",
                    remaining, max)
        }
        /// A conversion method was called on a `Value` which was not of the
        /// type the caller expected.
        UnexpectedType(expected: &'static str, actual: &'static str) {
            description("unexpected field type")
            display("expected field type {}, got {}", expected, actual)
        }
        /// A conversion method was called on a `Value` which held an integer,
        /// but that integer was out of the legal range for the desired type.
        IntegerOutOfRange(message: &'static str) {
            description(message)
            display("{}", message)
        }
        #[doc(hidden)]
        #[allow(missing_docs)]
        _NonExhaustive { }
    }
}

/// General result type returned by `Stream`.
pub type Result<T> = ::std::result::Result<T, Error>;

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
/// content read, unless any method call returns an `Error`, in which case the
/// exact position is unspecified and continued use of the stream will not
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
    /// If there is an uncommitted dynamic blob, the byte offset where it
    /// starts.
    dynamic_blob_start: u64,
    /// The current struct nesting depth. 0 = true top-level. Incremented by
    /// `Struct` and `Enum` elements; decremented by `EndOfStruct`, set to 0 by
    /// `EndOfDoc`. Additionally, the a pair read when this is equal to 0
    /// increments it (since the start of the top-level struct is implicit).
    struct_depth: u64,
    /// Whether an EOF from the underlying input should be translated to an
    /// `EndOfDoc` descriptor.
    graceful_eof: bool,
    /// `Seek::seek` on `inner` if known.
    seek: Option<Nd<fn (inner: &mut R, whence: io::SeekFrom)
                        -> io::Result<u64>>>,
    /// If `Some`, an operation that must be called on `self` to bring the
    /// stream into a consistent state.
    commit: Option<Nd<fn (&mut Stream<R>) -> Result<()>>>,
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
    /// The struct nesting depth of this field in the stream. Always at least
    /// 1. See also `Stream::struct_depth()`.
    ///
    /// Note that even for `Struct`s and `Enum`s, this is the depth of the
    /// field itself, and not its contents, whereas immediately after reading
    /// such a field the value of `Stream::struct_depth()` will reflect the
    /// depth of the contents.
    pub depth: u64,
    /// The value of this field.
    pub value: Value<'d, R>,
}

/// A value of a decoded field.
#[derive(Debug)]
pub enum Value<'d, R : 'd> {
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
    ///
    /// This contains a reference back to the `Stream` that read the tag to
    /// simplify recursive deserialisers.
    Struct(&'d mut Stream<R>),
    /// An enumeration with the given discriminant. The struct body of the enum
    /// is accessible via the embedded `Stream` the same way as for `Struct`.
    Enum(u64, &'d mut Stream<R>),
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

impl<T : AsRef<[u8]>> Stream<TransparentCursor<T>> {
    /// Create a new stream which decodes the given slice.
    ///
    /// To use the most flexible zero-copy APIs, `t` should be a `&[u8]`.
    pub fn from_slice(t: T) -> Self {
        Self::new_seek(TransparentCursor(io::Cursor::new(t)))
    }
}

macro_rules! write_int {
    ($name:ident, $t:ty, $conv:ident, $t2:ty) => {
        /// Writes a field with the given integer value to the output.
        ///
        /// ## Panics
        ///
        /// Panics if `tag` is not a valid field tag.
        pub fn $name(&mut self, tag: u8, n: $t) -> Result<()>
        where R : Write {
            #[allow(unused_imports)]
            use wire::zigzag;

            self.write_u64(tag, $conv(n as $t2))
        }
    }
}

impl<R> Stream<R> {
    /// Create a new stream starting from byte offset 0.
    pub fn new(inner: R) -> Self {
        Stream {
            inner: inner,
            pos: 0,
            eof: false,
            blob_end: 0,
            dynamic_blob_start: 0,
            struct_depth: 0,
            graceful_eof: false,
            seek: None,
            commit: None,
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
            dynamic_blob_start: 0,
            struct_depth: 0,
            graceful_eof: false,
            seek: Some(Nd(<R as Seek>::seek)),
            commit: None,
        }
    }

    fn skip_by_discard(&mut self, n: u64) -> Result<u64>
    where R : Read {
        Ok(io::copy(&mut self.track(false).take(n), &mut io::sink())?)
    }

    fn skip_by_seek(&mut self, n: u64,
                    seek: fn (&mut R, io::SeekFrom) ->
                             io::Result<u64>)
                    -> Result<u64>
    where R : Read {
        // If the amount is to large to be passed to `SeekFrom:Current`, split
        // into smaller pieces. This is fine since we're allowed to fail partially.
        if n > (i64::MAX as u64) {
            let first = self.skip_by_seek(i64::MAX as u64, seek)?;
            if first < (i64::MAX as u64) {
                Ok(first)
            } else {
                let second = self.skip_by_seek(n - first, seek)?;
                Ok(first + second)
            }
        } else {
            // Otherwise, try to seek directly.
            self.check_advance_pos(n)?;
            if seek(&mut self.inner, io::SeekFrom::Current(n as i64)).is_ok() {
                self.pos += n;
                Ok(n)
            } else {
                // If seeking failed (maybe the underlying file descriptor isn't
                // actually seekable?), fall back to read+discard.
                self.skip_by_discard(n)
            }
        }
    }

    /// Ensures the `Stream` is in a fully consistent state.
    ///
    /// It is usually not necessary to call this except in very particular
    /// circumstances before closing a write stream, or when performing
    /// operations at a level lower than the `Stream` abstraction.
    ///
    /// Calls to `Stream` which read or write data will implicitly commit
    /// changes that occurred before that call.
    pub fn commit(&mut self) -> Result<()> {
        if let Some(Nd(f)) = self.commit {
            f(self)?;
            self.commit = None;
        }
        Ok(())
    }

    /// Consumes this `Stream` and returns the underlying byte stream.
    ///
    /// The byte stream is simply returned at whatever its current position is,
    /// which could be inside a blob. Use `commit()` to ensure the stream is
    /// positioned on a field boundary if that is desired.
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Borrows a reference to the underlying byte stream.
    ///
    /// This is mainly intended for things like syncing a file handle. If the
    /// intent is to do things that depend on the stream position, consider
    /// whether `commit()` should be called (depending on whether being in the
    /// middle of a blob is reasonable/desired). If the use of the byte stream
    /// causes the stream to be repositioned, ensure that `set_pos()` is later
    /// called to inform the `Stream` of this fact.
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Borrows a reference to the underlying byte stream.
    ///
    /// This is mainly intended for things like syncing a file handle. If the
    /// intent is to do things that depend on the stream position, consider
    /// whether `commit()` should be called (depending on whether being in the
    /// middle of a blob is reasonable/desired). If the use of the byte stream
    /// causes the stream to be repositioned, ensure that `set_pos()` is later
    /// called to inform the `Stream` of this fact.
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Returns the current byte offset of the stream.
    pub fn pos(&self) -> u64 {
        self.pos
    }

    /// Changes the stream's current conception of the position in the byte
    /// stream.
    ///
    /// This should only be used if some operation outside the `Stream`'s
    /// control caused the position of the byte stream to actually change
    /// (e.g., via use of `get_mut`), as the stream will assume that other
    /// positions it maintains are still valid. It may also be used immediately
    /// after construction to change the starting offset value.
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
    pub fn reset_pos(&mut self, pos: u64) -> Result<()> {
        self.commit()?;
        self.blob_end = 0;
        self.dynamic_blob_start = 0;
        self.pos = pos;
        Ok(())
    }

    /// Repositions the `Stream` according to `whence`.
    ///
    /// This is not `std::io::Seek` because it has somewhat different
    /// semantics; in particular, the stream's current position may be changed
    /// by this call before the seek operation itself is applied, and the
    /// operation will be applied relative to that position.
    ///
    /// It is the caller's responsibility to ensure that the new location is
    /// sensible; i.e., that the byte location points to a descriptor in the
    /// underlying byte stream.
    ///
    /// This resets the struct depth counter to 0. If this is not correct, it
    /// is the callers responsibility to call `set_struct_depth` to the correct
    /// value if features depending on struct depth tracking are being used.
    ///
    /// The `Stream`'s own `pos` is set to match what the underlying byte
    /// stream returns. If the client code is using a logical `pos` which
    /// differs from the underlying stream position, the caller will need to
    /// fix the discrepancy by calling `reset_pos()` afterwards.
    pub fn seek(&mut self, whence: io::SeekFrom) -> Result<u64>
    where R : Seek {
        self.commit()?;
        let off = self.inner.seek(whence)?;
        self.reset_pos(off)?;
        self.struct_depth = 0;
        Ok(off)
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

    /// Returns the current struct nesting depth of this stream.
    ///
    /// This specifically counts the number of `EndOfStruct` elements required
    /// to return to top-level. If the input causes the counter to overflow, it
    /// simply saturates at 0.
    ///
    /// Initially, the struct depth is set to 0. Upon reading a field of any
    /// kind, it becomes 1. `Struct` and `Enum` fields further increment this
    /// value, and corresponding `EndOfStruct` elements decrement it.
    /// `EndOfDoc` elements immediately set it to 0.
    ///
    /// `Stream` does not guarantee any particular behaviour if this counter
    /// overflows. Note that this is normally impossible, since such an input
    /// would also need to be greater than the maximum input length `Stream`
    /// can handle.
    ///
    /// The struct depth is only tracked for read operations, since it is
    /// intended for recovering from errors or skipping unknown items. For this
    /// reason the `Read` constraint is present, even though this call itself
    /// does not do any IO.
    pub fn struct_depth(&self) -> u64 where R : Read {
        self.struct_depth
    }

    /// Resets the struct depth counter.
    ///
    /// Generally, the only reason to call this is if the caller caused the
    /// position of the underlying stream to change and wishes to correct the
    /// counter, or in other extraordinary circumstances.
    pub fn set_struct_depth(&mut self, depth: u64) {
        self.struct_depth = depth;
    }

    fn track<'d>(&'d mut self, graceful_eof: bool) -> StreamTracker<'d, R> {
        let graceful_eof = graceful_eof && self.graceful_eof;
        StreamTracker(self, graceful_eof)
    }

    fn check_advance_pos(&self, n: u64) -> io::Result<()> {
        check_advance_pos(self.pos, n)
    }

    /// Decodes and discards input elements until the struct nesting depth is
    /// less than or equal to the given depth or an error occurs.
    ///
    /// This can be used to easily skip unknown fields, or to handle
    /// recoverable errors by moving to the next top-level item.
    ///
    /// See `struct_depth` for details on how struct depth is tracked.
    pub fn skip_up(&mut self, depth: u64) -> Result<()>
    where R : Read {
        while self.struct_depth > depth {
            self.next_element()?;
        }
        Ok(())
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
    pub fn next_field(&mut self) -> Result<Option<Field<R>>>
    where R : Read {
        match self.next_element_impl(true)? {
            Element::Padding => unreachable!(),
            Element::EndOfStruct | Element::EndOfDoc => return Ok(None),
            Element::Field(field) => return Ok(Some(field)),
            Element::Exception(mut blob) => {
                let message = blob.read_or_trunc(256)?;
                return Err(Error::Exception(
                    String::from_utf8_lossy(&message[..]).into_owned()));
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
    pub fn next_element(&mut self) -> Result<Element<R>>
    where R : Read {
        self.next_element_impl(false)
    }

    /// `next_element`, except that it allows implicitly skipping padding.
    ///
    /// This workaround is due to the limitations of lexical lifetimes;
    /// `next_field()` cannot loop over padding itself as the fact that it
    /// sometimes returns in the loop extends the loop borrows to the end of
    /// the function.
    fn next_element_impl(&mut self, skip_padding: bool)
                         -> Result<Element<R>>
    where R : Read {
        if self.eof {
            return Ok(Element::EndOfDoc);
        }

        self.commit()?;

        loop {
            let offset = self.pos;
            match wire::decode_descriptor(&mut self.track(true))?.parse() {
                ParsedDescriptor::Pair(ty, tag) => {
                    if 0 == self.struct_depth {
                        self.struct_depth = 1;
                    }
                    return Ok(Element::Field(Field {
                        tag: tag,
                        pos: offset,
                        depth: self.struct_depth,
                        value: self.next_value(ty)?,
                    }))
                },

                ParsedDescriptor::Special(SpecialType::EndOfStruct) => {
                    if self.struct_depth > 0 {
                        self.struct_depth -= 1;
                    }
                    return Ok(Element::EndOfStruct);
                },

                ParsedDescriptor::Special(SpecialType::EndOfDoc) => {
                    self.eof = true;
                    self.struct_depth = 0;
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
                  -> Result<Value<R>>
    where R : Read {
        Ok(match ty {
            DescriptorType::Integer => Value::Integer(
                wire::decode_u64(&mut self.track(false))?),
            DescriptorType::Blob => Value::Blob(self.next_blob()?),
            DescriptorType::Struct => {
                self.struct_depth += 1;
                Value::Struct(self)
            },
            DescriptorType::Enum => {
                let discriminant = wire::decode_u64(&mut self.track(false))?;
                self.struct_depth += 1;
                Value::Enum(discriminant, self)
            },
        })
    }

    fn next_blob(&mut self) -> Result<Blob<R>>
    where R : Read {
        let len = wire::decode_u64(&mut self.track(false))?;
        self.check_advance_pos(len)?;

        self.blob_end = self.pos + len;
        self.commit = Some(Nd(Self::skip_blob));
        Ok(Blob {
            stream: self,
            len: len,
        })
    }

    fn skip_blob(&mut self) -> Result<()>
    where R : Read {
        if self.blob_end > self.pos {
            let n = self.blob_end - self.pos;
            let skipped = if let Some(seek) = self.seek {
                self.skip_by_seek(n, seek.0)
            } else {
                self.skip_by_discard(n)
            }?;
            if skipped < n {
                return Err(Error::TruncatedBlob(n - skipped));
            }
        }
        Ok(())
    }

    /// Writes a field with the null/unit value to the output, i.e., a zero.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_null(&mut self, tag: u8) -> Result<()>
    where R : Write {
        self.write_u64(tag, 0)
    }

    /// Writes a field with the given integer value to the output.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_u64(&mut self, tag: u8, n: u64) -> Result<()>
    where R : Write {
        self.write_desc(wire::ParsedDescriptor::Pair(
            wire::DescriptorType::Integer, tag))?;
        wire::encode_u64(&mut self.track(false), n)?;
        Ok(())
    }

    write_int!(write_u8, u8, id, u64);
    write_int!(write_i8, i8, zigzag, i64);
    write_int!(write_u16, u16, id, u64);
    write_int!(write_i16, i16, zigzag, i64);
    write_int!(write_u32, u32, id, u64);
    write_int!(write_i32, i32, zigzag, i64);
    write_int!(write_i64, i64, zigzag, i64);
    write_int!(write_usize, usize, id, u64);
    write_int!(write_isize, isize, zigzag, i64);

    /// Writes a field with the given boolean value to the output.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_bool(&mut self, tag: u8, b: bool) -> Result<()>
    where R : Write {
        self.write_u64(tag, b as u64)
    }

    /// Writes a blob field with the given byte content to the output.
    ///
    /// The new blob is returned, positioned at the end. The caller is free to
    /// seek on the blob, but must restore the position to the end before
    /// attempting to continue using the `Stream`.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_blob_data<D : AsRef<[u8]>>(&mut self, tag: u8, data: D)
                                            -> Result<Blob<R>>
    where R : Write {
        let data = data.as_ref();
        let mut blob = self.write_blob_alloc(tag, data.len() as u64)?;
        blob.write_all(data)?;
        Ok(blob)
    }

    /// Writes the header for a blob field with the given length to the output.
    ///
    /// The new blob is returned, positioned at the beginning. The caller must
    /// advance the position to the end of the blob and leave the position at
    /// the end before continuing to use the `Stream`.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_blob_alloc(&mut self, tag: u8, len: u64)
                            -> Result<Blob<R>>
    where R : Write {
        self.write_desc_with_blob_alloc(wire::ParsedDescriptor::Pair(
            wire::DescriptorType::Blob, tag), len)
    }

    fn write_desc_with_blob_alloc(&mut self, desc: wire::ParsedDescriptor,
                                  len: u64) -> Result<Blob<R>>
    where R : Write {
        // 10 bytes length + 1 byte tag
        const OVERHEAD: u64 = 11;

        self.commit()?;

        if len > u64::MAX - OVERHEAD {
            return Err(Error::OverlongBlob);
        }

        self.check_advance_pos(len + OVERHEAD)?;
        self.write_desc(desc)?;
        wire::encode_u64(&mut self.track(false), len)?;

        self.blob_end = self.pos + len;
        self.commit = Some(Nd(Self::check_at_end_of_blob));
        Ok(Blob {
            stream: self,
            len: len,
        })
    }

    fn check_at_end_of_blob(&mut self) -> Result<()> {
        if self.pos != self.blob_end {
            Err(Error::IncompleteBlob(self.blob_end - self.pos))
        } else {
            Ok(())
        }
    }

    /// Writes the header for a blob field with unknown length to the output.
    ///
    /// The new blob is returned, positioned at the beginning. The caller must
    /// write the desired data to the blob, and then cause the `Stream` to be
    /// committed, either by calling `commit()` or by using another read or
    /// write function.
    ///
    /// This function operates by initially nominally allocating the maximum
    /// possible size for the blob and returning that. When the `Stream`
    /// commits, it uses the current position to determine the actual size of
    /// the blob, then seeks back to the blob header and writes the real length
    /// in, then seeks back to the end of the blob to continue operation.
    ///
    /// Because the length is written after the blob, the length must be in
    /// fixed-width format, which may incur up to 9 bytes of overhead. Because
    /// of this and of the overhead of multiple seeks, this should only be used
    /// for blobs which are not reasonable to buffer otherwise.
    ///
    /// It is unspecified what the result is if the caller writes the dynamic
    /// blob but then seeks the position to an earlier point of the blob and
    /// leaves position there.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_blob_dynamic(&mut self, tag: u8) -> Result<Blob<R>>
    where R : Write + Seek {
        self.write_desc_with_blob_dynamic(wire::ParsedDescriptor::Pair(
            wire::DescriptorType::Blob, tag))
    }

    fn write_desc_with_blob_dynamic(&mut self, desc: wire::ParsedDescriptor)
                                    -> Result<Blob<R>>
    where R : Write + Seek {
        self.write_desc(desc)?;
        let len = u64::MAX - self.pos - 10;
        wire::encode_fixed_u64(&mut self.track(false), len)?;

        self.dynamic_blob_start = self.pos;
        self.blob_end = self.pos + len;
        self.commit = Some(Nd(Self::finish_dynamic_blob));
        Ok(Blob {
            stream: self,
            len: len,
        })
    }

    fn finish_dynamic_blob(&mut self) -> Result<()>
    where R : Write + Seek {
        let blob_start = self.dynamic_blob_start;
        let blob_end = self.pos;
        if self.pos < blob_start {
            return Err(Error::PositionBeforeStartOfDynamicBlob);
        }

        let header = blob_start - 10;
        let displacement = self.pos - header;
        if displacement > (i64::MAX as u64) {
            return Err(Error::OverlongDynamicBlob);
        }

        self.inner.seek(io::SeekFrom::Current(-(displacement as i64)))?;
        self.pos -= displacement;
        wire::encode_fixed_u64(&mut self.track(false), blob_end - blob_start)?;
        self.inner.seek(io::SeekFrom::Current((blob_end - blob_start) as i64))?;
        self.pos = blob_end;
        Ok(())
    }

    /// Writes a struct field to the output.
    ///
    /// The body of the struct can be constructed by continuing to make calls
    /// to the `write_*` methods of this `Stream`, and terminating with the
    /// `write_end_struct` method.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_struct(&mut self, tag: u8) -> Result<()>
    where R : Write {
        self.write_desc(wire::ParsedDescriptor::Pair(
            wire::DescriptorType::Struct, tag))
    }

    /// Writes an enum field to the output.
    ///
    /// The body of the enum can be constructed by continuing to make calls to
    /// the `write_*` methods of this `Stream`, and terminating with the
    /// `write_end_struct` method.
    ///
    /// ## Panics
    ///
    /// Panics if `tag` is not a valid field tag.
    pub fn write_enum(&mut self, tag: u8, discriminant: u64) -> Result<()>
    where R : Write {
        self.write_desc(wire::ParsedDescriptor::Pair(
            wire::DescriptorType::Enum, tag))?;
        wire::encode_u64(&mut self.track(false), discriminant)?;
        Ok(())
    }

    /// Writes an end-of-struct element to the output.
    pub fn write_end_struct(&mut self) -> Result<()>
    where R : Write {
        self.write_desc(wire::ParsedDescriptor::Special(
            wire::SpecialType::EndOfStruct))
    }

    /// Writes an end-of-document element to the output.
    pub fn write_end_doc(&mut self) -> Result<()>
    where R : Write {
        self.write_desc(wire::ParsedDescriptor::Special(
            wire::SpecialType::EndOfDoc))
    }

    /// Writes an exception to the output whose content is the given byte
    /// slice.
    ///
    /// The semantics of the blob itself are the same as for `write_blob_data`.
    pub fn write_exception_data<D : AsRef<[u8]>>(&mut self, data: D)
                                                 -> Result<Blob<R>>
    where R : Write {
        let data = data.as_ref();
        let mut blob = self.write_exception_alloc(data.len() as u64)?;
        blob.write_all(data)?;
        Ok(blob)
    }

    /// Writes the header for an exception with the given data length to the
    /// output.
    ///
    /// The semantics of the blob itself are the same as for
    /// `write_blob_alloc`.
    pub fn write_exception_alloc(&mut self, len: u64)
                                 -> Result<Blob<R>>
    where R : Write {
        self.write_desc_with_blob_alloc(wire::ParsedDescriptor::Special(
            wire::SpecialType::Exception), len)
    }

    /// Writes the header for an exception whose data length is unknown to the
    /// output.
    ///
    /// The semantics of the blob itself are the same as for
    /// `write_blob_dynamic`.
    pub fn write_exception_dynamic(&mut self) -> Result<Blob<R>>
    where R : Write + Seek {
        self.write_desc_with_blob_dynamic(wire::ParsedDescriptor::Special(
            wire::SpecialType::Exception))
    }

    /// Writes a padding element to the output.
    pub fn write_padding(&mut self) -> Result<()>
    where R : Write {
        self.write_desc(wire::ParsedDescriptor::Special(
            wire::SpecialType::Padding))
    }

    /// Writes padding bytes to the output until the position of this `Stream`
    /// is a multiple of `alignment`.
    ///
    /// If the position is already a multiple of `alignment`, nothing is
    /// written, but the effect of a call to `commit()` happens regardless.
    ///
    /// `alignment` must be a power of two.
    pub fn pad_to_align(&mut self, align: u64) -> Result<()>
    where R : Write {
        debug_assert!(0 == (align & (align - 1)),
                      "`fourleaf::stream::Stream::pad_to_align()` called with \
                       non-power-of-two alignment {}", align);
        // For consistency, always commit.
        self.commit()?;

        while 0 != (self.pos & (align - 1)) {
            self.write_padding()?;
        }
        Ok(())
    }

    fn write_desc(&mut self, desc: wire::ParsedDescriptor) -> Result<()>
    where R : Write {
        self.commit()?;
        wire::encode_descriptor(&mut self.track(false),
                                wire::Descriptor::from(desc))
    }

    /// Writes the given element to this stream.
    ///
    /// This is useful for copying from one `Stream` to another. For other
    /// uses, prefer calling the direct functions instead of constructing
    /// `Element`s programatically.
    pub fn write_element<I>(&mut self, e: &mut Element<I>) -> Result<()>
    where R : Write, I : Read {
        match *e {
            Element::Field(ref mut f) => self.write_field(f),
            Element::EndOfStruct => self.write_end_struct(),
            Element::EndOfDoc => self.write_end_doc(),
            Element::Padding => self.write_padding(),
            Element::Exception(ref mut src) => {
                let mut dst = self.write_exception_alloc(src.len())?;
                io::copy(src, &mut dst)?;
                Ok(())
            },
        }
    }

    /// Writes the given field to this stream.
    ///
    /// This is useful for copying from one `Stream` to another. For other
    /// uses, prefer calling the direct functions instead of constructing
    /// `Field`s programatically.
    pub fn write_field<I>(&mut self, f: &mut Field<I>) -> Result<()>
    where R : Write, I : Read {
        match f.value {
            Value::Integer(i) => self.write_u64(f.tag, i),
            Value::Struct(..) => self.write_struct(f.tag),
            Value::Enum(discriminant, ..) =>
                self.write_enum(f.tag, discriminant),
            Value::Blob(ref mut src) => {
                let mut dst = self.write_blob_alloc(f.tag, src.len())?;
                io::copy(src, &mut dst)?;
                Ok(())
            },
        }
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

    /// Directly change the current position of the stream.
    ///
    /// This is like `set_pos()` on `Stream` --- it directly affects what the
    /// `Stream` believes to be its current byte offset and interacts with
    /// other tracked byte offsets. It should only be used in conjunction with
    /// `stream_get_ref()` and `stream_mut_ref()`.
    pub fn stream_set_pos(&mut self, pos: u64) {
        self.stream.pos = pos;
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
    pub fn read_fully(&mut self, max: usize) -> Result<Vec<u8>>
    where R : Read {
        if self.remaining() > (max as u64) {
            return Err(Error::LargeBlob(max, self.remaining()));
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
    pub fn read_or_trunc(&mut self, max: usize) -> Result<Vec<u8>>
    where R : Read {
        let mut ret = Vec::new();
        self.take(max as u64).read_to_end(&mut ret)?;
        Ok(ret)
    }

    /// Returns a reference to the unconsumed bytes in this blob.
    ///
    /// This does not consume the blob.
    ///
    /// Returns `Err` if the nominal length of the blob is larger than the
    /// underlying slice.
    pub fn slice(&self) -> Result<&[u8]>
    where R : AsRef<[u8]> {
        let rem = self.remaining();
        let inner = self.stream.inner.as_ref();
        if rem <= (inner.len() as u64) {
            Ok(&inner[..(rem as usize)])
        } else {
            Err(Error::TruncatedBlob(rem - (inner.len() as u64)))
        }
    }

    /// Returns a reference to the rest of the unconsumed bytes in this blob,
    /// consuming them.
    ///
    /// Unlike `slice()`, this does not hold a borrow on the `Blob` or even on
    /// the `Stream`.
    ///
    /// Returns `Err` if the nominal length of the blob is larger than the
    /// underlying slice.
    pub fn ext_slice<'a>(&mut self) -> Result<&'a [u8]>
    where R : AsExtBytes<'a> {
        let buf = self.stream.inner.as_ext_bytes();
        let remaining = self.remaining();
        if remaining > (buf.len() as u64) {
            Err(Error::TruncatedBlob(remaining - (buf.len() as u64)))
        } else {
            Ok(&buf[..(remaining as usize)])
        }
    }

    /// Returns a mutable reference to the unconsumed bytes in this blob.
    ///
    /// This does not consume the blob.
    ///
    /// The caller is free to manipulate the content of the blob arbitrarily;
    /// this will not corrupt the underlying data (but will obviously modify
    /// it).
    ///
    /// Returns `Err` if the nominal length of the blob is larger than the
    /// underlying slice.
    pub fn slice_mut(&mut self) -> Result<&mut [u8]>
    where R : AsMut<[u8]> {
        let rem = self.remaining();
        let inner = self.stream.inner.as_mut();
        if rem <= (inner.len() as u64) {
            Ok(&mut inner[..(rem as usize)])
        } else {
            Err(Error::TruncatedBlob(rem - (inner.len() as u64)))
        }
    }

    /// Borrows a reference to the underlying byte stream.
    ///
    /// It is the caller's responsibility to respect the blob's boundaries.
    ///
    /// This is equivalent to calling `get_ref` on the `Stream` and all the
    /// same notes apply.
    pub fn stream_get_ref(&self) -> &R {
        &self.stream.inner
    }

    /// Borrows a reference to the underlying byte stream.
    ///
    /// It is the caller's responsibility to respect the blob's boundaries.
    ///
    /// This is equivalent to calling `get_mut` on the `Stream` and all the
    /// same notes apply.
    pub fn stream_get_mut(&mut self) -> &mut R {
        &mut self.stream.inner
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
                    "attempt to seek blob by >= 8 EB"));
            }
            self.stream.inner.seek(
                io::SeekFrom::Current(-(displacement as i64)))?;
            self.stream.pos -= displacement;
        } else {
            let displacement = pos - self.stream_pos();
            if displacement > (i64::MAX as u64) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "attempt to seek blob by >= 8 EB"));
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
        pub fn $meth(&self) -> Result<$t> {
            #[allow(unused_imports)]
            use wire::unzigzag;

            match *self {
                Value::Blob(..) =>
                    Err(Error::UnexpectedType("Integer", "Blob")),
                Value::Struct(..) =>
                    Err(Error::UnexpectedType("Integer", "Struct")),
                Value::Enum(..) =>
                    Err(Error::UnexpectedType("Integer", "Enum")),
                Value::Integer(v) => {
                    let v = $zz(v);
                    if v < ($t::MIN as $long) {
                        Err(Error::IntegerOutOfRange(
                            concat!("integer value is less than ",
                                    stringify!($t), "::MIN")))
                    } else if v > ($t::MAX as $long) {
                        Err(Error::IntegerOutOfRange(
                            concat!("integer value is greater than ",
                                    stringify!($t), "::MAX")))
                    } else {
                        Ok(v as $t)
                    }
                },
            }
        }
    }
}

fn id<T>(t: T) -> T { t }

impl<'d, R : 'd> Field<'d, R> {
    /// Causes this field and all its children to be skipped.
    ///
    /// The actual IO of skipping this field does not necessarily happen within
    /// this call, and may be deferred to the next call to `next_field` or
    /// anything else that results in committing the `Stream`.
    pub fn skip(self) -> Result<()> where R : Read {
        match self.value {
            Value::Enum(_, dec) | Value::Struct(dec) =>
                dec.skip_up(self.depth),
            Value::Integer(..) | Value::Blob(..) => Ok(()),
        }
    }
}

impl<'d, R : 'd> Value<'d, R> {
    /// If this value is null/unit (i.e., integer zero), return `()`.
    /// Otherwise, return an error.
    pub fn to_null(&self) -> Result<()> {
        match *self {
            Value::Integer(n) =>
                if 0 == n { Ok(()) } else {
                    Err(Error::IntegerOutOfRange(
                        "null/unit value is non-zero")) },
            Value::Blob(..) =>
                Err(Error::UnexpectedType("Integer", "Blob")),
            Value::Struct(..) =>
                Err(Error::UnexpectedType("Integer", "Struct")),
            Value::Enum(..) =>
                Err(Error::UnexpectedType("Integer", "Enum")),
        }
    }

    /// If this value is a Struct, return the source stream. Otherwise, return
    /// an error.
    pub fn to_struct(&mut self) -> Result<&mut Stream<R>> {
        match *self {
            Value::Struct(ref mut s) => Ok(s),
            Value::Integer(..) =>
                Err(Error::UnexpectedType("Struct", "Integer")),
            Value::Blob(..) =>
                Err(Error::UnexpectedType("Struct", "Blob")),
            Value::Enum(..) =>
                Err(Error::UnexpectedType("Struct", "Enum")),
        }
    }

    /// If this value is an Enum, return its discriminant and the source
    /// stream. Otherwise, return an error.
    pub fn to_enum(&mut self) -> Result<(u64, &mut Stream<R>)> {
        match *self {
            Value::Enum(discriminant, ref mut s) => Ok((discriminant, s)),
            Value::Integer(..) =>
                Err(Error::UnexpectedType("Enum", "Integer")),
            Value::Blob(..) =>
                Err(Error::UnexpectedType("Enum", "Blob")),
            Value::Struct(..) =>
                Err(Error::UnexpectedType("Enum", "Struct")),
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
    pub fn to_bool(&self) -> Result<bool> {
        match self.to_u64()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(Error::IntegerOutOfRange(
                "boolean value was neither 0 nor 1")),
        }
    }

    /// If this value is a Blob, return a reference to the blob.
    ///
    /// An error is returned if this value is not a blob.
    pub fn to_blob(&mut self) -> Result<&mut Blob<'d, R>> {
        match *self {
            Value::Blob(ref mut b) => Ok(b),
            Value::Integer(..) =>
                Err(Error::UnexpectedType("Blob", "Integer")),
            Value::Struct(..) =>
                Err(Error::UnexpectedType("Blob", "Struct")),
            Value::Enum(..) =>
                Err(Error::UnexpectedType("Blob", "Enum")),
        }
    }
}

#[cfg(test)]
mod test {
    use std::io::{self, BufRead, Read, Seek, Write};
    use std::str;

    use test_helpers::parse;
    use super::*;

    fn stream(text: &str) -> Stream<io::Cursor<Vec<u8>>> {
        Stream::new(io::Cursor::new(parse(text)))
    }

    #[test]
    fn simple() {
        let mut dec = stream("41 00 00");
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(0, field.pos);
            field.value.to_null().unwrap();
        }

        assert!(dec.next_field().unwrap().is_none());

        match dec.next_field() {
            Ok(r) => panic!("next_field succeeded unexpectedly: {:?}", r),
            Err(Error::Io(e)) => assert_eq!(io::ErrorKind::UnexpectedEof,
                                            e.kind()),
            Err(e) => panic!("Failed with wrong error: {}", e),
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
        let mut dec = stream("81 0B 'hello world' 42 00 00");

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
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(0, field.pos);
            field.value.to_struct().unwrap();
        }
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(1, field.pos);
            field.value.to_struct().unwrap();
        }
        assert!(dec.next_field().unwrap().is_none());
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(3, field.tag);
            assert_eq!(3, field.pos);
            field.value.to_struct().unwrap();
        }
        assert!(dec.next_field().unwrap().is_none());
        assert!(dec.next_field().unwrap().is_none());
    }

    #[test]
    fn read_enum() {
        let mut dec = stream("02 81 01 00");

        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(0, field.pos);
            assert_eq!(129, field.value.to_enum().unwrap().0);
        }

        assert!(dec.next_field().unwrap().is_none());
    }

    #[test]
    fn read_explicit_eof() {
        let mut dec = stream("C1 40 42 00");

        {
            let mut field = dec.next_field().unwrap().unwrap();
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
        let mut dec = stream("41 00");
        assert!(!dec.graceful_eof());
        {
            let field = dec.next_field().unwrap().unwrap();
            field.value.to_null().unwrap();
        }

        match dec.next_field() {
            Ok(f) => panic!("next_field succeeded unexpectedly: {:?}", f),
            Err(Error::Io(e)) => assert_eq!(io::ErrorKind::UnexpectedEof,
                                            e.kind()),
            Err(e) => panic!("Failed with wrong error: {}", e),
        }
    }

    #[test]
    fn graceful_eof() {
        let mut dec = stream("41 00");
        dec.set_graceful_eof(true);
        assert!(dec.graceful_eof());
        {
            let field = dec.next_field().unwrap().unwrap();
            field.value.to_null().unwrap();
        }

        assert!(dec.next_field().unwrap().is_none());
        assert!(dec.eof());
        assert_eq!(2, dec.pos());
    }

    #[test]
    fn padding_skipped() {
        let mut dec = stream("41 00 C0 C0 C0 42 00");
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            assert_eq!(0, field.pos);
            field.value.to_null().unwrap();
        }
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(5, field.pos);
            field.value.to_null().unwrap();
        }
    }

    #[test]
    fn read_inband_error() {
        let mut dec = stream("80 05 'plugh' 41 00");

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
        let mut dec = stream("81 05 'plugh' 42 00 00");
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
        let mut dec = stream("81 0B 'hello world' 42 00");
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
        let mut dec = stream("81 0B 'hello world' 42 00");
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
        let mut data = parse("81 0B 'hello world' 42 00");
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

        let data2 = parse("81 0B 'hello World' 42 00");
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
            assert!(blob.slice().is_err());
            assert!(blob.slice_mut().is_err());
        }
    }

    #[test]
    fn blob_bufread() {
        let mut dec = stream("81 0B 'hello world' 42 00");
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

    #[test]
    fn blob_zero_copy() {
        let data = parse("81 0B 'hello world' 82 05 'plugh'");
        let (hw, plugh) = {
            let mut dec = Stream::from_slice(&data[..]);
            let hw = {
                let mut field = dec.next_field().unwrap().unwrap();
                assert_eq!(1, field.tag);
                let blob = field.value.to_blob().unwrap();

                blob.ext_slice().unwrap()
            };

            let plugh = {
                let mut field = dec.next_field().unwrap().unwrap();
                assert_eq!(2, field.tag);
                let blob = field.value.to_blob().unwrap();
                blob.ext_slice().unwrap()
            };

            (hw, plugh)
        };

        assert_eq!(b"hello world", hw);
        assert_eq!(b"plugh", plugh);
    }

    #[test]
    fn struct_depth_tracking() {
        let mut dec = stream("41 01 01 2A C1 41 02 00 00 00 \
                              C1 C1 C1 40");
        assert_eq!(0, dec.struct_depth());
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.value.to_u64().unwrap());
            assert_eq!(1, field.depth);
        }
        assert_eq!(1, dec.struct_depth());
        {
            let mut field = dec.next_field().unwrap().unwrap();
            field.value.to_enum().unwrap();
            assert_eq!(1, field.depth);
        }
        assert_eq!(2, dec.struct_depth());
        {
            let mut field = dec.next_field().unwrap().unwrap();
            field.value.to_struct().unwrap();
            assert_eq!(2, field.depth);
        }
        assert_eq!(3, dec.struct_depth());
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.value.to_u64().unwrap());
            assert_eq!(3, field.depth);
        }
        assert!(dec.next_field().unwrap().is_none());
        assert_eq!(2, dec.struct_depth());
        assert!(dec.next_field().unwrap().is_none());
        assert_eq!(1, dec.struct_depth());
        assert!(dec.next_field().unwrap().is_none());
        assert_eq!(0, dec.struct_depth());

        {
            let mut field = dec.next_field().unwrap().unwrap();
            field.value.to_struct().unwrap();
            assert_eq!(1, field.depth);
        }
        assert_eq!(2, dec.struct_depth());
        {
            let mut field = dec.next_field().unwrap().unwrap();
            field.value.to_struct().unwrap();
            assert_eq!(2, field.depth);
        }
        assert_eq!(3, dec.struct_depth());
        {
            let mut field = dec.next_field().unwrap().unwrap();
            field.value.to_struct().unwrap();
            assert_eq!(3, field.depth);
        }
        assert_eq!(4, dec.struct_depth());
        assert!(dec.next_field().unwrap().is_none());
        assert_eq!(0, dec.struct_depth());
    }

    #[test]
    fn struct_depth_tracking_handles_underflow() {
        let mut dec = stream("00 00");
        assert!(dec.next_field().unwrap().is_none());
        assert_eq!(0, dec.struct_depth());
        assert!(dec.next_field().unwrap().is_none());
        assert_eq!(0, dec.struct_depth());
    }

    #[test]
    fn skip_up_to_container() {
        let mut dec = stream("C1 C2 C3 41 01 00 00 00 42 02 00");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            field.value.to_struct().unwrap();
            field.skip().unwrap();
        }
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(2, field.tag);
            assert_eq!(2, field.value.to_u64().unwrap());
        }
    }

    #[test]
    fn skip_up_to_top() {
        let mut dec = stream("C1 C2 C3 41 01 00 00 00 42 02 00 43 03 00");
        {
            let mut field = dec.next_field().unwrap().unwrap();
            assert_eq!(1, field.tag);
            field.value.to_struct().unwrap();
        }
        dec.skip_up(0).unwrap();
        {
            let field = dec.next_field().unwrap().unwrap();
            assert_eq!(3, field.tag);
            assert_eq!(3, field.value.to_u64().unwrap());
        }
    }

    #[test]
    fn write_scalars() {
        let mut enc = Stream::new(Vec::<u8>::new());
        enc.write_null(1).unwrap();
        assert_eq!(2, enc.pos());
        enc.write_u64(2, 42).unwrap();
        assert_eq!(4, enc.pos());
        enc.write_struct(3).unwrap();
        assert_eq!(5, enc.pos());
        enc.write_end_struct().unwrap();
        assert_eq!(6, enc.pos());
        enc.write_end_doc().unwrap();
        assert_eq!(7, enc.pos());
        enc.write_padding().unwrap();
        assert_eq!(8, enc.pos());
        enc.write_enum(4, 42u64).unwrap();
        assert_eq!(10, enc.pos());

        let data = enc.into_inner();
        let expected = parse("41 00 42 2A C3 00 40 C0 04 2A");
        assert_eq!(expected, data);
    }

    #[test]
    fn write_integers() {
        let mut enc = Stream::new(Vec::new());
        enc.write_bool(1, false).unwrap();
        enc.write_bool(1, true).unwrap();
        enc.write_u8(2, 8).unwrap();
        enc.write_i8(3, 8).unwrap();
        enc.write_u16(4, 16).unwrap();
        enc.write_i16(5, 16).unwrap();
        enc.write_u32(6, 32).unwrap();
        enc.write_i32(7, 32).unwrap();
        enc.write_usize(8, 48).unwrap();
        enc.write_isize(9, 48).unwrap();
        enc.write_u64(10, 64).unwrap();
        enc.write_i64(11, 64).unwrap();

        let mut dec = Stream::new(io::Cursor::new(enc.into_inner()));
        macro_rules! assert_int {
            ($tag:expr, $expected:expr, $meth:ident) => { {
                let field = dec.next_field().unwrap().unwrap();
                assert_eq!($tag, field.tag);
                assert_eq!($expected, field.value.$meth().unwrap());
            } }
        }
        assert_int!(1, false, to_bool);
        assert_int!(1, true, to_bool);
        assert_int!(2, 8, to_u8);
        assert_int!(3, 8, to_i8);
        assert_int!(4, 16, to_u16);
        assert_int!(5, 16, to_i16);
        assert_int!(6, 32, to_u32);
        assert_int!(7, 32, to_i32);
        assert_int!(8, 48, to_usize);
        assert_int!(9, 48, to_isize);
        assert_int!(10, 64, to_u64);
        assert_int!(11, 64, to_i64);
    }

    #[test]
    fn write_direct_blob() {
        let mut enc = Stream::new(Vec::<u8>::new());
        enc.write_blob_data(1, "hello world").unwrap();
        assert_eq!(13, enc.pos());
        enc.write_exception_data("plugh").unwrap();
        assert_eq!(20, enc.pos());
        enc.write_end_doc().unwrap();
        assert_eq!(21, enc.pos());

        let data = enc.into_inner();
        let expected = parse("81 0B 'hello world' 80 05 'plugh' 40");
        assert_eq!(expected, data);
    }

    #[test]
    fn write_alloc_blob() {
        let mut enc = Stream::new(Vec::<u8>::new());
        {
            let mut blob = enc.write_blob_alloc(1, 11).unwrap();
            write!(blob, "hello {}", "world").unwrap();
        }
        {
            let mut blob = enc.write_exception_alloc(5).unwrap();
            write!(blob, "plugh").unwrap();
        }
        enc.write_end_doc().unwrap();

        let data = enc.into_inner();
        let expected = parse("81 0B 'hello world' 80 05 'plugh' 40");
        assert_eq!(expected, data);
    }

    #[test]
    fn write_alloc_dynamic() {
        let mut enc = Stream::new(io::Cursor::new(Vec::new()));
        {
            let mut blob = enc.write_blob_dynamic(1).unwrap();
            write!(blob, "hello {}", "world").unwrap();
        }
        {
            let mut blob = enc.write_exception_dynamic().unwrap();
            write!(blob, "plugh").unwrap();
        }
        enc.write_end_doc().unwrap();

        let data = enc.into_inner().into_inner();
        let expected = parse("81 8B808080808080808000 'hello world' \
                              80 85808080808080808000 'plugh' 40");
        assert_eq!(expected, data);
    }

    #[test]
    fn incomplete_alloc_blob_fails() {
        let mut enc = Stream::new(Vec::new());
        {
            let mut blob = enc.write_blob_alloc(1, 11).unwrap();
            write!(blob, "plugh").unwrap();
        }
        assert!(enc.write_end_doc().is_err());
    }

    #[cfg(debug)]
    #[test]
    #[should_panic]
    fn write_tag_zero_panics() {
        let mut enc = Stream::new(Vec::new());
        let _ = enc.write_null(0);
    }

    #[cfg(debug)]
    #[test]
    #[should_panic]
    fn write_tag_too_large_panics() {
        let mut enc = Stream::new(Vec::new());
        let _ = enc.write_null(64);
    }

    #[test]
    fn write_padding_to_alignment() {
        let mut enc = Stream::new(Vec::new());
        enc.pad_to_align(4).unwrap();
        enc.write_struct(1).unwrap();
        enc.pad_to_align(4).unwrap();
        enc.write_struct(1).unwrap();
        enc.pad_to_align(2).unwrap();
        enc.write_struct(1).unwrap();
        enc.pad_to_align(8).unwrap();

        let data = enc.into_inner();
        let expected = parse("C1 C0 C0 C0 C1 C0 C1 C0");
        assert_eq!(expected, data);
    }
}
