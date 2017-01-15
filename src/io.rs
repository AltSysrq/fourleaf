//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Specialised adapters for doing IO.

use std::io::{self, BufRead, Read, Seek, Write};

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

/// Like `AsRef<[T]>`, but the lifetime of the slice is independent of `self`.
pub trait AsExtBytes<'a> {
    /// Returns a reference to the first `n` bytes of this buffer.
    ///
    /// Returns `None` if `n` is greater than the length of this buffer.
    fn as_ext_bytes(&mut self, n: usize) -> Option<&'a [u8]>;
}

impl<'a> AsExtBytes<'a> for &'a [u8] {
    fn as_ext_bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        if n > self.len() { return None; }
        Some(&self[..n])
    }
}

impl<'a> AsExtBytes<'a> for io::Cursor<&'a [u8]> {
    fn as_ext_bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        let buf: &'a [u8] = *self.get_ref();
        let buf = &buf[(self.position() as usize)..];

        if n > buf.len() {
            None
        } else {
            Some(&buf[..n])
        }
    }
}

impl<'a> AsExtBytes<'a> for TransparentCursor<&'a [u8]> {
    fn as_ext_bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        self.0.as_ext_bytes(n)
    }
}
