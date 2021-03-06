//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Defines traits and utilities for high-level serialisation.

use std::io::Write;

use stream::{Result, Stream};

/// Serialises `t` into a `Vec<u8>`.
pub fn to_vec<T : Serialize>(t: T) -> Result<Vec<u8>> {
    let mut stream = Stream::new(Vec::new());
    t.serialize_body(&mut stream)?;
    stream.commit()?;
    Ok(stream.into_inner())
}

/// Serialises `t` and writes it to `writer`.
///
/// This can be called multiple times in succession to write multiple values,
/// which can later be read by sequential calls to the corresponding
/// deserialisation functions.
///
/// This creates a `Stream` with its default properties. If this is not
/// desired, create a `Stream` manually and pass it to `to_stream`.
pub fn to_writer<T : Serialize, W : Write>(writer: W, t: T)
                                           -> Result<()> {
    let mut stream = Stream::new(writer);
    t.serialize_body(&mut stream)?;
    stream.commit()?;
    Ok(())
}

/// Serialises `t` to `stream`.
///
/// This can be called multiple times in succession to write multiple values,
/// which can later be read by sequential calls to the corresponding
/// deserialisation functions.
pub fn to_stream<T : Serialize, R : Write>(stream: &mut Stream<R>,
                                           t: T)
                                           -> Result<()> {
    t.serialize_body(stream)?;
    stream.commit()?;
    Ok(())
}

/// Trait for serialising values via fourleaf.
pub trait Serialize {
    /// Serialises this value, which is at top-level or the tail part of a
    /// struct.
    ///
    /// The callee shall write any number (including zero) of field elements
    /// with balanced `EndOfStruct` elements, followed by exactly one
    /// `EndOfStruct` element.
    ///
    /// By default, this calls `serialize_field` with a tag of 1 and then
    /// writes an end-of-struct.
    fn serialize_body<R : Write>(&self, dst: &mut Stream<R>)
                                 -> Result<()> {
        self.serialize_field(dst, 1)?;
        dst.write_end_struct()
    }
    /// Serialises this value, which is a field of a struct, to the given
    /// stream.
    ///
    /// The callee may write any number (including 0) of field pairs with a
    /// field tag of `tag` to the stream.
    ///
    /// By default, this delegates to `serialize_element`.
    fn serialize_field<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                  -> Result<()> {
        self.serialize_element(dst, tag)
    }
    /// Serialises this value, which is an element of a collection, to the
    /// given stream.
    ///
    /// The callee must write exactly one field pair with a field tag of `tag`
    /// to the stream.
    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()>;
    /// If slices of this type should be written specially, do so and return
    /// `Some` result. Otherwise, return `None`.
    ///
    /// If this does handle the value specially, it must write exactly one
    /// field with the given tag to `dst`.
    ///
    /// This mainly exists so that `[u8]` is serialised as a blob.
    #[allow(unused_variables)]
    fn serialize_slice<R : Write>
        (selves: &[Self], dst: &mut Stream<R>, tag: u8)
         -> Option<Result<()>>
    where Self : Sized {
        None
    }
}

/// If implemented, provides a blanket implementation of `Serialize` to
/// delegate to the chosen value.
pub trait SerializeAs {
    /// The actual type to serialise.
    type T : Serialize + ?Sized;

    /// Returns the value to be serialised in lieu of `self`.
    fn serialize_as(&self) -> &Self::T;
}

impl<T : SerializeAs + ?Sized> Serialize for T {
    fn serialize_body<R : Write>(&self, dst: &mut Stream<R>)
                                 -> Result<()> {
        self.serialize_as().serialize_body(dst)
    }
    fn serialize_field<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                  -> Result<()> {
        self.serialize_as().serialize_field(dst, tag)
    }
    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        self.serialize_as().serialize_element(dst, tag)
    }

}

impl Serialize for () {
    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        dst.write_struct(tag)?;
        dst.write_end_struct()
    }
}

impl<T : ?Sized> Serialize for ::std::marker::PhantomData<T> {
    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        dst.write_null(tag)
    }
}

impl<'a, T : 'a + ?Sized + Serialize> SerializeAs for &'a T {
    type T = T;

    fn serialize_as(&self) -> &T { *self }
}
impl<'a, T : 'a + ?Sized + Serialize> SerializeAs for &'a mut T {
    type T = T;

    fn serialize_as(&self) -> &T { *self }
}
impl<T : ?Sized + Serialize> SerializeAs for Box<T> {
    type T = T;

    fn serialize_as(&self) -> &T { &*self }
}
impl<T : ?Sized + Serialize> SerializeAs for ::std::rc::Rc<T> {
    type T = T;

    fn serialize_as(&self) -> &T { &*self }
}
impl<T : ?Sized + Serialize> SerializeAs for ::std::sync::Arc<T> {
    type T = T;

    fn serialize_as(&self) -> &T { &*self }
}
impl<'a, T : ?Sized + Serialize + ToOwned> SerializeAs
for ::std::borrow::Cow<'a, T> {
    type T = T;

    fn serialize_as(&self) -> &T { &*self }
}
impl<T : Serialize> SerializeAs for Vec<T> {
    type T = [T];

    fn serialize_as(&self) -> &[T] { &self[..] }
}

impl Serialize for u8 {
    fn serialize_element<R : Write>
        (&self, dst: &mut Stream<R>, tag: u8)
        -> Result<()>
    {
        dst.write_u8(tag, *self)
    }

    fn serialize_slice<R : Write>
        (selves: &[u8], dst: &mut Stream<R>, tag: u8)
        -> Option<Result<()>>
    {
        Some(dst.write_blob_data(tag, selves).map(|_| ()))
    }
}

macro_rules! ser_direct {
    ($ty:ty, $meth:ident) => {
        impl Serialize for $ty {
            fn serialize_element<R : Write>
                (&self, dst: &mut Stream<R>, tag: u8)
                -> Result<()>
            {
                dst.$meth(tag, *self)
            }
        }
    }
}
ser_direct!(bool, write_bool);
ser_direct!(i8, write_i8);
ser_direct!(u16, write_u16);
ser_direct!(i16, write_i16);
ser_direct!(u32, write_u32);
ser_direct!(i32, write_i32);
ser_direct!(u64, write_u64);
ser_direct!(i64, write_i64);
ser_direct!(usize, write_usize);
ser_direct!(isize, write_isize);
impl Serialize for char {
    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        dst.write_u32(tag, *self as u32)
    }
}

macro_rules! ser_bytes {
    ($($stuff:tt)*) => {
        impl $($stuff)* {
            fn serialize_element<R : Write>
                (&self, dst: &mut Stream<R>, tag: u8)
                -> Result<()>
            {
                let data = AsRef::<[u8]>::as_ref(self);
                dst.write_blob_data(tag, data)?;
                Ok(())
            }
        }
    }
}

ser_bytes!(Serialize for String);
ser_bytes!(Serialize for str);

macro_rules! ser_array {
    ($n:tt) => {
        impl<T> SerializeAs for [T;$n] where [T]: Serialize {
            type T = [T];
            fn serialize_as(&self) -> &[T] {
                &self[..]
            }
        }
    }
}
ser_array!(0);
ser_array!(1);
ser_array!(2);
ser_array!(3);
ser_array!(4);
ser_array!(5);
ser_array!(6);
ser_array!(7);
ser_array!(8);
ser_array!(9);
ser_array!(10);
ser_array!(11);
ser_array!(12);
ser_array!(13);
ser_array!(14);
ser_array!(15);
ser_array!(16);
ser_array!(17);
ser_array!(18);
ser_array!(19);
ser_array!(20);
ser_array!(21);
ser_array!(22);
ser_array!(23);
ser_array!(24);
ser_array!(25);
ser_array!(26);
ser_array!(27);
ser_array!(28);
ser_array!(29);
ser_array!(30);
ser_array!(31);
ser_array!(32);
ser_array!(64);
ser_array!(128);
ser_array!(256);
ser_array!(512);
ser_array!(1024);
ser_array!(2048);
ser_array!(4096);
ser_array!(8192);
ser_array!(16384);
ser_array!(32768);
ser_array!(65536);
ser_array!(131072);
ser_array!(262144);
ser_array!(524288);
ser_array!(1048576);
ser_array!(2097152);
ser_array!(4194304);
ser_array!(8388608);
ser_array!(16777216);

macro_rules! ser_tuple {
    ($($t:ident : $v:tt),*) => {
        impl <$($t : Serialize),*> Serialize for ($($t,)*) {
            fn serialize_body<R : Write>
                (&self, dst: &mut Stream<R>) -> Result<()>
            {
                $(self.$v.serialize_field(dst, $v + 1)?;)*
                dst.write_end_struct()
            }

            fn serialize_element<R : Write>
                (&self, dst: &mut Stream<R>, tag: u8) -> Result<()>
            {
                dst.write_struct(tag)?;
                self.serialize_body(dst)
            }
        }
    }
}
ser_tuple!(F0 : 0);
ser_tuple!(F0 : 0, F1 : 1);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8, F9 : 9);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8, F9 : 9, F10 : 10);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8, F9 : 9, F10 : 10, F11 : 11);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8, F9 : 9, F10 : 10, F11 : 11, F12 : 12);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8, F9 : 9, F10 : 10, F11 : 11, F12 : 12, F13 : 13);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8, F9 : 9, F10 : 10, F11 : 11, F12 : 12, F13 : 13,
           F14 : 14);
ser_tuple!(F0 : 0, F1 : 1, F2 : 2, F3 : 3, F4 : 4, F5 : 5, F6 : 6,
           F7 : 7, F8 : 8, F9 : 9, F10 : 10, F11 : 11, F12 : 12, F13 : 13,
           F14 : 14, F15 : 15);

impl <T : Serialize> Serialize for [T] {
    fn serialize_field<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                  -> Result<()> {
        if let Some(handled) = T::serialize_slice(self, dst, tag) {
            return handled;
        }

        for e in self {
            e.serialize_element(dst, tag)?;
        }
        Ok(())
    }

    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        if let Some(handled) = T::serialize_slice(self, dst, tag) {
            return handled;
        }

        dst.write_struct(tag)?;
        self.serialize_field(dst, 1)?;
        dst.write_end_struct()
    }
}

macro_rules! ser_iter_mut {
    ($($stuff:tt)*) => {
impl $($stuff)* {
    fn serialize_field<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                  -> Result<()> {
        for e in self {
            e.serialize_element(dst, tag)?;
        }
        Ok(())
    }

    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        dst.write_struct(tag)?;
        self.serialize_field(dst, 1)?;
        dst.write_end_struct()
    }
}
}
}

ser_iter_mut!(<T : Serialize> Serialize for ::std::collections::LinkedList<T>);
ser_iter_mut!(<T : Serialize> Serialize for ::std::collections::VecDeque<T>);
ser_iter_mut!(<T : Serialize> Serialize for Option<T>);

macro_rules! ser_iter {
    ($($stuff:tt)*) => {
impl $($stuff)* {
    fn serialize_field<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                  -> Result<()> {
        for e in self.iter() {
            e.serialize_element(dst, tag)?;
        }
        Ok(())
    }

    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        dst.write_struct(tag)?;
        self.serialize_field(dst, 1)?;
        dst.write_end_struct()
    }
}
}
}

ser_iter!(<T : Serialize + ::std::cmp::Ord> Serialize
          for ::std::collections::BTreeSet<T>);
ser_iter!(<T : Serialize + ::std::cmp::Eq + ::std::hash::Hash,
           H : ::std::hash::BuildHasher> Serialize
          for ::std::collections::HashSet<T, H>);
ser_iter!(<T : Serialize + ::std::cmp::Ord> Serialize
          for ::std::collections::BinaryHeap<T>);

macro_rules! ser_map {
    ($($stuff:tt)*) => {
impl $($stuff)* {
    fn serialize_field<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                  -> Result<()> {
        for (k, v) in self.iter() {
            dst.write_struct(tag)?;
            k.serialize_field(dst, 1)?;
            v.serialize_field(dst, 2)?;
            dst.write_end_struct()?;
        }
        Ok(())
    }

    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> Result<()> {
        dst.write_struct(tag)?;
        self.serialize_field(dst, 1)?;
        dst.write_end_struct()
    }
}
}
}

ser_map!(<K : Serialize + ::std::cmp::Ord, V : Serialize> Serialize
         for ::std::collections::BTreeMap<K, V>);
ser_map!(<K : Serialize + ::std::hash::Hash + ::std::cmp::Eq,
          V : Serialize,
          H : ::std::hash::BuildHasher> Serialize
         for ::std::collections::HashMap<K, V, H>);
