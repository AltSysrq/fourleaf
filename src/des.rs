//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Defines traits and utilities for high-level deserialisation.

use std::borrow::Cow;
use std::char;
use std::cmp::{Eq, Ord};
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::io::Read;
use std::str;
use std::usize;

use quick_error::ResultExt;

use io::AsExtBytes;
use stream;

quick_error! {
    /// Errors that can be produced during deserialisation.
    ///
    /// Every variant begins with a string indicating the field names and
    /// positions that led to the error, including the problematic field
    /// itself.
    #[derive(Debug)]
    pub enum Error {
        /// An error was returned by the underlying `Stream`.
        Stream(wo: String, err: stream::Error) {
            description(err.description())
            display("{} at {}", err, wo)
            cause(err)
            context(wo: &'a Context<'a>, err: stream::Error) ->
                (wo.to_string(), err)
        }
        /// Deserialisation recursed too deeply.
        ///
        /// See `Config::recursion_limit` to control the cut-off point.
        RecursionLimitExceeded(wo: String) {
            description("recursion limit exceeded")
            display("recursion limit exceeded at {}", wo)
        }
        /// An unknown field was encountered and
        /// `Config::ignore_unknown_fields` was false.
        UnknownField(wo: String, tag: u8, pos: u64) {
            description("unknown field encountered")
            display("unknown field {} encountered at {}.{{{}}}", tag, wo, pos)
        }
        /// A field was encountered fewer times than is permitted. This error
        /// is flagged at the end of the struct containing the field.
        FieldOccursTooFewTimes(wo: String, min: u64) {
            description("too few occurrences of field")
            display("too few occurrences (min {}) of field at {}", min, wo)
        }
        /// A field was encountered more times than is permitted. This error is
        /// flagged at the first occurrence that exceeds the maximum.
        FieldOccursTooManyTimes(wo: String, max: u64) {
            description("too many occurrences of field")
            display("too many occurrences (max {}) of field at {}", max, wo)
        }
        /// A field which is required in a structure was not found by the time
        /// the end of the structure was reached. This error is flagged at the
        /// end of the structure, but includes the name of the missing field in
        /// the location.
        RequiredFieldMissing(wo: String) {
            description("required field missing")
            display("required field missing at {}", wo)
        }
        /// A field failed to deserialise because its serialised value is
        /// inappropriate for the field type.
        InvalidValue(wo: String,
                     err: Box<::std::error::Error + Send + Sync>) {
            description(err.description())
            display("{} at {}", err, wo)
        }
        /// Like `InvalidValue`, but the nested value is simply a string.
        InvalidValueMsg(wo: String, err: &'static str) {
            description(err)
            display("{} at {}", err, wo)
        }
        /// A collection being deserialised grew to be larger than the value of
        /// `Config::max_collect`.
        MaxCollectExceeded(wo: String) {
            description("collection size limit exceeded")
            display("collection size limit exceeded at {}", wo)
        }
        #[allow(missing_docs)]
        #[doc(hidden)]
        _NonExhaustive
    }
}

type Result<T> = ::std::result::Result<T, Error>;

/// Run-time configuration for deserialisation.
#[derive(Debug, Clone)]
pub struct Config {
    /// The maximum recursion level to allow.
    pub recursion_limit: usize,
    /// If true, deserialisers should silently ignore fields with tags they do
    /// not know how to handle. If false, deserialisers should raise an error
    /// if they encounter such a field.
    pub ignore_unknown_fields: bool,
    /// The maximum blob size to buffer into an owned object.
    ///
    /// This does not affect zero-copy values, which will reference arbitrarily
    /// large blobs. It also does not affect fixed-length arrays.
    ///
    /// The default is 65536.
    pub max_blob: usize,
    /// The maximum collection size to accumulate.
    ///
    /// The default is 256.
    pub max_collect: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            recursion_limit: 32,
            ignore_unknown_fields: true,
            max_blob: 65536,
            max_collect: 256,
        }
    }
}

/// Tracks contextual information during deserialisation.
///
/// This is used for constructing helpful error messages and controlling
/// recursion depth.
///
/// `Context` objects are typically constructed on the stack and passed to
/// sub-deserialisers by reference.
///
/// A `Context` can be formatted with `Display` to show the path to the current
/// location, including both field names and offsets.
#[derive(Debug, Clone)]
pub struct Context<'a> {
    /// The context for the "container" of this level of deserialisation, if
    /// any.
    pub next: Option<&'a Context<'a>>,
    /// The name of the field being deserialised at this level.
    pub field: &'a str,
    /// The position of the field being deserialised at this level.
    pub pos: u64,
    /// The recursion depth.
    pub depth: usize,
    /// The configuration to use when deserialising this level's immediate
    /// children.
    pub config: &'a Config,
}

impl<'a> Context<'a> {
    /// Creates a context subordinate to this one for the given field, provided
    /// it does not exceed the recursion limit.
    pub fn push(&'a self, field: &'a str, pos: u64) -> Result<Self> {
        if self.depth >= self.config.recursion_limit {
            Err(Error::RecursionLimitExceeded(self.to_string()))
        } else {
            Ok(Context {
                next: Some(self),
                field: field,
                pos: pos,
                depth: self.depth + 1,
                config: self.config,
            })
        }
    }

    /// If unknown fields are to result in an error, return such an error.
    /// Otherwise, return `Ok(())`.
    pub fn unknown_field<R>(&self, field: &stream::Field<R>)
                            -> Result<()> {
        if self.config.ignore_unknown_fields {
            Ok(())
        } else {
            Err(Error::UnknownField(self.to_string(), field.tag, field.pos))
        }
    }

    /// If `n + 1` is within the configured maximum collection size, return
    /// `Ok`. Otherwise, return `Err`.
    pub fn check_collect(&self, n: usize) -> Result<()> {
        if n + 1 > self.config.max_collect {
            Err(Error::MaxCollectExceeded(self.to_string()))
        } else {
            Ok(())
        }
    }
}

impl<'a> fmt::Display for Context<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(ref next) = self.next {
            write!(f, "{}.{}{{{}}}", next, self.field, self.pos)
        } else {
            write!(f, "{}{{{}}}", self.field, self.pos)
        }
    }
}

macro_rules! des_struct_body {
    (($context:expr, $stream:expr); ($ctor:expr); $(
         $tag:tt : $field:ident: $t:ty,
     )*) => { {
        $(
            let mut $field =
                <<$t as Deserialize<R, STYLE>>::Accum as Default>::default();
        )*
         while let Some(mut field) = $stream.next_field().context($context)? {
            match field.tag {
                $(
                    $tag => {
                        let subcontext = $context.push(
                            stringify!($field), field.pos)?;
                        <$t as Deserialize<R, STYLE>>::deserialize_field(
                            &mut $field, &subcontext, &mut field)?;
                    },
                )*
                _ => $context.unknown_field(&field)?,
            }
        }

        $(
            let subcontext = $context.push(stringify!($field), $stream.pos())?;
            let $field = <$t as Deserialize<R, STYLE>>::finish(
                $field, &subcontext)?;
        )*

        $ctor
    } }
}

/// Marker structs indicating the "style" of deserialisation to use.
pub mod style {
    /// Indicates that values are to be copied out of the input into owned
    /// buffers, resulting in a `'static` deserialised result.
    pub struct Copying;
    /// Indicates that values are to be references into the input data (with
    /// a lifetime bounded by it).
    pub struct ZeroCopy;
}

/// Trait for high-level deserialisation.
///
/// The `STYLE` type parameter (which is supposed to be a marker struct from
/// the `style` submodule) is used to select between buffering and referencing
/// the input.
///
/// Unlike `Sererialize`, the reader type is parameterised on the trait itself,
/// since `ZeroCopy` for certain types requires additional capabilities on `R`.
pub trait Deserialize<R : Read, STYLE = style::Copying> : Sized {
    /// Type used to accumulate the deserialised value of this field.
    ///
    /// Single-valued fields usually use `Option<Self>` here.
    ///
    /// Parent deserialisers default-initialise accumulators for their fields
    /// before starting deserialisation.
    type Accum : Default + Sized;

    /// Deserialises this type from a top-level stream.
    ///
    /// The default inverts the default implementation of
    /// `Serialize::serialize_top_level`.
    fn deserialize_top_level
        (context: &Context, stream: &mut stream::Stream<R>)
        -> Result<Self>
    {
        Ok(des_struct_body! {
            (context, stream); (top);
            1: top: Self,
        })
    }

    /// Deserialises this type from a field in a container.
    ///
    /// This may be called any number of times with the same accumulator to
    /// account for the field occurring more than once.
    fn deserialize_field
        (accum: &mut Self::Accum, context: &Context,
         field: &mut stream::Field<R>)
        -> Result<()>;

    /// Deserialises this type from a single field entry, which is known to be
    /// the only occurrence that would constitute this value.
    ///
    /// The default implementation default-initialises an `Accum`, calls
    /// `deserialize_field`, and then `finish`.
    fn deserialize_element
        (context: &Context, field: &mut stream::Field<R>) -> Result<Self>
    {
        let mut accum = <Self::Accum as Default>::default();
        Self::deserialize_field(&mut accum, context, field)?;
        Self::finish(accum, context)
    }

    /// Convert an accumulated value to a value of this type.
    ///
    /// May fail if the appropriate number of items have not been accumulated,
    /// etc.
    fn finish(accum: Self::Accum, context: &Context) -> Result<Self>;
}

macro_rules! des_unary {
    (($($stuff:tt)*); |$context:ident, $field:ident| ($cvt:expr)) => {

$($stuff)* {
    type Accum = Option<Self>;

    fn deserialize_field(accum: &mut Option<Self>, $context: &Context,
                         $field: &mut stream::Field<R>)
                         -> Result<()> {
        if accum.is_some() {
            return Err(Error::FieldOccursTooManyTimes(
                $context.to_string(), 1));
        }

        *accum = Some($cvt);
        Ok(())
    }

    fn finish(accum: Option<Self>, $context: &Context) -> Result<Self> {
        accum.ok_or_else(|| Error::RequiredFieldMissing(
            $context.to_string()))
    }
}
} }

des_unary! {
    (impl<R : Read, STYLE> Deserialize<R, STYLE> for ());
    |context, field| (field.value.to_null().context(context)?)
}

des_unary! {
    (impl<T : ?Sized, R : Read, STYLE> Deserialize<R, STYLE>
     for ::std::marker::PhantomData<T>);
    |context, field| (field.value.to_null().context(context)
                      .map(|_| ::std::marker::PhantomData)?)
}

des_unary! {
    (impl<'a, R : Read + AsExtBytes<'a>> Deserialize<R, style::ZeroCopy>
     for &'a [u8]);
    |context, field| (field.value.to_blob().and_then(|b| b.ext_slice())
                      .context(context)?)
}

des_unary! {
    (impl<'a, R : Read + AsExtBytes<'a>> Deserialize<R, style::ZeroCopy>
     for &'a str);
    |context, field| (
        str::from_utf8(
            field.value.to_blob().and_then(|b| b.ext_slice())
                .context(context)?)
            .map_err(|e| Error::InvalidValue(context.to_string(),
                                             Box::new(e)))?)
}

des_unary! {
    (impl<R : Read, STYLE> Deserialize<R, STYLE> for String);
    |context, field| (
        String::from_utf8(
            field.value.to_blob().context(context)?
            .read_fully(context.config.max_blob).context(context)?)
        .map_err(|e| Error::InvalidValue(context.to_string(),
                                         Box::new(e)))?)
}

/* TODO Coherence rules don't like this; need to find another way.
des_unary! {
    (impl<R : Read, STYLE> Deserialize<R, STYLE> for Vec<u8>);
    |context, field| (field.value.to_blob().context(context)?
                      .read_fully(context.config.max_blob).context(context)?)
}
*/

macro_rules! des_boxed {
    ($($what:tt)*) => {
impl<R : Read, STYLE, T : Deserialize<R, STYLE>> Deserialize<R, STYLE>
for $($what)*<T> {
    type Accum = T::Accum;

    fn deserialize_top_level
        (context: &Context, stream: &mut stream::Stream<R>)
        -> Result<Self>
    {
        T::deserialize_top_level(context, stream).map($($what)*::new)
    }

    fn deserialize_field
        (accum: &mut Self::Accum, context: &Context,
         field: &mut stream::Field<R>)
        -> Result<()>
    {
        T::deserialize_field(accum, context, field)
    }

    fn deserialize_element
        (context: &Context, field: &mut stream::Field<R>) -> Result<Self>
    {
        T::deserialize_element(context, field).map($($what)*::new)
    }

    fn finish(accum: T::Accum, context: &Context) -> Result<Self> {
        T::finish(accum, context).map($($what)*::new)
    }
}
} }
des_boxed!(Box);
des_boxed!(::std::rc::Rc);
des_boxed!(::std::sync::Arc);

impl<'a, R : Read, T : ?Sized + ToOwned> Deserialize<R, style::Copying>
for Cow<'a, T> where T::Owned : Deserialize<R, style::Copying> {
    type Accum = <T::Owned as Deserialize<R, style::Copying>>::Accum;

    fn deserialize_top_level
        (context: &Context, stream: &mut stream::Stream<R>)
        -> Result<Self>
    {
        <T::Owned as Deserialize<R, style::Copying>>::
        deserialize_top_level(context, stream).map(Cow::Owned)
    }

    fn deserialize_field
        (accum: &mut Self::Accum, context: &Context,
         field: &mut stream::Field<R>)
        -> Result<()>
    {
        <T::Owned as Deserialize<R, style::Copying>>::
        deserialize_field(accum, context, field)
    }

    fn deserialize_element
        (context: &Context, field: &mut stream::Field<R>) -> Result<Self>
    {
        <T::Owned as Deserialize<R, style::Copying>>::
        deserialize_element(context, field).map(Cow::Owned)
    }

    fn finish(accum: Self::Accum, context: &Context) -> Result<Self> {
        <T::Owned as Deserialize<R, style::Copying>>::
        finish(accum, context).map(Cow::Owned)
    }
}

impl<'a, R : Read, T : ?Sized + ToOwned> Deserialize<R, style::ZeroCopy>
for Cow<'a, T> where &'a T : Deserialize<R, style::ZeroCopy> {
    type Accum = <&'a T as Deserialize<R, style::ZeroCopy>>::Accum;

    fn deserialize_top_level
        (context: &Context, stream: &mut stream::Stream<R>)
        -> Result<Self>
    {
        <&'a T as Deserialize<R, style::ZeroCopy>>::
        deserialize_top_level(context, stream).map(Cow::Borrowed)
    }

    fn deserialize_field
        (accum: &mut Self::Accum, context: &Context,
         field: &mut stream::Field<R>)
        -> Result<()>
    {
        <&'a T as Deserialize<R, style::ZeroCopy>>::
        deserialize_field(accum, context, field)
    }

    fn deserialize_element
        (context: &Context, field: &mut stream::Field<R>) -> Result<Self>
    {
        <&'a T as Deserialize<R, style::ZeroCopy>>::
        deserialize_element(context, field).map(Cow::Borrowed)
    }

    fn finish(accum: Self::Accum, context: &Context) -> Result<Self> {
        <&'a T as Deserialize<R, style::ZeroCopy>>::
        finish(accum, context).map(Cow::Borrowed)
    }
}

macro_rules! des_direct {
    ($ty:ty, $meth:ident) => {
        des_unary! {
            (impl<R : Read, STYLE> Deserialize<R, STYLE> for $ty);
            |context, field| (field.value.$meth().context(context)?)
        }
    }
}
des_direct!(bool, to_bool);
des_direct!(i8, to_i8);
des_direct!(u16, to_u16);
des_direct!(i16, to_i16);
des_direct!(u32, to_u32);
des_direct!(i32, to_i32);
des_direct!(u64, to_u64);
des_direct!(i64, to_i64);
des_direct!(usize, to_usize);
des_direct!(isize, to_isize);
des_unary! {
    (impl<R : Read, STYLE> Deserialize<R, STYLE> for char);
    |context, field| (char::from_u32(field.value.to_u32().context(context)?)
                      .ok_or(Error::InvalidValueMsg(
                          context.to_string(),
                          "char not in valid range"))?)
}

macro_rules! des_small_array {
    ($n:tt $(, $count:expr)*) => {
        impl<R : Read, STYLE, T : Deserialize<R, STYLE>>
        Deserialize<R, STYLE> for [T;$n] {
            type Accum = (usize, [Option<T>;$n]);

            fn deserialize_element
                (context: &Context, field: &mut stream::Field<R>) -> Result<Self>
            {
                Self::deserialize_top_level(
                    context, field.value.to_struct().context(context)?)
            }


            #[allow(unused_comparisons)]
            fn deserialize_field
                (accum: &mut Self::Accum, context: &Context,
                 field: &mut stream::Field<R>)
                 -> Result<()>
            {
                if accum.0 >= $n {
                    Err(Error::FieldOccursTooManyTimes(
                        context.to_string(), $n))
                } else {
                    accum.1[accum.0] = Some(
                        T::deserialize_element(context, field)?);
                    accum.0 += 1;
                    Ok(())
                }
            }

            #[allow(unused_comparisons, unused_mut)]
            fn finish(mut accum: Self::Accum, context: &Context)
                      -> Result<Self> {
                if accum.0 < $n {
                    if 0 == accum.0 {
                        Err(Error::RequiredFieldMissing(context.to_string()))
                    } else {
                        Err(Error::FieldOccursTooFewTimes(
                            context.to_string(), $n))
                    }
                } else {
                    Ok([$(accum.1[$count].take().unwrap()),*])
                }
            }
        }
    }
}
des_small_array!(0);
des_small_array!(1, 0);
des_small_array!(2, 0, 1);
des_small_array!(3, 0, 1, 2);
des_small_array!(4, 0, 1, 2, 3);
des_small_array!(5, 0, 1, 2, 3, 4);
des_small_array!(6, 0, 1, 2, 3, 4, 5);
des_small_array!(7, 0, 1, 2, 3, 4, 5, 6);
des_small_array!(8, 0, 1, 2, 3, 4, 5, 6, 7);
des_small_array!(9, 0, 1, 2, 3, 4, 5, 6, 7, 8);
des_small_array!(10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
des_small_array!(11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
des_small_array!(12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
des_small_array!(13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
des_small_array!(14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
des_small_array!(15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);
des_small_array!(16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
des_small_array!(17, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
des_small_array!(18, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17);
des_small_array!(19, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18);
des_small_array!(20, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19);
des_small_array!(21, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20);
des_small_array!(22, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21);
des_small_array!(23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22);
des_small_array!(24, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23);
des_small_array!(25, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24);
des_small_array!(26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25);
des_small_array!(27, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25, 26);
des_small_array!(28, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27);
des_small_array!(29, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28);
des_small_array!(30, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29);
des_small_array!(31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30);
des_small_array!(32, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31);

macro_rules! des_struct {
    (($($stuff:tt)*);
     ($ctor:expr);
     $($tag:tt : $field:ident: $t:ty,)*) => { des_unary! {
         ($($stuff)*);
         |context, field| ({
             let stream = field.value.to_struct().context(context)?;
             des_struct_body! {
                 (context, stream); ($ctor);
                 $($tag: $field: $t,)*
             }
         })
    } }
}

macro_rules! des_tuple {
    ($($ix:tt: $name:ident: $tname:ident),*) => { des_struct! {
        (impl <R : Read, STYLE, $($tname : Deserialize<R, STYLE>),*>
         Deserialize<R, STYLE> for ($($tname,)*));
        (($($name,)*));
        $($ix : $name : $tname,)*
    } }
}

des_tuple!(1: field_0: F0);
des_tuple!(1: field_0: F0, 2: field_1: F1);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8, 10: field_9: F9);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8, 10: field_9: F9, 11: field_10: F10);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8, 10: field_9: F9, 11: field_10: F10,
           12: field_11: F11);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8, 10: field_9: F9, 11: field_10: F10,
           12: field_11: F11, 13: field_12: F12);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8, 10: field_9: F9, 11: field_10: F10,
           12: field_11: F11, 13: field_12: F12, 14: field_13: F13);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8, 10: field_9: F9, 11: field_10: F10,
           12: field_11: F11, 13: field_12: F12, 14: field_13: F13,
           15: field_14: F14);
des_tuple!(1: field_0: F0, 2: field_1: F1, 3: field_2: F2, 4: field_3: F3,
           5: field_4: F4, 6: field_5: F5, 7: field_6: F6, 8: field_7: F7,
           9: field_8: F8, 10: field_9: F9, 11: field_10: F10,
           12: field_11: F11, 13: field_12: F12, 14: field_13: F13,
           15: field_14: F14, 16: field_15: F15);

macro_rules! des_push_seq {
    (($($stuff:tt)*); $meth:ident) => {
$($stuff)* {
    type Accum = Self;

    fn deserialize_element
        (context: &Context, field: &mut stream::Field<R>) -> Result<Self>
    {
        Self::deserialize_top_level(
            context, field.value.to_struct().context(context)?)
    }

    fn deserialize_field
        (accum: &mut Self, context: &Context,
         field: &mut stream::Field<R>) -> Result<()>
    {
        context.check_collect(accum.len())?;
        accum.$meth(T::deserialize_element(context, field)?);
        Ok(())
    }

    fn finish(accum: Self, _: &Context) -> Result<Self> {
        Ok(accum)
    }
}
}
}

des_push_seq!((impl<R : Read, STYLE, T : Deserialize<R, STYLE>>
               Deserialize<R, STYLE> for Vec<T>); push);
des_push_seq!((impl<R : Read, STYLE, T : Deserialize<R, STYLE>>
               Deserialize<R, STYLE> for ::std::collections::LinkedList<T>);
              push_back);
des_push_seq!((impl<R : Read, STYLE, T : Deserialize<R, STYLE>>
               Deserialize<R, STYLE> for ::std::collections::VecDeque<T>);
              push_back);
des_push_seq!((impl<R : Read, STYLE, T : Deserialize<R, STYLE> + Ord>
               Deserialize<R, STYLE> for ::std::collections::BTreeSet<T>);
              insert);
des_push_seq!((impl<R : Read, STYLE, T : Deserialize<R, STYLE> + Hash + Eq,
                    H : BuildHasher + Default>
               Deserialize<R, STYLE> for ::std::collections::HashSet<T, H>);
              insert);
des_push_seq!((impl<R : Read, STYLE, T : Deserialize<R, STYLE> + Ord>
               Deserialize<R, STYLE> for ::std::collections::BinaryHeap<T>);
              push);

macro_rules! des_map {
    ($($stuff:tt)*) => {
$($stuff)* {
    type Accum = Self;

    fn deserialize_element
        (context: &Context, field: &mut stream::Field<R>) -> Result<Self>
    {
        Self::deserialize_top_level(
            context, field.value.to_struct().context(context)?)
    }

    fn deserialize_field
        (accum: &mut Self, context: &Context,
         field: &mut stream::Field<R>) -> Result<()>
    {
        context.check_collect(accum.len())?;

        let (k, v) = <(K, V) as Deserialize<R, STYLE>>::
            deserialize_element(context, field)?;
        accum.insert(k, v);
        Ok(())
    }

    fn finish(accum: Self, _: &Context) -> Result<Self> {
        Ok(accum)
    }
}
}
}

des_map!(impl<R : Read, STYLE, K : Deserialize<R, STYLE> + Hash + Eq,
              V : Deserialize<R, STYLE>, H : BuildHasher + Default>
         Deserialize<R, STYLE> for ::std::collections::HashMap<K, V, H>);
des_map!(impl<R : Read, STYLE, K : Deserialize<R, STYLE> + Ord,
              V : Deserialize<R, STYLE>>
         Deserialize<R, STYLE> for ::std::collections::BTreeMap<K, V>);
