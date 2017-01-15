//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Defines traits and utilities for high-level deserialisation.

use std::fmt;
use std::io::Read;

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
}

impl Default for Config {
    fn default() -> Self {
        Config {
            recursion_limit: 32,
            ignore_unknown_fields: true,
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
    (($context:expr, $stream:expr);
     ($ctor:expr); $(
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
            (context, stream);
            (top);
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

/// Trait for deserialisable values which are represented as exactly one field
/// entry in all context.
///
/// Implementing this provides a blanket implementation of `Deserialize`.
pub trait UnaryDeserialize<R : Read, STYLE> : Sized {
    /// Deserialise an instance of `Self` from the given field.
    fn deserialize_unary(context: &Context, field: &mut stream::Field<R>)
                         -> Result<Self>;
}

impl<T, R : Read, STYLE> Deserialize<R, STYLE> for T
where T : UnaryDeserialize<R, STYLE> {
    type Accum = Option<T>;

    fn deserialize_field(accum: &mut Option<T>, context: &Context,
                         field: &mut stream::Field<R>)
                         -> Result<()> {
        if accum.is_some() {
            return Err(Error::FieldOccursTooManyTimes(
                context.to_string(), 1));
        }

        *accum = Some(T::deserialize_unary(context, field)?);
        Ok(())
    }

    fn finish(accum: Option<T>, context: &Context) -> Result<T> {
        accum.ok_or_else(|| Error::RequiredFieldMissing(
            context.to_string()))
    }
}

impl<R : Read, STYLE> UnaryDeserialize<R, STYLE> for () {
    fn deserialize_unary(context: &Context, field: &mut stream::Field<R>)
                         -> Result<()> {
        Ok(field.value.to_null().context(context)?)
    }
}

impl<'a, R : Read + AsExtBytes<'a>> UnaryDeserialize<R, style::ZeroCopy>
for &'a [u8] {
    fn deserialize_unary(context: &Context, field: &mut stream::Field<R>)
                         -> Result<&'a [u8]> {
        Ok(field.value.to_blob().and_then(|b| b.ext_slice())
           .context(context)?)
    }
}
