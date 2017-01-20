//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Structures for working with fourleaf streams or portions of streams with
//! unknown contents.

use std::borrow::Cow;
use std::io::{Read, Write};

use quick_error::ResultExt;

use de::{Context, Deserialize, Error, Result};
use stream::{self, Stream};
use ser::Serialize;

/// Stores a sequence of tags and the field values associated with them.
///
/// This is most useful in conjunction with the `(?)` pseudo-tag of a structure
/// definition, as this will result in all unknown fields being preserved after
/// deserialisation and being replicated on serialisation.
///
/// Note that this won't be a 100% perfect replica, since all unknown fields in
/// the reserialisation will be grouped together even if they were not in the
/// original.
///
/// Beware that this **cannot** be used as a tagged field of a struct-like
/// composite, since its serialised format must use the tags it stores rather
/// than the tag of its container. Attempting to serialise such an
/// `UnknownFields` instance will result in a panic! If you really want to pass
/// this around in a structure field, wrapping this in a 1-element array (i.e.,
/// `[UnknownFields<'a>;1]`) will work.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnknownFields<'a>(
    /// The sequence of field tags and field values.
    pub Vec<(u8, UnknownField<'a>)>);

/// A single field of arbitrary type.
///
/// This is not intended to be particularly easy use; it mainly exists as a
/// storage mechanism for `UnknownFields`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownField<'a> {
    /// An integer value.
    ///
    /// There is no way to tell what the integer actually represents, whether
    /// it is signed (with ZigZag) or unsigned, etc.
    Integer(u64),
    /// A binary blob.
    Blob(Cow<'a, [u8]>),
    /// A child structure.
    Struct(UnknownFields<'a>),
    /// A child enum with the given discriminant.
    Enum(u64, UnknownFields<'a>),
}

impl<'a> Serialize for UnknownFields<'a> {
    fn serialize_body<R : Write>(&self, dst: &mut Stream<R>)
                                 -> stream::Result<()> {
        for &(tag, ref field) in &self.0 {
            field.serialize_field(dst, tag)?;
        }
        dst.write_end_struct()
    }

    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> stream::Result<()> {
        dst.write_struct(tag)?;
        self.serialize_body(dst)
    }

    fn serialize_field<R : Write>(&self, _: &mut Stream<R>, _: u8)
                                  -> stream::Result<()> {
        panic!("fourleaf::unknown::UnknownFields cannot be used as field \
                of a struct or other heterogeneous construct");
    }
}

impl<'a, R : Read, STYLE> Deserialize<R, STYLE> for UnknownFields<'a>
where Cow<'a, [u8]>: Deserialize<R, STYLE> {
    type Accum = Self;

    fn deserialize_body
        (context: &Context, stream: &mut Stream<R>)
        -> Result<Self>
    {
        let mut this = Self::default();
        let mut name = [0u8;2];

        while let Some(mut field) = stream.next_field().context(context)? {
            Self::deserialize_field(
                &mut this,
                &context.push_tag(&mut name, field.tag, field.pos)?,
                &mut field)?;
        }

        Self::finish(this, context)
    }

    fn deserialize_field
        (this: &mut Self, context: &Context, field: &mut stream::Field<R>)
        -> Result<()>
    {
        context.check_collect(this.0.len())?;
        this.0.push((field.tag, UnknownField::deserialize_element(
            context, field)?));
        Ok(())
    }

    fn deserialize_element
        (context: &Context, field: &mut stream::Field<R>)
        -> Result<Self>
    {
        Self::deserialize_body(
            context, field.value.to_struct().context(context)?)
    }

    fn finish(this: Self, _: &Context) -> Result<Self> { Ok(this) }
}

impl<'a> Serialize for UnknownField<'a> {
    fn serialize_element<R : Write>(&self, dst: &mut Stream<R>, tag: u8)
                                    -> stream::Result<()> {
        match *self {
            UnknownField::Integer(n) => dst.write_u64(tag, n),
            UnknownField::Blob(ref data) =>
                dst.write_blob_data(tag, data).map(|_| ()),
            UnknownField::Struct(ref sub) => {
                dst.write_struct(tag)?;
                sub.serialize_body(dst)
            },
            UnknownField::Enum(discriminant, ref sub) => {
                dst.write_enum(tag, discriminant)?;
                sub.serialize_body(dst)
            },
        }
    }
}

impl<'a, R : Read, STYLE> Deserialize<R, STYLE> for UnknownField<'a>
where Cow<'a, [u8]> : Deserialize<R, STYLE> {
    type Accum = Option<Self>;

    fn deserialize_field(accum: &mut Option<Self>, context: &Context,
                         field: &mut stream::Field<R>) -> Result<()> {
        if accum.is_some() {
            Err(Error::FieldOccursTooManyTimes(context.to_string(), 1))
        } else {
            *accum = Some(match field.value {
                stream::Value::Integer(n) => UnknownField::Integer(n),
                stream::Value::Blob(_) => UnknownField::Blob(
                    Cow::<'a, [u8]>::deserialize_element(context, field)?),
                stream::Value::Struct(ref mut stream) => UnknownField::Struct(
                    UnknownFields::deserialize_body(context, stream)?),
                stream::Value::Enum(d, ref mut stream) => UnknownField::Enum(
                    d, UnknownFields::deserialize_body(context, stream)?),
            });
            Ok(())
        }
    }

    fn finish(accum: Option<Self>, context: &Context) -> Result<Self> {
        accum.ok_or_else(|| Error::RequiredFieldMissing(context.to_string()))
    }
}

#[cfg(test)]
mod test {
    use de::*;
    use ser::*;
    use test_helpers::parse;
    use super::*;

    #[test]
    fn deser_and_ser() {
        let orig = parse(
            "41 2A \
             82 0B 'hello world' \
             03 12 44 10 00 \
             C5 46 11 00 \
             00");
        let parsed = from_slice_borrow::<UnknownFields>(
            &orig, &Config::default()).unwrap();
        assert_eq!(4, parsed.0.len());

        match parsed.0[0] {
            (1, UnknownField::Integer(42)) => (),
            ref v => panic!("wrong value for first field: {:?}", v),
        }

        match parsed.0[1] {
            (2, UnknownField::Blob(ref cow)) if b"hello world" == &**cow => (),
            ref v => panic!("wrong value for second field: {:?}", v),
        }

        match parsed.0[2] {
            (3, UnknownField::Enum(18, ref sub)) => {
                assert_eq!(1, sub.0.len());
                match sub.0[0] {
                    (4, UnknownField::Integer(16)) => (),
                    ref v => panic!("wrong value for nested field: {:?}", v),
                }
            },
            ref v => panic!("wrong value for third field: {:?}", v),
        }

        match parsed.0[3] {
            (5, UnknownField::Struct(ref sub)) => {
                assert_eq!(1, sub.0.len());
                match sub.0[0] {
                    (6, UnknownField::Integer(17)) => (),
                    ref v => panic!("wrong value for nested field: {:?}", v),
                }
            },
            ref v => panic!("wrong value for fourth field: {:?}", v),
        }

        let reser = to_vec(parsed).unwrap();
        assert_eq!(orig, reser);
    }
}
