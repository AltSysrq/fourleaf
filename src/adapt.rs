//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Various adaptors to control serialisation and deserialisation.

use std::io::Read;

use de::{self, Deserialize};
use ser;
use stream;

/// Causes the inner type to be deserialised with the `Copying` style
/// regardless of the overarching deserialisation style.
#[derive(Debug, Default, Copy, Clone,
         PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Copied<T>(#[allow(missing_docs)] pub T);

impl<T : ser::Serialize> ser::SerializeAs for Copied<T> {
    type T = T;
    fn serialize_as(&self) -> &T { &self.0 }
}

impl<T, R : Read, STYLE> Deserialize<R, STYLE> for Copied<T>
where T : Deserialize<R, de::style::Copying> {
    type Accum = T::Accum;

    fn deserialize_body(context: &de::Context,
                        stream: &mut stream::Stream<R>)
                        -> de::Result<Self> {
        T::deserialize_body(context, stream).map(Copied)
    }

    fn deserialize_field(accum: &mut T::Accum,
                         context: &de::Context,
                         field: &mut stream::Field<R>)
                         -> de::Result<()> {
        T::deserialize_field(accum, context, field)
    }

    fn deserialize_element(context: &de::Context,
                           field: &mut stream::Field<R>)
                           -> de::Result<Self> {
        T::deserialize_element(context, field).map(Copied)
    }

    fn finish(accum: T::Accum, context: &de::Context)
              -> de::Result<Self> {
        T::finish(accum, context).map(Copied)
    }
}
