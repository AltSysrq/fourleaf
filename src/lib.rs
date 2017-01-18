//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! TODO

#![deny(missing_docs)]
#![recursion_limit = "1024"]

#[macro_use] extern crate quick_error;

pub mod io;
pub mod wire;
pub mod stream;
pub mod ser;
pub mod de;
#[allow(missing_docs)] #[doc(hidden)]
#[macro_use] pub mod sugar;

#[allow(missing_docs)]
#[doc(hidden)] pub mod ms {
    pub use quick_error::ResultExt;
}

#[cfg(test)] mod ser_des_builtin_tests;
#[cfg(test)] mod test_helpers;

pub use self::de::Config as DeConfig;
pub use self::de::Deserialize;
pub use self::de::from_reader;
pub use self::de::from_slice_borrow;
pub use self::de::from_slice_copy;
pub use self::de::from_stream_borrow;
pub use self::de::from_stream_copy;
pub use self::ser::Serialize;
pub use self::ser::to_stream;
pub use self::ser::to_vec;
pub use self::ser::to_writer;
pub use self::stream::Stream;
