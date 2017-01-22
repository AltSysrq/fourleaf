//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! fourleaf is a simple, efficient, and reasonably compact format and library
//! for serialising Rust values.
//!
//! # Introduction
//!
//! ## Features
//!
//! - Non-allocating serialisation and deserialisation.
//!
//! - Byte slices can be borrowed from the input instead of copied.
//!
//! - Explicit tagging makes both backward- and forward-compatibility easy to
//! maintain as desired.
//!
//! ## Why use fourleaf?
//!
//! - You want a binary data format, so JSON/TOML/etc is out.
//!
//! - You need to serialise large blobs, so CBOR is out.
//!
//! - You want to avoid copying large blobs, which requires library support
//! (e.g., not available in serde).
//!
//! - You want to serialise/deserialise mundane Rust data types, so protobufs /
//! flatbuffers are out.
//!
//! - You want fine control over compatibility.
//!
//! - You want to make a stream protocol without needing an extra framing
//! mechanism.
//!
//! ## Why *not* to use fourleaf
//!
//! - You want a self-describing data format. fourleaf requires the reader to
//! already have a good idea of what it is deserialising. If pre-agreed schemas
//! are not available, fourleaf likely isn't the right choice.
//!
//! - You want support in something other than Rust. There are no fourleaf
//! decoders available for other languages nor any plans to write one any time
//! soon (though doing so likely wouldn't be too difficult).
//!
//! - You already have `serde` working on your data and want to keep it that
//! way. fourleaf does not (and cannot) integrate with serde.
//!
//! # Getting Started
//!
//! First, we need some data structures we want to [de]serialise. For the
//! example here, we'll stick with a couple relatively basic things.
//!
//! ```no_run
//! #[derive(Debug, PartialEq)]
//! struct Widget {
//!   name: String,
//!   manufacturer: Option<String>,
//!   count: u64,
//! }
//!
//! #[derive(Debug, PartialEq)]
//! enum Order {
//!   Purchase(Vec<Widget>),
//!   Notice(String),
//! }
//! # fn main() { }
//! ```
//!
//! The `Serialize` and `Deserialize` traits are used to control fourleaf
//! serialisation and deserialisation, respectively. Implementing these by hand
//! is extremely tedious, but you can easily use the `fourleaf_retrofit!` macro
//! to generate them from a concise definition. Note that this is a declaration
//! separate from the data types themselves, and so is unfortunately a bit
//! redundant. A more concise macro may be added in a future version of
//! fourleaf.
//!
//! When defining the format for a struct or enum variant, you need to choose a
//! "tag" for each field. A tag is an integer between 1 and 63, inclusive,
//! which is how the field is identified in the binary format. For an enum,
//! each variant must also be assigned a numeric discriminant, which may be an
//! arbitrary `u64`. Obviously, each field in the same structure must have a
//! unique tag, and each variant in an enum must have a unique discriminant.
//!
//! See the `fourleaf_retrofit!` macro documentation for full information on
//! how that macro works.
//!
//! Here's how the definition for our data above might look:
//!
//! ```no_run
//! #[macro_use] extern crate fourleaf;
//! # #[derive(Debug, PartialEq)]
//! # struct Widget {
//! #   name: String,
//! #   manufacturer: Option<String>,
//! #   count: u64,
//! # }
//! #
//! # #[derive(Debug, PartialEq)]
//! # enum Order {
//! #   Purchase(Vec<Widget>),
//! #   Notice(String),
//! # }
//!
//! fourleaf_retrofit!(struct Widget : {} {} {
//!   |_context, this|
//!   [1] name: String = &this.name,
//!   [2] manufacturer: Option<String> = &this.manufacturer,
//!   [3] count: u64 = this.count,
//!   { Ok(Widget { name: name, manufacturer: manufacturer, count: count }) }
//! });
//!
//! fourleaf_retrofit!(enum Order : {} {} {
//!   |_context|
//!   [1] Order::Purchase(ref widgets) => {
//!     [1] widgets: Vec<Widget> = widgets,
//!     { Ok(Order::Purchase(widgets)) }
//!   },
//!   [2] Order::Notice(ref text) => {
//!     [1] text: String = text,
//!     { Ok(Order::Notice(text)) }
//!   },
//! });
//! # fn main() { }
//! ```
//!
//! And that's it! These structures can now be subject to fourleaf
//! serialisation.
//!
//! ```
//! #[macro_use] extern crate fourleaf;
//! # #[derive(Debug, PartialEq)]
//! # struct Widget {
//! #   name: String,
//! #   manufacturer: Option<String>,
//! #   count: u64,
//! # }
//! #
//! # #[derive(Debug, PartialEq)]
//! # enum Order {
//! #   Purchase(Vec<Widget>),
//! #   Notice(String),
//! # }
//! #
//! # fourleaf_retrofit!(struct Widget : {} {} {
//! #   |_context, this|
//! #   [1] name: String = &this.name,
//! #   [2] manufacturer: Option<String> = &this.manufacturer,
//! #   [3] count: u64 = this.count,
//! #   { Ok(Widget { name: name, manufacturer: manufacturer, count: count }) }
//! # });
//! #
//! # fourleaf_retrofit!(enum Order : {} {} {
//! #   |_context|
//! #   [1] Order::Purchase(ref widgets) => {
//! #     [1] widgets: Vec<Widget> = widgets,
//! #     { Ok(Order::Purchase(widgets)) }
//! #   },
//! #   [2] Order::Notice(ref text) => {
//! #     [1] text: String = text,
//! #     { Ok(Order::Notice(text)) }
//! #   },
//! # });
//! # fn main() {
//! let defunct_widget = Widget { name: "Defunct".to_owned(),
//!                               manufacturer: None,
//!                               count: 42 };
//! let serialised = fourleaf::to_vec(&defunct_widget).unwrap();
//! assert_eq!(b"\x81\x07Defunct\x43\x2A\x00", &serialised[..]);
//! // Type annotation not required in this case, but included for clarity.
//! let deserialised = fourleaf::from_slice_copy::<Widget>(
//!   &serialised, &fourleaf::DeConfig::default()).unwrap();
//! assert_eq!(defunct_widget, deserialised);
//!
//! let modern_widget = Widget { name: "Modern".to_owned(),
//!                              manufacturer: Some("Widgedyne".to_owned()),
//!                              count: 5 };
//! let serialised = fourleaf::to_vec(&modern_widget).unwrap();
//! assert_eq!(b"\x81\x06Modern\x82\x09Widgedyne\x43\x05\x00",
//!            &serialised[..]);
//! let deserialised = fourleaf::from_slice_copy::<Widget>(
//!   &serialised, &fourleaf::DeConfig::default()).unwrap();
//! assert_eq!(modern_widget, deserialised);
//!
//! let order = Order::Notice("nothing today".to_owned());
//! let serialised = fourleaf::to_vec(&order).unwrap();
//! assert_eq!(b"\x01\x02\x81\x0Dnothing today\x00\x00",
//!            &serialised[..]);
//! let deserialised = fourleaf::from_slice_copy::<Order>(
//!   &serialised, &fourleaf::DeConfig::default()).unwrap();
//! assert_eq!(order, deserialised);
//! # }
//! ```
//!
//! Notice the configuration that is passed in to the deserialisation
//! functions. By default, fourleaf uses fairly conservative limits on struct
//! recursion and allocations made for things like `Vec`s and `String`s. If you
//! have deeply nested structures, large collections, or large strings, you may
//! need to adjust the configuration as desired.

#![deny(missing_docs)]
#![recursion_limit = "1024"]

#[macro_use] extern crate quick_error;

pub mod io;
pub mod wire;
pub mod stream;
pub mod ser;
pub mod de;
pub mod unknown;
pub mod adapt;
#[allow(missing_docs)] #[doc(hidden)]
#[macro_use] pub mod sugar;
mod retrofit;

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
pub use self::unknown::UnknownFields;
