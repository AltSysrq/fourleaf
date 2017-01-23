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
//! - Support for in-band padding, errors, or other signalling.
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
//!
//! # The fourleaf format
//!
//! The fourleaf format is built around exactly four types:
//!
//! - Arbitrary-width integers. (But note that the current implementation is
//! limited to 64 bits.)
//!
//! - Blobs (i.e., arbitrary byte arrays).
//!
//! - Structs, or sequences of tag/value pairs terminated with an `EndOfStruct`
//! marker.
//!
//! - Enums, essentially structs prefixed with an integer discriminant.
//!
//! Notably absent from this list is "null" or collections of any kind. This is
//! because fourleaf essentially models every struct field as being a
//! collection in and of itself by repeating the field as many times as needed;
//! e.g., a plain `u32` simply restricts that collection to be exactly one
//! element, whereas `Option<u32>` allows it to be zero or one, and `Vec<u32>`
//! allows arbitrary repitition.
//!
//! Because of this, the exact way a type is serialised is somewhat
//! context-sensitive. There are three general contexts:
//!
//! - "Struct body", which is also the top level. Things which are serialised
//! as structs are written without any kind of header; other things get wrapped
//! in a single-field struct.
//!
//! - "Struct field", where a value is directly contained within a struct.
//! Here, collections are flattened as described above.
//!
//! - "Collection element", where a value must be represented as exactly one
//! tag/value pair. In general, types which always serialise to exactly one
//! tag/value pair behave the same as in the "struct field" context, but
//! collections and so forth wrap themselves in a struct which contains all
//! their values.
//!
//! To illustrate, let's start with a simple structure.
//!
//! ```no_run
//! # #[macro_use] extern crate fourleaf;
//! struct S(u32, Option<u32>, Vec<u32>);
//!
//! fourleaf_retrofit!(struct S : {} {} {
//!   |_context, this|
//!   [1] a: u32 = this.0,
//!   [2] b: Option<u32> = this.1,
//!   [3] c: Vec<u32> = &this.2,
//!   { Ok(S(a, b, c)) }
//! });
//! # fn main() { }
//! ```
//!
//! If we serialise the value `S(42, None, vec![])`, we get the following:
//!
//! ```text
//! 41 2a       ; Field tag=1 type=integer value=42
//! 00          ; End of struct
//! ```
//!
//! Notice that there is no "start of struct" at the top level. Note also that
//! fields `b` and `c` are totally unrepresented in the serialised form. Since
//! `Option` and `Vec` are both treated as collections, and a collection with
//! _n_ elements is represented as _n_ repititions of the field, there are thus
//! 0 repittions of the field. If we instead populate everything, for example
//! with `S(42, Some(1), vec![2, 3])`, we get
//!
//! ```text
//! 41 2a       ; Field tag=1 type=integer value=42
//! 42 01       ; Field tag=2 type=integer value=1
//! 43 02       ; Field tag=3 type=integer value=2
//! 43 03       ; Field tag=3 type=integer value=3
//! 00          ; End of struct
//! ```
//!
//! We can see here that field `c` was simply handled by writing two instances
//! of the field without any wrapping. That is because the `Vec<u32>` is in
//! "struct field" context.
//!
//! This flat representation obviously can't work when collections are nested,
//! since there would be no way to recreate the nesting. This is why
//! "collection element" context exists. We see it, for example, if we
//! serialise `vec![Some(42u32), None]`:
//!
//! ```text
//! c1          ; field tag=1 type=struct (element of vec)
//!   41 2a     ; field tag=1 type=integer value=42
//!   00        ; end of struct (element of vec)
//! c1          ; field tag=1 type=struct (element of vec)
//!   00        ; end of struct (element of vec)
//! 00          ; end of struct (top-level)
//! ```
//!
//! There are two interesting things here. First, since `Vec` finds itself at
//! top-level, it is in "struct body" context, and so serialises as if it were
//! a field of tag 1 in a struct containing just that field. Second, because
//! `Option` is inside a collection, it instead nests itself inside a struct in
//! a similar way. In the case of `None`, this inner struct ends up being
//! completely empty.
//!
//! ## Built-in types
//!
//! fourleaf ships with built-in support for a large portion of `std`.
//! Particularly, it aims to support everything that serde does out-of-the-box.
//! A notable exception right now are the floating-point types, which do not
//! currently have a defined fourleaf representation.
//!
//! All integer types serialise to integers. Signed integers are ZigZagged
//! rather than sign-extended. `bool` is treated as an integer which is either
//! 0 or 1.
//!
//! `PhantomData` serialises to integer 0.
//!
//! Slices, `Vec`, `VecDeque`, `LinkedList`, `BinaryHeap`, `BTreeSet`, and
//! `HashSet` serialise the way collections were described above, except that
//! `&[u8]` and `Vec<u8>` serialise to blobs instead of collections of
//! integers. (Other collections have no special behaviour for `u8`.)
//!
//! `Option<T>` serialises as a collection of `T`.
//!
//! Arrays of size 0 to 32, as well as all powers of 2 up to 24, serialise the
//! same way as the slices of the same type; but note that _deserialising_
//! slices larger than 32 elements requires the elements to be both `Copy` and
//! `Default`. This includes the special behaviours of `u8`.
//!
//! `HashMap<K,V>` and `BTreeMap<K,V>` serialise the same way as `[(K,V)]`.
//!
//! Tuples with 0 to 15 elements, inclusive, serialise as structs with
//! sequential tags for each field starting from 1.
//!
//! `String` and `&str` serialise to blobs.
//!
//! `&T`, `&mut T`, `Box<T>`, `Rc<T>`, and `Arc<T>` serialise the same way as
//! `T`.
//!
//! A number of other `std` types are supported; see `retrofit.rs` in the
//! repository for their exact definitions.
//!
//! # Zero-Copy Support
//!
//! The types `&[u8]` and `&str` must, and `Cow` of the same things can, be
//! used in "zero-copy" mode. In zero-copy mode, the deserialised values will
//! reference the input buffer itself instead of being copied, which is
//! obviously faster and requires less memory, but does make management more
//! difficult and requires buffering the whole input first. In the case of
//! `Cow`, this behaviour is selectable via the `_copy` vs `_borrow` functions,
//! or the `STYLE` generic parameter to `Deserialize` when using the trait
//! directly.
//!
//! ```
//! #[macro_use] extern crate fourleaf;
//! use std::borrow::Cow;
//! use std::io::Read;
//!
//! #[derive(Debug, PartialEq)]
//! struct ZeroCopyOnly<'a> {
//!   s: &'a str,
//! }
//!
//! #[derive(Debug, PartialEq)]
//! struct EitherMode<'a> {
//!   s: Cow<'a, str>,
//! }
//!
//! fourleaf_retrofit!(struct ZeroCopyOnly<'a> : {
//!   impl<'a> fourleaf::Serialize for ZeroCopyOnly<'a>
//! } {
//!   impl<'a, R : Read, STYLE> fourleaf::Deserialize<R, STYLE>
//!   for ZeroCopyOnly<'a> where &'a str: fourleaf::Deserialize<R, STYLE>
//! } {
//!   |_context, this|
//!   [1] s: &'a str = this.s,
//!   { Ok(ZeroCopyOnly { s: s }) }
//! });
//! fourleaf_retrofit!(struct EitherMode<'a> : {
//!   impl<'a> fourleaf::Serialize for EitherMode<'a>
//! } {
//!   impl<'a, R : Read, STYLE> fourleaf::Deserialize<R, STYLE>
//!   for EitherMode<'a> where Cow<'a,str>: fourleaf::Deserialize<R, STYLE>
//! } {
//!   |_context, this|
//!   [1] s: Cow<'a,str> = this.s,
//!   { Ok(EitherMode { s: s }) }
//! });
//!
//! # fn main() {
//! // Some data we want to deserialise. It needs to be in a contiguous buffer.
//! // Here we put it in a `Vec` and borrow that to demonstrate that this
//! // works without a `'static` buffer.
//! let data = b"\x81\x0Bhello world\x00".to_owned();
//! let data = &data[..];
//! // Do a zero-copy parse of data.
//! let value = fourleaf::from_slice_borrow::<ZeroCopyOnly>(
//!   data, &fourleaf::DeConfig::default()).unwrap();
//! assert_eq!(ZeroCopyOnly { s: "hello world" }, value);
//! // Not only is it the expected value, but the string is also pointing into
//! // `data`.
//! assert_eq!(&data[2..13] as *const [u8], value.s.as_bytes() as *const [u8]);
//!
//! // This line would not compile, because `&[u8]` does not support `Copying`
//! // mode since it has no place to copy to.
//! // let value = fourleaf::from_slice_copy::<ZeroCopyOnly>( // Compile error
//! //   data, &fourleaf::DeConfig::default()).unwrap();
//!
//! // With `Cow`, we also can do zero-copy.
//! let value = fourleaf::from_slice_borrow::<EitherMode>(
//!   data, &fourleaf::DeConfig::default()).unwrap();
//! assert_eq!(EitherMode { s: Cow::Borrowed("hello world") }, value);
//! assert_eq!(&data[2..13] as *const [u8], value.s.as_bytes() as *const [u8]);
//!
//! // And `Cow` supports copying mode as well. This also lets us use a
//! // `'static` lifetime since the life of the result does not depend on the
//! // life of the input.
//! let value = fourleaf::from_slice_copy::<EitherMode<'static>>(
//!   data, &fourleaf::DeConfig::default()).unwrap();
//! match value.s {
//!   Cow::Owned(ref s) => assert_eq!("hello world", s),
//!   _ => panic!("Didn't copy"),
//! }
//! # }
//! ```
//!
//! # Maintaining Compatibility
//!
//! A large focus of fourleaf — both the format and the implementation — was
//! the ability to maintain compatibility between older and newer software.
//! Compatibility comes down to three aspects:
//!
//! - Backward-compatibility; whether a newer software version can understand
//! values written by an older version.
//!
//! - Forward-compatibility; whether an older software version can, to a a
//! reasonable extent, handle values written by a newer version.
//!
//! - Edit-compatibility; whether a program can perform read-modify-write
//! operations on the subset of serialised data it understands without
//! destroying serialised data it does not understand.
//!
//! ## Backwards-compatibility
//!
//! The set of possible changes to a type which are backwards-compatible mostly
//! flow naturally from the serialised format.
//!
//! - Adding a field is backwards-compatible as long as the type accepts a
//! cardinality of 0 (eg, `Option`, collections).
//!
//! - Widening an integer type is backwards-compatible.
//!
//! - Narrowing an integer type is backwards-compatible with the subset of
//! values which still fall within the new range.
//!
//! - Changing the signedness of an integer type is **not**
//! backwards-compatible.
//!
//! - Changing a non-collection type field to a collection of the original type
//! is backwards-compatible (but the same change at top-level or within a
//! collection is not).
//!
//! - Widening the set of acceptable cardinalities for a collection is
//! backwards-compatible.
//!
//! - Deleting a field is backwards-compatible as long as
//! `ignore_unknown_fields` is left enabled or the container has an unknown
//! field handler.
//!
//! - Adding an enum variant is backwards-compatible.
//!
//! In many cases, it is possible to "paper over" compatibility concerns
//! entirely in the code in `fourleaf_retrofit!`. For example:
//!
//! ```
//! #[macro_use] extern crate fourleaf;
//!
//! mod v1 {
//!   pub struct Message {
//!     pub target: u64
//!   }
//!   fourleaf_retrofit!(struct Message : {} {} {
//!     |_context, this|
//!     [1] target: u64 = this.target,
//!     { Ok(Message { target: target }) }
//!   });
//! }
//!
//! mod v2 {
//!   pub struct Message {
//!     pub target: u64,
//!     // New in version 2: mandatory flag
//!     pub frobnicate: bool,
//!   }
//!   fourleaf_retrofit!(struct Message : {} {} {
//!     |_context, this|
//!     [1] target: u64 = this.target,
//!     // Version 1 did not include this field
//!     [2] frobnicate: Option<bool> = Some(this.frobnicate),
//!     { Ok(Message { target: target,
//!                    frobnicate: frobnicate.unwrap_or(false) }) }
//!   });
//! }
//!
//! # fn main() {
//! // Write a message with the V1 schema...
//! let old_message = fourleaf::to_vec(v1::Message { target: 42 }).unwrap();
//! // .. and then decode it with the V2 schema.
//! let message = fourleaf::from_slice_copy::<v2::Message>(
//!   &old_message, &fourleaf::DeConfig::default()).unwrap();
//!
//! assert_eq!(42, message.target);
//! // Code outside of deserialisation doesn't need to care about the
//! // compatibility issue.
//! assert!(!message.frobnicate);
//! # }
//! ```
//!
//! ## Forwards-compatibility
//!
//! Forwards-compatibility is largely the reverse of backwards-compatibility;
//! i.e., the change from version 1 to version 2 is forwards-compatible if a
//! change from version 2 to version 1 would be backwards-compatible.
//!
//! Forwards-compatibility can be more difficult, though, since compatibility
//! workarounds must be done in the serialisation side of the new version.
//!
//! ## Edit-compatibility
//!
//! In some cases, it is desirable to allow older versions to manipulate data
//! written by newer versions while preserving things they don't understand.
//! This can be accomplished via a catch-all "unknown fields" field on structs,
//! and an "unknown variant" variant on enums. Beware that unlike other
//! compatibility concerns, this cannot be confined to [de]serialisation logic;
//! handling of unknowns becomes somewhat pervasive since it must be refletcted
//! in the underyling types.
//!
//! Here is an example demonstrating both features:
//!
//! ```
//! #[macro_use] extern crate fourleaf;
//!
//! mod v1 {
//!   use fourleaf;
//!   use fourleaf::adapt::Copied;
//!
//!   pub enum Operation {
//!     Create,
//!     Delete,
//!     // For future expansion, if a new enum variant is added, its
//!     // discriminant and inner fields are stored here instead of raising an
//!     // error.
//!     Unknown(u64, fourleaf::UnknownFields<'static>),
//!   }
//!
//!   pub struct Message {
//!     pub id: u32,
//!     pub operation: Operation,
//!     // Unknown fields will be saved here.
//!     pub unknown: fourleaf::UnknownFields<'static>,
//!   }
//!
//!   fourleaf_retrofit!(enum Operation : {} {} {
//!     |_context|
//!     [1] Operation::Create => {
//!       { Ok(Operation::Create) }
//!     },
//!     [2] Operation::Delete => {
//!       { Ok(Operation::Delete) }
//!     },
//!     (?) Operation::Unknown(discriminant, ref fields) => {
//!       (=) discriminant: u64 = discriminant,
//!       (?) fields: Copied<fourleaf::UnknownFields<'static>> = fields,
//!       { Ok(Operation::Unknown(discriminant, fields.0)) }
//!     }
//!   });
//!
//!   fourleaf_retrofit!(struct Message : {} {} {
//!     |_context, this|
//!     [1] id: u32 = this.id,
//!     [2] operation: Operation = &this.operation,
//!     (?) unknown: Copied<fourleaf::UnknownFields<'static>> = &this.unknown,
//!     { Ok(Message { id: id, operation: operation, unknown: unknown.0 }) }
//!   });
//! }
//!
//!
//! mod v2 {
//!   use fourleaf;
//!   use fourleaf::adapt::Copied;
//!
//!   pub enum Operation {
//!     Create,
//!     Delete,
//!     // New in v2. We could also have `UnknownFields` in here, but that has
//!     // been elided here for clarity.
//!     RenameTo(u32),
//!     // For future expansion, if a new enum variant is added, its
//!     // discriminant and inner fields are stored here instead of raising an
//!     // error.
//!     Unknown(u64, fourleaf::UnknownFields<'static>),
//!   }
//!
//!   pub struct Message {
//!     pub id: u32,
//!     pub operation: Operation,
//!     // New in v2
//!     pub frobnicate: bool,
//!     // Unknown fields will be saved here.
//!     pub unknown: fourleaf::UnknownFields<'static>,
//!   }
//!
//!   fourleaf_retrofit!(enum Operation : {} {} {
//!     |_context|
//!     [1] Operation::Create => {
//!       { Ok(Operation::Create) }
//!     },
//!     [2] Operation::Delete => {
//!       { Ok(Operation::Delete) }
//!     },
//!     [3] Operation::RenameTo(id) => {
//!       [1] id: u32 = id,
//!       { Ok(Operation::RenameTo(id)) }
//!     },
//!     (?) Operation::Unknown(discriminant, ref fields) => {
//!       (=) discriminant: u64 = discriminant,
//!       (?) fields: Copied<fourleaf::UnknownFields<'static>> = fields,
//!       { Ok(Operation::Unknown(discriminant, fields.0)) }
//!     }
//!   });
//!
//!   fourleaf_retrofit!(struct Message : {} {} {
//!     |_context, this|
//!     [1] id: u32 = this.id,
//!     [2] operation: Operation = &this.operation,
//!     [3] frobnicate: Option<bool> = this.frobnicate,
//!     (?) unknown: Copied<fourleaf::UnknownFields<'static>> = &this.unknown,
//!     { Ok(Message { id: id, operation: operation,
//!                    frobnicate: frobnicate.unwrap_or(false),
//!                    unknown: unknown.0 }) }
//!   });
//! }
//!
//! # fn main() {
//! let mut config = fourleaf::DeConfig::default();
//! // Fail deserialisation if we would destroy anything.
//! config.ignore_unknown_fields = false;
//!
//! // A v2 program creates a `Message` and serialises it.
//! let data = fourleaf::to_vec(v2::Message {
//!   id: 42,
//!   frobnicate: true,
//!   operation: v2::Operation::RenameTo(56),
//!   unknown: Default::default(),
//! }).unwrap();
//!
//! // Now a v1 program reads it in and edits a field and reserialises it.
//! let mut val = fourleaf::from_slice_copy::<v1::Message>(&data, &config)
//!     .unwrap();
//! assert_eq!(42, val.id);
//! val.id = 99;
//! let data = fourleaf::to_vec(val).unwrap();
//!
//! // Finally, another v2 program reads that in. The non-v1 things are still
//! // preserved.
//! let val = fourleaf::from_slice_copy::<v2::Message>(&data, &config)
//!     .unwrap();
//! assert_eq!(99, val.id);
//! assert!(val.frobnicate);
//! match val.operation {
//!   v2::Operation::RenameTo(56) => (),
//!   _ => panic!("wrong operation"),
//! }
//! # }
//! ```
//!
//! # Limitations
//!
//! ## This Implementation
//!
//! Integers wider than 64 bits are not supported.
//!
//! Inputs longer than 16 EB are not supported. Some operations are not
//! supported on streams longer than 8 EB. Structs/enums cannot be nested more
//! than 16 quintillion levels deep.
//!
//! The high-level deserialisation mechanism will construct each declared type
//! on the stack before moving it to its final location. I.e., a large
//! `Vec<u64>` is fine, but using a `[u64;16777216]` is probably unwise.
//!
//! ## Arteficial
//!
//! fourleaf places arteficial limits on the data that can be deserialised via
//! the high-level API in order to help harden programs against malicious
//! inputs. If you run afoul of these limits, you can change them by modifying
//! the `Config` object.
//!
//! When copying byte slices into a buffer (e.g., `Vec<u8>` or `String`), the
//! configuration field `max_blob` places a cap on the largest total size of
//! blobs to be deserialised in this way. Larger blobs, or large numbers of
//! smaller blobs, will result in an error. `max_blob` defaults to 64 kB.
//!
//! When populating a collection that has an unbounded cardinality (e.g.,
//! `Vec<u64>`, `HashMap<String, String>`), an error will occur if the total
//! length of all such collections exceeds `max_collect`. `max_collect`
//! defaults to 256. This limit even applies to `UnknownFields`.
//!
//! The `recursion_limit` configuration sets the maximum nesting depth that
//! will be deserialised.
//!
//! # Physical Format
//!
//! Knowing how fourleaf elements translate to bytes is not required to use
//! fourleaf, but may make help debugging issues or writing alternate
//! implementations.
//!
//! A fourleaf stream is a sequence of elements. Each element begins with a
//! single byte. The upper two bits of this byte are the "type", and the lower
//! 6 bits are the "tag".
//!
//! If the tag is zero, this is a special element, and the types map as follows:
//!
//! - 00 — End of struct.
//! - 40 — End of document.
//! - 80 — Exception. Followed by a blob.
//! - C0 — Padding. Readers are usually expected to ignore padding.
//!
//! If the tag is non-zero, this is a struct field. The tag identifies the
//! field being described, and the type is one of:
//!
//! - 00 — Enum. Followed by an integer indicating the discriminant, then
//! elements specifying fields for the enum body.
//!
//! - 40 — Integer. Followed by an integer indicating the value.
//!
//! - 80 — Blob. Followed by a blob indicating the value.
//!
//! - C0 — Struct. Followed by elements specifying fields for the struct body.
//!
//! Integers are written as in [protobufs](https://developers.google.com/protocol-buffers/docs/encoding).
//! That is, an integer is written as a sequence of little-endian 7-bit fields,
//! with the high bit of each byte set if another byte follows. Signed integers
//! are first ZigZagged (see `zigzag` in `wire.rs`) before being written.
//!
//! Readers MUST accept integers in denormalised form.
//!
//! A blob is simply an integer indicating the blob length in bytes, followed
//! by exactly that number of bytes.

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
