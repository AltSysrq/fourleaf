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
pub mod des;
