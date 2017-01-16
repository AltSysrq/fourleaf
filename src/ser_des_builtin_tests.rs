//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::*;
use std::io::Read;

use des::*;
use ser::*;
use stream::Stream;
use test_helpers::parse;

macro_rules! tcase {
    ($name:ident ($ty:ty[$($style:ident)+]: $input:expr => $binary:expr)) => {
        #[test]
        fn $name() {
            let orig: $ty = $input;
            let mut encoded = Vec::new();
            {
                let mut stream = Stream::new(&mut encoded);
                orig.serialize_top_level(&mut stream).unwrap();
                stream.commit().unwrap();
            }

            assert_eq!(parse($binary), encoded);

            $({
                let mut stream = Stream::from_slice(&encoded[..]);
                fn deser<R : Read, T : Deserialize<R, style::$style>>
                    (stream: &mut Stream<R>) -> T
                {
                    let config = Config::default();
                    let context = Context {
                        config: &config,
                        next: None,
                        field: "",
                        pos: 0,
                        depth: 0,
                    };
                    T::deserialize_top_level(&context, stream).unwrap()
                }

                let result: $ty = deser(&mut stream);
                assert_eq!(orig, result);
            })*
        }
    }
}

// There are generally 3 cases for everything: top-level, as a struct field,
// and as a collection element.

// Basic primitives
tcase!(tl_false (bool   [Copying ZeroCopy]: false       => "41 00 00"));
tcase!(tl_true  (bool   [Copying ZeroCopy]: true        => "41 01 00"));
tcase!(tl_i8    (i8     [Copying ZeroCopy]: 42i8        => "41 54 00"));
tcase!(tl_i16   (i16    [Copying ZeroCopy]: 300i16      => "41 D8 04 00"));
tcase!(tl_u16   (u16    [Copying ZeroCopy]: 300u16      => "41 AC 02 00"));
tcase!(tl_i32   (i32    [Copying ZeroCopy]: 300i32      => "41 D8 04 00"));
tcase!(tl_u32   (u32    [Copying ZeroCopy]: 300u32      => "41 AC 02 00"));
tcase!(tl_i64   (i64    [Copying ZeroCopy]: 300i64      => "41 D8 04 00"));
tcase!(tl_u64   (u64    [Copying ZeroCopy]: 300u64      => "41 AC 02 00"));
tcase!(tl_isize (isize  [Copying ZeroCopy]: 300isize    => "41 D8 04 00"));
tcase!(tl_usize (usize  [Copying ZeroCopy]: 300usize    => "41 AC 02 00"));
tcase!(sf_false ((bool,)   [Copying ZeroCopy]: (false,)       => "41 00 00"));
tcase!(sf_true  ((bool,)   [Copying ZeroCopy]: (true,)        => "41 01 00"));
tcase!(sf_i8    ((i8,)     [Copying ZeroCopy]: (42i8,)        => "41 54 00"));
tcase!(sf_i16   ((i16,)    [Copying ZeroCopy]: (300i16,)      => "41 D8 04 00"));
tcase!(sf_u16   ((u16,)    [Copying ZeroCopy]: (300u16,)      => "41 AC 02 00"));
tcase!(sf_i32   ((i32,)    [Copying ZeroCopy]: (300i32,)      => "41 D8 04 00"));
tcase!(sf_u32   ((u32,)    [Copying ZeroCopy]: (300u32,)      => "41 AC 02 00"));
tcase!(sf_i64   ((i64,)    [Copying ZeroCopy]: (300i64,)      => "41 D8 04 00"));
tcase!(sf_u64   ((u64,)    [Copying ZeroCopy]: (300u64,)      => "41 AC 02 00"));
tcase!(sf_isize ((isize,)  [Copying ZeroCopy]: (300isize,)    => "41 D8 04 00"));
tcase!(sf_usize ((usize,)  [Copying ZeroCopy]: (300usize,)    => "41 AC 02 00"));
tcase!(ce_false (Vec<bool>   [Copying ZeroCopy]: vec![false]       => "41 00 00"));
tcase!(ce_true  (Vec<bool>   [Copying ZeroCopy]: vec![true]        => "41 01 00"));
tcase!(ce_i8    (Vec<i8>     [Copying ZeroCopy]: vec![42i8]        => "41 54 00"));
tcase!(ce_i16   (Vec<i16>    [Copying ZeroCopy]: vec![300i16]      => "41 D8 04 00"));
tcase!(ce_u16   (Vec<u16>    [Copying ZeroCopy]: vec![300u16]      => "41 AC 02 00"));
tcase!(ce_i32   (Vec<i32>    [Copying ZeroCopy]: vec![300i32]      => "41 D8 04 00"));
tcase!(ce_u32   (Vec<u32>    [Copying ZeroCopy]: vec![300u32]      => "41 AC 02 00"));
tcase!(ce_i64   (Vec<i64>    [Copying ZeroCopy]: vec![300i64]      => "41 D8 04 00"));
tcase!(ce_u64   (Vec<u64>    [Copying ZeroCopy]: vec![300u64]      => "41 AC 02 00"));
tcase!(ce_isize (Vec<isize>  [Copying ZeroCopy]: vec![300isize]    => "41 D8 04 00"));
tcase!(ce_usize (Vec<usize>  [Copying ZeroCopy]: vec![300usize]    => "41 AC 02 00"));

// Tuples
tcase!(tl_empty_tuple (() [Copying ZeroCopy]: () => "01 00"));
tcase!(tl_one_tuple ((u32,) [Copying ZeroCopy]: (5,) => "41 05 00"));
tcase!(tl_two_tuple ((u32,i32) [Copying ZeroCopy]: (5,4) => "41 05 42 08 00"));
tcase!(sf_empty_tuple (((),) [Copying ZeroCopy]: ((),) => "01 00"));
tcase!(sf_one_tuple (((u32,),) [Copying ZeroCopy]: ((5,),) => "C1 41 05 00 00"));
tcase!(sf_two_tuple (((u32,i32),) [Copying ZeroCopy]: ((5,4),) =>
                     "C1 41 05 42 08 00 00"));
tcase!(ce_empty_tuple (Vec<()> [Copying ZeroCopy]: vec![()] => "01 00"));
tcase!(ce_one_tuple (Vec<(u32,)> [Copying ZeroCopy]: vec![(5,)] =>
                     "C1 41 05 00 00"));
tcase!(ce_two_tuple (Vec<(u32,i32)> [Copying ZeroCopy]: vec![(5,4)] =>
                     "C1 41 05 42 08 00 00"));
