//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::borrow::Cow;
use std::collections::*;
use std::io::Read;
use std::rc::Rc;
use std::sync::Arc;

use de::*;
use ser::*;
use stream::{self, Stream};
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
                    let context = Context::top(&config);
                    T::deserialize_top_level(&context, stream).unwrap()
                }

                let result: $ty = deser(&mut stream);
                assert_eq!(orig, result);
            })*
        }
    }
}

macro_rules! ll {
    ($($val:expr),*) => {{
        let mut _ll = LinkedList::new();
        $(_ll.push_back($val);)*
        _ll
    }}
}

macro_rules! vd {
    ($($val:expr),*) => {{
        let mut _vd = VecDeque::new();
        $(_vd.push_back($val);)*
        _vd
    }}
}

macro_rules! bts {
    ($($val:expr),*) => {{
        let mut _bts = BTreeSet::new();
        $(_bts.insert($val);)*
        _bts
    }}
}

macro_rules! hs {
    ($($val:expr),*) => {{
        let mut _hs = HashSet::new();
        $(_hs.insert($val);)*
        _hs
    }}
}

macro_rules! bh {
    ($($val:expr),*) => {{
        let mut _bh = BinaryHeap::new();
        $(_bh.push($val);)*
        _bh
    }}
}

macro_rules! btm {
    ($($key:expr => $val:expr),*) => {{
        let mut _btm = BTreeMap::new();
        $(_btm.insert($key, $val);)*
        _btm
    }}
}

macro_rules! hm {
    ($($key:expr => $val:expr),*) => {{
        let mut _hm = HashMap::new();
        $(_hm.insert($key, $val);)*
        _hm
    }}
}

// There are generally 3 cases for everything: top-level, as a struct field,
// and as a collection element.

// Basic primitives
tcase!(tl_false (bool   [Copying ZeroCopy]: false       => "41 00 00"));
tcase!(tl_true  (bool   [Copying ZeroCopy]: true        => "41 01 00"));
tcase!(tl_i8    (i8     [Copying ZeroCopy]: 42i8        => "41 54 00"));
tcase!(tl_u8    (u8     [Copying ZeroCopy]: 42u8        => "41 2A 00"));
tcase!(tl_i16   (i16    [Copying ZeroCopy]: 300i16      => "41 D8 04 00"));
tcase!(tl_u16   (u16    [Copying ZeroCopy]: 300u16      => "41 AC 02 00"));
tcase!(tl_i32   (i32    [Copying ZeroCopy]: 300i32      => "41 D8 04 00"));
tcase!(tl_u32   (u32    [Copying ZeroCopy]: 300u32      => "41 AC 02 00"));
tcase!(tl_i64   (i64    [Copying ZeroCopy]: 300i64      => "41 D8 04 00"));
tcase!(tl_u64   (u64    [Copying ZeroCopy]: 300u64      => "41 AC 02 00"));
tcase!(tl_isize (isize  [Copying ZeroCopy]: 300isize    => "41 D8 04 00"));
tcase!(tl_usize (usize  [Copying ZeroCopy]: 300usize    => "41 AC 02 00"));
tcase!(sf_false (((),bool)   [Copying ZeroCopy]: ((),false)       => "C1 00 42 00 00"));
tcase!(sf_true  (((),bool)   [Copying ZeroCopy]: ((),true)        => "C1 00 42 01 00"));
tcase!(sf_i8    (((),i8)     [Copying ZeroCopy]: ((),42i8)        => "C1 00 42 54 00"));
tcase!(sf_u8    (((),u8)     [Copying ZeroCopy]: ((),42u8)        => "C1 00 42 2A 00"));
tcase!(sf_i16   (((),i16)    [Copying ZeroCopy]: ((),300i16)      => "C1 00 42 D8 04 00"));
tcase!(sf_u16   (((),u16)    [Copying ZeroCopy]: ((),300u16)      => "C1 00 42 AC 02 00"));
tcase!(sf_i32   (((),i32)    [Copying ZeroCopy]: ((),300i32)      => "C1 00 42 D8 04 00"));
tcase!(sf_u32   (((),u32)    [Copying ZeroCopy]: ((),300u32)      => "C1 00 42 AC 02 00"));
tcase!(sf_i64   (((),i64)    [Copying ZeroCopy]: ((),300i64)      => "C1 00 42 D8 04 00"));
tcase!(sf_u64   (((),u64)    [Copying ZeroCopy]: ((),300u64)      => "C1 00 42 AC 02 00"));
tcase!(sf_isize (((),isize)  [Copying ZeroCopy]: ((),300isize)    => "C1 00 42 D8 04 00"));
tcase!(sf_usize (((),usize)  [Copying ZeroCopy]: ((),300usize)    => "C1 00 42 AC 02 00"));
tcase!(ce_false (Vec<bool>   [Copying ZeroCopy]: vec![false]       => "41 00 00"));
tcase!(ce_true  (Vec<bool>   [Copying ZeroCopy]: vec![true]        => "41 01 00"));
tcase!(ce_i8    (Vec<i8>     [Copying ZeroCopy]: vec![42i8]        => "41 54 00"));
// No test with `Vec<u8>` here because it behaves specially.
//tcase!(ce_u8    (Vec<u8>     [Copying ZeroCopy]: vec![42u8]        => "41 2A 00"));
tcase!(ce_i16   (Vec<i16>    [Copying ZeroCopy]: vec![300i16]      => "41 D8 04 00"));
tcase!(ce_u16   (Vec<u16>    [Copying ZeroCopy]: vec![300u16]      => "41 AC 02 00"));
tcase!(ce_i32   (Vec<i32>    [Copying ZeroCopy]: vec![300i32]      => "41 D8 04 00"));
tcase!(ce_u32   (Vec<u32>    [Copying ZeroCopy]: vec![300u32]      => "41 AC 02 00"));
tcase!(ce_i64   (Vec<i64>    [Copying ZeroCopy]: vec![300i64]      => "41 D8 04 00"));
tcase!(ce_u64   (Vec<u64>    [Copying ZeroCopy]: vec![300u64]      => "41 AC 02 00"));
tcase!(ce_isize (Vec<isize>  [Copying ZeroCopy]: vec![300isize]    => "41 D8 04 00"));
tcase!(ce_usize (Vec<usize>  [Copying ZeroCopy]: vec![300usize]    => "41 AC 02 00"));

// Tuples
tcase!(tl_empty_tuple (() [Copying ZeroCopy]: () => "C1 00 00"));
tcase!(tl_one_tuple ((u32,) [Copying ZeroCopy]: (5,) => "41 05 00"));
tcase!(tl_two_tuple ((u32,i32) [Copying ZeroCopy]: (5,4) => "41 05 42 08 00"));
tcase!(sf_empty_tuple (((),()) [Copying ZeroCopy]: ((),()) => "C1 00 C2 00 00"));
tcase!(sf_one_tuple (((), (u32,)) [Copying ZeroCopy]: ((),(5,)) => "C1 00 C2 41 05 00 00"));
tcase!(sf_two_tuple (((),(u32,i32)) [Copying ZeroCopy]: ((),(5,4)) =>
                     "C1 00 C2 41 05 42 08 00 00"));
tcase!(ce_empty_tuple (Vec<()> [Copying ZeroCopy]: vec![()] => "C1 00 00"));
tcase!(ce_one_tuple (Vec<(u32,)> [Copying ZeroCopy]: vec![(5,)] =>
                     "C1 41 05 00 00"));
tcase!(ce_two_tuple (Vec<(u32,i32)> [Copying ZeroCopy]: vec![(5,4)] =>
                     "C1 41 05 42 08 00 00"));

// Byte containers
tcase!(tl_str (&str [ZeroCopy]: "plugh" => "81 05 'plugh' 00"));
tcase!(tl_string (String [Copying ZeroCopy]: "plugh".to_owned() =>
                  "81 05 'plugh' 00"));
tcase!(tl_byte_slice (&[u8] [ZeroCopy]: b"plugh\xff" =>
                      "81 06 'plugh' FF 00"));
tcase!(tl_vec_bytes (Vec<u8> [Copying ZeroCopy]: vec![42, 255] =>
                     "81 02 2A FF 00"));
tcase!(tl_byte_array ([u8;4] [Copying ZeroCopy]: [0, 1, 2, 3] =>
                      "81 04 00 01 02 03 00"));
tcase!(sf_str (((),&str) [ZeroCopy]: ((),"plugh") => "C1 00 82 05 'plugh' 00"));
tcase!(sf_string (((),String) [Copying ZeroCopy]: ((),"plugh".to_owned()) =>
                  "C1 00 82 05 'plugh' 00"));
tcase!(sf_byte_slice (((),&[u8]) [ZeroCopy]: ((),b"plugh\xff") =>
                      "C1 00 82 06 'plugh' FF 00"));
tcase!(sf_vec_bytes (((),Vec<u8>) [Copying ZeroCopy]: ((),vec![42, 255]) =>
                     "C1 00 82 02 2A FF 00"));
tcase!(sf_byte_array (((),[u8;4]) [Copying ZeroCopy]: ((),[0, 1, 2, 3]) =>
                      "C1 00 82 04 00 01 02 03 00"));
tcase!(ce_str (Vec<&str> [ZeroCopy]: vec!["plugh"] =>
               "81 05 'plugh' 00"));
tcase!(ce_string (Vec<String> [Copying ZeroCopy]: vec!["plugh".to_owned()] =>
                  "81 05 'plugh' 00"));
tcase!(ce_byte_slice (Vec<&[u8]> [ZeroCopy]: vec![b"plugh\xff"] =>
                      "81 06 'plugh' FF 00"));
tcase!(ce_vec_bytes (Vec<Vec<u8>> [Copying ZeroCopy]: vec![vec![42, 255]] =>
                     "81 02 2A FF 00"));
tcase!(ce_byte_array (Vec<[u8;4]> [Copying ZeroCopy]: vec![[0, 1, 2, 3]] =>
                      "81 04 00 01 02 03 00"));

// Empty collections
tcase!(tl_e_option (Option<u32> [Copying ZeroCopy]: None => "00"));
tcase!(tl_e_vec (Vec<u32> [Copying ZeroCopy]: vec![] => "00"));
tcase!(tl_e_vd (VecDeque<u32> [Copying ZeroCopy]: vd![] => "00"));
tcase!(tl_e_ll (LinkedList<u32> [Copying ZeroCopy]: ll![] => "00"));
tcase!(tl_e_bts (BTreeSet<u32> [Copying ZeroCopy]: bts![] => "00"));
tcase!(tl_e_hs (HashSet<u32> [Copying ZeroCopy]: hs![] => "00"));
tcase!(tl_e_array ([u32;0] [Copying ZeroCopy]: [] => "00"));
tcase!(sf_e_option (((),Option<u32>) [Copying ZeroCopy]: ((),None) => "C1 00 00"));
tcase!(sf_e_vec (((),Vec<u32>) [Copying ZeroCopy]: ((),vec![]) => "C1 00 00"));
tcase!(sf_e_vd (((),VecDeque<u32>) [Copying ZeroCopy]: ((),vd![]) => "C1 00 00"));
tcase!(sf_e_ll (((),LinkedList<u32>) [Copying ZeroCopy]: ((),ll![]) => "C1 00 00"));
tcase!(sf_e_bts (((),BTreeSet<u32>) [Copying ZeroCopy]: ((),bts![]) => "C1 00 00"));
tcase!(sf_e_hs (((),HashSet<u32>) [Copying ZeroCopy]: ((),hs![]) => "C1 00 00"));
tcase!(sf_e_array (((),[u32;0]) [Copying ZeroCopy]: ((),[]) => "C1 00 00"));
tcase!(ce_e_option (Vec<Option<u32>> [Copying ZeroCopy]: vec![None] =>
                    "C1 00 00"));
tcase!(ce_e_vec (Vec<Vec<u32>> [Copying ZeroCopy]: vec![vec![]] =>
                 "C1 00 00"));
tcase!(ce_e_vd (Vec<VecDeque<u32>> [Copying ZeroCopy]: vec![vd![]] =>
                "C1 00 00"));
tcase!(ce_e_ll (Vec<LinkedList<u32>> [Copying ZeroCopy]: vec![ll![]] =>
                "C1 00 00"));
tcase!(ce_e_bts (Vec<BTreeSet<u32>> [Copying ZeroCopy]: vec![bts![]] =>
                 "C1 00 00"));
tcase!(ce_e_hs (Vec<HashSet<u32>> [Copying ZeroCopy]: vec![hs![]] =>
                "C1 00 00"));
tcase!(te_e_array (Vec<[u32;0]> [Copying ZeroCopy]: vec![[]] =>
                   "C1 00 00"));

// Populated collections
tcase!(tl_p_option (Option<u32> [Copying ZeroCopy]: Some(5) => "41 05 00"));
tcase!(tl_p_vec (Vec<u32> [Copying ZeroCopy]: vec![5, 6] =>
                 "41 05 41 06 00"));
tcase!(tl_p_vd (VecDeque<u32> [Copying ZeroCopy]: vd![5, 6] =>
                "41 05 41 06 00"));
tcase!(tl_p_ll (LinkedList<u32> [Copying ZeroCopy]: ll![5, 6] =>
                "41 05 41 06 00"));
tcase!(tl_p_bts (BTreeSet<u32> [Copying ZeroCopy]: bts![5, 6] =>
                 "41 05 41 06 00"));
// Because `HashSet` has nondeterministic order, we only test it with one
// element here.
tcase!(tl_p_hs (HashSet<u32> [Copying ZeroCopy]: hs![5] =>
                "41 05 00"));
tcase!(tl_p_array ([u32;2] [Copying ZeroCopy]: [5, 6] =>
                   "41 05 41 06 00"));
tcase!(sf_p_option (((),Option<u32>) [Copying ZeroCopy]: ((),Some(5)) =>
                    "C1 00 42 05 00"));
tcase!(sf_p_vec (((),Vec<u32>) [Copying ZeroCopy]: ((),vec![5, 6]) =>
                 "C1 00 42 05 42 06 00"));
tcase!(sf_p_vd (((),VecDeque<u32>) [Copying ZeroCopy]: ((),vd![5, 6]) =>
                "C1 00 42 05 42 06 00"));
tcase!(sf_p_ll (((),LinkedList<u32>) [Copying ZeroCopy]: ((),ll![5, 6]) =>
                "C1 00 42 05 42 06 00"));
tcase!(sf_p_bts (((),BTreeSet<u32>) [Copying ZeroCopy]: ((),bts![5, 6]) =>
                 "C1 00 42 05 42 06 00"));
tcase!(sf_p_hs (((),HashSet<u32>) [Copying ZeroCopy]: ((),hs![5]) =>
                "C1 00 42 05 00"));
tcase!(sf_p_array (((),[u32;2]) [Copying ZeroCopy]: ((),[5,6]) =>
                   "C1 00 42 05 42 06 00"));
tcase!(ce_p_option (Vec<Option<u32>> [Copying ZeroCopy]:
                    vec![Some(5), Some(6)] => "C1 41 05 00 C1 41 06 00 00"));
tcase!(ce_p_vec (Vec<Vec<u32>> [Copying ZeroCopy]:
                 vec![vec![5, 6], vec![7, 8]] =>
                 "C1 41 05 41 06 00 C1 41 07 41 08 00 00"));
tcase!(ce_p_vd (Vec<VecDeque<u32>> [Copying ZeroCopy]:
                vec![vd![5, 6], vd![7, 8]] =>
                 "C1 41 05 41 06 00 C1 41 07 41 08 00 00"));
tcase!(ce_p_ll (Vec<LinkedList<u32>> [Copying ZeroCopy]:
                vec![ll![5, 6], ll![7, 8]] =>
                 "C1 41 05 41 06 00 C1 41 07 41 08 00 00"));
tcase!(ce_p_bts (Vec<BTreeSet<u32>> [Copying ZeroCopy]:
                vec![bts![5, 6], bts![7, 8]] =>
                 "C1 41 05 41 06 00 C1 41 07 41 08 00 00"));
tcase!(ce_p_hs (Vec<HashSet<u32>> [Copying ZeroCopy]:
                vec![hs![5], hs![7]] =>
                 "C1 41 05 00 C1 41 07 00 00"));
tcase!(ce_p_array (Vec<[u32;2]> [Copying ZeroCopy]:
                vec![[5, 6], [7, 8]] =>
                 "C1 41 05 41 06 00 C1 41 07 41 08 00 00"));

// Empty maps
tcase!(tl_e_btm (BTreeMap<u32,u32> [Copying ZeroCopy]: btm![] => "00"));
tcase!(tl_e_hm (HashMap<u32,u32> [Copying ZeroCopy]: hm![] => "00"));
tcase!(sf_e_btm (((),BTreeMap<u32,u32>) [Copying ZeroCopy]: ((),btm![]) => "C1 00 00"));
tcase!(sf_e_hm (((),HashMap<u32,u32>) [Copying ZeroCopy]: ((),hm![]) => "C1 00 00"));
tcase!(ce_e_btm (Vec<BTreeMap<u32,u32>> [Copying ZeroCopy]: vec![btm![]] =>
                 "C1 00 00"));
tcase!(ce_e_hm (Vec<HashMap<u32,u32>> [Copying ZeroCopy]: vec![hm![]] =>
                "C1 00 00"));

// Populated maps. As with `HashSet`, we only put one pair in `HashMap` since
// order is nondeterministic.
tcase!(tl_p_btm (BTreeMap<u32,u32> [Copying ZeroCopy]:
                 btm![5 => 6, 7 => 8] =>
                 "C1 41 05 42 06 00 C1 41 07 42 08 00 00"));
tcase!(tl_p_hm (HashMap<u32,u32> [Copying ZeroCopy]: hm![5 => 6] =>
                "C1 41 05 42 06 00 00"));
tcase!(sf_p_btm (((),BTreeMap<u32,u32>) [Copying ZeroCopy]:
                  ((),btm![5 => 6, 7 => 8]) =>
                  "C1 00 C2 41 05 42 06 00 C2 41 07 42 08 00 00"));
tcase!(sf_p_hm (((),HashMap<u32,u32>) [Copying ZeroCopy]: ((),hm![5 => 6]) =>
                 "C1 00 C2 41 05 42 06 00 00"));
tcase!(ce_p_btm (Vec<BTreeMap<u32,u32>> [Copying ZeroCopy]:
                 vec![btm![1 => 2, 3 => 4], btm![5 => 6, 7 => 8]] =>
                 "C1 C1 41 01 42 02 00 C1 41 03 42 04 00 00 \
                  C1 C1 41 05 42 06 00 C1 41 07 42 08 00 00 00"));
tcase!(ce_p_hm (Vec<HashMap<u32,u32>> [Copying ZeroCopy]:
                vec![hm![5 => 6], hm![7 => 8]] =>
                "C1 C1 41 05 42 06 00 00 C1 C1 41 07 42 08 00 00 00"));

// Boxed items
tcase!(tl_box (Box<u32> [Copying ZeroCopy]: Box::new(5) => "41 05 00"));
tcase!(tl_rc (Rc<u32> [Copying ZeroCopy]: Rc::new(5) => "41 05 00"));
tcase!(tl_arc (Arc<u32> [Copying ZeroCopy]: Arc::new(5) => "41 05 00"));
tcase!(sf_box (((),Box<u32>) [Copying ZeroCopy]: ((),Box::new(5)) =>
               "C1 00 42 05 00"));
tcase!(sf_rc (((),Rc<u32>) [Copying ZeroCopy]: ((),Rc::new(5)) =>
              "C1 00 42 05 00"));
tcase!(sf_arc (((),Arc<u32>) [Copying ZeroCopy]: ((),Arc::new(5)) =>
               "C1 00 42 05 00"));
tcase!(ce_box (Vec<Box<u32>> [Copying ZeroCopy]: vec![Box::new(5)] =>
               "41 05 00"));
tcase!(ce_rc (Vec<Rc<u32>> [Copying ZeroCopy]: vec![Rc::new(5)] =>
              "41 05 00"));
tcase!(ce_arc (Vec<Arc<u32>> [Copying ZeroCopy]: vec![Arc::new(5)] =>
               "41 05 00"));

#[test]
fn binary_heap_basically_works() {
    // Not as thorough as the others, but it uses the same macro and so should
    // work the same regardless.
    let orig: BinaryHeap<u32> = bh![5];
    let mut encoded = Vec::new();
    {
        let mut stream = Stream::new(&mut encoded);
        orig.serialize_top_level(&mut stream).unwrap();
        stream.commit().unwrap();
    }

    assert_eq!(parse("41 05 00"), encoded);

    let config = Config::default();
    let mut res: BinaryHeap<u32> = from_slice_copy(&encoded, &config).unwrap();
    assert_eq!(1, res.len());
    assert_eq!(5, res.pop().unwrap());
}

#[test]
fn cow_desers_according_to_style() {
    let orig: Cow<str> = Cow::Borrowed("hello world");
    let encoded = to_vec(&orig).unwrap();

    assert_eq!(parse("81 0B 'hello world' 00"), encoded);

    let config = Config::default();
    {
        let res: Cow<'static, str> =
            from_slice_copy(&encoded, &config).unwrap();
        match res {
            Cow::Owned(s) => assert_eq!("hello world", s),
            Cow::Borrowed(_) => panic!("somehow borrowed 'static?"),
        }
    }
    {
        let res: Cow<str> =
            from_slice_borrow(&encoded, &config).unwrap();
        match res {
            Cow::Owned(_) => panic!("copied instead of borrowing"),
            Cow::Borrowed(s) => assert_eq!("hello world", s),
        }
    }
}

#[test]
fn unknown_fields_ignored_by_default() {
    let data = parse("41 01 42 02 00");
    let res = from_slice_copy::<(u32,)>(&data, &Config::default()).unwrap();
    assert_eq!((1,), res);
}

macro_rules! ecase {
    ($name:ident ($config:ident $input:expr => $ty:ty : $err:pat)
     $config_edits:block) => {
        #[test] #[allow(unused_mut)]
        fn $name() {
            let data = parse($input);
            let mut $config = Config::default();
            $config_edits;
            match from_slice_copy::<$ty>(&data, &$config) {
                Ok(_) => panic!("unexpectedly succeeded"),
                Err($err) => (),
                Err(e) => panic!("failed for wrong reason: {}", e),
            }
        }
    }
}

ecase!(tuple_field_not_populated (config "00" => (u32,) :
                                  Error::RequiredFieldMissing(_)) { });
ecase!(recursion_limit_exceeded (config "C1 C1 C1 C1 C1 C1 C1 C1" =>
                                 Vec<Vec<Vec<Vec<Vec<u32>>>>> :
                                 Error::RecursionLimitExceeded(_))
       { config.recursion_limit = 4; });

ecase!(max_collect_exceeded_on_vec
       (config "4100 4100 4100 4100 4100 4100" => Vec<u32> :
        Error::MaxCollectExceeded(_))
       { config.max_collect = 4; });

ecase!(max_collect_exceeded_on_hash_map
       (config "C14100420000 C14101420100 C14102420200 C14103420300 \
                C14104420400 C14105420500 C14106420600 C14107420700 00"
        => HashMap<u32, u32> : Error::MaxCollectExceeded(_))
       { config.max_collect = 4; });

ecase!(max_blob_exceeded (config "81 0B 'hello world' 00" => String :
                          Error::Stream(_, stream::Error::LargeBlob(..)))
       { config.max_blob = 5; });

ecase!(unknown_field_rejected (config "42 00 00" => () :
                               Error::UnknownField(_, 2, 0))
       { config.ignore_unknown_fields = false; });

ecase!(option_with_two_values (config "41 00 41 01 00" => Option<u32> :
                               Error::FieldOccursTooManyTimes(_, 1)) { });

ecase!(fixed_array_with_no_values (config "00" => [u32;4] :
                                   Error::RequiredFieldMissing(_)) { });
ecase!(fixed_array_with_too_few_values
       (config "41 00 41 01 00" => [u32;4] :
        Error::FieldOccursTooFewTimes(_, 4)) { });
ecase!(fixed_array_with_too_many_values
       (config "41 00 41 01 41 02 41 03 41 04 00" => [u32;4] :
        Error::FieldOccursTooManyTimes(_, 4)) { });

ecase!(string_invalid_utf8 (config "81 06 'plugh' FF 00" => String :
                            Error::InvalidValue(..)) { });

ecase!(byte_array_wrong_length (config "81 01 01 00" => [u8;4] :
                                Error::InvalidValueMsg(..)) { });
