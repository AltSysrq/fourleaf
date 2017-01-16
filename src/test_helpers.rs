//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Parse the given text into a binary value.
///
/// Spaces are ignored. Bytes may be specified in hexadecimal. A single-quote
/// causes all characters up through the single quote to be cast to bytes and
/// added verbatim.
pub fn parse(text: &str) -> Vec<u8> {
    let mut data = Vec::new();

    fn decode_hexit(c: char) -> u8 {
        let n = c as u8;

        if c >= '0' && c <= '9' {
            (n - b'0')
        } else if c >= 'a' && c <= 'f' {
            (n - b'a' + 10) as u8
        } else if c >= 'A' && c <= 'F' {
            (n - b'A' + 10) as u8
        } else {
            panic!("Invalid hexit {}", c)
        }
    }

    let mut chars = text.chars();
    while let Some(first) = chars.next() {
        if ' ' == first {
            // ignore
        } else if '\'' == first {
            loop {
                let c = chars.next().unwrap();
                if '\'' == c {
                    break;
                } else {
                    data.push(c as u8);
                }
            }
        } else {
            data.push((decode_hexit(first) << 4) |
                      decode_hexit(chars.next().unwrap()));
        }
    }

    data
}

