//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `Serialize` and `Deserialize` support retrofitted onto std components not
//! defined with the intrinsics.

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

fourleaf_retrofit!(struct Ipv4Addr : {} {} {
    |_context, this|
    [1] octets: [u8;4] = this.octets(),
    { Ok(Ipv4Addr::new(octets[0], octets[1], octets[2], octets[3])) }
});


fourleaf_retrofit!(struct Ipv6Addr : {} {} {
    |_context, this|
    [1] octets: [u8;16] = this.octets(),
    { {
        macro_rules! seg {
            ($n:expr) => {
                ((octets[$n] as u16) << 8) | (octets[$n+1] as u16)
            }
        }
        Ok(Ipv6Addr::new(seg!(0), seg!(2), seg!(4), seg!(6),
                         seg!(8), seg!(10), seg!(12), seg!(14)))
    } }
});

fourleaf_retrofit!(enum IpAddr : {} {} {
    |_context|
    [4] IpAddr::V4(ip) => {
        // TODO This should delegate instead of nesting
        [1] ip: Ipv4Addr = ip,
        { Ok(IpAddr::V4(ip)) }
    },
    [6] IpAddr::V6(ip) => {
        [1] ip: Ipv6Addr = ip,
        { Ok(IpAddr::V6(ip)) }
    },
});
