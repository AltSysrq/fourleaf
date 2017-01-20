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

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr,
               SocketAddr, SocketAddrV4, SocketAddrV6};
use std::time::Duration;

use de;
use ser;

fourleaf_retrofit!(struct Ipv4Addr : {} {} {
    |_context, this|
    (*) octets: [u8;4] = this.octets(),
    { Ok(Ipv4Addr::new(octets[0], octets[1], octets[2], octets[3])) }
});


fourleaf_retrofit!(struct Ipv6Addr : {} {} {
    |_context, this|
    (*) octets: [u8;16] = this.octets(),
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
        (*) ip: Ipv4Addr = ip,
        { Ok(IpAddr::V4(ip)) }
    },
    [6] IpAddr::V6(ip) => {
        (*) ip: Ipv6Addr = ip,
        { Ok(IpAddr::V6(ip)) }
    },
});

fourleaf_retrofit!(struct Duration : {} {} {
    |context, this|
    [1] secs: u64 = this.as_secs(),
    [2] nsecs: u32 = this.subsec_nanos(),
    { if nsecs < 1_000_000_000 {
        Ok(Duration::new(secs, nsecs))
    } else {
        Err(de::Error::InvalidValueMsg(
            context.to_string(), "nanoseconds out of range"))
    } }
});

fourleaf_retrofit!(struct SocketAddrV4 : {} {} {
    |_context, this|
    [1] ip: Ipv4Addr = this.ip(),
    [2] port: u16 = this.port(),
    { Ok(SocketAddrV4::new(ip, port)) }
});

fourleaf_retrofit!(struct SocketAddrV6 : {} {} {
    |_context, this|
    [1] ip: Ipv6Addr = this.ip(),
    [2] port: u16 = this.port(),
    [3] flowinfo: u32 = this.flowinfo(),
    [4] scope_id: u32 = this.scope_id(),
    { Ok(SocketAddrV6::new(ip, port, flowinfo, scope_id)) }
});

fourleaf_retrofit!(enum SocketAddr : {} {} {
    |_context|
    [4] SocketAddr::V4(v4) => {
        (*) v4: SocketAddrV4 = v4,
        { Ok(SocketAddr::V4(v4)) }
    },
    [6] SocketAddr::V6(v6) => {
        (*) v6: SocketAddrV6 = v6,
        { Ok(SocketAddr::V6(v6)) }
    },
});

fourleaf_retrofit!(enum Result : {
    impl<T : ser::Serialize, E : ser::Serialize>
    ser::Serialize for Result<T, E>
} {
    impl<R : ::std::io::Read, STYLE,
         T : de::Deserialize<R, STYLE>, E : de::Deserialize<R, STYLE>>
    de::Deserialize<R, STYLE> for Result<T, E>
} {
    |_context|
    [1] Ok(ref t) => {
        (*) t: T = t,
        { Ok(Ok(t)) }
    },
    [2] Err(ref e) => {
        (*) e: E = e,
        { Ok(Err(e)) }
    },
});

#[cfg(test)]
mod test {
    use std::fmt;
    use std::net::*;
    use std::result::Result as StdResult;
    use std::time::Duration;

    use de::*;
    use io;
    use ser::*;
    use test_helpers::parse;

    fn round_trip<T : PartialEq + fmt::Debug + Serialize +
                  for <'a> Deserialize<io::TransparentCursor<&'a [u8]>>>
        (orig: T, binary: &str)
    {
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse(binary), encoded);
        assert_eq!(orig, from_slice_copy(&encoded, &Config::default())
                   .unwrap());
    }

    #[test]
    fn ipv4addr() {
        round_trip(Ipv4Addr::new(127, 0, 0, 1),
                   "81 04 7F 00 00 01 00");
    }

    #[test]
    fn ipv6addr() {
        round_trip(Ipv6Addr::new(0x1234, 0x5678, 0x9ABC, 0xDEF0,
                                 0xDEAD, 0xBEEF, 0xBAAD, 0xC0DE),
                   "81 10 1234 5678 9ABC DEF0 DEAD BEEF BAAD C0DE 00");
    }

    #[test]
    fn ipvaddr_v4() {
        round_trip(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
                   "01 04 81 04 7F 00 00 01 00 00");
    }

    #[test]
    fn ipaddr_v6() {
        round_trip(IpAddr::V6(Ipv6Addr::new(0x1234, 0x5678, 0x9ABC, 0xDEF0,
                                            0xDEAD, 0xBEEF, 0xBAAD, 0xC0DE)),
                   "01 06 81 10 1234 5678 9ABC DEF0 DEAD BEEF BAAD C0DE 00 00");
    }

    #[test]
    fn sockv4addr() {
        round_trip(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 80),
                   "81 04 7F 00 00 01 42 50 00");
    }

    #[test]
    fn sockv6addr() {
        let ip = Ipv6Addr::new(
            0x1234, 0x5678, 0x9ABC, 0xDEF0,
            0xDEAD, 0xBEEF, 0xBAAD, 0xC0DE);
        round_trip(SocketAddrV6::new(ip, 80, 42, 10),
                   "81 10 1234 5678 9ABC DEF0 DEAD BEEF BAAD C0DE \
                    42 50 43 2A 44 0A 00");
    }

    #[test]
    fn sockaddr_v4() {
        let sock = SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 80);
        round_trip(SocketAddr::V4(sock),
                   "01 04 81 04 7F 00 00 01 42 50 00 00");
    }

    #[test]
    fn sockaddr_v6() {
        let ip = Ipv6Addr::new(
            0x1234, 0x5678, 0x9ABC, 0xDEF0,
            0xDEAD, 0xBEEF, 0xBAAD, 0xC0DE);
        let sock = SocketAddrV6::new(ip, 80, 42, 10);
        round_trip(SocketAddr::V6(sock),
                   "01 06 81 10 1234 5678 9ABC DEF0 DEAD BEEF BAAD C0DE \
                    42 50 43 2A 44 0A 00 00");
    }

    #[test]
    fn duration() {
        round_trip(Duration::new(42, 256),
                   "41 2A 42 80 02 00");
    }

    #[test]
    fn duration_rejected_if_nsecs_too_big() {
        match from_slice_copy::<Duration>(
            &parse("41 2A 42 80 94 EB DC 03 00"), &Config::default())
        {
            Ok(r) => panic!("succeeded unexpectedly: {:?}", r),
            Err(Error::InvalidValueMsg(..)) => (),
            Err(e) => panic!("failed for wrong reason: {}", e),
        }
    }

    #[test]
    fn result_ok() {
        let r: StdResult<Ipv4Addr, ()> = Ok(Ipv4Addr::new(127, 0, 0, 1));
        round_trip(r, "01 01 81 04 7F 00 00 01 00 00");
    }

    #[test]
    fn result_err() {
        let r: StdResult<(), Ipv4Addr> = Err(Ipv4Addr::new(127, 0, 0, 1));
        round_trip(r, "01 02 81 04 7F 00 00 01 00 00");
    }
}
