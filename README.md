# fourleaf

## Introduction

fourleaf is a simple binary serialisation format and library for efficiently
producing portable, forwards- and backwards-compatible messages.

Features:

- Fields are identified by explicit numeric tag, like in thrift or protobufs.
  This avoids the space overhead of naming the fields (like in CBOR or JSON)
  while making it possible to reason about the compatibility of changes (unlike
  simply serialising the fields by order).

- Serialisation is built upon mundane Rust types (as in serde, but unlike
  protobufs) so there is no "impedance mismatch" between normal Rust and the
  serialised structures.

- Full support for tuples, named structs, tuple structs, enums (including
  variants with tuple/named fields).

- Zero-copy deserialisation. That is, you can design your structures so that
  deserialised byte-array-based items point into the original array.

- It is possible to have readers save fields they do not understand and
  preserve them when rewriting the structure.

- Messages can be written to a stream iteratively without knowing anything
  about what comes later in the stream. Similarly, values can be streamed in
  iteratively.

- Padding and exception elements can be used for in-band signaling in streaming
  protocols.

Non-features:

- This is not built upon serde, so you don't get interoperation with existing
  serde-based code for free.

See the [documentation](https://docs.rs/fourleaf) for more information.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
