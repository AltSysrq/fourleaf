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

## Physical Format

The physical format is based around exactly four types: integers, blobs,
structs, and enums. The top-level of the format is always a struct or a flat
stream of structs.

### integers

Integers are encoded as with
[protobufs](https://developers.google.com/protocol-buffers/docs/encoding). Note
that whether zig-zag encoding is used is up to the schema (i.e., signed
integers use it, unsigned don't). It is legal for integers to be in a
denormalised format; for example, the sequence `81 00` can be used to encode
the integer 1.

### blobs

A blob begins with a 64-bit unsigned integer encoded as with normal integer
types. It is followed by exactly that many bytes, which are the raw content of
the blob.

### structs

A struct is composed of an alternating sequence of descriptors and values,
optionally terminated with a terminating descriptor.

A descriptor is simply a one-byte value. The upper two bits indicate the type
(0 = enum, 1 = integer, 2 = blob, 3 = struct) and the lower 6 indicate the tag.
Except in special descriptors, the type indicates how the value following
the descriptor is interpreted.

The tag identifies the field whose value in the struct is being set. Valid tags
are in the range from 1 to 63; a descriptor with a tag of 0 is a special
descriptor.

The descriptor/value pairs in a struct define an ordered sequence of values for
that field. What exactly varying numbers of values mean depends on what is
being deserialised.

There are four types of special descriptor, keyed off the descriptor type:

0 - Followed by no data. End of struct (continue parsing the containing struct,
if any, with the next byte).

1 - Followed by no data. End of document; stop parsing this struct and all
containers.

2 - Followed by a blob. The blob can contain arbitrary data which can be used
for in-band signalling. Typically, it is used as an error message indicating
the encoder failed unexpectedly. This is intended to allow streaming producers
to produce some kind of informative failure after they have committed to
writing a stream.

3 - Padding. The byte is ignored. This could also be used as a heartbeat value
in realtime streaming protocols.

### enum

An enum is followed by an integer indicating the discriminant and then proceeds
the same way as a struct body.

## Logical Formats

Integers are represented directly as integers. `bool` is the integer 0 if false
or 1 if true. Strings, byte arrays, and such are represented as blobs.

`Vec`-like things embedded directly in a struct are represented "flat" ---
i.e., the field holding the `Vec`-like thing is simply repeated once for each
element. `Vec`-like things not directly in a struct are represented as a struct
of their own where each item is bound to field 1. `Option` is treated as a
`Vec`-like with a maximum cardinality of 1.

`HashMap`-like things are represented the way a list of (key,value) pairs would
be.

Anonymous tuples are treated as structs, where the first element is field 1,
the next is 2, and so on.

Unit types are serialised depending on whether they are "struct-like". `()` is
considered the empty tuple and serialised as an empty struct. On the other
hand, things like `PhantomData` are inherently units and serialised as integer
0.

User-defined structs of all kinds are represented as structs, with field tags
specified by the user. Newtype structs can of course directly delegate to
whatever they contain.

User-defined general enums are represented as an enum with a discriminant
selected by the user, and a struct body corresponding to the contents of the
variant. C-like enums can also be serialised as integers.

There is currently no pre-defined way to serialise floating-point values.
