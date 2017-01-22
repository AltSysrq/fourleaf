//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Retrofits fourleaf support onto arbitrary types.
///
/// That is, it generates matching `Serialize` and `Deserialize`
/// implementations for them. Note that this documentation skims over fourleaf
/// concepts in general; you should read the crate documentation for an
/// introduction to these and more detail.
///
/// This is currently a bit verbose. At some point in the future there may be
/// something nicer.
///
/// The basic structure of the syntax for this macro is
///
/// ```ignore
/// fourleaf_retrofit!(struct /* or `enum` */ SomeType :
///                    { /* Serialize impl */ } { /* Deserialize impl */ } {
///     /* body... */
///  });
/// ```
///
/// In many cases, the "Serialize impl" and "Deserialize impl" sections can be
/// left blank (i.e., empty braces) and will be filled in automatically.
///
/// ## Struct bodies
///
/// The body of a structure begins with the name of the `Context` variable and
/// the variable holding a reference to the struct being serialised written in
/// pipes (i.e., like a closure), followed by any number of field declarations,
/// followed by a braced expression to construct the type. Each field is a tag
/// number in brackets, the logical field name, a colon, the deserialised type
/// of the field, an `=`, and an expression to read the value of the field at
/// serialisation time. This is clearer with an example:
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// struct SimpleStruct {
///   foo: u32,
///   bar: u64,
/// }
///
/// fourleaf_retrofit!(struct SimpleStruct : {} {} {
///   |_context, this|
///   [1] foo: u32 = this.foo,
///   [2] bar: u64 = this.bar,
///   { Ok(SimpleStruct { foo: foo, bar: bar }) }
/// });
/// # fn main() { }
/// ```
///
/// During serialisation, `this` is available to the accessors (the right-hand
/// side of the `=`), and each accessor is evaluated to determine the
/// serialised value for each field.
///
/// During deserialisation, `_context` is available to the constructor
/// expression, as well as every logical field name, which are bound to exactly
/// the types specified. The constructor expression can perform arbitrary
/// validation on the inputs (and, e.g., return `Err` if validation fails,
/// using the context to indicate the location of the problem).
///
/// This is all somewhat repetitive for simple structs like this, but is
/// necessary for dealing with structs with non-public members. For example:
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// mod some_other_module {
///   pub struct TheStruct {
///     foo: u32,
///     bar: u64,
///   }
///
///   impl TheStruct {
///     pub fn new(foo: u32, bar: u64) -> Self {
///       TheStruct { foo: foo, bar: bar }
///     }
///     pub fn foo(&self) -> u32 { self.foo }
///     pub fn bar(&self) -> u64 { self.bar }
///   }
/// }
///
/// use some_other_module::TheStruct;
/// fourleaf_retrofit!(struct TheStruct : {} {} {
///   |_context, this|
///   [1] foo: u32 = this.foo(),
///   [2] bar: u64 = this.bar(),
///   { Ok(TheStruct::new(foo, bar)) }
/// });
/// # fn main() { }
/// ```
///
/// Beware that there is nothing constraining the serialised type of each field
/// to correspond to the deserialised field, since in many cases they won't
/// (e.g., `String` on construction, but `&str` via accessor). The macro will
/// not prevent declaring a struct whose serialised format is incompatible with
/// its deserialiser.
///
/// ### Field delegation
///
/// Instead of listing multiple tagged fields, you can instead have a single
/// field with the pseudo-tag `(*)`. This will cause the implementation to
/// delegate to that field for serialisation and deserialisation.
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// struct Wrapper(Vec<u8>);
///
/// fourleaf_retrofit!(struct Wrapper : {} {} {
///   |_context, this|
///   (*) inner: Vec<u8> = &this.0,
///   { Ok(Wrapper(inner)) }
/// });
/// # fn main() { }
/// ```
///
/// Note that this is not perfectly transparent delegation. The inner value
/// will always be serialised as a single element, which will cause collections
/// to be wrapped in a struct element, for example.
///
/// ### Preserving unknown fields
///
/// A field with the pseudo-tag `(?)` will cause all unknown fields on
/// deserialisation to be passed to that field, and for that field's body to be
/// concatenated with the container's body on serialisation. In conjunction
/// with `unknown::UnknownFields`, this allows for making structures which
/// preserve unknown fields. (That is, structures such that if deserialised and
/// deserialised will have all fields in the original, including those that the
/// reader did not understand.)
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// use fourleaf::adapt::Copied;
/// use fourleaf::UnknownFields;
///
/// struct UnknownPreserving {
///   foo: u32,
///   bar: u64,
///   unknown: UnknownFields<'static>,
/// }
///
/// fourleaf_retrofit!(struct UnknownPreserving : {} {} {
///   |_context, this|
///   [1] foo: u32 = this.foo,
///   [2] bar: u64 = this.bar,
///   (?) unknown: Copied<UnknownFields<'static>> = &this.unknown,
///   { Ok(UnknownPreserving { foo: foo, bar: bar, unknown: unknown.0 }) }
/// });
/// # fn main() { }
/// ```
///
/// Having an unknown field handler effectively suppresses the
/// `ignore_unknown_fields` configuration; i.e., an unknown field will alway
/// simply be added to the catch-all field instead of resulting in an error.
///
/// ## Enum bodies
///
/// An enum body begins with the name for the context variable in pipes. It is
/// followed by a number of variants. Each variant is a numeric discriminant in
/// brackets, a pattern matching that enum case, and a variant body. The
/// variant body is essentially like a struct body without the `context, this`
/// variable names at the front.
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// enum SimpleEnum {
///   Foo(u32, u64),
///   Bar(String),
/// }
///
/// fourleaf_retrofit!(enum SimpleEnum : {} {} {
///   |_context|
///   [1] SimpleEnum::Foo(a, b) => {
///     [1] a: u32 = a,
///     [2] b: u64 = b,
///     { Ok(SimpleEnum::Foo(a, b)) }
///   },
///   [2] SimpleEnum::Bar(ref a) => {
///     [1] a: String = a,
///     { Ok(SimpleEnum::Bar(a)) }
///   },
/// });
/// # fn main() { }
/// ```
///
/// On serialisation , the value to be serialised is matched against each
/// pattern. In the one that matches, the discriminant in the tag is written,
/// and then the value for each field, using the accessor to obtain the value
/// of the field. Note that unlike struct bodies, there is no `this` variable;
/// instead, the accessors can use the variables that were bound in the pattern
/// for that variant.
///
/// Serialisation works much the same way as for structs. The discriminant is
/// matched to one of the numeric discriminants, then each field is
/// deserialised, and then the constructor expression evaluated. Notice that
/// the constructor expression is also responsible for providing the correct
/// variant.
///
/// The `(*)` and `(?)` pseudo-tags are also available in variant bodies and
/// behave the same way as for structs.
///
/// ### Preserving unknown variants
///
/// To crate enums that can represent unknown deserialised values and
/// reserialise to the same thing, a `(?)` pseudo-discriminant similar to the
/// `(?)` pseudo-tag is available. This must be the last variant, and will
/// cause that variant to be deserialised from any input that does not match
/// any declared discriminant.
///
/// The "catch-all" variant's body must begin with an extra field with the
/// `(=)` pseudo-tag and with the `u64` type; this field is used to store the
/// discriminant that was read during deserialisation. This can be used in
/// conjunction with the `(?)` pseudo-tag to make an enum which preserves all
/// input.
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// use fourleaf::adapt::Copied;
/// use fourleaf::UnknownFields;
///
/// enum UnknownPreservingEnum {
///   Foo(u32, UnknownFields<'static>),
///   Bar(String, UnknownFields<'static>),
///   Unknown(u64, UnknownFields<'static>),
/// }
///
/// fourleaf_retrofit!(enum UnknownPreservingEnum : {} {} {
///   |_context|
///   [1] UnknownPreservingEnum::Foo(a, ref unknown) => {
///     [1] a: u32 = a,
///     (?) unknown: Copied<UnknownFields<'static>> = unknown,
///     { Ok(UnknownPreservingEnum::Foo(a, unknown.0)) }
///   },
///   [2] UnknownPreservingEnum::Bar(ref a, ref unknown) => {
///     [1] a: String = a,
///     (?) unknown: Copied<UnknownFields<'static>> = unknown,
///     { Ok(UnknownPreservingEnum::Bar(a, unknown.0)) }
///   },
///   (?) UnknownPreservingEnum::Unknown(discriminant, ref fields) => {
///     (=) discriminant: u64 = discriminant,
///     [1] fields: Copied<UnknownFields<'static>> = fields,
///     { Ok(UnknownPreservingEnum::Unknown(discriminant, fields.0)) }
///   },
/// });
/// # fn main() { }
/// ```
///
/// ## Use with types not in your crate
///
/// If you want to make a `Serialize` and `Deserialize` implementation for a
/// type not in your crate, you will need to wrap it in a newtype due to the
/// trait orphan rules. Fortunately, this is easy with this macro, though note
/// that the `struct`/`enum` distinction applies to the item being wrapped. For
/// example, if we wanted to serialise a custom `Result` type a way different
/// from the default implementation:
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// struct MyResult(Result<u32,u64>);
///
/// // Need to use `enum` because we're serialising it as an enum, even though
/// // `MyResult` itself is a struct.
/// fourleaf_retrofit!(enum MyResult : {} {} {
///   |_context|
///   [1] MyResult(Ok(a)) => {
///     [1] a: u32 = a,
///     { Ok(MyResult(Ok(a))) }
///   },
///   [2] MyResult(Err(e)) => {
///     [1] e: u64 = e,
///     { Ok(MyResult(Err(e))) }
///   },
/// });
/// # fn main() { }
/// ```
///
/// Notice how the patterns effectively unwrap the newtype away, and the
/// constructors add it back in. The pattern for structs is similar, in that
/// you can simply add `.0` in the accessors to go from the newtype to its
/// contents.
///
/// ## The `impl` sections
///
/// The two empty brace pairs in the above examples are used to provide
/// alternate `impl` declarations for `Serialize` and `Deserialize`. By
/// default, they expand to approximately:
///
/// ```ignore
/// impl Serialize for TYPE
/// impl<R : Read, STYLE> Deserialize<R, STYLE> for TYPE
/// ```
///
/// For many types, this is sufficient. However, if your type has special
/// requirements, you may need to provide these manually. Note that whatever
/// `impl` declaration is provided, it *must* have type parameters `R : Read`
/// and `STYLE` somewhere.
///
/// ### Types with special requirements
///
/// If a type cannot implement `Deserialize` for every `<R,STYLE>` pair, a
/// custom `impl` line will be needed for the second block. For example:
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// use std::io::Read;
///
/// use fourleaf::{Deserialize, UnknownFields};
///
/// struct MyStruct {
///   foo: u32,
///   unknown: UnknownFields<'static>,
/// }
///
/// fourleaf_retrofit!(struct MyStruct : {} {
///   impl<R : Read, STYLE> Deserialize<R, STYLE>
///   // `UnknownFields<'static>` cannot be deserialised from, eg,
///   // `<&'a [u8], style::ZeroCopy>` unless `'a` is `'static`, so we
///   // need this extra constraint on the implementation.
///   //
///   // The prior examples side-stepped this issue by deserialising
///   // the field wrapped in `Copied`.
///   for MyStruct where UnknownFields<'static>: Deserialize<R, STYLE>
/// } {
///   |_context, this|
///   [1] foo: u32 = this.foo,
///   (?) unknown: UnknownFields<'static> = &this.unknown,
///   { Ok(MyStruct { foo: foo, unknown: unknown }) }
/// });
/// # fn main() { }
/// ```
///
/// ### Generic types
///
/// If the type in question has generic parameters, defining both blocks will
/// be necessary so that those parameters are filled.
///
/// ```no_run
/// #[macro_use] extern crate fourleaf;
///
/// use std::borrow::Cow;
/// use std::io::Read;
///
/// use fourleaf::{Deserialize, Serialize};
///
/// enum MyEnum<'a, A, B> {
///   A(A),
///   B(B),
///   C(Cow<'a, [u8]>),
/// }
///
/// fourleaf_retrofit!(enum MyEnum<'a, A, B> : {
///   impl<'a, A : Serialize, B : Serialize> Serialize
///   for MyEnum<'a, A, B>
/// } {
///   impl<'a, R : Read, STYLE, A : Deserialize<R, STYLE>,
///        B : Deserialize<R, STYLE>> Deserialize<R, STYLE>
///   for MyEnum<'a, A, B> where Cow<'a, [u8]>: Deserialize<R, STYLE>
/// } {
///   |_context|
///   [1] MyEnum::A(ref a) => {
///     [1] a: A = a,
///     { Ok(MyEnum::A(a)) }
///   },
///   [2] MyEnum::B(ref b) => {
///     [1] b: B = b,
///     { Ok(MyEnum::B(b)) }
///   },
///   [3] MyEnum::C(ref c) => {
///     [1] c: Cow<'a, [u8]> = c,
///     { Ok(MyEnum::C(c)) }
///   },
/// });
/// # fn main() { }
/// ```
#[macro_export]
macro_rules! fourleaf_retrofit {
    (@_STRUCT_BODY_SER ($dst:expr) {
        $([$tag:expr] $accessor:expr,)*
        $((*) $del_accessor:expr,)*
        $((?) $unk_accessor:expr,)*
    }) => { {
        $($crate::ser::Serialize::serialize_field(
            &$accessor, $dst, $tag)?;)*
        let mut _terminated = false;
        $({
            assert!(!_terminated);
            $crate::ser::Serialize::serialize_body(&$del_accessor, $dst)?;
            _terminated = true;
        })*
        $({
            assert!(!_terminated);
            $crate::ser::Serialize::serialize_body(&$unk_accessor, $dst)?;
            _terminated = true;
        })*
        if !_terminated {
            $dst.write_end_struct()?;
        }
        Ok(())
    } };

    (@_STRUCT_ELEMENT_SER ($dst:expr, $tag:expr) {
        $((*) $del_accessor:expr,)*
    }) => { {
        $(
            return $crate::ser::Serialize::serialize_element(
                &$del_accessor, $dst, $tag);
        )*
    } };

    (@_STRUCT_ELEMENT_SER ($dst:expr, $tag:expr) {
        $((?) $unk_accessor:expr,)*
    }) => { {
    } };

    (@_STRUCT_BODY_DESER ($stream:expr, $context:expr) {
        $([$tag:expr] $field_name:ident: $field_type:ty,)*
        $((*) $del_field_name:ident: $del_field_type:ty,)*
        $((?) $unk_field_name:ident: $unk_field_type:ty,)*
        { $constructor:expr }
    }) => { {
        $(let mut $field_name =
          <<$field_type as $crate::de::Deserialize<R, STYLE>>::Accum
          as Default>::default();
        )*
        $(let mut $unk_field_name =
          <<$unk_field_type as $crate::de::Deserialize<R, STYLE>>::Accum
          as Default>::default();
        )*

        let mut _consumed = false;
        $(
            assert!(!_consumed);
            let $del_field_name = {
                let subcontext = $context.push(
                    stringify!($del_field_name), $stream.pos())?;
                <$del_field_type as $crate::de::Deserialize<R, STYLE>>::
                    deserialize_body(&subcontext, $stream)?
            };
            _consumed = true;
        )*;

        if !_consumed { while let Some(mut _field) =
            $crate::ms::ResultExt::context(
                $stream.next_field(), $context)?
        {
            match _field.tag {
                $( $tag => {
                    let subcontext = $context.push(
                        stringify!($field_name), _field.pos)?;
                    <$field_type as $crate::de::Deserialize<R, STYLE>>::
                    deserialize_field(&mut $field_name, &subcontext,
                                      &mut _field)?;
                })*
                _ => {
                    let mut _handled = false;
                    $({
                        let mut name = [0u8;2];
                        <$unk_field_type as $crate::de::Deserialize<R, STYLE>>::
                            deserialize_field(
                                &mut $unk_field_name,
                                &$context.push_tag(&mut name, _field.tag,
                                                   _field.pos)?,
                                &mut _field)?;
                        _handled = true;
                    })*
                    if !_handled {
                        $context.unknown_field(&_field)?;
                        $crate::ms::ResultExt::context(
                            _field.skip(), $context)?;
                    }
                },
            }
        } }

        $(
            let subcontext = $context.push(stringify!($field_name),
                                           $stream.pos())?;
            let $field_name = <$field_type as
                $crate::de::Deserialize<R, STYLE>>::
                    finish($field_name, &subcontext)?;
        )*
        $(
            let subcontext = $context.push(stringify!($unk_field_name),
                                           $stream.pos())?;
            let $unk_field_name = <$unk_field_type as
                $crate::de::Deserialize<R, STYLE>>::
                    finish($unk_field_name, &subcontext)?;
        )*

        $constructor
    } };

    (@_STRUCT_ELEMENT_DESER ($context:expr, $field:expr) {
        $((*) $del_field_name:ident: $del_field_type:ty,)*
        { $constructor:expr }
    }) => { {
        $(
            let subcontext = $context.push(
                stringify!($del_field_name), $field.pos)?;
            let $del_field_name =
                <$del_field_type as $crate::de::Deserialize<R, STYLE>>::
                    deserialize_element(&subcontext, $field)?;
            return $constructor;
        )*
    } };

    (@_STRUCT_ELEMENT_DESER ($context:expr, $field:expr) {
        $((?) $unk_field_name:ident: $unk_field_type:ty,)*
        { $constructor:expr }
    }) => { {
    } };

    (@_DESER_BOILERPLATE) => {
        type Accum = Option<Self>;

        fn deserialize_field(accum: &mut Option<Self>,
                             context: &$crate::de::Context,
                             field: &mut $crate::stream::Field<R>)
                             -> $crate::de::Result<()> {
            if accum.is_some() {
                return Err($crate::de::Error::FieldOccursTooFewTimes(
                    context.to_string(), 1));
            }

            *accum = Some(
                <Self as $crate::de::Deserialize<R, STYLE>>::
                deserialize_element(context, field)?);
            Ok(())
        }


        fn finish(accum: Option<Self>, context: &$crate::de::Context)
                  -> $crate::de::Result<Self> {
            accum.ok_or_else(|| $crate::de::Error::RequiredFieldMissing(
                context.to_string()))
        }
    };

    ($form:tt $self_ty:ty : {} $impl_deser:tt $body:tt) => {
        fourleaf_retrofit!($form $self_ty : {
            impl $crate::ser::Serialize for $self_ty
        } $impl_deser $body);
    };
    ($form:tt $self_ty:ty : $impl_ser:tt {} $body:tt) => {
        fourleaf_retrofit!($form $self_ty : $impl_ser {
            impl<R : ::std::io::Read, STYLE> $crate::de::Deserialize<R, STYLE>
            for $self_ty } $body);
    };
    (struct $self_ty:ty : {$($impl_ser:tt)*} {$($impl_deser:tt)*} {
        |$context:ident, $this:ident|
        $(
            [$tag:expr] $field_name:ident: $field_type:ty = $accessor:expr,
        )*
        $(
            ($special:tt) $s_field_name:ident: $s_field_type:ty =
                $s_accessor:expr,
        )*
        { $constructor:expr } }) => {
        $($impl_ser)* {
            fn serialize_body<R : ::std::io::Write>
                (&self, dst: &mut $crate::stream::Stream<R>)
                -> $crate::stream::Result<()>
            {
                let $this = self;
                fourleaf_retrofit!(@_STRUCT_BODY_SER (dst) {
                    $([$tag] $accessor,)*
                    $(($special) $s_accessor,)*
                })
            }

            #[allow(unreachable_code)]
            fn serialize_element<R : ::std::io::Write>
                (&self, dst: &mut $crate::stream::Stream<R>, tag: u8)
                 -> $crate::stream::Result<()>
            {
                let $this = self;
                let _ = $this;
                fourleaf_retrofit!(@_STRUCT_ELEMENT_SER (dst, tag) {
                    $(($special) $s_accessor,)*
                });
                dst.write_struct(tag)?;
                <Self as $crate::ser::Serialize>::serialize_body(self, dst)
            }
        }

        $($impl_deser)* {
            fourleaf_retrofit!(@_DESER_BOILERPLATE);

            fn deserialize_body($context: &$crate::de::Context,
                                stream: &mut $crate::stream::Stream<R>)
                                -> $crate::de::Result<Self> {
                fourleaf_retrofit!(@_STRUCT_BODY_DESER (stream, $context) {
                    $([$tag] $field_name: $field_type,)*
                    $(($special) $s_field_name: $s_field_type,)*
                    { $constructor }
                })
            }

            #[allow(unreachable_code)]
            fn deserialize_element(context: &$crate::de::Context,
                                   field: &mut $crate::stream::Field<R>)
                                   -> $crate::de::Result<Self> {
                fourleaf_retrofit!(@_STRUCT_ELEMENT_DESER (context, field) {
                    $(($special) $s_field_name: $s_field_type,)*
                    { $constructor }
                });

                <Self as $crate::de::Deserialize<R, STYLE>>::
                    deserialize_body(context, $crate::ms::ResultExt::context(
                        field.value.to_struct(), context)?)
            }
        }
    };

    (enum $self_ty:ty : {$($impl_ser:tt)*} {$($impl_deser:tt)*} {
        |$context:ident|
    $(
        [$discriminant:expr] $disc_pat:pat => {
            $([$tag:expr] $field_name:ident: $field_type:ty = $accessor:expr,)*
            $(($special:tt) $s_field_name:ident: $s_field_type:ty =
                  $s_accessor:expr,)*
            { $constructor:expr }
        }
    ),* $(,
        (?) $ca_disc_pat:pat => {
            (=) $ca_disc_field_name:ident: u64 = $ca_disc_field_accessor:expr,
            $([$ca_tag:expr] $ca_field_name:ident: $ca_field_type:ty =
                  $ca_accessor:expr,)*
            $(($ca_special:tt) $ca_s_field_name:ident: $ca_s_field_type:ty =
                  $ca_s_accessor:expr,)*
            { $ca_constructor:expr }
        }
    ),* $(,)* }) => {
        $($impl_ser)* {
            fn serialize_element<R : ::std::io::Write>
                (&self, dst: &mut $crate::stream::Stream<R>, tag: u8)
                -> $crate::stream::Result<()>
            {
                match *self {$(
                    $disc_pat => {
                        dst.write_enum(tag, $discriminant)?;
                        fourleaf_retrofit!(@_STRUCT_BODY_SER (dst) {
                            $([$tag] $accessor,)*
                            $(($special) $s_accessor,)*
                        })
                    },
                )* $(
                    $ca_disc_pat => {
                        dst.write_enum(tag, $ca_disc_field_accessor)?;
                        fourleaf_retrofit!(@_STRUCT_BODY_SER (dst) {
                            $([$ca_tag] $ca_accessor,)*
                            $(($ca_special) $ca_s_accessor,)*
                        })
                    },
                )*}
            }
        }

        $($impl_deser)* {
            fourleaf_retrofit!(@_DESER_BOILERPLATE);

            #[allow(unreachable_code)]
            fn deserialize_element($context: &$crate::de::Context,
                                   field: &mut $crate::stream::Field<R>)
                                   -> $crate::de::Result<Self> {
                let (discriminant, stream) = $crate::ms::ResultExt::context(
                    field.value.to_enum(), $context)?;
                match discriminant {
                    $($discriminant => {
                        fourleaf_retrofit!(@_STRUCT_BODY_DESER
                                           (stream, $context) {
                            $([$tag] $field_name: $field_type,)*
                            $(($special) $s_field_name: $s_field_type,)*
                            { $constructor }
                        })
                    },)*
                    _discriminant => {
                        $(
                            let $ca_disc_field_name = _discriminant;
                            return fourleaf_retrofit!(@_STRUCT_BODY_DESER
                                                      (stream, $context) {
                                $([$ca_tag] $ca_field_name: $ca_field_type,)*
                                $(($ca_special) $ca_s_field_name: $ca_s_field_type,)*
                                { $ca_constructor }
                            });
                        )*
                        Err($crate::de::Error::UnknownVariant(
                            $context.to_string(), discriminant))
                    },
                }
            }
        }
    };
}

#[cfg(test)]
mod test {
    use adapt::Copied;
    use unknown::UnknownFields;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct SimpleStruct {
        pub foo: u32,
        pub bar: u64,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum SimpleEnum {
        Unit,
        Tuple(u32, u64),
        Struct { foo: u32, bar: u64 },
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct DelegatingStruct(SimpleStruct);

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DelegatingEnum {
        Unit,
        Deleg(SimpleStruct),
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct UnknownPreserving {
        pub foo: u32,
        pub unknown: UnknownFields<'static>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum UnknownPreservingEnum {
        Unit,
        Unknown(u64, Copied<UnknownFields<'static>>),
    }

    mod declare {
        // Separate module to isolate imports
        use adapt::Copied;
        use unknown::UnknownFields;

        use super::{SimpleEnum, SimpleStruct,
                    DelegatingEnum, DelegatingStruct,
                    UnknownPreserving, UnknownPreservingEnum};

        fourleaf_retrofit!(struct SimpleStruct : {} {} {
            |_context, this|
            [1] foo: u32 = this.foo,
            [2] bar: u64 = this.bar,
            { Ok(SimpleStruct { foo: foo, bar: bar }) }
        });

        fourleaf_retrofit!(enum SimpleEnum : {} {} {
            |_context|
            [1] SimpleEnum::Unit => { { Ok(SimpleEnum::Unit) } },
            [2] SimpleEnum::Tuple(a, b) => {
                [1] a: u32 = a,
                [2] b: u64 = b,
                { Ok(SimpleEnum::Tuple(a, b)) }
            },
            [3] SimpleEnum::Struct { foo, bar } => {
                [1] foo: u32 = foo,
                [2] bar: u64 = bar,
                { Ok(SimpleEnum::Struct { foo: foo, bar: bar }) }
            },
        });

        fourleaf_retrofit!(struct DelegatingStruct : {} {} {
            |_context, this|
            (*) it: SimpleStruct = this.0,
            { Ok(DelegatingStruct(it)) }
        });

        fourleaf_retrofit!(enum DelegatingEnum : {} {} {
            |_context|
            [1] DelegatingEnum::Unit => { { Ok(DelegatingEnum::Unit) } },
            [2] DelegatingEnum::Deleg(inner) => {
                (*) inner: SimpleStruct = inner,
                { Ok(DelegatingEnum::Deleg(inner)) }
            },
        });

        fourleaf_retrofit!(struct UnknownPreserving : {} {
            impl<R : ::std::io::Read, STYLE>
            ::de::Deserialize<R, STYLE> for UnknownPreserving
            where UnknownFields<'static> : ::de::Deserialize<R, STYLE>
        } {
            |_context, this|
            [1] foo: u32 = this.foo,
            (?) unknown: UnknownFields<'static> = this.unknown,
            { Ok(UnknownPreserving { foo: foo, unknown: unknown }) }
        });

        fourleaf_retrofit!(enum UnknownPreservingEnum : {} {} {
            |_context|
            [1] UnknownPreservingEnum::Unit => {
                { Ok(UnknownPreservingEnum::Unit) }
            },
            (?) UnknownPreservingEnum::Unknown(discriminant, ref fields) => {
                (=) discriminant: u64 = discriminant,
                (?) fields: Copied<UnknownFields<'static>> = fields,
                { Ok(UnknownPreservingEnum::Unknown(discriminant, fields)) }
            },
        });
    }

    use de::*;
    use ser::*;
    use test_helpers::*;

    #[test]
    fn simple_struct_happy_path() {
        let orig = SimpleStruct { foo: 5, bar: 6 };
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse("41 05 42 06 00"), encoded);

        let res = from_slice_copy(&encoded, &Config::default()).unwrap();
        assert_eq!(orig, res);
    }

    #[test]
    fn simple_struct_ignores_unknown_field_by_default() {
        let res: SimpleStruct = from_slice_copy(&parse(
            "41 05 42 06 43 07 00"), &Config::default()).unwrap();
        assert_eq!(SimpleStruct { foo: 5, bar: 6 }, res);
    }

    #[test]
    fn simple_struct_unknown_field_error() {
        let mut config = Config::default();
        config.ignore_unknown_fields = false;

        match from_slice_copy::<SimpleStruct>(&parse(
            "41 05 42 06 43 07 00"), &config)
        {
            Ok(r) => panic!("unexpectedly succeeded: {:?}", r),
            Err(Error::UnknownField(_, 3, _)) => (),
            Err(e) => panic!("failed for wrong reason: {}", e),
        }
    }

    #[test]
    fn simple_enum_unit_happy_path() {
        let orig = SimpleEnum::Unit;
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse("01 01 00 00"), encoded);

        let res = from_slice_copy(&encoded, &Config::default()).unwrap();
        assert_eq!(orig, res);
    }

    #[test]
    fn simple_enum_tuple_happy_path() {
        let orig = SimpleEnum::Tuple(5, 6);
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse("01 02 41 05 42 06 00 00"), encoded);

        let res = from_slice_copy(&encoded, &Config::default()).unwrap();
        assert_eq!(orig, res);
    }

    #[test]
    fn simple_enum_struct_happy_path() {
        let orig = SimpleEnum::Struct { foo: 5, bar: 6 };
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse("01 03 41 05 42 06 00 00"), encoded);

        let res = from_slice_copy(&encoded, &Config::default()).unwrap();
        assert_eq!(orig, res);
    }

    #[test]
    fn simple_enum_ignores_unknown_field_by_default() {
        let res: SimpleEnum = from_slice_copy(&parse(
            "01 01 41 2A 00 42 2B 00"), &Config::default()).unwrap();
        assert_eq!(SimpleEnum::Unit, res);
    }

    #[test]
    fn simple_enum_unknown_field_error_inner() {
        let mut config = Config::default();
        config.ignore_unknown_fields = false;

        match from_slice_copy::<SimpleEnum>(&parse(
            "01 01 43 2A 00 00"), &config)
        {
            Ok(r) => panic!("unexpectedly succeeded: {:?}", r),
            Err(Error::UnknownField(_, 3, _)) => (),
            Err(e) => panic!("failed for wrong reason: {}", e),
        }
    }

    #[test]
    fn simple_enum_unknown_field_error_outer() {
        let mut config = Config::default();
        config.ignore_unknown_fields = false;

        match from_slice_copy::<SimpleEnum>(&parse(
            "01 01 00 43 2A 00"), &config)
        {
            Ok(r) => panic!("unexpectedly succeeded: {:?}", r),
            Err(Error::UnknownField(_, 3, _)) => (),
            Err(e) => panic!("failed for wrong reason: {}", e),
        }
    }

    #[test]
    fn simple_enum_unknown_variant() {
        match from_slice_copy::<SimpleEnum>(&parse("01 04 00 00"),
                                            &Config::default()) {
            Ok(r) => panic!("unexpectedly succeeded: {:?}", r),
            Err(Error::UnknownVariant(_, 4)) => (),
            Err(e) => panic!("failed for wrong reason: {}", e),
        }
    }

    #[test]
    fn struct_delegation() {
        let orig = DelegatingStruct(SimpleStruct { foo: 5, bar: 6 });
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse("41 05 42 06 00"), encoded);

        let res = from_slice_copy(&encoded, &Config::default()).unwrap();
        assert_eq!(orig, res);
    }

    #[test]
    fn enum_delegation() {
        let orig = DelegatingEnum::Deleg(SimpleStruct { foo: 5, bar: 6 });
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse("01 02 41 05 42 06 00 00"), encoded);

        let res = from_slice_copy(&encoded, &Config::default()).unwrap();
        assert_eq!(orig, res);
    }

    #[test]
    fn unknown_fields_collected_in_unknown() {
        let mut config = Config::default();
        config.ignore_unknown_fields = false;

        let orig = parse("41 2A 42 2B 43 2C 00");
        let parsed = from_slice_copy::<UnknownPreserving>(&orig, &config)
            .unwrap();
        assert_eq!(42, parsed.foo);
        assert_eq!(2, parsed.unknown.0.len());
        assert_eq!(2, parsed.unknown.0[0].0);
        assert_eq!(3, parsed.unknown.0[1].0);

        let res = to_vec(parsed).unwrap();
        assert_eq!(orig, res);
    }

    #[test]
    fn handling_unknown_enum_variants() {
        let mut config = Config::default();
        config.ignore_unknown_fields = false;

        let orig = parse("01 2A 41 01 42 02 00 00");
        let parsed = from_slice_copy::<UnknownPreservingEnum>(
            &orig, &config).unwrap();
        match parsed {
            UnknownPreservingEnum::Unknown(42, ref fields) =>
                assert_eq!(2, (fields.0).0.len()),
            _ => panic!("unexpected result: {:?}", parsed),
        }

        let res = to_vec(parsed).unwrap();
        assert_eq!(orig, res);
    }
}
