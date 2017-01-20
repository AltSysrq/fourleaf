//-
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[macro_export]
macro_rules! fourleaf_retrofit {
    (@_STRUCT_BODY_SER ($dst:expr) {
        $([$tag:expr] $accessor:expr,)*
        $((*) $del_accessor:expr,)*
    }) => { {
        $($crate::ser::Serialize::serialize_field(
            &$accessor, $dst, $tag)?;)*
        let mut _terminated = false;
        $({
            assert!(!_terminated);
            $crate::ser::Serialize::serialize_body(
                &$del_accessor, $dst)?;
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

    (@_STRUCT_BODY_DESER ($stream:expr, $context:expr) {
        $([$tag:expr] $field_name:ident: $field_type:ty,)*
        $((*) $del_field_name:ident: $del_field_type:ty,)*
        { $constructor:expr }
    }) => { {
        $(let mut $field_name =
          <<$field_type as $crate::de::Deserialize<R, STYLE>>::Accum
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
                    $context.unknown_field(&_field)?;
                    $crate::ms::ResultExt::context(_field.skip(), $context)?
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
                )*}
            }
        }

        $($impl_deser)* {
            fourleaf_retrofit!(@_DESER_BOILERPLATE);

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
                    _ => Err($crate::de::Error::UnknownVariant(
                        $context.to_string(), discriminant)),
                }
            }
        }
    };
}

#[cfg(test)]
mod test {
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

    mod declare {
        // Separate module to isolate imports
        use super::{SimpleEnum, SimpleStruct, DelegatingEnum, DelegatingStruct};

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
}
