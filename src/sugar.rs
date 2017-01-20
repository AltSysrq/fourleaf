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
    }) => { {
        $(
            $crate::ser::Serialize::serialize_field(
                &$accessor, $dst, $tag)?;
        )*
        $dst.write_end_struct()
    } };

    (@_STRUCT_BODY_DESER ($stream:expr, $context:expr) {
        $([$tag:expr] $field_name:ident: $field_type:ty,)*
        { $constructor:expr }
    }) => { {
        $(let mut $field_name =
          <<$field_type as $crate::de::Deserialize<R, STYLE>>::Accum
          as Default>::default();
        )*

        while let Some(mut _field) =
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
        }

        $(
            let subcontext = $context.push(stringify!($field_name),
                                           $stream.pos())?;
            let $field_name = <$field_type as
                $crate::de::Deserialize<R, STYLE>>::
            finish($field_name, &subcontext)?;
        )*

        $constructor
    } };

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
    )* { $constructor:expr } }) => {
        $($impl_ser)* {
            fn serialize_top_level<R : ::std::io::Write>
                (&self, dst: &mut $crate::stream::Stream<R>)
                -> $crate::stream::Result<()>
            {
                let $this = self;
                fourleaf_retrofit!(@_STRUCT_BODY_SER (dst) {
                    $([$tag] $accessor,)*
                })
            }

            fn serialize_element<R : ::std::io::Write>
                (&self, dst: &mut $crate::stream::Stream<R>, tag: u8)
                 -> $crate::stream::Result<()>
            {
                dst.write_struct(tag)?;
                <Self as $crate::ser::Serialize>::serialize_top_level(self, dst)
            }
        }

        $($impl_deser)* {
            type Accum = Option<Self>;

            fn deserialize_top_level($context: &$crate::de::Context,
                                     stream: &mut $crate::stream::Stream<R>)
                                     -> $crate::de::Result<Self> {
                fourleaf_retrofit!(@_STRUCT_BODY_DESER (stream, $context) {
                    $([$tag] $field_name: $field_type,)*
                    { $constructor }
                })
            }

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

            fn deserialize_element(context: &$crate::de::Context,
                                   field: &mut $crate::stream::Field<R>)
                                   -> $crate::de::Result<Self> {
                <Self as $crate::de::Deserialize<R, STYLE>>::
                deserialize_top_level(context, $crate::ms::ResultExt::context(
                    field.value.to_struct(), context)?)
            }

            fn finish(accum: Option<Self>, context: &$crate::de::Context)
                      -> $crate::de::Result<Self> {
                accum.ok_or_else(|| $crate::de::Error::RequiredFieldMissing(
                    context.to_string()))
            }
        }
    }
}

#[cfg(test)]
mod test {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct SimpleStruct {
        pub foo: u32,
        pub bar: u64,
    }

    mod declare {
        // Separate module to isolate imports
        use super::SimpleStruct;
        fourleaf_retrofit!(struct SimpleStruct : {} {} {
            |_context, this|
            [1] foo: u32 = this.foo,
            [2] bar: u64 = this.bar,
            { Ok(SimpleStruct { foo: foo, bar: bar }) }
        });
    }

    use de::*;
    use ser::*;
    use test_helpers::*;

    #[test]
    fn it_basically_works() {
        let orig = SimpleStruct { foo: 5, bar: 6 };
        let encoded = to_vec(&orig).unwrap();
        assert_eq!(parse("41 05 42 06 00"), encoded);

        let res = from_slice_copy(&encoded, &Config::default()).unwrap();
        assert_eq!(orig, res);
    }
}
