use std::{ffi::CString, str::FromStr};

use paste::paste;

use crate::{
    error::Error,
    sys::{
        type_t, type_vector_t, yices_bool_type, yices_bv_type, yices_bvtype_size,
        yices_clear_type_name, yices_compatible_types, yices_decref_type, yices_delete_type_vector,
        yices_function_type, yices_get_type_by_name, yices_get_type_name, yices_incref_type,
        yices_init_type_vector, yices_int_type, yices_new_scalar_type,
        yices_new_uninterpreted_type, yices_parse_type, yices_real_type, yices_remove_type_name,
        yices_scalar_type_card, yices_set_type_name, yices_test_subtype, yices_tuple_type,
        yices_type_child, yices_type_children, yices_type_is_bitvector, yices_type_is_bool,
        yices_type_is_function, yices_type_is_int, yices_type_is_real, yices_type_is_scalar,
        yices_type_is_tuple, yices_type_is_uninterpreted, yices_type_num_children, NULL_TYPE,
    },
    yices, yices_try, Result,
};

pub trait InnerType {
    fn inner_type(&self) -> type_t;
}

pub trait SubType: InnerType {
    fn subtype<S>(&self, other: &S) -> Result<bool>
    where
        S: SubType + InnerType,
        Self: Sized,
    {
        Ok(yices! { yices_test_subtype(self.inner_type(), other.inner_type()) } != 0)
    }
}
pub trait CompatibleType: InnerType {
    fn compatible<S>(&self, other: &S) -> Result<bool>
    where
        S: CompatibleType + InnerType,
        Self: Sized,
    {
        Ok(yices! { yices_compatible_types(self.inner_type(), other.inner_type()) } != 0)
    }
}

pub trait ChildType: InnerType {
    /// Get the number of children of a type. Only valid for Function and Tuple types
    fn num_children(&self) -> Result<i32>
    where
        Self: Sized,
    {
        Ok(yices! { yices_type_num_children(self.inner_type()) })
    }

    /// Get a child of a type. Only valid for Function and Tuple types
    fn child(&self, index: i32) -> Result<Type>
    where
        Self: Sized,
    {
        let typ = yices! { yices_type_child(self.inner_type(), index) };

        if typ == NULL_TYPE {
            Err(Error::InvalidType)
        } else {
            Type::try_from(typ)
        }
    }

    /// Get the child types of a type. Only valid for Function and Tuple types
    ///
    /// Returns the most general type of the children, which can be cast back to the
    /// original type.
    fn children(&self) -> Result<Vec<Type>>
    where
        Self: Sized,
    {
        let mut vec = type_vector_t {
            size: 0,
            capacity: 0,
            data: std::ptr::null_mut(),
        };

        yices! { yices_init_type_vector(&mut vec as *mut type_vector_t) };

        if yices! { yices_type_children(self.inner_type(), &mut vec as *mut type_vector_t) } == -1 {
            yices! { yices_delete_type_vector(&mut vec as *mut type_vector_t) };

            Err(Error::InvalidType)
        } else {
            let mut types = Vec::with_capacity(vec.size as usize);

            (0..vec.size).try_for_each(|i| {
                let typ = unsafe { *vec.data.offset(i as isize) };

                if typ == NULL_TYPE {
                    Err(Error::InvalidType)
                } else {
                    types.push(Type::try_from(typ)?);
                    Ok(())
                }
            })?;

            yices! { yices_delete_type_vector(&mut vec as *mut type_vector_t) };

            Ok(types)
        }
    }
}
pub trait Gc: InnerType {
    fn incref(&self) -> Result<()> {
        yices_try! { yices_incref_type(self.inner_type()) }.and_then(|r| {
            if r != 0 {
                Ok(())
            } else {
                Err(Error::InvalidType)
            }
        })
    }

    fn decref(&self) -> Result<()> {
        yices_try! { yices_decref_type(self.inner_type()) }.and_then(|r| {
            if r != 0 {
                Ok(())
            } else {
                Err(Error::InvalidType)
            }
        })
    }
}

pub trait NamedType: InnerType {
    fn name(&self) -> Result<Option<String>>
    where
        Self: Sized,
    {
        let name = yices! { yices_get_type_name(self.inner_type()) };

        if name.is_null() {
            Ok(None)
        } else {
            Ok(Some(
                unsafe { std::ffi::CStr::from_ptr(name) }
                    .to_str()
                    .map_err(|_| Error::InvalidType)?
                    .to_owned(),
            ))
        }
    }

    fn set_name(&self, name: &str) -> Result<()>
    where
        Self: Sized,
    {
        yices! { yices_set_type_name(self.inner_type(), name.as_ptr() as *const i8) };

        Ok(())
    }

    fn clear_name(&self) -> Result<()>
    where
        Self: Sized,
    {
        yices! { yices_clear_type_name(self.inner_type()) };

        Ok(())
    }
}

/// Implement a type
///
/// # Example
///
/// impl_type! { Bool, bool };
macro_rules! impl_type {
    ($id:ident) => {
        impl_type! { $id, $id }
    };
    ($id:ident, $abbrev:ident) => {
        paste! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub struct $id {
                typ: type_t,
            }

            impl $id {
                pub fn [<is_ $id:lower>](&self) -> Result<bool> {
                    Ok(yices! { [<yices_type_is_ $abbrev:lower>](self.inner_type()) } != 0)
                }
            }

            impl InnerType for $id {
                fn inner_type(&self) -> type_t {
                    self.typ
                }
            }

            impl SubType for $id {}
            impl CompatibleType for $id {}
            impl NamedType for $id {}
            impl Gc for $id {}

            impl From<type_t> for $id {
                fn from(typ: type_t) -> Self {
                    Self { typ }
                }
            }

            impl From<&type_t> for $id {
                fn from(typ: &type_t) -> Self {
                    Self { typ: *typ }
                }
            }

            impl From<$id> for type_t {
                fn from(typ: $id) -> Self {
                    typ.inner_type()
                }
            }

            impl From<&$id> for type_t {
                fn from(typ: &$id) -> Self {
                    typ.inner_type()
                }
            }

            impl TryFrom<Type> for $id {
                type Error = Error;

                fn try_from(typ: Type) -> Result<Self> {
                    match typ {
                        Type::$id(typ) => Ok(typ),
                        _ => Err(Error::InvalidType),
                    }
                }
            }

            impl TryFrom<&Type> for $id {
                type Error = Error;

                fn try_from(typ: &Type) -> Result<Self> {
                    match typ {
                        Type::$id(typ) => Ok(*typ),
                        _ => Err(Error::InvalidType),
                    }
                }
            }

            impl From<$id> for Type {
                fn from(typ: $id) -> Self {
                    Self::$id(typ)
                }
            }
        }
    };
}

impl_type! { Bool }

impl Bool {
    pub fn new() -> Result<Self> {
        Ok(Self {
            typ: yices! { yices_bool_type() },
        })
    }
}

impl_type! { Integer, int }

impl Integer {
    /// Return the integer type
    pub fn new() -> Result<Self> {
        Ok(Self {
            typ: yices! { yices_int_type() },
        })
    }
}

impl_type! { Real }

impl Real {
    /// Return the real type
    pub fn new() -> Result<Self> {
        Ok(Self {
            typ: yices! { yices_real_type() },
        })
    }
}

impl_type! { BitVector }

impl BitVector {
    /// Construct or return the bitvector type for a bitvector with a bit-width of
    /// `size`.
    pub fn new(size: u32) -> Result<Self> {
        Ok(Self {
            typ: yices! { yices_bv_type(size) },
        })
    }

    /// Number of bits in a bitvector type, or an error if this is not a bitvector
    /// type.
    pub fn size(&self) -> Result<u32> {
        Ok(yices! { yices_bvtype_size(self.typ) })
    }
}

impl_type! { Scalar }

impl Scalar {
    /// Construct or return the scalar type with `cardinality` elements.
    pub fn new(card: u32) -> Result<Self> {
        Ok(Self {
            typ: yices! { yices_new_scalar_type(card) },
        })
    }

    pub fn card(&self) -> Result<u32> {
        Ok(yices! { yices_scalar_type_card(self.typ) })
    }
}

impl_type! { Uninterpreted }

impl Uninterpreted {
    /// Construct a new uninterpreted type.
    pub fn new() -> Result<Self> {
        Ok(Self {
            typ: yices! { yices_new_uninterpreted_type() },
        })
    }
}

impl_type! { Tuple }

impl Tuple {
    /// Construct a new tuple type.
    pub fn new<I, T>(types: I) -> Result<Self>
    where
        I: IntoIterator<Item = T>,
        T: InnerType,
    {
        let types: Vec<_> = types.into_iter().map(|t| t.inner_type()).collect();

        Ok(Self {
            typ: yices! { yices_tuple_type(types.len() as u32, types.as_ptr()) },
        })
    }
}

impl ChildType for Tuple {}

impl_type! { Function }

impl Function {
    /// Construct a new function type with `domain` as the domain and `range` as
    /// the range.
    pub fn new<I, T>(domain: I, range: T) -> Result<Self>
    where
        I: IntoIterator<Item = T>,
        T: InnerType,
    {
        let domain: Vec<_> = domain.into_iter().map(|t| t.inner_type()).collect();
        Ok(Self {
            typ: yices! {
                yices_function_type(domain.len() as u32, domain.as_ptr(), range.inner_type())
            },
        })
    }
}

impl ChildType for Function {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    Bool(Bool),
    Integer(Integer),
    Real(Real),
    BitVector(BitVector),
    Scalar(Scalar),
    Uninterpreted(Uninterpreted),
    Tuple(Tuple),
    Function(Function),
}

impl Type {
    pub fn is_bool(&self) -> Result<bool> {
        yices_try! { yices_type_is_bool(self.into()) }.map(|b| b != 0)
    }

    pub fn is_int(&self) -> Result<bool> {
        yices_try! { yices_type_is_int(self.into()) }.map(|b| b != 0)
    }

    pub fn is_real(&self) -> Result<bool> {
        yices_try! { yices_type_is_real(self.into()) }.map(|b| b != 0)
    }

    pub fn is_bitvector(&self) -> Result<bool> {
        yices_try! { yices_type_is_bitvector(self.into()) }.map(|b| b != 0)
    }

    pub fn is_scalar(&self) -> Result<bool> {
        yices_try! { yices_type_is_scalar(self.into()) }.map(|b| b != 0)
    }

    pub fn is_uninterpreted(&self) -> Result<bool> {
        yices_try! { yices_type_is_uninterpreted(self.into()) }.map(|b| b != 0)
    }

    pub fn is_tuple(&self) -> Result<bool> {
        yices_try! { yices_type_is_tuple(self.into()) }.map(|b| b != 0)
    }

    pub fn is_function(&self) -> Result<bool> {
        yices_try! { yices_type_is_function(self.into()) }.map(|b| b != 0)
    }
}

impl TryFrom<type_t> for Type {
    type Error = Error;

    fn try_from(value: type_t) -> Result<Self> {
        if yices_try! { yices_type_is_bool(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Bool(Bool::from(value)))
        } else if yices_try! { yices_type_is_int(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Integer(Integer::from(value)))
        } else if yices_try! { yices_type_is_real(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Real(Real::from(value)))
        } else if yices_try! { yices_type_is_bitvector(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::BitVector(BitVector::from(value)))
        } else if yices_try! { yices_type_is_scalar(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Scalar(Scalar::from(value)))
        } else if yices_try! { yices_type_is_uninterpreted(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Uninterpreted(Uninterpreted::from(value)))
        } else if yices_try! { yices_type_is_tuple(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Tuple(Tuple::from(value)))
        } else if yices_try! { yices_type_is_function(value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Function(Function::from(value)))
        } else {
            Err(Error::InvalidType)
        }
    }
}

impl TryFrom<&type_t> for Type {
    type Error = Error;

    fn try_from(value: &type_t) -> Result<Self> {
        if yices_try! { yices_type_is_bool(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Bool(Bool::from(value)))
        } else if yices_try! { yices_type_is_int(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Integer(Integer::from(value)))
        } else if yices_try! { yices_type_is_real(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Real(Real::from(value)))
        } else if yices_try! { yices_type_is_bitvector(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::BitVector(BitVector::from(value)))
        } else if yices_try! { yices_type_is_scalar(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Scalar(Scalar::from(value)))
        } else if yices_try! { yices_type_is_uninterpreted(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Uninterpreted(Uninterpreted::from(value)))
        } else if yices_try! { yices_type_is_tuple(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Tuple(Tuple::from(value)))
        } else if yices_try! { yices_type_is_function(*value) }.is_ok_and(|b| b != 0) {
            Ok(Type::Function(Function::from(value)))
        } else {
            Err(Error::InvalidType)
        }
    }
}

impl From<Type> for type_t {
    fn from(value: Type) -> Self {
        match value {
            Type::Bool(typ) => typ.inner_type(),
            Type::Integer(typ) => typ.inner_type(),
            Type::Real(typ) => typ.inner_type(),
            Type::BitVector(typ) => typ.inner_type(),
            Type::Scalar(typ) => typ.inner_type(),
            Type::Uninterpreted(typ) => typ.inner_type(),
            Type::Tuple(typ) => typ.inner_type(),
            Type::Function(typ) => typ.inner_type(),
        }
    }
}

impl From<&Type> for type_t {
    fn from(value: &Type) -> Self {
        match value {
            Type::Bool(typ) => typ.inner_type(),
            Type::Integer(typ) => typ.inner_type(),
            Type::Real(typ) => typ.inner_type(),
            Type::BitVector(typ) => typ.inner_type(),
            Type::Scalar(typ) => typ.inner_type(),
            Type::Uninterpreted(typ) => typ.inner_type(),
            Type::Tuple(typ) => typ.inner_type(),
            Type::Function(typ) => typ.inner_type(),
        }
    }
}

impl Type {
    pub fn try_from_name(name: &str) -> Result<Type>
    where
        Self: Sized,
    {
        let typ = yices! { yices_get_type_by_name(name.as_ptr() as *const i8) };

        if typ == NULL_TYPE {
            Err(Error::InvalidType)
        } else {
            Self::try_from(typ)
        }
    }
}

pub fn remove_type_name(name: &str) -> Result<()> {
    let c_str = CString::new(name).map_err(|_| Error::InvalidType)?;
    yices! { yices_remove_type_name(c_str.as_ptr()) };

    Ok(())
}

impl FromStr for Type {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let c_str = CString::new(s).map_err(|_| Error::InvalidType)?;
        let typ = yices! { yices_parse_type(c_str.as_ptr()) };

        if typ == NULL_TYPE {
            Err(Error::InvalidType)
        } else {
            Self::try_from(typ)
        }
    }
}
