pub use yices2_sys::*;

#[macro_export]
/// Make a call to the Yices2 API. This macro will automatically report any errors
/// that occur as an [`Error`](crate::error::Error).
macro_rules! yices_try {
    ($x:expr) => {
        unsafe {
            let res = $x;
            $crate::err!(res)
        }
    };
}

#[macro_export]
/// Make a call to the Yices2 API. This macro will automatically report any errors
/// that occur as an [`Error`](crate::error::Error), similar to [`yices_try!`](crate::yices_try!)
/// but returns immediately if there is an error.
macro_rules! yices {
    ($x:expr) => {
        unsafe {
            match $crate::yices_try!($x) {
                Ok(ok) => ok,
                Err(err) => {
                    return Err(err);
                }
            }
        }
    };
}
