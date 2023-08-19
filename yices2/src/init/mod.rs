use crate::sys::{yices_exit, yices_init, yices_set_out_of_mem_callback};
use ctor::{ctor, dtor};

#[no_mangle]
extern "C" fn oom_cb() {
    panic!("yices2: out of memory");
}

#[cfg(feature = "ctor")]
#[ctor]
/// Constructor: initialize yices at initialization time
fn init() {
    unsafe { yices_set_out_of_mem_callback(Some(oom_cb)) };
    unsafe { yices_init() };
}

#[cfg(feature = "ctor")]
#[dtor]
/// Destructor: clean up yices at exit time
fn exit() {
    unsafe { yices_exit() };
}
