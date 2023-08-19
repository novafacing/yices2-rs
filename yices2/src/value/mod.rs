use crate::sys::{yval_t, yval_tag};

pub struct Value {
    pub(crate) value: yval_t,
}

impl Default for Value {
    fn default() -> Self {
        Self {
            value: yval_t {
                node_id: 0,
                node_tag: yval_tag::YVAL_UNKNOWN,
            },
        }
    }
}

impl From<yval_t> for Value {
    fn from(value: yval_t) -> Self {
        Self { value }
    }
}

impl From<&yval_t> for Value {
    fn from(value: &yval_t) -> Self {
        Self {
            value: yval_t {
                node_id: value.node_id,
                node_tag: value.node_tag,
            },
        }
    }
}
