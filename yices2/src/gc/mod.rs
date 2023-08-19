use crate::{
    sys::{term_t, type_t, yices_garbage_collect, yices_num_posref_terms, yices_num_posref_types},
    yices, Result,
};

pub fn num_posref_types() -> Result<u32> {
    Ok(yices! { yices_num_posref_types() })
}

pub fn num_posref_terms() -> Result<u32> {
    Ok(yices! { yices_num_posref_terms() })
}

pub fn garbage_collect<T, TY, IT, ITY>(
    preserve_terms: IT,
    preserve_types: ITY,
    preserve_named: bool,
) -> Result<()>
where
    IT: IntoIterator<Item = T>,
    ITY: IntoIterator<Item = TY>,
    T: Into<term_t>,
    TY: Into<type_t>,
{
    let terms: Vec<_> = preserve_terms.into_iter().map(|t| t.into()).collect();
    let types: Vec<_> = preserve_types.into_iter().map(|t| t.into()).collect();

    yices! { yices_garbage_collect(
        terms.as_ptr(),
        terms.len() as u32,
        types.as_ptr(),
        types.len() as u32,
        preserve_named as i32
    ) };

    Ok(())
}
