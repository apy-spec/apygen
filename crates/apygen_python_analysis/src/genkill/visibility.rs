use crate::inference::{QualifiedName, Visibility};

pub fn is_dunder_name(name: &str) -> bool {
    name.starts_with("__") && name.ends_with("__")
}

pub fn is_internal_name(name: &str) -> bool {
    name.starts_with("_") && !is_dunder_name(name)
}

pub fn is_internal_mangled_name(name: &str) -> bool {
    name.starts_with("__") && !name.ends_with("__")
}

pub fn visibility_from_name(name: &QualifiedName) -> Visibility {
    if name
        .identifiers
        .iter()
        .any(|component| is_internal_mangled_name(component))
    {
        Visibility::Internal
    } else {
        Visibility::Public
    }
}

pub fn visibility_from_class_name(name: &str) -> Visibility {
    if is_internal_mangled_name(name) {
        Visibility::Internal
    } else if is_internal_name(name) {
        Visibility::Subclass
    } else {
        Visibility::Public
    }
}
