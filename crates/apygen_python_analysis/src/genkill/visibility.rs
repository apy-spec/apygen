use std::collections::HashMap;
use std::sync::Arc;
use apygen_analysis::cfg::{Cfg, ProgramPointData};
use apygen_analysis::cfg::nodes::Stmt;
use apygen_analysis::namespace::Location;
use crate::abstract_environment::{QualifiedName, Visibility};

pub fn is_dunder_name(name: &str) -> bool {
    name.starts_with("__") && name.ends_with("__")
}

pub fn is_internal_name(name: &str) -> bool {
    name.starts_with("_") && !is_dunder_name(name)
}

pub fn is_internal_mangled_name(name: &str) -> bool {
    name.starts_with("__") && !name.ends_with("__")
}

pub fn visibility_from_module_name(name: &QualifiedName) -> Visibility {
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


pub fn gen_visibility(
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    location: &Location<QualifiedName>,
    name: &str,
) -> Visibility {
    match visibility_from_class_name(name) {
        Visibility::Subclass => {
            let data = cfgs
                .get(&location.namespace_location.module)
                .map(|cfg| {
                    Some({
                        if let Some(program_point_id) = location.namespace_location.program_point_id
                        {
                            cfg.sub_cfg(program_point_id)?
                        } else {
                            cfg
                        }
                    })
                })
                .flatten()
                .map(|cfg| cfg.node_data(&location.program_point))
                .flatten();

            if matches!(
                data,
                Some(ProgramPointData {
                    statement: Stmt::ClassDef(_),
                    ..
                })
            ) {
                Visibility::Subclass
            } else {
                Visibility::Internal
            }
        }
        visibility => visibility,
    }
}
