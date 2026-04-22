use crate::abstract_environment::{QualifiedName, Visibility};
use apygen_analysis::cfg::nodes::Stmt;
use apygen_analysis::cfg::{Cfg, NodeData, StatementData};
use apygen_analysis::namespace::NamespaceLocation;
use std::collections::HashMap;
use std::sync::Arc;

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
    namespace_location: &NamespaceLocation<QualifiedName>,
    name: &str,
) -> Visibility {
    match visibility_from_class_name(name) {
        Visibility::Subclass => {
            let Some(module_cfg) = cfgs.get(&namespace_location.module) else {
                return Visibility::Internal;
            };
            let Some(parent_location) = namespace_location.parent_location() else {
                return Visibility::Internal;
            };
            let Some(cfg) = parent_location.resolve(module_cfg) else {
                return Visibility::Internal;
            };

            let data = cfg
                .node_data(
                    &namespace_location
                        .program_points
                        .last()
                        .expect("Program point not found"),
                )
                .expect("resolution failed");

            if matches!(
                data,
                NodeData::Statement(StatementData {
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
