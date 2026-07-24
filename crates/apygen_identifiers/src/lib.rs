use std::fmt::{Display, Formatter};
use std::sync::Arc;

pub use crate::smol_str::SmolStr;
pub use smol_str;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub line: usize,
    pub offset: usize,
}

impl Location {
    pub fn new(line: usize, offset: usize) -> Self {
        Self { line, offset }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.offset)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QualifiedLocation {
    pub location: Location,
    pub namespace: Arc<Namespace>,
}

impl QualifiedLocation {
    pub fn new(location: Location, namespace: Arc<Namespace>) -> Self {
        Self {
            location,
            namespace,
        }
    }
}

impl Display for QualifiedLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]", self.namespace, self.location)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NamedQualifiedLocation {
    pub name: SmolStr,
    pub location: Location,
    pub namespace: Arc<Namespace>,
}

impl NamedQualifiedLocation {
    pub fn new(name: SmolStr, location: Location, namespace: Arc<Namespace>) -> Self {
        Self {
            name,
            location,
            namespace,
        }
    }
}

impl Display for NamedQualifiedLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}@{{{}}}]", self.namespace, self.name, self.location)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Namespace {
    Module(SmolStr),
    ProgramEntity(QualifiedLocation),
    NamedProgramEntity(NamedQualifiedLocation),
}

impl Namespace {
    pub fn parent(&self) -> Option<&Arc<Self>> {
        match self {
            Namespace::Module(_) => None,
            Namespace::ProgramEntity(qualified_location) => Some(&qualified_location.namespace),
            Namespace::NamedProgramEntity(named_qualified_location) => {
                Some(&named_qualified_location.namespace)
            }
        }
    }

    pub fn module_name(&self) -> &SmolStr {
        match self {
            Namespace::Module(module_name) => module_name,
            Namespace::ProgramEntity(qualified_location) => {
                qualified_location.namespace.module_name()
            }
            Namespace::NamedProgramEntity(named_qualified_location) => {
                named_qualified_location.namespace.module_name()
            }
        }
    }
}

impl Display for Namespace {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Namespace::Module(module_name) => write!(f, "{}", module_name),
            Namespace::ProgramEntity(program_entity_location) => {
                write!(f, "{}", program_entity_location)
            }
            Namespace::NamedProgramEntity(named_program_entity_location) => {
                write!(f, "{}", named_program_entity_location)
            }
        }
    }
}
