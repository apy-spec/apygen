pub use apy;
pub use apy::v1::{Identifier, ParseIdentifierError, ParseQualifiedNameError, QualifiedName};
pub use apy::{EmptyCollectionError, OneOrMany};
use std::fmt::{Display, Formatter};
use std::sync::Arc;

pub type ModuleName = Arc<QualifiedName>;
pub type VariableName = Arc<Identifier>;

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
    pub module_name: ModuleName,
    pub locations: Arc<Vec<Location>>,
}

impl QualifiedLocation {
    pub fn new(module_name: ModuleName, locations: Arc<Vec<Location>>) -> Self {
        Self {
            module_name,
            locations,
        }
    }

    pub fn at_sublocation(&self, location: Location) -> Self {
        let mut locations = self.locations.as_ref().clone();
        locations.push(location);
        Self::new(self.module_name.clone(), Arc::new(locations))
    }
}

impl Display for QualifiedLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.module_name)?;
        if !self.locations.is_empty() {
            for location in self.locations.as_ref() {
                write!(f, "[{}]", location)?;
            }
        }
        Ok(())
    }
}

impl From<ModuleName> for QualifiedLocation {
    fn from(module_name: ModuleName) -> Self {
        Self::new(module_name, Arc::new(Vec::new()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProgramEntityIdentifier {
    pub qualified_location: QualifiedLocation,

    pub name: VariableName,
}

impl ProgramEntityIdentifier {
    pub fn new(qualified_location: QualifiedLocation, name: VariableName) -> Self {
        Self {
            qualified_location,
            name,
        }
    }
}

impl Display for ProgramEntityIdentifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.name, self.qualified_location)
    }
}
