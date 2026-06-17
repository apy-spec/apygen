use crate::cfg::{Cfg, ProgramPoint};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::sync::Arc;

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SubLocation {
    pub program_points: Vec<ProgramPoint>,
}

impl SubLocation {
    pub fn new(program_points: Vec<ProgramPoint>) -> Self {
        Self { program_points }
    }

    pub fn sub_location(&self, program_point: ProgramPoint) -> Self {
        let mut program_points = self.program_points.clone();
        program_points.push(program_point);
        Self { program_points }
    }

    pub fn parent_location(&self) -> Option<SubLocation> {
        if self.program_points.is_empty() {
            None
        } else {
            Some(Self {
                program_points: self.program_points[..self.program_points.len() - 1].to_vec(),
            })
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NamespaceLocation<M> {
    pub module: Arc<M>,
    pub sublocation: Arc<SubLocation>,
}

impl<M> NamespaceLocation<M> {
    pub fn new(module: Arc<M>, sublocation: Arc<SubLocation>) -> Self {
        Self {
            module,
            sublocation,
        }
    }

    pub fn root_location(&self) -> Self {
        Self::from(self.module.clone())
    }

    pub fn parent_location(&self) -> Option<Self> {
        Some(Self::new(
            self.module.clone(),
            Arc::new(self.sublocation.parent_location()?),
        ))
    }

    pub fn sub_location(&self, program_point: ProgramPoint) -> Self {
        Self::new(
            self.module.clone(),
            Arc::new(self.sublocation.sub_location(program_point)),
        )
    }

    pub fn resolve<'a>(&self, cfg: &'a Cfg) -> Option<&'a Cfg> {
        let mut cfg = cfg;
        for program_point in &self.sublocation.program_points {
            cfg = cfg.cfgs().get(program_point)?;
        }
        Some(cfg)
    }
}

impl<M> From<Arc<M>> for NamespaceLocation<M> {
    fn from(module: Arc<M>) -> Self {
        NamespaceLocation::new(module, Arc::new(SubLocation::default()))
    }
}

impl<M> From<M> for NamespaceLocation<M> {
    fn from(module: M) -> Self {
        Self::from(Arc::new(module))
    }
}

impl<M: Display> Display for NamespaceLocation<M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.module)?;

        if !self.sublocation.program_points.is_empty() {
            write!(f, "@")?;
            for program_point in &self.sublocation.program_points {
                write!(f, "{}", program_point)?;
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location<M> {
    pub namespace_location: NamespaceLocation<M>,
    pub program_point: ProgramPoint,
}

impl<M> Location<M> {
    pub fn new(namespace_location: NamespaceLocation<M>, program_point: ProgramPoint) -> Self {
        Location {
            namespace_location,
            program_point,
        }
    }

    pub fn at_exit(location: NamespaceLocation<M>) -> Self {
        Location {
            namespace_location: location,
            program_point: ProgramPoint::Exit,
        }
    }

    pub fn as_sub_location(&self) -> NamespaceLocation<M> {
        self.namespace_location.sub_location(self.program_point)
    }
}

impl<M> From<Arc<M>> for Location<M> {
    fn from(module: Arc<M>) -> Self {
        Self::at_exit(NamespaceLocation::from(module))
    }
}

impl<M> From<M> for Location<M> {
    fn from(module: M) -> Self {
        Self::from(Arc::new(module))
    }
}

impl<M: Display> Display for Location<M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.namespace_location, self.program_point)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Namespace<E: Clone + Default> {
    pub abstract_environments: HashMap<ProgramPoint, E>,
}

impl<E: Clone + Default> Namespace<E> {
    pub fn new() -> Self {
        let mut namespace = Self::default();
        namespace
            .abstract_environments
            .insert(ProgramPoint::Entry, E::default());
        namespace
            .abstract_environments
            .insert(ProgramPoint::Exit, E::default());
        namespace
    }

    pub fn at_exit(&self) -> Option<&E> {
        self.abstract_environments.get(&ProgramPoint::Exit)
    }

    pub fn clone_abstract_environment_or_default(&self, program_point: ProgramPoint) -> E {
        self.abstract_environments
            .get(&program_point)
            .cloned()
            .unwrap_or_default()
    }
}

pub trait Namespaces<M: Clone + PartialEq + Eq + Hash, E: Clone + Default> {
    fn reset_abstract_environments(&mut self, namespace_location: &NamespaceLocation<M>);
    fn get_abstract_environment(&self, location: &Location<M>) -> Option<&E>;
    fn abstract_environment_entry(
        &'_ mut self,
        location: Location<M>,
    ) -> Entry<'_, ProgramPoint, E>;
}

#[derive(Debug, Default, Clone)]
pub struct NamespaceLocations<M, E: Clone + Default> {
    pub locations: HashMap<NamespaceLocation<M>, Namespace<E>>,
}

impl<M, E: Clone + Default> NamespaceLocations<M, E> {
    pub fn new() -> Self {
        NamespaceLocations {
            locations: HashMap::new(),
        }
    }
}

impl<M: Clone + PartialEq + Eq + Hash, E: Clone + Default> Namespaces<M, E>
    for NamespaceLocations<M, E>
{
    fn reset_abstract_environments(&mut self, namespace_location: &NamespaceLocation<M>) {
        self.locations.remove(namespace_location);
    }

    fn get_abstract_environment(&self, location: &Location<M>) -> Option<&E> {
        let namespace = self.locations.get(&location.namespace_location)?;
        namespace.abstract_environments.get(&location.program_point)
    }

    fn abstract_environment_entry(
        &'_ mut self,
        location: Location<M>,
    ) -> Entry<'_, ProgramPoint, E> {
        let namespace = self
            .locations
            .entry(location.namespace_location)
            .or_default();
        namespace
            .abstract_environments
            .entry(location.program_point)
    }
}

#[derive(Debug)]
pub struct NamespaceLocationsProxy<'n, M: Clone + PartialEq + Eq + Hash, E: Clone + Default> {
    pub namespaces: &'n NamespaceLocations<M, E>,
    pub override_namespaces: NamespaceLocations<M, E>,
}

impl<'n, M: Clone + PartialEq + Eq + Hash, E: Clone + Default> NamespaceLocationsProxy<'n, M, E> {
    pub fn new(namespaces: &'n NamespaceLocations<M, E>) -> Self {
        NamespaceLocationsProxy {
            namespaces,
            override_namespaces: NamespaceLocations::new(),
        }
    }
}

impl<M: Clone + PartialEq + Eq + Hash, E: Clone + Default> Namespaces<M, E>
    for NamespaceLocationsProxy<'_, M, E>
{
    fn reset_abstract_environments(&mut self, namespace_location: &NamespaceLocation<M>) {
        if let Some(override_namespace) = self
            .override_namespaces
            .locations
            .get_mut(namespace_location)
        {
            override_namespace.abstract_environments.clear();
        } else if self.namespaces.locations.contains_key(&namespace_location) {
            self.override_namespaces
                .locations
                .insert(namespace_location.clone(), Namespace::default());
        }
    }

    fn get_abstract_environment(&self, location: &Location<M>) -> Option<&E> {
        if let Some(override_namespace) = self
            .override_namespaces
            .locations
            .get(&location.namespace_location)
        {
            override_namespace
                .abstract_environments
                .get(&location.program_point)
        } else {
            self.namespaces.get_abstract_environment(location)
        }
    }

    fn abstract_environment_entry(
        &'_ mut self,
        location: Location<M>,
    ) -> Entry<'_, ProgramPoint, E> {
        let override_entry = self
            .override_namespaces
            .locations
            .entry(location.namespace_location);

        let override_namespace = match override_entry {
            Entry::Occupied(occupied_entry) => occupied_entry.into_mut(),
            Entry::Vacant(vacant_entry) => {
                let namespace = self
                    .namespaces
                    .locations
                    .get(vacant_entry.key())
                    .cloned()
                    .unwrap_or_default();

                vacant_entry.insert(namespace)
            }
        };

        override_namespace
            .abstract_environments
            .entry(location.program_point)
    }
}
