use crate::cfg::ProgramPoint;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NamespaceLocation<M> {
    pub module: Arc<M>,
    pub program_point_id: Option<usize>,
}

impl<M> NamespaceLocation<M> {
    pub fn new(module: Arc<M>) -> Self {
        NamespaceLocation {
            module,
            program_point_id: None,
        }
    }

    pub fn root_location(&self) -> Self {
        NamespaceLocation {
            module: self.module.clone(),
            program_point_id: None,
        }
    }

    pub fn sub_location(&self, id: usize) -> Self {
        NamespaceLocation {
            module: self.module.clone(),
            program_point_id: Some(id),
        }
    }
}

impl<M> From<Arc<M>> for NamespaceLocation<M> {
    fn from(module: Arc<M>) -> Self {
        NamespaceLocation {
            module,
            program_point_id: None,
        }
    }
}

impl<M> From<M> for NamespaceLocation<M> {
    fn from(module: M) -> Self {
        Self::from(Arc::new(module))
    }
}

impl<M: Display> Display for NamespaceLocation<M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(id) = self.program_point_id {
            write!(f, "{}:{}", self.module, id)
        } else {
            write!(f, "{}", self.module)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location<M> {
    pub namespace_location: NamespaceLocation<M>,
    pub program_point: ProgramPoint,
}

impl<M> Location<M> {
    pub fn at_exit(location: NamespaceLocation<M>) -> Self {
        Location {
            namespace_location: location,
            program_point: ProgramPoint::Exit,
        }
    }

    pub fn at_sub_location_exit(&self) -> Self {
        Location {
            namespace_location: self
                .namespace_location
                .sub_location(self.program_point.id()),
            program_point: ProgramPoint::Exit,
        }
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

#[derive(Debug, Default, Clone)]
pub struct Namespace<E> {
    pub environments: HashMap<ProgramPoint, E>,
}

impl<E> Namespace<E> {
    pub fn at_exit(&self) -> Option<&E> {
        self.environments.get(&ProgramPoint::Exit)
    }
}

pub trait NamespacesContext<M: Clone + PartialEq + Eq + Hash, E: Clone + Default> {
    fn reset_abstract_environments(&mut self, namespace_location: &NamespaceLocation<M>);
    fn get_abstract_environment(&self, location: &Location<M>) -> Option<&E>;
    fn abstract_environment_entry(
        &'_ mut self,
        location: Location<M>,
    ) -> Entry<'_, ProgramPoint, E>;
}

#[derive(Debug, Default, Clone)]
pub struct Namespaces<M, E> {
    pub locations: HashMap<NamespaceLocation<M>, Namespace<E>>,
}

impl<M, E> Namespaces<M, E> {
    pub fn new() -> Self {
        Namespaces {
            locations: HashMap::new(),
        }
    }
}

impl<M: Clone + PartialEq + Eq + Hash, E: Clone + Default> NamespacesContext<M, E>
    for Namespaces<M, E>
{
    fn reset_abstract_environments(&mut self, namespace_location: &NamespaceLocation<M>) {
        self.locations.remove(namespace_location);
    }

    fn get_abstract_environment(&self, location: &Location<M>) -> Option<&E> {
        let namespace = self.locations.get(&location.namespace_location)?;
        namespace.environments.get(&location.program_point)
    }

    fn abstract_environment_entry(
        &'_ mut self,
        location: Location<M>,
    ) -> Entry<'_, ProgramPoint, E> {
        let namespace = self
            .locations
            .entry(location.namespace_location)
            .or_default();
        namespace.environments.entry(location.program_point)
    }
}

#[derive(Debug)]
pub struct NamespacesProxy<'n, M: Clone + PartialEq + Eq + Hash, E: Clone + Default> {
    pub namespaces: &'n Namespaces<M, E>,
    pub override_namespaces: Namespaces<M, E>,
}

impl<'n, M: Clone + PartialEq + Eq + Hash, E: Clone + Default> NamespacesProxy<'n, M, E> {
    pub fn new(namespaces: &'n Namespaces<M, E>) -> Self {
        NamespacesProxy {
            namespaces,
            override_namespaces: Namespaces::new(),
        }
    }
}

impl<M: Clone + PartialEq + Eq + Hash, E: Clone + Default> NamespacesContext<M, E>
    for NamespacesProxy<'_, M, E>
{
    fn reset_abstract_environments(&mut self, namespace_location: &NamespaceLocation<M>) {
        if let Some(override_namespace) = self
            .override_namespaces
            .locations
            .get_mut(namespace_location)
        {
            override_namespace.environments.clear();
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
            override_namespace.environments.get(&location.program_point)
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
            .environments
            .entry(location.program_point)
    }
}
