pub use apygen_cfg as cfg;
use std::collections::BTreeSet;

pub mod lattice;
pub mod namespace;

pub trait CfgAnalyser<A, N> {
    type Error;

    fn successors(
        &self,
        program_point: &cfg::ProgramPoint,
    ) -> Result<impl Iterator<Item = cfg::ProgramPoint>, Self::Error>;

    fn initialise_abstract_environments(&self) -> Result<N, Self::Error>;
    fn analyse_program_point(
        &self,
        abstract_environments: &N,
        program_point: cfg::ProgramPoint,
    ) -> Result<A, Self::Error>;
    fn update_abstract_environment(
        &self,
        abstract_environments: &N,
        abstract_environment: &A,
        from: cfg::ProgramPoint,
        to: cfg::ProgramPoint,
    ) -> Result<Option<A>, Self::Error>;
    fn get_abstract_environment(
        &self,
        abstract_environments: &N,
        program_point: cfg::ProgramPoint,
    ) -> Result<Option<A>, Self::Error>;
    fn set_abstract_environment(
        &self,
        abstract_environments: &mut N,
        program_point: cfg::ProgramPoint,
        abstract_environment: &A,
    ) -> Result<(), Self::Error>;

    fn includes(
        &self,
        abstract_environments: &N,
        program_point: cfg::ProgramPoint,
        including: &A,
        included: &A,
    ) -> Result<bool, Self::Error>;
    fn join(
        &self,
        abstract_environments: &N,
        program_point: cfg::ProgramPoint,
        left: &A,
        right: &A,
    ) -> Result<A, Self::Error>;
}

pub fn worklist<A: Default, N, E, T: CfgAnalyser<A, N, Error = E>>(analyser: &T) -> Result<N, E> {
    let mut abstract_environments = analyser.initialise_abstract_environments()?;

    let mut worklist = BTreeSet::from_iter([cfg::ProgramPoint::Entry]);

    while let Some(program_point) = worklist.pop_first() {
        let res_abstract_environment =
            analyser.analyse_program_point(&mut abstract_environments, program_point)?;

        for successor in analyser.successors(&program_point)? {
            let Some(res_cond_abstract_environment) = analyser.update_abstract_environment(
                &abstract_environments,
                &res_abstract_environment,
                program_point,
                successor,
            )?
            else {
                continue;
            };

            let (successor_is_included, successor_abstract_environment) =
                match analyser.get_abstract_environment(&abstract_environments, successor)? {
                    Some(successor_abstract_environment) => (
                        analyser.includes(
                            &abstract_environments,
                            successor,
                            &successor_abstract_environment,
                            &res_cond_abstract_environment,
                        )?,
                        successor_abstract_environment,
                    ),
                    None => (false, A::default()),
                };

            if !successor_is_included {
                let joined_abstract_environment = analyser.join(
                    &abstract_environments,
                    successor,
                    &successor_abstract_environment,
                    &res_cond_abstract_environment,
                )?;
                analyser.set_abstract_environment(
                    &mut abstract_environments,
                    successor,
                    &joined_abstract_environment,
                )?;
                worklist.insert(successor);
            }
        }
    }

    Ok(abstract_environments)
}
