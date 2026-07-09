use crate::AnalysisObserver;
use log::{debug, info};
use std::collections::BTreeSet;
use std::time::Instant;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LogAnalysisObserver {
    prefix: String,
    iteration: usize,
    instant: Instant,
}

impl LogAnalysisObserver {
    pub fn with_prefix(prefix: String) -> Self {
        Self {
            prefix,
            ..Self::default()
        }
    }
}

impl Default for LogAnalysisObserver {
    fn default() -> Self {
        Self {
            prefix: String::new(),
            iteration: 0,
            instant: Instant::now(),
        }
    }
}

impl<N, S> AnalysisObserver<N, S> for LogAnalysisObserver {
    fn before_iteration(&mut self, _state: &S, worklist: &BTreeSet<N>) {
        self.instant = Instant::now();
        info!(
            "[{}] Iteration {} (Worklist size: {})",
            self.prefix,
            self.iteration,
            worklist.len()
        );
    }
    fn after_iteration(&mut self, _state: &S, _worklist: &BTreeSet<N>) {
        debug!(
            "[{}] Iteration {} done (after {:?})",
            self.prefix,
            self.iteration,
            self.instant.elapsed()
        );
        self.iteration += 1;
    }
}
