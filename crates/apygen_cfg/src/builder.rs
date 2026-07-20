use crate::ast::{
    ExceptHandler, Stmt, StmtBreak, StmtClassDef, StmtContinue, StmtFor, StmtFunctionDef, StmtIf,
    StmtMatch, StmtPass, StmtRaise, StmtReturn, StmtTry, StmtWhile, StmtWith, Suite,
};
use crate::source_file::LineIndex;
use crate::text_size::Ranged;
use crate::{
    Cfg, CfgEdge, CfgEdgeKind, CfgNode, ConvertTextSizeError, Location, ProgramPoint,
    convert_text_size_to_location,
};
use bitflags::bitflags;
use ruff_python_ast::ModModule;
use std::collections::HashSet;
use thiserror::Error;

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct PointType: u8 {
        const NONE = 0;
        const PREVIOUS = 1 << 0;
        const RETURN = 1 << 1;
        const EXCEPTION = 1 << 2;
        const CONTINUE = 1 << 3;
        const BREAK = 1 << 4;
    }
}

pub fn map_with<T, V: Clone>(
    iter: impl IntoIterator<Item = T>,
    value: V,
) -> impl Iterator<Item = (T, V)> {
    iter.into_iter().map(move |key| (key, value.clone()))
}

#[derive(Debug, Clone, Default)]
pub struct ResultPoints {
    pub previous_points: HashSet<(ProgramPoint, CfgEdgeKind)>,
    pub return_points: HashSet<ProgramPoint>,
    pub exception_points: HashSet<ProgramPoint>,
    pub continue_points: HashSet<ProgramPoint>,
    pub break_points: HashSet<ProgramPoint>,
}

impl ResultPoints {
    pub fn merge_into(&mut self, other: ResultPoints) {
        self.previous_points.extend(other.previous_points);
        self.return_points.extend(other.return_points);
        self.exception_points.extend(other.exception_points);
        self.continue_points.extend(other.continue_points);
        self.break_points.extend(other.break_points);
    }

    pub fn with_previous_point(mut self, point: ProgramPoint, edge_data: CfgEdgeKind) -> Self {
        self.previous_points.insert((point, edge_data));
        self
    }

    pub fn with_return_point(mut self, point: ProgramPoint) -> Self {
        self.return_points.insert(point);
        self
    }

    pub fn with_exception_point(mut self, point: ProgramPoint) -> Self {
        self.exception_points.insert(point);
        self
    }

    pub fn with_continue_point(mut self, point: ProgramPoint) -> Self {
        self.continue_points.insert(point);
        self
    }

    pub fn with_break_point(mut self, point: ProgramPoint) -> Self {
        self.break_points.insert(point);
        self
    }

    pub fn point_type(&self) -> PointType {
        let mut point_type = PointType::NONE;
        if !self.previous_points.is_empty() {
            point_type |= PointType::PREVIOUS;
        }
        if !self.return_points.is_empty() {
            point_type |= PointType::RETURN;
        }
        if !self.exception_points.is_empty() {
            point_type |= PointType::EXCEPTION;
        }
        if !self.continue_points.is_empty() {
            point_type |= PointType::CONTINUE;
        }
        if !self.break_points.is_empty() {
            point_type |= PointType::BREAK;
        }
        point_type
    }

    pub fn insert_as(&mut self, point_type: PointType, program_point: ProgramPoint) {
        if point_type.contains(PointType::PREVIOUS) {
            self.previous_points
                .insert((program_point, CfgEdgeKind::Unconditional));
        }
        if point_type.contains(PointType::RETURN) {
            self.return_points.insert(program_point);
        }
        if point_type.contains(PointType::EXCEPTION) {
            self.exception_points.insert(program_point);
        }
        if point_type.contains(PointType::CONTINUE) {
            self.continue_points.insert(program_point);
        }
        if point_type.contains(PointType::BREAK) {
            self.break_points.insert(program_point);
        }
    }

    pub fn drain(&mut self) -> impl Iterator<Item = (ProgramPoint, CfgEdgeKind)> {
        self.previous_points
            .drain()
            .chain(map_with(
                self.return_points.drain(),
                CfgEdgeKind::Unconditional,
            ))
            .chain(map_with(
                self.exception_points.drain(),
                CfgEdgeKind::Unconditional,
            ))
            .chain(map_with(
                self.continue_points.drain(),
                CfgEdgeKind::Unconditional,
            ))
            .chain(map_with(
                self.break_points.drain(),
                CfgEdgeKind::Unconditional,
            ))
    }
}

pub enum StmtLoop<'s> {
    For(&'s StmtFor),
    While(&'s StmtWhile),
}

pub enum StmtDef<'s> {
    FunctionDef(&'s StmtFunctionDef),
    ClassDef(&'s StmtClassDef),
}

#[derive(Debug, Error)]
pub enum BuildCfgError {
    #[error("{0}")]
    TryFromTextSize(#[from] ConvertTextSizeError),
    #[error("invalid elif statement at location {0}")]
    InvalidElifStatement(Location),
    #[error("break statement outside of any loop")]
    BreakStatementOutsideLoop,
    #[error("continue statement outside of any loop")]
    ContinueStatementOutsideLoop,
}

#[derive(Debug, Clone)]
pub struct CfgBuilder<'i> {
    pub index: &'i LineIndex,
}

impl<'i> CfgBuilder<'i> {
    pub fn new(index: &'i LineIndex) -> Self {
        Self { index }
    }

    pub fn create_location(&self, ranged: &impl Ranged) -> Result<Location, ConvertTextSizeError> {
        convert_text_size_to_location(self.index, ranged.start())
    }

    pub fn create_program_point(
        &self,
        ranged: &impl Ranged,
    ) -> Result<ProgramPoint, ConvertTextSizeError> {
        Ok(ProgramPoint::Location(self.create_location(ranged)?))
    }

    pub fn insert_current_node<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        current_point: ProgramPoint,
        node: Option<CfgNode<'s>>,
    ) {
        cfg.insert_node(current_point, node);

        for (previous_point, edge_kind) in previous_points {
            cfg.insert_edge_kind(CfgEdge::new(previous_point, current_point), edge_kind);
        }
    }

    pub fn build_cfg<'s>(&self, suite: &'s Suite) -> Result<Cfg<'s>, BuildCfgError> {
        let mut cfg = Cfg::default();

        let result_points = self.process_suite(
            &mut cfg,
            HashSet::from_iter([(ProgramPoint::Entry, CfgEdgeKind::Unconditional)]),
            suite,
        )?;

        if !result_points.break_points.is_empty() {
            return Err(BuildCfgError::BreakStatementOutsideLoop);
        }
        if !result_points.continue_points.is_empty() {
            return Err(BuildCfgError::ContinueStatementOutsideLoop);
        }

        let previous_points = result_points
            .previous_points
            .into_iter()
            .chain(map_with(result_points.return_points, CfgEdgeKind::Return))
            .chain(map_with(
                result_points.exception_points,
                CfgEdgeKind::UnhandledException,
            ));

        self.insert_current_node(&mut cfg, previous_points, ProgramPoint::Exit, None);

        Ok(cfg)
    }

    pub fn process_def_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_def: StmtDef<'s>,
    ) -> Result<ResultPoints, BuildCfgError> {
        let (location, node, body_suite) = match stmt_def {
            StmtDef::FunctionDef(stmt_function_def) => (
                self.create_location(stmt_function_def)?,
                CfgNode::FunctionDef(stmt_function_def),
                &stmt_function_def.body,
            ),
            StmtDef::ClassDef(stmt_class_def) => (
                self.create_location(stmt_class_def)?,
                CfgNode::ClassDef(stmt_class_def),
                &stmt_class_def.body,
            ),
        };
        cfg.insert_cfg(location, self.build_cfg(body_suite)?);

        let current_point = ProgramPoint::Location(location);

        self.insert_current_node(cfg, previous_points, current_point, Some(node));

        Ok(ResultPoints::default()
            .with_previous_point(current_point, CfgEdgeKind::Unconditional)
            .with_exception_point(current_point))
    }

    pub fn process_return_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_return: &'s StmtReturn,
    ) -> Result<ResultPoints, BuildCfgError> {
        let current_point = self.create_program_point(stmt_return)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::Return(stmt_return)),
        );

        Ok(ResultPoints::default()
            .with_return_point(current_point)
            .with_exception_point(current_point))
    }

    pub fn process_if_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_if: &'s StmtIf,
    ) -> Result<ResultPoints, BuildCfgError> {
        let mut current_point = self.create_program_point(stmt_if)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::If(stmt_if)),
        );

        let mut result_points = self
            .process_suite(
                cfg,
                HashSet::from_iter([(current_point, CfgEdgeKind::Conditional(true))]),
                &stmt_if.body,
            )?
            .with_exception_point(current_point);

        let mut else_reached = false;
        for elif_else_clause in &stmt_if.elif_else_clauses {
            let elif_else_clause_location = self.create_location(elif_else_clause)?;

            if else_reached {
                return Err(BuildCfgError::InvalidElifStatement(
                    elif_else_clause_location,
                ));
            }

            let elif_else_clause_point = ProgramPoint::Location(elif_else_clause_location);

            result_points.merge_into(if elif_else_clause.test.is_some() {
                self.insert_current_node(
                    cfg,
                    [(current_point, CfgEdgeKind::Conditional(false))],
                    elif_else_clause_point,
                    Some(CfgNode::Elif(elif_else_clause)),
                );
                self.process_suite(
                    cfg,
                    HashSet::from_iter([(elif_else_clause_point, CfgEdgeKind::Conditional(true))]),
                    &elif_else_clause.body,
                )?
                .with_exception_point(elif_else_clause_point)
            } else {
                else_reached = true;
                self.process_suite(
                    cfg,
                    HashSet::from_iter([(current_point, CfgEdgeKind::Conditional(false))]),
                    &elif_else_clause.body,
                )?
            });

            current_point = elif_else_clause_point;
        }

        if !else_reached {
            result_points
                .previous_points
                .insert((current_point, CfgEdgeKind::Conditional(false)));
        }

        Ok(result_points)
    }

    pub fn process_loop_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_loop: StmtLoop<'s>,
    ) -> Result<ResultPoints, BuildCfgError> {
        let (current_point, node, body_suite, else_suite) = match stmt_loop {
            StmtLoop::For(stmt_for) => (
                self.create_program_point(stmt_for)?,
                CfgNode::For(stmt_for),
                &stmt_for.body,
                &stmt_for.orelse,
            ),
            StmtLoop::While(stmt_while) => (
                self.create_program_point(stmt_while)?,
                CfgNode::While(stmt_while),
                &stmt_while.body,
                &stmt_while.orelse,
            ),
        };

        self.insert_current_node(cfg, previous_points, current_point, Some(node));

        let mut result_points = self.process_suite(
            cfg,
            HashSet::from_iter([(current_point, CfgEdgeKind::Conditional(true))]),
            body_suite,
        )?;

        for continue_point in result_points.continue_points.drain() {
            cfg.insert_edge_kind(
                CfgEdge::new(continue_point, current_point),
                CfgEdgeKind::Continue,
            );
        }
        for (previous_point, edge_kind) in result_points.previous_points.drain() {
            cfg.insert_edge_kind(CfgEdge::new(previous_point, current_point), edge_kind);
        }

        result_points.previous_points.extend(map_with(
            result_points.break_points.drain(),
            CfgEdgeKind::Break,
        ));

        result_points.merge_into(self.process_suite(
            cfg,
            HashSet::from_iter([(current_point, CfgEdgeKind::Conditional(false))]),
            else_suite,
        )?);

        Ok(result_points.with_exception_point(current_point))
    }

    pub fn process_with_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_with: &'s StmtWith,
    ) -> Result<ResultPoints, BuildCfgError> {
        let location = self.create_location(stmt_with)?;

        let current_point = ProgramPoint::Location(location);

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::With(stmt_with)),
        );

        let mut result_points = self.process_suite(
            cfg,
            HashSet::from_iter([(current_point, CfgEdgeKind::Unconditional)]),
            &stmt_with.body,
        )?;

        let mut previous_points_type = result_points.point_type();

        let previous_points = result_points.drain();

        let end_point = ProgramPoint::End(location);

        self.insert_current_node(cfg, previous_points, end_point, None);

        previous_points_type.remove(PointType::EXCEPTION); // Exception are handled after
        result_points.insert_as(previous_points_type, end_point);

        Ok(result_points
            .with_exception_point(current_point)
            .with_exception_point(end_point))
    }

    pub fn process_match_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_match: &'s StmtMatch,
    ) -> Result<ResultPoints, BuildCfgError> {
        let current_point = self.create_program_point(stmt_match)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::Match(stmt_match)),
        );

        let mut result_points = ResultPoints::default();

        for (index, match_case) in stmt_match.cases.iter().enumerate() {
            result_points.merge_into(self.process_suite(
                cfg,
                HashSet::from_iter([(current_point, CfgEdgeKind::Match(index))]),
                &match_case.body,
            )?);
        }

        Ok(result_points.with_exception_point(current_point))
    }

    pub fn process_raise_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_raise: &'s StmtRaise,
    ) -> Result<ResultPoints, BuildCfgError> {
        let current_point = self.create_program_point(stmt_raise)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::Raise(stmt_raise)),
        );

        Ok(ResultPoints::default().with_exception_point(current_point))
    }

    pub fn process_try_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_try: &'s StmtTry,
    ) -> Result<ResultPoints, BuildCfgError> {
        let location = self.create_location(stmt_try)?;

        let current_point = ProgramPoint::Location(location);

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::Try(stmt_try)),
        );

        let mut result_points = self.process_suite(
            cfg,
            HashSet::from_iter([(current_point, CfgEdgeKind::Unconditional)]),
            &stmt_try.body,
        )?;

        let body_previous_points = result_points.previous_points;
        result_points.previous_points = HashSet::default();

        let body_exception_points = result_points.exception_points;
        result_points.exception_points = HashSet::default();

        result_points.merge_into(self.process_suite(
            cfg,
            body_previous_points,
            &stmt_try.orelse,
        )?);

        for (index, ExceptHandler::ExceptHandler(handler)) in stmt_try.handlers.iter().enumerate() {
            let handler_previous_points = body_exception_points
                .iter()
                .map(|exception_point| {
                    (
                        *exception_point,
                        CfgEdgeKind::Exception(current_point, index),
                    )
                })
                .collect();
            result_points.merge_into(self.process_suite(
                cfg,
                handler_previous_points,
                &handler.body,
            )?);
        }

        let previous_points_type = result_points.point_type();

        let previous_points = result_points.drain();

        let end_point = ProgramPoint::End(location);

        let mut finally_result_points =
            self.process_suite(cfg, previous_points.collect(), &stmt_try.finalbody)?;

        self.insert_current_node(
            cfg,
            finally_result_points.previous_points.drain(),
            end_point,
            None,
        );

        result_points.merge_into(finally_result_points);

        result_points.insert_as(previous_points_type, end_point);

        Ok(result_points)
    }

    pub fn process_pass_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_pass: &'s StmtPass,
    ) -> Result<ResultPoints, BuildCfgError> {
        let current_point = self.create_program_point(stmt_pass)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::Pass(stmt_pass)),
        );

        Ok(ResultPoints::default().with_previous_point(current_point, CfgEdgeKind::Unconditional))
    }

    pub fn process_break_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_break: &'s StmtBreak,
    ) -> Result<ResultPoints, BuildCfgError> {
        let current_point = self.create_program_point(stmt_break)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::Break(stmt_break)),
        );

        Ok(ResultPoints::default().with_break_point(current_point))
    }

    pub fn process_continue_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt_continue: &'s StmtContinue,
    ) -> Result<ResultPoints, BuildCfgError> {
        let current_point = self.create_program_point(stmt_continue)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::Continue(stmt_continue)),
        );

        Ok(ResultPoints::default().with_continue_point(current_point))
    }

    pub fn process_stmt<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        previous_points: impl IntoIterator<Item = (ProgramPoint, CfgEdgeKind)>,
        stmt: &'s Stmt,
    ) -> Result<ResultPoints, BuildCfgError> {
        let current_point = self.create_program_point(stmt)?;

        self.insert_current_node(
            cfg,
            previous_points,
            current_point,
            Some(CfgNode::from(stmt)),
        );

        Ok(ResultPoints::default()
            .with_previous_point(current_point, CfgEdgeKind::Unconditional)
            .with_exception_point(current_point))
    }

    pub fn process_suite<'s>(
        &self,
        cfg: &mut Cfg<'s>,
        mut previous_points: HashSet<(ProgramPoint, CfgEdgeKind)>,
        suite: &'s Suite,
    ) -> Result<ResultPoints, BuildCfgError> {
        let mut result_points = ResultPoints::default();

        for stmt in suite {
            let mut stmt_result_points = match stmt {
                Stmt::FunctionDef(stmt_function_def) => self.process_def_stmt(
                    cfg,
                    previous_points,
                    StmtDef::FunctionDef(stmt_function_def),
                )?,
                Stmt::ClassDef(stmt_class_def) => {
                    self.process_def_stmt(cfg, previous_points, StmtDef::ClassDef(stmt_class_def))?
                }
                Stmt::Return(stmt_return) => {
                    self.process_return_stmt(cfg, previous_points, stmt_return)?
                }
                Stmt::For(stmt_for) => {
                    self.process_loop_stmt(cfg, previous_points, StmtLoop::For(stmt_for))?
                }
                Stmt::While(stmt_while) => {
                    self.process_loop_stmt(cfg, previous_points, StmtLoop::While(stmt_while))?
                }
                Stmt::If(stmt_if) => self.process_if_stmt(cfg, previous_points, stmt_if)?,
                Stmt::With(stmt_with) => self.process_with_stmt(cfg, previous_points, stmt_with)?,
                Stmt::Match(stmt_match) => {
                    self.process_match_stmt(cfg, previous_points, stmt_match)?
                }
                Stmt::Raise(stmt_raise) => {
                    self.process_raise_stmt(cfg, previous_points, stmt_raise)?
                }
                Stmt::Try(stmt_try) => self.process_try_stmt(cfg, previous_points, stmt_try)?,
                Stmt::Pass(stmt_pass) => self.process_pass_stmt(cfg, previous_points, stmt_pass)?,
                Stmt::Break(stmt_break) => {
                    self.process_break_stmt(cfg, previous_points, stmt_break)?
                }
                Stmt::Continue(stmt_continue) => {
                    self.process_continue_stmt(cfg, previous_points, stmt_continue)?
                }
                _ => self.process_stmt(cfg, previous_points, stmt)?,
            };

            previous_points = stmt_result_points.previous_points;
            stmt_result_points.previous_points = HashSet::default();

            result_points.merge_into(stmt_result_points);
        }

        result_points.previous_points = previous_points;

        Ok(result_points)
    }
}

pub fn build_cfg<'s>(
    line_index: &LineIndex,
    mod_module: &'s ModModule,
) -> Result<Cfg<'s>, BuildCfgError> {
    CfgBuilder::new(line_index).build_cfg(&mod_module.body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ModModule;
    use crate::graph::dot::ToDot;
    use crate::parser::{Mode, parse};
    use indoc::{formatdoc, indoc};
    use rstest::{fixture, rstest};
    use std::collections::BTreeMap;

    fn parse_source(source: &str) -> (LineIndex, ModModule) {
        (
            LineIndex::from_source_text(source),
            parse(source, Mode::Module)
                .expect("Should parse source")
                .try_into_module()
                .expect("Should be a module")
                .into_syntax(),
        )
    }

    fn unchecked_build_cfg<'s>(line_index: &LineIndex, mod_module: &'s ModModule) -> Cfg<'s> {
        build_cfg(line_index, mod_module).expect("should build cfg")
    }

    fn build_dot(source: &str) -> String {
        let (line_index, mod_module) = parse_source(source);

        let cfg = unchecked_build_cfg(&line_index, &mod_module);

        cfg.dot("CFG")
    }

    #[fixture]
    fn for_i_fixture() -> (String, String) {
        (String::from("for i in range(10)"), String::from("for"))
    }

    #[fixture]
    fn for_j_fixture() -> (String, String) {
        (String::from("for j in range(5)"), String::from("for"))
    }

    #[fixture]
    fn while_i_fixture() -> (String, String) {
        (String::from("while i < 10"), String::from("while"))
    }

    #[fixture]
    fn while_j_fixture() -> (String, String) {
        (String::from("while j < 5"), String::from("while"))
    }

    #[rstest]
    #[case::generic_statement(
        indoc! {r##"
        a = 5
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Exit";
            "Location(1:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::multiple_generic_statements(
        indoc! {r##"
        a = 5
        b = 10
        c = a + b
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="assign"];
            "Location(2:0)" [label="assign"];
            "Location(3:0)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:0)";
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:0)" -> "Location(3:0)";
            "Location(2:0)" -> "Exit" [label="except"];
            "Location(3:0)" -> "Exit";
            "Location(3:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_if_else_statement(
        indoc! {r##"
        if True:
            a = 5
        else:
            a = 10
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="if"];
            "Location(2:4)" [label="assign"];
            "Location(4:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(4:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Exit";
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(4:4)" -> "Exit";
            "Location(4:4)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_if_without_else_statement(
        indoc! {r##"
        if True:
            a = 5
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="if"];
            "Location(2:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Exit";
            "Location(2:4)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_if_elif_else_statement(
        indoc! {r##"
        if True:
            a = 5
        elif False:
            a = 10
        else:
            a = 15
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="if"];
            "Location(2:4)" [label="assign"];
            "Location(3:0)" [label="elif"];
            "Location(4:4)" [label="assign"];
            "Location(6:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(3:0)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Exit";
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:0)" -> "Location(4:4)" [label="true"];
            "Location(3:0)" -> "Location(6:4)" [label="false"];
            "Location(3:0)" -> "Exit" [label="except"];
            "Location(4:4)" -> "Exit";
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(6:4)" -> "Exit";
            "Location(6:4)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_if_elif_without_else_statement(
        indoc! {r##"
        if True:
            a = 5
        elif False:
            a = 10
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="if"];
            "Location(2:4)" [label="assign"];
            "Location(3:0)" [label="elif"];
            "Location(4:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(3:0)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Exit";
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:0)" -> "Location(4:4)" [label="true"];
            "Location(3:0)" -> "Exit" [label="false"];
            "Location(3:0)" -> "Exit" [label="except"];
            "Location(4:4)" -> "Exit";
            "Location(4:4)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_with_statement(
        indoc! {r##"
        with open('file.txt') as f:
            a = f.read()
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="with"];
            "Location(2:4)" [label="assign"];
            "End(1:0)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)";
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "End(1:0)";
            "End(1:0)" -> "Exit";
            "End(1:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::return_in_with_statement(
        indoc! {r##"
        with open('file.txt') as f:
            if True:
                return f.read()
        a = 100
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="with"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="return"];
            "Location(4:0)" [label="assign"];
            "End(1:0)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)";
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "End(1:0)";
            "Location(2:4)" -> "End(1:0)" [label="false"];
            "Location(3:8)" -> "End(1:0)";
            "Location(4:0)" -> "Exit";
            "Location(4:0)" -> "Exit" [label="except"];
            "End(1:0)" -> "Location(4:0)";
            "End(1:0)" -> "Exit" [label="except"];
            "End(1:0)" -> "Exit" [label="return"];
        }
        "##},
    )]
    #[case::raise_in_with_statement(
        indoc! {r##"
        with open('file.txt') as f:
            if True:
                raise Exception()
        a = 100
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="with"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="raise"];
            "Location(4:0)" [label="assign"];
            "End(1:0)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)";
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "End(1:0)";
            "Location(2:4)" -> "End(1:0)" [label="false"];
            "Location(3:8)" -> "End(1:0)";
            "Location(4:0)" -> "Exit";
            "Location(4:0)" -> "Exit" [label="except"];
            "End(1:0)" -> "Location(4:0)";
            "End(1:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::match_statement(
        indoc! {r##"
        match command:
            case "start":
                a = 0
            case "stop":
                a += 1
            case _:
                None
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="match"];
            "Location(3:8)" [label="assign"];
            "Location(5:8)" [label="aug_assign"];
            "Location(7:8)" [label="expr"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(3:8)" [label="match(0)"];
            "Location(1:0)" -> "Location(5:8)" [label="match(1)"];
            "Location(1:0)" -> "Location(7:8)" [label="match(2)"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit";
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(5:8)" -> "Exit";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:8)" -> "Exit";
            "Location(7:8)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_try_single_except_statement(
        indoc! {r##"
        try:
            a = 1 / 0
        except:
            None
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="try"];
            "Location(2:4)" [label="assign"];
            "Location(4:4)" [label="expr"];
            "End(1:0)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)";
            "Location(2:4)" -> "Location(4:4)" [label="except(Location(1:0), 0)"];
            "Location(2:4)" -> "End(1:0)";
            "Location(4:4)" -> "End(1:0)";
            "End(1:0)" -> "Exit";
            "End(1:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_try_multiple_except_statement(
        indoc! {r##"
        try:
            a = 1 / 0
        except ZeroDivisionError:
            a += 50
        except:
            100
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="try"];
            "Location(2:4)" [label="assign"];
            "Location(4:4)" [label="aug_assign"];
            "Location(6:4)" [label="expr"];
            "End(1:0)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)";
            "Location(2:4)" -> "Location(4:4)" [label="except(Location(1:0), 0)"];
            "Location(2:4)" -> "Location(6:4)" [label="except(Location(1:0), 1)"];
            "Location(2:4)" -> "End(1:0)";
            "Location(4:4)" -> "End(1:0)";
            "Location(6:4)" -> "End(1:0)";
            "End(1:0)" -> "Exit";
            "End(1:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_try_except_else_statement(
        indoc! {r##"
        try:
            a = 1 / 0
        except:
            None
        else:
            a += 100
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="try"];
            "Location(2:4)" [label="assign"];
            "Location(4:4)" [label="expr"];
            "Location(6:4)" [label="aug_assign"];
            "End(1:0)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)";
            "Location(2:4)" -> "Location(4:4)" [label="except(Location(1:0), 0)"];
            "Location(2:4)" -> "Location(6:4)";
            "Location(4:4)" -> "End(1:0)";
            "Location(6:4)" -> "End(1:0)";
            "End(1:0)" -> "Exit";
            "End(1:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    #[case::simple_try_except_finally_statement(
        indoc! {r##"
        try:
            a = 1 / 0
        except:
            None
        finally:
            a += 50
        "##},
        indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="try"];
            "Location(2:4)" [label="assign"];
            "Location(4:4)" [label="expr"];
            "Location(6:4)" [label="aug_assign"];
            "End(1:0)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)";
            "Location(2:4)" -> "Location(4:4)" [label="except(Location(1:0), 0)"];
            "Location(2:4)" -> "Location(6:4)";
            "Location(4:4)" -> "Location(6:4)";
            "Location(6:4)" -> "End(1:0)";
            "Location(6:4)" -> "Exit" [label="except"];
            "End(1:0)" -> "Exit";
            "End(1:0)" -> "Exit" [label="except"];
        }
        "##},
    )]
    fn test_build_cfg(#[case] source: &str, #[case] expected_dot: &str) {
        let actual_dot = build_dot(source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_simple_loop_statement(#[case] (loop_header, loop_name): (String, String)) {
        let source = formatdoc! {r##"
        {loop_header}:
            a = i
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(1:0)";
            "Location(2:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_with_continue_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i % 2 == 0:
                continue
            a = i
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="continue"];
            "Location(4:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(1:0)" [label="continue"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_with_break_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i % 2 == 0:
                break
            a = 1
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="break"];
            "Location(4:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="break"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_with_return_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i % 2 == 0:
                return a
            a = i
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="return"];
            "Location(4:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="return"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_with_raise_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i % 2 == 0:
                raise Exception()
            a = i
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="raise"];
            "Location(4:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_simple_loop_else_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            a = i
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="assign"];
            "Location(4:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(4:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(1:0)";
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(4:4)" -> "Exit";
            "Location(4:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_else_with_break_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i == 5:
                break
            a = i
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="break"];
            "Location(4:4)" [label="assign"];
            "Location(6:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(6:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="break"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(6:4)" -> "Exit";
            "Location(6:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_else_with_continue_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i == 5:
                continue
            a = i
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="continue"];
            "Location(4:4)" [label="assign"];
            "Location(6:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(6:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(1:0)" [label="continue"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(6:4)" -> "Exit";
            "Location(6:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_else_with_return_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i == 5:
                return
            a = i
        else:
            a = 100
        a = 200
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="return"];
            "Location(4:4)" [label="assign"];
            "Location(6:4)" [label="assign"];
            "Location(7:0)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(6:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="return"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(6:4)" -> "Location(7:0)";
            "Location(6:4)" -> "Exit" [label="except"];
            "Location(7:0)" -> "Exit";
            "Location(7:0)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_else_with_raise_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            if i == 5:
                raise Exception()
            a = i
        else:
            a = 100
        a = 200
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="raise"];
            "Location(4:4)" [label="assign"];
            "Location(6:4)" [label="assign"];
            "Location(7:0)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(6:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(4:4)" -> "Location(1:0)";
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(6:4)" -> "Location(7:0)";
            "Location(6:4)" -> "Exit" [label="except"];
            "Location(7:0)" -> "Exit";
            "Location(7:0)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_double_loop_statements(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            {inner_loop_header}:
                a = i + j
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="{inner_loop_name}"];
            "Location(3:8)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(1:0)" [label="false"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(2:4)";
            "Location(3:8)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_inner_loop_else_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            {inner_loop_header}:
                a = i + j
            else:
                a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="{inner_loop_name}"];
            "Location(3:8)" [label="assign"];
            "Location(5:8)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(5:8)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(2:4)";
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(5:8)" -> "Location(1:0)";
            "Location(5:8)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_inner_loop_else_with_break_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    break
                a = i
            else:
                a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="{inner_loop_name}"];
            "Location(3:8)" [label="if"];
            "Location(4:12)" [label="break"];
            "Location(5:8)" [label="assign"];
            "Location(7:8)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(7:8)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(4:12)" [label="true"];
            "Location(3:8)" -> "Location(5:8)" [label="false"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(4:12)" -> "Location(1:0)" [label="break"];
            "Location(5:8)" -> "Location(2:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:8)" -> "Location(1:0)";
            "Location(7:8)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_inner_loop_else_with_continue_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    continue
                a = i
            else:
                a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="{inner_loop_name}"];
            "Location(3:8)" [label="if"];
            "Location(4:12)" [label="continue"];
            "Location(5:8)" [label="assign"];
            "Location(7:8)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(7:8)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(4:12)" [label="true"];
            "Location(3:8)" -> "Location(5:8)" [label="false"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(4:12)" -> "Location(2:4)" [label="continue"];
            "Location(5:8)" -> "Location(2:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:8)" -> "Location(1:0)";
            "Location(7:8)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_inner_loop_else_with_return_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    return
                a = i
            else:
                a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="{inner_loop_name}"];
            "Location(3:8)" [label="if"];
            "Location(4:12)" [label="return"];
            "Location(5:8)" [label="assign"];
            "Location(7:8)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(7:8)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(4:12)" [label="true"];
            "Location(3:8)" -> "Location(5:8)" [label="false"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(4:12)" -> "Exit" [label="except"];
            "Location(4:12)" -> "Exit" [label="return"];
            "Location(5:8)" -> "Location(2:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:8)" -> "Location(1:0)";
            "Location(7:8)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_inner_loop_else_with_raise_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    raise Exception()
                a = i
            else:
                a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="{inner_loop_name}"];
            "Location(3:8)" [label="if"];
            "Location(4:12)" [label="raise"];
            "Location(5:8)" [label="assign"];
            "Location(7:8)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(7:8)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(4:12)" [label="true"];
            "Location(3:8)" -> "Location(5:8)" [label="false"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(4:12)" -> "Exit" [label="except"];
            "Location(5:8)" -> "Location(2:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:8)" -> "Location(1:0)";
            "Location(7:8)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_outer_loop_else_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="{inner_loop_name}"];
            "Location(3:8)" [label="assign"];
            "Location(5:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(5:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(1:0)" [label="false"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(2:4)";
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(5:4)" -> "Exit";
            "Location(5:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_outer_loop_else_with_break_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            if i == 5:
                break
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="break"];
            "Location(4:4)" [label="{inner_loop_name}"];
            "Location(5:8)" [label="assign"];
            "Location(7:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(7:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="break"];
            "Location(4:4)" -> "Location(1:0)" [label="false"];
            "Location(4:4)" -> "Location(5:8)" [label="true"];
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(5:8)" -> "Location(4:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:4)" -> "Exit";
            "Location(7:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_outer_loop_else_with_continue_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            if i == 5:
                continue
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="continue"];
            "Location(4:4)" [label="{inner_loop_name}"];
            "Location(5:8)" [label="assign"];
            "Location(7:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(7:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(1:0)" [label="continue"];
            "Location(4:4)" -> "Location(1:0)" [label="false"];
            "Location(4:4)" -> "Location(5:8)" [label="true"];
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(5:8)" -> "Location(4:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:4)" -> "Exit";
            "Location(7:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_outer_loop_else_with_return_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            if i == 5:
                return
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="return"];
            "Location(4:4)" [label="{inner_loop_name}"];
            "Location(5:8)" [label="assign"];
            "Location(7:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(7:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="return"];
            "Location(4:4)" -> "Location(1:0)" [label="false"];
            "Location(4:4)" -> "Location(5:8)" [label="true"];
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(5:8)" -> "Location(4:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:4)" -> "Exit";
            "Location(7:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_build_cfg_outer_loop_else_with_raise_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {outer_loop_header}:
            if i == 5:
                raise Exception()
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{outer_loop_name}"];
            "Location(2:4)" [label="if"];
            "Location(3:8)" [label="raise"];
            "Location(4:4)" [label="{inner_loop_name}"];
            "Location(5:8)" [label="assign"];
            "Location(7:4)" [label="assign"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Location(7:4)" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)" [label="true"];
            "Location(2:4)" -> "Location(4:4)" [label="false"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(4:4)" -> "Location(1:0)" [label="false"];
            "Location(4:4)" -> "Location(5:8)" [label="true"];
            "Location(4:4)" -> "Exit" [label="except"];
            "Location(5:8)" -> "Location(4:4)";
            "Location(5:8)" -> "Exit" [label="except"];
            "Location(7:4)" -> "Exit";
            "Location(7:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_break_in_with_statement(#[case] (loop_header, loop_name): (String, String)) {
        let source = formatdoc! {r##"
        {loop_header}:
            with open('file.txt') as f:
                if True:
                    break
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="with"];
            "Location(3:8)" [label="if"];
            "Location(4:12)" [label="break"];
            "Location(5:4)" [label="assign"];
            "End(2:4)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)";
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(4:12)" [label="true"];
            "Location(3:8)" -> "End(2:4)";
            "Location(3:8)" -> "End(2:4)" [label="false"];
            "Location(4:12)" -> "End(2:4)";
            "Location(5:4)" -> "Location(1:0)";
            "Location(5:4)" -> "Exit" [label="except"];
            "End(2:4)" -> "Location(5:4)";
            "End(2:4)" -> "Exit" [label="except"];
            "End(2:4)" -> "Exit" [label="break"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_continue_in_with_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            with open('file.txt') as f:
                if True:
                    continue
            a = 100
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="with"];
            "Location(3:8)" [label="if"];
            "Location(4:12)" [label="continue"];
            "Location(5:4)" [label="assign"];
            "End(2:4)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)";
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Location(4:12)" [label="true"];
            "Location(3:8)" -> "End(2:4)";
            "Location(3:8)" -> "End(2:4)" [label="false"];
            "Location(4:12)" -> "End(2:4)";
            "Location(5:4)" -> "Location(1:0)";
            "Location(5:4)" -> "Exit" [label="except"];
            "End(2:4)" -> "Location(1:0)" [label="continue"];
            "End(2:4)" -> "Location(5:4)";
            "End(2:4)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_loop_with_match_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            match command:
                case "return":
                    return
                case "break":
                    break
                case "continue":
                    continue
                case _:
                    None
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="match"];
            "Location(4:12)" [label="return"];
            "Location(6:12)" [label="break"];
            "Location(8:12)" [label="continue"];
            "Location(10:12)" [label="expr"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(4:12)" [label="match(0)"];
            "Location(2:4)" -> "Location(6:12)" [label="match(1)"];
            "Location(2:4)" -> "Location(8:12)" [label="match(2)"];
            "Location(2:4)" -> "Location(10:12)" [label="match(3)"];
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(4:12)" -> "Exit" [label="except"];
            "Location(4:12)" -> "Exit" [label="return"];
            "Location(6:12)" -> "Exit" [label="break"];
            "Location(8:12)" -> "Location(1:0)" [label="continue"];
            "Location(10:12)" -> "Location(1:0)";
            "Location(10:12)" -> "Exit" [label="except"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_build_cfg_complex_try_except_else_finally_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let source = formatdoc! {r##"
        {loop_header}:
            try:
                if True:
                    return a
                elif False:
                    break
                elif None:
                    continue
                elif b:
                    raise Exception()
                else:
                    a = 1 / 0
            except:
                if True:
                    return a
                elif False:
                    break
                elif None:
                    continue
                elif b:
                    raise Exception()
                else:
                    a = 1 / 0
            else:
                if True:
                    return a
                elif False:
                    break
                elif None:
                    continue
                elif b:
                    raise Exception()
                else:
                    a = 1 / 0
            finally:
                if True:
                    return a
                elif False:
                    break
                elif None:
                    continue
                elif b:
                    raise Exception()
                else:
                    a = 1 / 0
        "##};

        let expected_dot = formatdoc! {r##"
        digraph "CFG" {{
            "Entry";
            "Location(1:0)" [label="{loop_name}"];
            "Location(2:4)" [label="try"];
            "Location(3:8)" [label="if"];
            "Location(4:12)" [label="return"];
            "Location(5:8)" [label="elif"];
            "Location(6:12)" [label="break"];
            "Location(7:8)" [label="elif"];
            "Location(8:12)" [label="continue"];
            "Location(9:8)" [label="elif"];
            "Location(10:12)" [label="raise"];
            "Location(12:12)" [label="assign"];
            "Location(14:8)" [label="if"];
            "Location(15:12)" [label="return"];
            "Location(16:8)" [label="elif"];
            "Location(17:12)" [label="break"];
            "Location(18:8)" [label="elif"];
            "Location(19:12)" [label="continue"];
            "Location(20:8)" [label="elif"];
            "Location(21:12)" [label="raise"];
            "Location(23:12)" [label="assign"];
            "Location(25:8)" [label="if"];
            "Location(26:12)" [label="return"];
            "Location(27:8)" [label="elif"];
            "Location(28:12)" [label="break"];
            "Location(29:8)" [label="elif"];
            "Location(30:12)" [label="continue"];
            "Location(31:8)" [label="elif"];
            "Location(32:12)" [label="raise"];
            "Location(34:12)" [label="assign"];
            "Location(36:8)" [label="if"];
            "Location(37:12)" [label="return"];
            "Location(38:8)" [label="elif"];
            "Location(39:12)" [label="break"];
            "Location(40:8)" [label="elif"];
            "Location(41:12)" [label="continue"];
            "Location(42:8)" [label="elif"];
            "Location(43:12)" [label="raise"];
            "Location(45:12)" [label="assign"];
            "End(2:4)";
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Location(2:4)" [label="true"];
            "Location(1:0)" -> "Exit" [label="false"];
            "Location(1:0)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Location(3:8)";
            "Location(3:8)" -> "Location(4:12)" [label="true"];
            "Location(3:8)" -> "Location(5:8)" [label="false"];
            "Location(3:8)" -> "Location(14:8)" [label="except(Location(2:4), 0)"];
            "Location(4:12)" -> "Location(14:8)" [label="except(Location(2:4), 0)"];
            "Location(4:12)" -> "Location(36:8)";
            "Location(5:8)" -> "Location(6:12)" [label="true"];
            "Location(5:8)" -> "Location(7:8)" [label="false"];
            "Location(5:8)" -> "Location(14:8)" [label="except(Location(2:4), 0)"];
            "Location(6:12)" -> "Location(36:8)";
            "Location(7:8)" -> "Location(8:12)" [label="true"];
            "Location(7:8)" -> "Location(9:8)" [label="false"];
            "Location(7:8)" -> "Location(14:8)" [label="except(Location(2:4), 0)"];
            "Location(8:12)" -> "Location(36:8)";
            "Location(9:8)" -> "Location(10:12)" [label="true"];
            "Location(9:8)" -> "Location(12:12)" [label="false"];
            "Location(9:8)" -> "Location(14:8)" [label="except(Location(2:4), 0)"];
            "Location(10:12)" -> "Location(14:8)" [label="except(Location(2:4), 0)"];
            "Location(12:12)" -> "Location(14:8)" [label="except(Location(2:4), 0)"];
            "Location(12:12)" -> "Location(25:8)";
            "Location(14:8)" -> "Location(15:12)" [label="true"];
            "Location(14:8)" -> "Location(16:8)" [label="false"];
            "Location(14:8)" -> "Location(36:8)";
            "Location(15:12)" -> "Location(36:8)";
            "Location(16:8)" -> "Location(17:12)" [label="true"];
            "Location(16:8)" -> "Location(18:8)" [label="false"];
            "Location(16:8)" -> "Location(36:8)";
            "Location(17:12)" -> "Location(36:8)";
            "Location(18:8)" -> "Location(19:12)" [label="true"];
            "Location(18:8)" -> "Location(20:8)" [label="false"];
            "Location(18:8)" -> "Location(36:8)";
            "Location(19:12)" -> "Location(36:8)";
            "Location(20:8)" -> "Location(21:12)" [label="true"];
            "Location(20:8)" -> "Location(23:12)" [label="false"];
            "Location(20:8)" -> "Location(36:8)";
            "Location(21:12)" -> "Location(36:8)";
            "Location(23:12)" -> "Location(36:8)";
            "Location(25:8)" -> "Location(26:12)" [label="true"];
            "Location(25:8)" -> "Location(27:8)" [label="false"];
            "Location(25:8)" -> "Location(36:8)";
            "Location(26:12)" -> "Location(36:8)";
            "Location(27:8)" -> "Location(28:12)" [label="true"];
            "Location(27:8)" -> "Location(29:8)" [label="false"];
            "Location(27:8)" -> "Location(36:8)";
            "Location(28:12)" -> "Location(36:8)";
            "Location(29:8)" -> "Location(30:12)" [label="true"];
            "Location(29:8)" -> "Location(31:8)" [label="false"];
            "Location(29:8)" -> "Location(36:8)";
            "Location(30:12)" -> "Location(36:8)";
            "Location(31:8)" -> "Location(32:12)" [label="true"];
            "Location(31:8)" -> "Location(34:12)" [label="false"];
            "Location(31:8)" -> "Location(36:8)";
            "Location(32:12)" -> "Location(36:8)";
            "Location(34:12)" -> "Location(36:8)";
            "Location(36:8)" -> "Location(37:12)" [label="true"];
            "Location(36:8)" -> "Location(38:8)" [label="false"];
            "Location(36:8)" -> "Exit" [label="except"];
            "Location(37:12)" -> "Exit" [label="except"];
            "Location(37:12)" -> "Exit" [label="return"];
            "Location(38:8)" -> "Location(39:12)" [label="true"];
            "Location(38:8)" -> "Location(40:8)" [label="false"];
            "Location(38:8)" -> "Exit" [label="except"];
            "Location(39:12)" -> "Exit" [label="break"];
            "Location(40:8)" -> "Location(41:12)" [label="true"];
            "Location(40:8)" -> "Location(42:8)" [label="false"];
            "Location(40:8)" -> "Exit" [label="except"];
            "Location(41:12)" -> "Location(1:0)" [label="continue"];
            "Location(42:8)" -> "Location(43:12)" [label="true"];
            "Location(42:8)" -> "Location(45:12)" [label="false"];
            "Location(42:8)" -> "Exit" [label="except"];
            "Location(43:12)" -> "Exit" [label="except"];
            "Location(45:12)" -> "End(2:4)";
            "Location(45:12)" -> "Exit" [label="except"];
            "End(2:4)" -> "Location(1:0)";
            "End(2:4)" -> "Location(1:0)" [label="continue"];
            "End(2:4)" -> "Exit" [label="except"];
            "End(2:4)" -> "Exit" [label="break"];
            "End(2:4)" -> "Exit" [label="return"];
        }}
        "##};

        let actual_dot = build_dot(&source);

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    fn test_build_cfg_function_statement() {
        let source = indoc! {r##"
        def multiply(a, b):
            return a * b
        "##};

        let expected_dot = indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="function_def"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Exit";
            "Location(1:0)" -> "Exit" [label="except"];
        }
        digraph "1:0" {
            "Entry";
            "Location(2:4)" [label="return"];
            "Exit";
            "Entry" -> "Location(2:4)";
            "Location(2:4)" -> "Exit" [label="except"];
            "Location(2:4)" -> "Exit" [label="return"];
        }
        "##};

        let (line_index, mod_module) = parse_source(&source);

        let cfg = unchecked_build_cfg(&line_index, &mod_module);

        let mut actual_dot = cfg.dot("CFG");
        for (sub_location, sub_cfg) in cfg.cfgs().iter().collect::<BTreeMap<_, _>>() {
            actual_dot.push_str(&sub_cfg.dot(&sub_location.to_string()));
        }

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }

    #[rstest]
    fn test_build_cfg_class_statement() {
        let source = indoc! {r##"
        class Calculator:
            def multiply(a, b):
                return a * b
        "##};

        let expected_dot = indoc! {r##"
        digraph "CFG" {
            "Entry";
            "Location(1:0)" [label="class_def"];
            "Exit";
            "Entry" -> "Location(1:0)";
            "Location(1:0)" -> "Exit";
            "Location(1:0)" -> "Exit" [label="except"];
        }
        digraph "1:0" {
            "Entry";
            "Location(2:4)" [label="function_def"];
            "Exit";
            "Entry" -> "Location(2:4)";
            "Location(2:4)" -> "Exit";
            "Location(2:4)" -> "Exit" [label="except"];
        }
        digraph "2:4" {
            "Entry";
            "Location(3:8)" [label="return"];
            "Exit";
            "Entry" -> "Location(3:8)";
            "Location(3:8)" -> "Exit" [label="except"];
            "Location(3:8)" -> "Exit" [label="return"];
        }
        "##};

        let (line_index, mod_module) = parse_source(&source);

        let cfg = unchecked_build_cfg(&line_index, &mod_module);

        let mut actual_dot = cfg.dot("CFG");
        for (sub_location, sub_cfg) in cfg.cfgs().iter().collect::<BTreeMap<_, _>>() {
            actual_dot.push_str(&sub_cfg.dot(&sub_location.to_string()));
            for (sub_sub_location, sub_sub_cfg) in sub_cfg.cfgs().iter().collect::<BTreeMap<_, _>>()
            {
                actual_dot.push_str(&sub_sub_cfg.dot(&sub_sub_location.to_string()));
            }
        }

        assert_eq!(expected_dot, actual_dot, "{actual_dot}");
    }
}
