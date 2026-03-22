pub use ruff_python_ast as nodes;
use ruff_python_ast::{
    ExceptHandler::ExceptHandler, Mod, Stmt, StmtBreak, StmtClassDef, StmtContinue, StmtFor,
    StmtFunctionDef, StmtIf, StmtMatch, StmtRaise, StmtReturn, StmtTry, StmtWhile, StmtWith,
};
use ruff_python_parser::{Mode, TokenKind, parse};
pub use ruff_source_file::OneIndexed;
use ruff_source_file::{LineIndex, Locator, SourceCode};
use ruff_text_size::{Ranged, TextRange};
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

#[derive(Eq, Hash, PartialEq, Debug, Clone, Copy, PartialOrd, Ord)]
pub enum ProgramPoint {
    Entry,
    Point(usize),
    PointEnd(usize),
    Exit,
}

impl ProgramPoint {
    pub fn try_id(&self) -> Option<usize> {
        match self {
            ProgramPoint::Point(id) => Some(*id),
            _ => None,
        }
    }

    pub fn id(&self) -> usize {
        self.try_id().expect("Only Point variant has an id")
    }
}

#[derive(Debug, Clone)]
pub struct ProgramPointData {
    pub statement: Stmt,
    pub line_number: OneIndexed,
    pub comments: HashMap<OneIndexed, String>,
}

impl ProgramPointData {
    pub fn statement(&self) -> &Stmt {
        &self.statement
    }

    pub fn line_number(&self) -> OneIndexed {
        self.line_number
    }

    pub fn comments(&self) -> &HashMap<OneIndexed, String> {
        &self.comments
    }
}

#[derive(Debug, Clone, Default)]
struct NodeData {
    data: Option<ProgramPointData>,
    successors: HashSet<ProgramPoint>,
    predecessors: HashSet<ProgramPoint>,
}

impl NodeData {
    fn set_statement(&mut self, context: &CfgContext, statement: Stmt) {
        let statement_range = statement.range();
        self.data = Some(ProgramPointData {
            statement,
            line_number: context.get_line_number(&statement_range),
            comments: context.comments_in_range(statement_range),
        });
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Copy)]
pub enum EdgeData {
    Unconditional,
    Conditional(bool),
    Match(usize),
    Exception(usize, usize),
    UnhandledException,
    Break,
    Continue,
    Return,
}

#[derive(Debug, Clone, Default)]
struct ResultPoints {
    previous_points: HashMap<ProgramPoint, EdgeData>,
    return_points: HashSet<ProgramPoint>,
    exception_points: HashSet<ProgramPoint>,
    continue_points: HashSet<ProgramPoint>,
    break_points: HashSet<ProgramPoint>,
}

impl ResultPoints {
    fn merge_into(&mut self, other: ResultPoints) {
        self.previous_points.extend(other.previous_points);
        self.return_points.extend(other.return_points);
        self.exception_points.extend(other.exception_points);
        self.continue_points.extend(other.continue_points);
        self.break_points.extend(other.break_points);
    }

    fn with_previous_point(mut self, point: ProgramPoint, edge_data: EdgeData) -> Self {
        self.previous_points.insert(point, edge_data);
        self
    }

    fn with_return_point(mut self, point: ProgramPoint) -> Self {
        self.return_points.insert(point);
        self
    }

    fn with_exception_point(mut self, point: ProgramPoint) -> Self {
        self.exception_points.insert(point);
        self
    }

    fn with_continue_point(mut self, point: ProgramPoint) -> Self {
        self.continue_points.insert(point);
        self
    }

    fn with_break_point(mut self, point: ProgramPoint) -> Self {
        self.break_points.insert(point);
        self
    }
}

enum StmtLoop {
    For(StmtFor),
    While(StmtWhile),
}

impl StmtLoop {
    fn body_mut(&mut self) -> &mut Vec<Stmt> {
        match self {
            StmtLoop::For(stmt) => &mut stmt.body,
            StmtLoop::While(stmt) => &mut stmt.body,
        }
    }

    fn orelse_mut(&mut self) -> &mut Vec<Stmt> {
        match self {
            StmtLoop::For(stmt) => &mut stmt.orelse,
            StmtLoop::While(stmt) => &mut stmt.orelse,
        }
    }
}

impl Into<Stmt> for StmtLoop {
    fn into(self) -> Stmt {
        match self {
            StmtLoop::For(stmt) => Stmt::For(stmt),
            StmtLoop::While(stmt) => Stmt::While(stmt),
        }
    }
}

struct CfgContext<'text> {
    locator: &'text Locator<'text>,
    source: &'text SourceCode<'text, 'text>,
    comment_ranges: &'text Vec<TextRange>,
    cfgs: HashMap<usize, Cfg>,
    counter: usize,
}

impl<'text> CfgContext<'text> {
    fn new(
        locator: &'text Locator<'text>,
        source: &'text SourceCode<'text, 'text>,
        comment_ranges: &'text Vec<TextRange>,
    ) -> CfgContext<'text> {
        CfgContext {
            locator,
            source,
            comment_ranges,
            cfgs: HashMap::new(),
            counter: 0,
        }
    }

    fn get_line_number<R: Ranged>(&self, statement: &R) -> OneIndexed {
        self.source.line_index(statement.range().start())
    }

    fn next_point(&mut self) -> ProgramPoint {
        let point = ProgramPoint::Point(self.counter);
        self.counter += 1;
        point
    }

    fn comments_in_range(&self, range: TextRange) -> HashMap<OneIndexed, String> {
        self.comment_ranges
            .iter()
            .filter(|comment_range| {
                self.locator
                    .line_range(range.start())
                    .contains_range(**comment_range)
            })
            .map(|comment_range| {
                let line_number = self.source.line_index(comment_range.start());
                let comment_text = self.locator.slice(*comment_range).to_string();
                (line_number, comment_text)
            })
            .collect()
    }
}

#[derive(Debug, Clone, Default)]
pub struct Cfg {
    nodes: HashMap<ProgramPoint, NodeData>,
    edges: HashMap<(ProgramPoint, ProgramPoint), HashSet<EdgeData>>,
    cfgs: Option<HashMap<usize, Cfg>>,
}

impl Cfg {
    pub fn empty() -> Self {
        let mut cfg = Cfg::default();
        cfg.nodes.insert(ProgramPoint::Entry, NodeData::default());
        cfg.nodes.insert(ProgramPoint::Exit, NodeData::default());
        cfg.edges
            .insert((ProgramPoint::Entry, ProgramPoint::Exit), HashSet::new());
        cfg
    }

    pub fn parse(source: &str) -> Option<Self> {
        let parsed_module = parse(source, Mode::Module).ok()?;

        let comment_ranges: Vec<TextRange> = parsed_module
            .tokens()
            .iter()
            .filter(|token_kind| token_kind.kind() == TokenKind::Comment)
            .map(|token| token.range())
            .collect();

        let Mod::Module(module_syntax) = parsed_module.into_syntax() else {
            return None;
        };

        let line_index = LineIndex::from_source_text(source);
        let locator = Locator::with_index(source, line_index.clone());
        let source_code = SourceCode::new(source, &line_index);

        let mut context = CfgContext::new(&locator, &source_code, &comment_ranges);

        let mut cfg = Self::process_cfg(&mut context, module_syntax.body);

        cfg.cfgs = Some(context.cfgs);

        Some(cfg)
    }

    pub fn nodes(&self) -> impl Iterator<Item = &ProgramPoint> {
        self.nodes.keys()
    }

    pub fn node_data(&self, program_point: &ProgramPoint) -> Option<&ProgramPointData> {
        self.nodes.get(program_point)?.data.as_ref()
    }

    pub fn edge_data(&self, from: ProgramPoint, to: ProgramPoint) -> Option<&HashSet<EdgeData>> {
        self.edges.get(&(from, to))
    }

    pub fn sub_cfg_nodes(&self) -> Vec<usize> {
        if let Some(cfgs) = self.cfgs.as_ref() {
            cfgs.keys().cloned().collect()
        } else {
            Vec::new()
        }
    }

    pub fn sub_cfg(&self, cfg_id: usize) -> Option<&Cfg> {
        self.cfgs.as_ref()?.get(&cfg_id)
    }

    pub fn successors(&self, program_point: &ProgramPoint) -> impl Iterator<Item = &ProgramPoint> {
        self.nodes[program_point].successors.iter()
    }

    pub fn predecessors(
        &self,
        program_point: &ProgramPoint,
    ) -> impl Iterator<Item = &ProgramPoint> {
        self.nodes[program_point].predecessors.iter()
    }

    fn map_program_points<I: IntoIterator<Item = ProgramPoint>>(
        program_points: I,
        edge_data: EdgeData,
    ) -> HashMap<ProgramPoint, EdgeData> {
        program_points
            .into_iter()
            .map(|point| (point, edge_data.clone()))
            .collect()
    }

    fn drain_map(
        points: &mut HashSet<ProgramPoint>,
        edge_data: EdgeData,
    ) -> HashMap<ProgramPoint, EdgeData> {
        Self::map_program_points(points.drain(), edge_data)
    }

    fn drain_then_add(
        points: &mut HashMap<ProgramPoint, EdgeData>,
        add: ProgramPoint,
    ) -> HashMap<ProgramPoint, EdgeData> {
        let drained_points = points.drain().collect::<HashMap<_, _>>();
        if !drained_points.is_empty() {
            points.insert(add, EdgeData::Unconditional);
        }
        drained_points
    }

    fn drain_map_unconditional_then_add(
        points: &mut HashSet<ProgramPoint>,
        add: ProgramPoint,
    ) -> HashMap<ProgramPoint, EdgeData> {
        let drained_points = Self::drain_map(points, EdgeData::Unconditional);
        if !drained_points.is_empty() {
            points.insert(add);
        }
        drained_points
    }

    fn insert_edge(&mut self, from: ProgramPoint, to: ProgramPoint, edge_data: EdgeData) {
        self.nodes
            .get_mut(&from)
            .expect(&format!["Node {:?} is missing in cfg", from])
            .successors
            .insert(to);
        self.nodes
            .get_mut(&to)
            .expect(&format!["Node {:?} is missing in cfg", to])
            .predecessors
            .insert(from);
        self.edges
            .entry((from, to))
            .or_insert(HashSet::new())
            .insert(edge_data);
    }

    fn insert_node<I: IntoIterator<Item = (ProgramPoint, EdgeData)>>(
        &mut self,
        previous_points: I,
        current_point: ProgramPoint,
    ) -> &mut NodeData {
        let mut predecessors = HashSet::new();
        for (previous_point, edge_data) in previous_points {
            self.nodes
                .get_mut(&previous_point)
                .expect(&format!["Node {:?} is missing in cfg", previous_point])
                .successors
                .insert(current_point);
            predecessors.insert(previous_point);
            self.edges
                .entry((previous_point, current_point))
                .or_insert(HashSet::new())
                .insert(edge_data);
        }

        let Entry::Vacant(entry) = self.nodes.entry(current_point) else {
            panic!("Node {:?} already exists", current_point);
        };

        entry.insert(NodeData {
            data: None,
            successors: HashSet::new(),
            predecessors,
        })
    }

    fn set_statement(
        &mut self,
        context: &CfgContext,
        program_point: ProgramPoint,
        statement: Stmt,
    ) {
        let Entry::Occupied(mut entry) = self.nodes.entry(program_point) else {
            panic!("Node {:?} does not exist", program_point);
        };
        entry.get_mut().set_statement(context, statement);
    }

    fn process_cfg(context: &mut CfgContext, statements: Vec<Stmt>) -> Cfg {
        let mut cfg = Cfg::default();
        cfg.nodes.insert(ProgramPoint::Entry, NodeData::default());

        let result_points = cfg.process_statements(
            context,
            HashMap::from_iter([(ProgramPoint::Entry, EdgeData::Unconditional)]),
            statements,
        );

        cfg.insert_node(
            [
                Self::map_program_points(
                    result_points.exception_points,
                    EdgeData::UnhandledException,
                ),
                Self::map_program_points(result_points.return_points, EdgeData::Return),
                result_points.previous_points,
            ]
            .into_iter()
            .flatten(),
            ProgramPoint::Exit,
        );

        assert!(
            result_points.break_points.is_empty(),
            "Break points should be handled within loops."
        );
        assert!(
            result_points.continue_points.is_empty(),
            "Continue points should be handled within loops."
        );

        cfg.check_invariant();

        cfg
    }

    fn check_invariant(&self) {
        self.nodes.contains_key(&ProgramPoint::Entry);
        self.nodes.contains_key(&ProgramPoint::Exit);

        for (point, data) in &self.nodes {
            match *point {
                ProgramPoint::Entry | ProgramPoint::Exit => {
                    assert!(
                        data.data.is_none(),
                        "Entry/Exit points should not have data"
                    );
                }
                ProgramPoint::PointEnd(id) => {
                    assert!(
                        data.data.is_none(),
                        "TryEnd({}) point should not have data",
                        id
                    );
                    assert!(self.nodes.contains_key(&ProgramPoint::Point(id)));
                }
                _ => {
                    assert!(
                        data.data.is_some(),
                        "Non-entry/exit points should have data"
                    );
                }
            }
        }

        for ((from, to), edge_data_set) in &self.edges {
            assert!(
                self.nodes[from].successors.contains(to),
                "Successor {:?} missing in {:?}",
                to,
                from,
            );
            assert!(
                self.nodes[to].predecessors.contains(from),
                "Predecessor {:?} missing in {:?}",
                from,
                to
            );

            for edge_data in edge_data_set {
                match edge_data {
                    EdgeData::Conditional(_) => {
                        assert!(
                            matches!(
                                self.nodes[from].data,
                                Some(ProgramPointData {
                                    statement: Stmt::If(_),
                                    ..
                                })
                            ) || matches!(
                                self.nodes[from].data,
                                Some(ProgramPointData {
                                    statement: Stmt::For(_),
                                    ..
                                })
                            ) || matches!(
                                self.nodes[from].data,
                                Some(ProgramPointData {
                                    statement: Stmt::While(_),
                                    ..
                                })
                            ),
                            "Conditional edge from {:?} to {:?} must originate from an If statement",
                            from,
                            to
                        );
                    }
                    EdgeData::Match(_) => {
                        assert!(
                            matches!(
                                self.nodes[from].data,
                                Some(ProgramPointData {
                                    statement: Stmt::Match(_),
                                    ..
                                })
                            ),
                            "Match edge from {:?} to {:?} must originate from an Match statement",
                            from,
                            to
                        );
                    }
                    EdgeData::Exception(point, _) => {
                        assert!(
                            self.nodes.contains_key(&ProgramPoint::Point(*point)),
                            "Exception edge from {:?} to {:?} references non-existent point {:?}",
                            from,
                            to,
                            point
                        );
                        assert!(
                            matches!(
                                self.nodes[&ProgramPoint::Point(*point)].data,
                                Some(ProgramPointData {
                                    statement: Stmt::Try(_),
                                    ..
                                })
                            ),
                            "Match edge from {:?} to {:?} must originate from an Try statement",
                            from,
                            to
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    fn process_statements(
        &mut self,
        context: &mut CfgContext,
        mut previous_points: HashMap<ProgramPoint, EdgeData>,
        statements: Vec<Stmt>,
    ) -> ResultPoints {
        let mut result_points = ResultPoints::default();

        for statement in statements {
            let current_point = context.next_point();
            let mut current_result_points = match statement {
                Stmt::FunctionDef(stmt_function_def) => self.process_function_statement(
                    context,
                    previous_points,
                    current_point,
                    stmt_function_def,
                ),
                Stmt::ClassDef(stmt_class_def) => self.process_class_statement(
                    context,
                    previous_points,
                    current_point,
                    stmt_class_def,
                ),
                Stmt::Return(stmt_return) => self.process_return_statement(
                    context,
                    previous_points,
                    current_point,
                    stmt_return,
                ),
                Stmt::For(stmt_for) => self.process_loop_statement(
                    context,
                    previous_points,
                    current_point,
                    StmtLoop::For(stmt_for),
                ),
                Stmt::While(stmt_while) => self.process_loop_statement(
                    context,
                    previous_points,
                    current_point,
                    StmtLoop::While(stmt_while),
                ),
                Stmt::If(stmt_if) => {
                    self.process_if_statement(context, previous_points, current_point, stmt_if)
                }
                Stmt::With(stmt_with) => {
                    self.process_with_statement(context, previous_points, current_point, stmt_with)
                }
                Stmt::Match(stmt_match) => self.process_match_statement(
                    context,
                    previous_points,
                    current_point,
                    stmt_match,
                ),
                Stmt::Raise(stmt_raise) => self.process_raise_statement(
                    context,
                    previous_points,
                    current_point,
                    stmt_raise,
                ),
                Stmt::Try(stmt_try) => {
                    self.process_try_statement(context, previous_points, current_point, stmt_try)
                }
                Stmt::Break(stmt_break) => self.process_break_statement(
                    context,
                    previous_points,
                    current_point,
                    stmt_break,
                ),
                Stmt::Continue(stmt_continue) => self.process_continue_statement(
                    context,
                    previous_points,
                    current_point,
                    stmt_continue,
                ),
                _ => self.process_generic_statement(
                    context,
                    previous_points,
                    current_point,
                    statement,
                ),
            };
            previous_points = current_result_points.previous_points.drain().collect();
            result_points.merge_into(current_result_points);
        }

        result_points.previous_points.extend(previous_points);

        result_points
    }

    fn process_generic_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        stmt: Stmt,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point)
            .set_statement(context, stmt);

        ResultPoints::default()
            .with_previous_point(current_point, EdgeData::Unconditional)
            .with_exception_point(current_point)
    }

    fn process_function_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        mut stmt_function_def: StmtFunctionDef,
    ) -> ResultPoints {
        let function_cfg = Self::process_cfg(context, stmt_function_def.body.drain(..).collect());

        context.cfgs.insert(current_point.id(), function_cfg);

        self.process_generic_statement(
            context,
            previous_points,
            current_point,
            Stmt::FunctionDef(stmt_function_def),
        )
    }

    fn process_class_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        mut stmt_class_def: StmtClassDef,
    ) -> ResultPoints {
        let class_cfg = Self::process_cfg(context, stmt_class_def.body.drain(..).collect());

        context.cfgs.insert(current_point.id(), class_cfg);

        self.process_generic_statement(
            context,
            previous_points,
            current_point,
            Stmt::ClassDef(stmt_class_def),
        )
    }

    fn process_return_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        stmt_return: StmtReturn,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point)
            .set_statement(context, Stmt::Return(stmt_return));

        ResultPoints::default()
            .with_return_point(current_point)
            .with_exception_point(current_point)
    }

    fn process_if_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        mut stmt_if: StmtIf,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point);

        let mut result_points = self.process_statements(
            context,
            HashMap::from_iter([(current_point, EdgeData::Conditional(true))]),
            stmt_if.body.drain(..).collect(),
        );

        let mut elif_else_stmts_iterator = stmt_if
            .elif_else_clauses
            .drain(..)
            .collect::<Vec<_>>()
            .into_iter();

        if let Some(mut elif_else) = elif_else_stmts_iterator.next() {
            let elif_else_clauses = elif_else_stmts_iterator.collect::<Vec<_>>();
            if let Some(test) = elif_else.test {
                let elif = StmtIf {
                    test: Box::new(test),
                    body: elif_else.body,
                    elif_else_clauses,
                    range: elif_else.range,
                };
                let elif_point = context.next_point();
                result_points.merge_into(self.process_if_statement(
                    context,
                    HashMap::from_iter([(current_point, EdgeData::Conditional(false))]),
                    elif_point,
                    elif,
                ));
            } else {
                assert!(
                    elif_else_clauses.is_empty(),
                    "Else clause cannot have further elif/else clauses."
                );
                result_points.merge_into(self.process_statements(
                    context,
                    HashMap::from_iter([(current_point, EdgeData::Conditional(false))]),
                    elif_else.body.drain(..).collect(),
                ));
                stmt_if.elif_else_clauses = vec![elif_else];
            }
        } else {
            result_points
                .previous_points
                .insert(current_point, EdgeData::Conditional(false));
        }

        self.set_statement(context, current_point, Stmt::If(stmt_if));

        result_points.with_exception_point(current_point)
    }

    fn process_loop_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        mut stmt_loop: StmtLoop,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point);

        let mut result_points = self.process_statements(
            context,
            HashMap::from_iter([(current_point, EdgeData::Conditional(true))]),
            stmt_loop.body_mut().drain(..).collect(),
        );

        for continue_point in result_points.continue_points.drain() {
            self.insert_edge(continue_point, current_point, EdgeData::Continue);
        }
        for (previous_point, edge_data) in result_points.previous_points.drain() {
            self.insert_edge(previous_point, current_point, edge_data);
        }

        result_points.previous_points.extend(Self::drain_map(
            &mut result_points.break_points,
            EdgeData::Break,
        ));

        result_points.merge_into(self.process_statements(
            context,
            HashMap::from_iter([(current_point, EdgeData::Conditional(false))]),
            stmt_loop.orelse_mut().drain(..).collect(),
        ));

        self.set_statement(context, current_point, stmt_loop.into());

        result_points.with_exception_point(current_point)
    }

    fn process_with_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        mut stmt_with: StmtWith,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point);

        let mut result_points = self.process_statements(
            context,
            HashMap::from_iter([(current_point, EdgeData::Unconditional)]),
            stmt_with.body.drain(..).collect(),
        );

        let point_end = ProgramPoint::PointEnd(current_point.id());

        self.insert_node(
            [
                Self::drain_then_add(&mut result_points.previous_points, point_end),
                Self::drain_map_unconditional_then_add(&mut result_points.return_points, point_end),
                Self::drain_map(&mut result_points.exception_points, EdgeData::Unconditional), // Exception can always propagate here
                Self::drain_map_unconditional_then_add(
                    &mut result_points.continue_points,
                    point_end,
                ),
                Self::drain_map_unconditional_then_add(&mut result_points.break_points, point_end),
            ]
            .into_iter()
            .flatten(),
            point_end,
        );

        self.set_statement(context, current_point, Stmt::With(stmt_with));

        result_points
            .with_exception_point(current_point)
            .with_exception_point(point_end)
    }

    fn process_match_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        mut stmt_match: StmtMatch,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point);

        let mut result_points = ResultPoints::default();

        for (index, case) in stmt_match.cases.iter_mut().enumerate() {
            result_points.merge_into(self.process_statements(
                context,
                HashMap::from_iter([(current_point, EdgeData::Match(index))]),
                case.body.drain(..).collect(),
            ));
        }

        self.set_statement(context, current_point, Stmt::Match(stmt_match));

        result_points.with_exception_point(current_point)
    }

    fn process_raise_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        stmt_raise: StmtRaise,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point)
            .set_statement(context, Stmt::Raise(stmt_raise));

        ResultPoints::default().with_exception_point(current_point)
    }

    fn process_try_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        mut stmt_try: StmtTry,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point);

        let mut result_points = self.process_statements(
            context,
            HashMap::from_iter([(current_point, EdgeData::Unconditional)]),
            stmt_try.body.drain(..).collect(),
        );
        let body_previous_points = result_points
            .previous_points
            .drain()
            .collect::<HashMap<_, _>>();
        let body_exception_points = result_points
            .exception_points
            .drain()
            .collect::<HashSet<_>>();
        result_points.merge_into(self.process_statements(
            context,
            body_previous_points,
            stmt_try.orelse.drain(..).collect(),
        ));

        for (index, ExceptHandler(handler)) in stmt_try.handlers.iter_mut().enumerate() {
            let handler_previous_points = body_exception_points
                .iter()
                .map(|exception_point| {
                    (
                        *exception_point,
                        EdgeData::Exception(current_point.id(), index),
                    )
                })
                .collect::<HashMap<_, _>>();
            result_points.merge_into(self.process_statements(
                context,
                handler_previous_points,
                handler.body.drain(..).collect(),
            ));
        }

        let point_end = ProgramPoint::PointEnd(current_point.id());

        let mut finally_result_points = self.process_statements(
            context,
            [
                Self::drain_then_add(&mut result_points.previous_points, point_end),
                Self::drain_map_unconditional_then_add(&mut result_points.return_points, point_end),
                Self::drain_map_unconditional_then_add(
                    &mut result_points.exception_points,
                    point_end,
                ),
                Self::drain_map_unconditional_then_add(
                    &mut result_points.continue_points,
                    point_end,
                ),
                Self::drain_map_unconditional_then_add(&mut result_points.break_points, point_end),
            ]
            .into_iter()
            .flatten()
            .collect(),
            stmt_try.finalbody.drain(..).collect::<Vec<_>>(),
        );

        self.insert_node(finally_result_points.previous_points.drain(), point_end);

        result_points.merge_into(finally_result_points);

        self.set_statement(context, current_point, Stmt::Try(stmt_try));

        result_points
    }

    fn process_break_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        stmt_break: StmtBreak,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point)
            .set_statement(context, Stmt::Break(stmt_break));

        ResultPoints::default().with_break_point(current_point)
    }

    fn process_continue_statement(
        &mut self,
        context: &mut CfgContext,
        previous_points: HashMap<ProgramPoint, EdgeData>,
        current_point: ProgramPoint,
        stmt_continue: StmtContinue,
    ) -> ResultPoints {
        self.insert_node(previous_points, current_point)
            .set_statement(context, Stmt::Continue(stmt_continue));

        ResultPoints::default().with_continue_point(current_point)
    }

    fn program_point_label(point: &ProgramPoint) -> String {
        match point {
            ProgramPoint::Entry => "\"Entry\"".to_string(),
            ProgramPoint::Exit => "\"Exit\"".to_string(),
            ProgramPoint::PointEnd(id) => format!("\"PointEnd({})\"", id),
            ProgramPoint::Point(id) => format!("\"Point({})\"", id),
        }
    }

    pub fn dot(&self, graph_name: &str) -> String {
        let mut dot_representation = String::from(format!["digraph \"{}\" {{\n", graph_name]);

        let mut nodes = self.nodes.iter().collect::<Vec<_>>();
        let mut edges = self.edges.iter().collect::<Vec<_>>();
        let mut cfgs: Vec<(usize, &Cfg)> = Vec::new();
        if let Some(cfgs_map) = &self.cfgs {
            for (point, cfg) in cfgs_map {
                cfgs.push((*point, cfg));
            }
        }

        nodes.sort_by_key(|(program_point, _)| **program_point);
        edges.sort_by_key(|((from, to), _)| (*from, *to));
        cfgs.sort_by_key(|(program_point, _)| *program_point);

        for (point, node_data) in nodes {
            let line = if let Some(point_data) = &node_data.data {
                let label = match point_data.statement {
                    Stmt::FunctionDef(_) => "function_def",
                    Stmt::ClassDef(_) => "class_def",
                    Stmt::Return(_) => "return",
                    Stmt::Delete(_) => "delete",
                    Stmt::Assign(_) => "assign",
                    Stmt::AugAssign(_) => "aug_assign",
                    Stmt::AnnAssign(_) => "ann_assign",
                    Stmt::TypeAlias(_) => "type_alias",
                    Stmt::For(_) => "for",
                    Stmt::While(_) => "while",
                    Stmt::If(_) => "if",
                    Stmt::With(_) => "with",
                    Stmt::Match(_) => "match",
                    Stmt::Raise(_) => "raise",
                    Stmt::Try(_) => "try",
                    Stmt::Assert(_) => "assert",
                    Stmt::Import(_) => "import",
                    Stmt::ImportFrom(_) => "import_from",
                    Stmt::Global(_) => "global",
                    Stmt::Nonlocal(_) => "nonlocal",
                    Stmt::Expr(_) => "expr",
                    Stmt::Pass(_) => "pass",
                    Stmt::Break(_) => "break",
                    Stmt::Continue(_) => "continue",
                    Stmt::IpyEscapeCommand(_) => "ipy_escape_command",
                };
                format!(
                    "    {} [label=\"{}\"];\n",
                    Self::program_point_label(point),
                    label,
                )
            } else if let ProgramPoint::PointEnd(_) = point {
                format!("    {} [label=\"\"];\n", Self::program_point_label(point))
            } else {
                format!("    {};\n", Self::program_point_label(point))
            };
            dot_representation.push_str(&line);
        }

        for ((from, to), edge_data_set) in edges {
            let mut edge_data_vec = edge_data_set.iter().collect::<Vec<_>>();
            edge_data_vec.sort();
            for edge_data in edge_data_vec {
                let line = match edge_data {
                    EdgeData::Unconditional => format!(
                        "    {} -> {};\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to)
                    ),
                    EdgeData::Conditional(cond) => format!(
                        "    {} -> {} [label=\"{}\"];\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to),
                        cond
                    ),
                    EdgeData::Match(index) => format!(
                        "    {} -> {} [label=\"match({})\"];\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to),
                        index
                    ),
                    EdgeData::Exception(id, index) => format!(
                        "    {} -> {} [label=\"except({}, {})\"];\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to),
                        id,
                        index
                    ),
                    EdgeData::UnhandledException => format!(
                        "    {} -> {} [label=\"except\"];\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to)
                    ),
                    EdgeData::Break => format!(
                        "    {} -> {} [label=\"break\"];\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to)
                    ),
                    EdgeData::Continue => format!(
                        "    {} -> {} [label=\"continue\"];\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to)
                    ),
                    EdgeData::Return => format!(
                        "    {} -> {} [label=\"return\"];\n",
                        Self::program_point_label(from),
                        Self::program_point_label(to)
                    ),
                };
                dot_representation.push_str(&line);
            }
        }

        dot_representation.push_str("}\n");

        for (inner_point, inner_cfg) in cfgs {
            let inner_dot = inner_cfg.dot(&format!("{}({})", graph_name, inner_point));
            dot_representation.push_str(&inner_dot);
        }

        dot_representation
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::{fixture, rstest};

    fn build_dot_cfg_from_source(source: &str) -> String {
        Cfg::parse(source)
            .expect("Should build CFG")
            .dot("CFG")
            .trim()
            .to_owned()
    }

    fn source_code(text: &str) -> String {
        text.trim()
            .lines()
            .map(|line| line.strip_prefix("        ").unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n")
            .to_owned()
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
    fn test_process_comments() {
        let text = source_code(
            r#"
        a = 5
        b = 10 # This is a comment
        c = 15
        "#,
        );

        let cfg = Cfg::parse(&text).expect("Should build CFG");

        let program_point_0 = cfg.nodes[&ProgramPoint::Point(0)]
            .data
            .as_ref()
            .expect("Program point 0 should have data");
        let program_point_1 = cfg.nodes[&ProgramPoint::Point(1)]
            .data
            .as_ref()
            .expect("Program point 1 should have data");
        let program_point_2 = cfg.nodes[&ProgramPoint::Point(2)]
            .data
            .as_ref()
            .expect("Program point 2 should have data");

        assert!(
            program_point_0.comments.is_empty(),
            "Program point 0 should have no comments"
        );
        assert_eq!(
            program_point_1.comments,
            HashMap::from_iter(vec![(
                program_point_1.line_number,
                String::from("# This is a comment")
            )]),
            "Program point 1 should have the correct comment"
        );
        assert!(
            program_point_2.comments.is_empty(),
            "Program point 2 should have no comments"
        );
    }

    #[rstest]
    fn test_process_generic_statement() {
        let text = source_code(
            r#"
        a = 5
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Exit";
            "Point(0)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_multiple_generic_statements() {
        let text = source_code(
            r#"
        a = 5
        b = 10
        c = a + b
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="assign"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit";
            "Point(2)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_if_else_statement() {
        let text = source_code(
            r#"
        if True:
            a = 5
        else:
            a = 10
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="if"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(2)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Exit";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit";
            "Point(2)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_if_without_else_statement() {
        let text = source_code(
            r#"
        if True:
            a = 5
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="if"];
            "Point(1)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Exit";
            "Point(1)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_if_elif_else_statement() {
        let text = source_code(
            r#"
        if True:
            a = 5
        elif False:
            a = 10
        else:
            a = 15
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="if"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="if"];
            "Point(3)" [label="assign"];
            "Point(4)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(2)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Exit";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "Point(4)" [label="false"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit";
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Exit";
            "Point(4)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_if_elif_without_else_statement() {
        let text = source_code(
            r#"
        if True:
            a = 5
        elif False:
            a = 10
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="if"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="if"];
            "Point(3)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(2)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Exit";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "Exit" [label="false"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit";
            "Point(3)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_simple_loop_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            a = i
        "#
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(0)";
            "Point(1)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_with_continue_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i % 2 == 0:
                continue
            a = i
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="continue"];
            "Point(3)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(0)" [label="continue"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_with_break_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i % 2 == 0:
                a = 1
            else:
                break
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="assign"];
            "Point(3)" [label="break"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(0)";
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit" [label="break"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_with_return_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i % 2 == 0:
                return a
            a = i
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="return"];
            "Point(3)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="return"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_with_raise_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i % 2 == 0:
                raise Exception()
            a = i
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="raise"];
            "Point(3)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_simple_loop_else_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            a = i
        else:
            a = 100
        "#
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(2)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(0)";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit";
            "Point(2)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_else_with_break_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i == 5:
                break
            a = i
        else:
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="break"];
            "Point(3)" [label="assign"];
            "Point(4)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(4)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="break"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Exit";
            "Point(4)" -> "Exit" [label="except"];
        }}
        "#
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_else_with_continue_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i == 5:
                continue
            a = i
        else:
            a = 100
        "#
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="continue"];
            "Point(3)" [label="assign"];
            "Point(4)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(4)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(0)" [label="continue"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Exit";
            "Point(4)" -> "Exit" [label="except"];
        }}
        "#
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_else_with_return_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i == 5:
                return
            a = i
        else:
            a = 100
        a = 200
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="return"];
            "Point(3)" [label="assign"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(4)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="return"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Point(5)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Exit";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_else_with_raise_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            if i == 5:
                raise Exception()
            a = i
        else:
            a = 100
        a = 200
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="raise"];
            "Point(3)" [label="assign"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(4)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Point(5)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Exit";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_double_loop_statements(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            {inner_loop_header}:
                a = i + j
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="{inner_loop_name}"];
            "Point(2)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(0)" [label="false"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(1)";
            "Point(2)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_inner_loop_else_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            {inner_loop_header}:
                a = i + j
            else:
                a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="{inner_loop_name}"];
            "Point(2)" [label="assign"];
            "Point(3)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(1)";
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Point(0)";
            "Point(3)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_inner_loop_else_with_break_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    break
                a = i
            else:
                a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="{inner_loop_name}"];
            "Point(2)" [label="if"];
            "Point(3)" [label="break"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(5)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "Point(4)" [label="false"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Point(0)" [label="break"];
            "Point(4)" -> "Point(1)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Point(0)";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_inner_loop_else_with_continue_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    continue
                a = i
            else:
                a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="{inner_loop_name}"];
            "Point(2)" [label="if"];
            "Point(3)" [label="continue"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(5)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "Point(4)" [label="false"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Point(1)" [label="continue"];
            "Point(4)" -> "Point(1)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Point(0)";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_inner_loop_else_with_return_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
       {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    return
                a = i
            else:
                a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="{inner_loop_name}"];
            "Point(2)" [label="if"];
            "Point(3)" [label="return"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(5)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "Point(4)" [label="false"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit" [label="return"];
            "Point(4)" -> "Point(1)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Point(0)";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_inner_loop_else_with_raise_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
       {outer_loop_header}:
            {inner_loop_header}:
                if j == 5:
                    raise Exception()
                a = i
            else:
                a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="{inner_loop_name}"];
            "Point(2)" [label="if"];
            "Point(3)" [label="raise"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(5)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "Point(4)" [label="false"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Point(1)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Point(0)";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_outer_loop_else_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="{inner_loop_name}"];
            "Point(2)" [label="assign"];
            "Point(3)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(3)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(0)" [label="false"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(1)";
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit";
            "Point(3)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_outer_loop_else_with_break_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            if i == 5:
                break
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="break"];
            "Point(3)" [label="{inner_loop_name}"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(5)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="break"];
            "Point(3)" -> "Point(0)" [label="false"];
            "Point(3)" -> "Point(4)" [label="true"];
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Point(3)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Exit";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_outer_loop_else_with_continue_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            if i == 5:
                continue
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="continue"];
            "Point(3)" [label="{inner_loop_name}"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(5)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(0)" [label="continue"];
            "Point(3)" -> "Point(0)" [label="false"];
            "Point(3)" -> "Point(4)" [label="true"];
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Point(3)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Exit";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_outer_loop_else_with_return_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            if i == 5:
                return
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="return"];
            "Point(3)" [label="{inner_loop_name}"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(5)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="return"];
            "Point(3)" -> "Point(0)" [label="false"];
            "Point(3)" -> "Point(4)" [label="true"];
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Point(3)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Exit";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loops(while_i_fixture(), while_j_fixture())]
    #[case::for_loops(for_i_fixture(), for_j_fixture())]
    #[case::for_while(while_i_fixture(), for_j_fixture())]
    #[case::while_for(for_i_fixture(), while_j_fixture())]
    fn test_process_outer_loop_else_with_raise_statement(
        #[case] (outer_loop_header, outer_loop_name): (String, String),
        #[case] (inner_loop_header, inner_loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
        {outer_loop_header}:
            if i == 5:
                raise Exception()
            {inner_loop_header}:
                a = i + j
        else:
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{outer_loop_name}"];
            "Point(1)" [label="if"];
            "Point(2)" [label="raise"];
            "Point(3)" [label="{inner_loop_name}"];
            "Point(4)" [label="assign"];
            "Point(5)" [label="assign"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Point(5)" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "Point(3)" [label="false"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Point(0)" [label="false"];
            "Point(3)" -> "Point(4)" [label="true"];
            "Point(3)" -> "Exit" [label="except"];
            "Point(4)" -> "Point(3)";
            "Point(4)" -> "Exit" [label="except"];
            "Point(5)" -> "Exit";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_with_statement() {
        let text = source_code(
            r#"
        with open('file.txt') as f:
            a = f.read()
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="with"];
            "Point(1)" [label="assign"];
            "PointEnd(0)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "PointEnd(0)";
            "PointEnd(0)" -> "Exit";
            "PointEnd(0)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_break_in_with_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            with open('file.txt') as f:
                if True:
                    break
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="with"];
            "Point(2)" [label="if"];
            "Point(3)" [label="break"];
            "Point(4)" [label="assign"];
            "PointEnd(1)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "PointEnd(1)";
            "Point(2)" -> "PointEnd(1)" [label="false"];
            "Point(3)" -> "PointEnd(1)";
            "Point(4)" -> "Point(0)";
            "Point(4)" -> "Exit" [label="except"];
            "PointEnd(1)" -> "Point(4)";
            "PointEnd(1)" -> "Exit" [label="except"];
            "PointEnd(1)" -> "Exit" [label="break"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_continue_in_with_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
        {loop_header}:
            with open('file.txt') as f:
                if True:
                    continue
            a = 100
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="with"];
            "Point(2)" [label="if"];
            "Point(3)" [label="continue"];
            "Point(4)" [label="assign"];
            "PointEnd(1)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "PointEnd(1)";
            "Point(2)" -> "PointEnd(1)" [label="false"];
            "Point(3)" -> "PointEnd(1)";
            "Point(4)" -> "Point(0)";
            "Point(4)" -> "Exit" [label="except"];
            "PointEnd(1)" -> "Point(0)" [label="continue"];
            "PointEnd(1)" -> "Point(4)";
            "PointEnd(1)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_return_in_with_statement() {
        let text = source_code(
            r#"
        with open('file.txt') as f:
            if True:
                return f.read()
        a = 100
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="with"];
            "Point(1)" [label="if"];
            "Point(2)" [label="return"];
            "Point(3)" [label="assign"];
            "PointEnd(0)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "PointEnd(0)";
            "Point(1)" -> "PointEnd(0)" [label="false"];
            "Point(2)" -> "PointEnd(0)";
            "Point(3)" -> "Exit";
            "Point(3)" -> "Exit" [label="except"];
            "PointEnd(0)" -> "Point(3)";
            "PointEnd(0)" -> "Exit" [label="except"];
            "PointEnd(0)" -> "Exit" [label="return"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_raise_in_with_statement() {
        let text = source_code(
            r#"
        with open('file.txt') as f:
            if True:
                raise Exception()
        a = 100
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="with"];
            "Point(1)" [label="if"];
            "Point(2)" [label="raise"];
            "Point(3)" [label="assign"];
            "PointEnd(0)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="true"];
            "Point(1)" -> "PointEnd(0)";
            "Point(1)" -> "PointEnd(0)" [label="false"];
            "Point(2)" -> "PointEnd(0)";
            "Point(3)" -> "Exit";
            "Point(3)" -> "Exit" [label="except"];
            "PointEnd(0)" -> "Point(3)";
            "PointEnd(0)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_match_statement() {
        let text = source_code(
            r#"
        match command:
            case "start":
                a = 0
            case "stop":
                a += 1
            case _:
                None
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="match"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="aug_assign"];
            "Point(3)" [label="expr"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="match(0)"];
            "Point(0)" -> "Point(2)" [label="match(1)"];
            "Point(0)" -> "Point(3)" [label="match(2)"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Exit";
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit";
            "Point(2)" -> "Exit" [label="except"];
            "Point(3)" -> "Exit";
            "Point(3)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_loop_with_match_statement(#[case] (loop_header, loop_name): (String, String)) {
        let text = source_code(&format!(
            r#"
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
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="match"];
            "Point(2)" [label="return"];
            "Point(3)" [label="break"];
            "Point(4)" [label="continue"];
            "Point(5)" [label="expr"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)" [label="match(0)"];
            "Point(1)" -> "Point(3)" [label="match(1)"];
            "Point(1)" -> "Point(4)" [label="match(2)"];
            "Point(1)" -> "Point(5)" [label="match(3)"];
            "Point(1)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="return"];
            "Point(3)" -> "Exit" [label="break"];
            "Point(4)" -> "Point(0)" [label="continue"];
            "Point(5)" -> "Point(0)";
            "Point(5)" -> "Exit" [label="except"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_try_single_except_statement() {
        let text = source_code(
            r#"
        try:
            a = 1 / 0
        except:
            None
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="try"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="expr"];
            "PointEnd(0)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(1)" -> "Point(2)" [label="except(0, 0)"];
            "Point(1)" -> "PointEnd(0)";
            "Point(2)" -> "PointEnd(0)";
            "PointEnd(0)" -> "Exit";
            "PointEnd(0)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_try_multiple_except_statement() {
        let text = source_code(
            r#"
        try:
            a = 1 / 0
        except ZeroDivisionError:
            a += 50
        except:
            100
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="try"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="aug_assign"];
            "Point(3)" [label="expr"];
            "PointEnd(0)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(1)" -> "Point(2)" [label="except(0, 0)"];
            "Point(1)" -> "Point(3)" [label="except(0, 1)"];
            "Point(1)" -> "PointEnd(0)";
            "Point(2)" -> "PointEnd(0)";
            "Point(3)" -> "PointEnd(0)";
            "PointEnd(0)" -> "Exit";
            "PointEnd(0)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_try_except_else_statement() {
        let text = source_code(
            r#"
        try:
            a = 1 / 0
        except:
            None
        else:
            a += 100
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="try"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="aug_assign"];
            "Point(3)" [label="expr"];
            "PointEnd(0)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(1)" -> "Point(2)";
            "Point(1)" -> "Point(3)" [label="except(0, 0)"];
            "Point(2)" -> "PointEnd(0)";
            "Point(3)" -> "PointEnd(0)";
            "PointEnd(0)" -> "Exit";
            "PointEnd(0)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_simple_try_except_finally_statement() {
        let text = source_code(
            r#"
        try:
            a = 1 / 0
        except:
            None
        finally:
            a += 50
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="try"];
            "Point(1)" [label="assign"];
            "Point(2)" [label="expr"];
            "Point(3)" [label="aug_assign"];
            "PointEnd(0)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)";
            "Point(1)" -> "Point(2)" [label="except(0, 0)"];
            "Point(1)" -> "Point(3)";
            "Point(2)" -> "Point(3)";
            "Point(3)" -> "PointEnd(0)";
            "Point(3)" -> "Exit" [label="except"];
            "PointEnd(0)" -> "Exit";
            "PointEnd(0)" -> "Exit" [label="except"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    #[case::while_loop(while_i_fixture())]
    #[case::for_loop(for_i_fixture())]
    fn test_process_simple_complex_try_except_else_finally_statement(
        #[case] (loop_header, loop_name): (String, String),
    ) {
        let text = source_code(&format!(
            r#"
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
        "#,
        ));

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(&format!(
            r#"
        digraph "CFG" {{
            "Entry";
            "Point(0)" [label="{loop_name}"];
            "Point(1)" [label="try"];
            "Point(2)" [label="if"];
            "Point(3)" [label="return"];
            "Point(4)" [label="if"];
            "Point(5)" [label="break"];
            "Point(6)" [label="if"];
            "Point(7)" [label="continue"];
            "Point(8)" [label="if"];
            "Point(9)" [label="raise"];
            "Point(10)" [label="assign"];
            "Point(11)" [label="if"];
            "Point(12)" [label="return"];
            "Point(13)" [label="if"];
            "Point(14)" [label="break"];
            "Point(15)" [label="if"];
            "Point(16)" [label="continue"];
            "Point(17)" [label="if"];
            "Point(18)" [label="raise"];
            "Point(19)" [label="assign"];
            "Point(20)" [label="if"];
            "Point(21)" [label="return"];
            "Point(22)" [label="if"];
            "Point(23)" [label="break"];
            "Point(24)" [label="if"];
            "Point(25)" [label="continue"];
            "Point(26)" [label="if"];
            "Point(27)" [label="raise"];
            "Point(28)" [label="assign"];
            "Point(29)" [label="if"];
            "Point(30)" [label="return"];
            "Point(31)" [label="if"];
            "Point(32)" [label="break"];
            "Point(33)" [label="if"];
            "Point(34)" [label="continue"];
            "Point(35)" [label="if"];
            "Point(36)" [label="raise"];
            "Point(37)" [label="assign"];
            "PointEnd(1)" [label=""];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Point(1)" [label="true"];
            "Point(0)" -> "Exit" [label="false"];
            "Point(0)" -> "Exit" [label="except"];
            "Point(1)" -> "Point(2)";
            "Point(2)" -> "Point(3)" [label="true"];
            "Point(2)" -> "Point(4)" [label="false"];
            "Point(2)" -> "Point(20)" [label="except(1, 0)"];
            "Point(3)" -> "Point(20)" [label="except(1, 0)"];
            "Point(3)" -> "Point(29)";
            "Point(4)" -> "Point(5)" [label="true"];
            "Point(4)" -> "Point(6)" [label="false"];
            "Point(4)" -> "Point(20)" [label="except(1, 0)"];
            "Point(5)" -> "Point(29)";
            "Point(6)" -> "Point(7)" [label="true"];
            "Point(6)" -> "Point(8)" [label="false"];
            "Point(6)" -> "Point(20)" [label="except(1, 0)"];
            "Point(7)" -> "Point(29)";
            "Point(8)" -> "Point(9)" [label="true"];
            "Point(8)" -> "Point(10)" [label="false"];
            "Point(8)" -> "Point(20)" [label="except(1, 0)"];
            "Point(9)" -> "Point(20)" [label="except(1, 0)"];
            "Point(10)" -> "Point(11)";
            "Point(10)" -> "Point(20)" [label="except(1, 0)"];
            "Point(11)" -> "Point(12)" [label="true"];
            "Point(11)" -> "Point(13)" [label="false"];
            "Point(11)" -> "Point(29)";
            "Point(12)" -> "Point(29)";
            "Point(13)" -> "Point(14)" [label="true"];
            "Point(13)" -> "Point(15)" [label="false"];
            "Point(13)" -> "Point(29)";
            "Point(14)" -> "Point(29)";
            "Point(15)" -> "Point(16)" [label="true"];
            "Point(15)" -> "Point(17)" [label="false"];
            "Point(15)" -> "Point(29)";
            "Point(16)" -> "Point(29)";
            "Point(17)" -> "Point(18)" [label="true"];
            "Point(17)" -> "Point(19)" [label="false"];
            "Point(17)" -> "Point(29)";
            "Point(18)" -> "Point(29)";
            "Point(19)" -> "Point(29)";
            "Point(20)" -> "Point(21)" [label="true"];
            "Point(20)" -> "Point(22)" [label="false"];
            "Point(20)" -> "Point(29)";
            "Point(21)" -> "Point(29)";
            "Point(22)" -> "Point(23)" [label="true"];
            "Point(22)" -> "Point(24)" [label="false"];
            "Point(22)" -> "Point(29)";
            "Point(23)" -> "Point(29)";
            "Point(24)" -> "Point(25)" [label="true"];
            "Point(24)" -> "Point(26)" [label="false"];
            "Point(24)" -> "Point(29)";
            "Point(25)" -> "Point(29)";
            "Point(26)" -> "Point(27)" [label="true"];
            "Point(26)" -> "Point(28)" [label="false"];
            "Point(26)" -> "Point(29)";
            "Point(27)" -> "Point(29)";
            "Point(28)" -> "Point(29)";
            "Point(29)" -> "Point(30)" [label="true"];
            "Point(29)" -> "Point(31)" [label="false"];
            "Point(29)" -> "Exit" [label="except"];
            "Point(30)" -> "Exit" [label="except"];
            "Point(30)" -> "Exit" [label="return"];
            "Point(31)" -> "Point(32)" [label="true"];
            "Point(31)" -> "Point(33)" [label="false"];
            "Point(31)" -> "Exit" [label="except"];
            "Point(32)" -> "Exit" [label="break"];
            "Point(33)" -> "Point(34)" [label="true"];
            "Point(33)" -> "Point(35)" [label="false"];
            "Point(33)" -> "Exit" [label="except"];
            "Point(34)" -> "Point(0)" [label="continue"];
            "Point(35)" -> "Point(36)" [label="true"];
            "Point(35)" -> "Point(37)" [label="false"];
            "Point(35)" -> "Exit" [label="except"];
            "Point(36)" -> "Exit" [label="except"];
            "Point(37)" -> "PointEnd(1)";
            "Point(37)" -> "Exit" [label="except"];
            "PointEnd(1)" -> "Point(0)";
            "PointEnd(1)" -> "Point(0)" [label="continue"];
            "PointEnd(1)" -> "Exit" [label="except"];
            "PointEnd(1)" -> "Exit" [label="break"];
            "PointEnd(1)" -> "Exit" [label="return"];
        }}
        "#,
        ));

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_function_statement() {
        let text = source_code(
            r#"
        def multiply(a, b):
            return a * b
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="function_def"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Exit";
            "Point(0)" -> "Exit" [label="except"];
        }
        digraph "CFG(0)" {
            "Entry";
            "Point(1)" [label="return"];
            "Exit";
            "Entry" -> "Point(1)";
            "Point(1)" -> "Exit" [label="except"];
            "Point(1)" -> "Exit" [label="return"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }

    #[rstest]
    fn test_process_class_statement() {
        let text = source_code(
            r#"
        class Calculator:
            def multiply(a, b):
                return a * b
        "#,
        );

        let cfg = build_dot_cfg_from_source(&text);

        let expected = source_code(
            r#"
        digraph "CFG" {
            "Entry";
            "Point(0)" [label="class_def"];
            "Exit";
            "Entry" -> "Point(0)";
            "Point(0)" -> "Exit";
            "Point(0)" -> "Exit" [label="except"];
        }
        digraph "CFG(0)" {
            "Entry";
            "Point(1)" [label="function_def"];
            "Exit";
            "Entry" -> "Point(1)";
            "Point(1)" -> "Exit";
            "Point(1)" -> "Exit" [label="except"];
        }
        digraph "CFG(1)" {
            "Entry";
            "Point(2)" [label="return"];
            "Exit";
            "Entry" -> "Point(2)";
            "Point(2)" -> "Exit" [label="except"];
            "Point(2)" -> "Exit" [label="return"];
        }
        "#,
        );

        assert_eq!(expected, cfg);
    }
}
