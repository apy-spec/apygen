pub mod builder;

pub use apygen_graph as graph;
use ast::{
    ElifElseClause, Stmt, StmtAnnAssign, StmtAssert, StmtAssign, StmtAugAssign, StmtBreak,
    StmtClassDef, StmtContinue, StmtDelete, StmtExpr, StmtFor, StmtFunctionDef, StmtGlobal, StmtIf,
    StmtImport, StmtImportFrom, StmtIpyEscapeCommand, StmtMatch, StmtNonlocal, StmtPass, StmtRaise,
    StmtReturn, StmtTry, StmtTypeAlias, StmtWhile, StmtWith,
};
pub use builder::{BuildCfgError, build_cfg};
use graph::dot::Dot;
pub use ruff_python_ast as ast;
pub use ruff_python_parser as parser;
pub use ruff_source_file as source_file;
pub use ruff_text_size as text_size;
use source_file::LineIndex;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use text_size::TextSize;
use thiserror::Error;

#[derive(Debug, Error)]
#[error("failed to convert text size {0:?} to a location in the source code")]
pub struct TryFromTextSizeError(TextSize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub line: usize,
    pub offset: usize,
}

impl Location {
    pub fn new(line: usize, offset: usize) -> Self {
        Self { line, offset }
    }

    pub fn try_from_text_size(
        line_index: &LineIndex,
        size: TextSize,
    ) -> Result<Self, TryFromTextSizeError> {
        let line = line_index.line_index(size).get();
        let Some(line_size) = line_index.line_starts().get(line - 1) else {
            return Err(TryFromTextSizeError(size));
        };
        let offset_size = size - line_size;
        Ok(Location::new(line, offset_size.to_usize()))
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.offset)
    }
}

#[derive(Eq, Hash, PartialEq, Debug, Clone, PartialOrd, Ord, Copy)]
pub enum ProgramPoint {
    Entry,
    Location(Location),
    End(Location),
    Exit,
}

impl Display for ProgramPoint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramPoint::Entry => write!(f, "Entry"),
            ProgramPoint::Exit => write!(f, "Exit"),
            ProgramPoint::Location(location) => write!(f, "Location({})", location),
            ProgramPoint::End(location) => write!(f, "End({})", location),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Node<'s> {
    FunctionDef(&'s StmtFunctionDef),
    ClassDef(&'s StmtClassDef),
    Return(&'s StmtReturn),
    Delete(&'s StmtDelete),
    Assign(&'s StmtAssign),
    AugAssign(&'s StmtAugAssign),
    AnnAssign(&'s StmtAnnAssign),
    TypeAlias(&'s StmtTypeAlias),
    For(&'s StmtFor),
    While(&'s StmtWhile),
    If(&'s StmtIf),
    Elif(&'s ElifElseClause),
    With(&'s StmtWith),
    Match(&'s StmtMatch),
    Raise(&'s StmtRaise),
    Try(&'s StmtTry),
    Assert(&'s StmtAssert),
    Import(&'s StmtImport),
    ImportFrom(&'s StmtImportFrom),
    Global(&'s StmtGlobal),
    Nonlocal(&'s StmtNonlocal),
    Expr(&'s StmtExpr),
    Pass(&'s StmtPass),
    Break(&'s StmtBreak),
    Continue(&'s StmtContinue),

    IpyEscapeCommand(&'s StmtIpyEscapeCommand),
}

impl<'s> From<&'s Stmt> for Node<'s> {
    fn from(value: &'s Stmt) -> Self {
        match value {
            Stmt::FunctionDef(stmt_function_def) => Node::FunctionDef(stmt_function_def),
            Stmt::ClassDef(stmt_class_def) => Node::ClassDef(stmt_class_def),
            Stmt::Return(stmt_return) => Node::Return(stmt_return),
            Stmt::Delete(stmt_delete) => Node::Delete(stmt_delete),
            Stmt::Assign(stmt_assign) => Node::Assign(stmt_assign),
            Stmt::AugAssign(stmt_aug_assign) => Node::AugAssign(stmt_aug_assign),
            Stmt::AnnAssign(stmt_ann_assign) => Node::AnnAssign(stmt_ann_assign),
            Stmt::TypeAlias(stmt_type_alias) => Node::TypeAlias(stmt_type_alias),
            Stmt::For(stmt_for) => Node::For(stmt_for),
            Stmt::While(stmt_while) => Node::While(stmt_while),
            Stmt::If(stmt_if) => Node::If(stmt_if),
            Stmt::With(stmt_with) => Node::With(stmt_with),
            Stmt::Match(stmt_match) => Node::Match(stmt_match),
            Stmt::Raise(stmt_raise) => Node::Raise(stmt_raise),
            Stmt::Try(stmt_try) => Node::Try(stmt_try),
            Stmt::Assert(stmt_assert) => Node::Assert(stmt_assert),
            Stmt::Import(stmt_import) => Node::Import(stmt_import),
            Stmt::ImportFrom(stmt_import_from) => Node::ImportFrom(stmt_import_from),
            Stmt::Global(stmt_global) => Node::Global(stmt_global),
            Stmt::Nonlocal(stmt_non_local) => Node::Nonlocal(stmt_non_local),
            Stmt::Expr(stmt_expr) => Node::Expr(stmt_expr),
            Stmt::Pass(stmt_pass) => Node::Pass(stmt_pass),
            Stmt::Break(stmt_break) => Node::Break(stmt_break),
            Stmt::Continue(stmt_continue) => Node::Continue(stmt_continue),
            Stmt::IpyEscapeCommand(stmt_ipy_escape_command) => {
                Node::IpyEscapeCommand(stmt_ipy_escape_command)
            }
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct NodeEntry<'s> {
    pub node: Option<Node<'s>>,
    pub successors: BTreeSet<ProgramPoint>,
    pub predecessors: BTreeSet<ProgramPoint>,
}

impl<'s> NodeEntry<'s> {
    pub fn new(
        node: Option<Node<'s>>,
        successors: BTreeSet<ProgramPoint>,
        predecessors: BTreeSet<ProgramPoint>,
    ) -> Self {
        Self {
            node,
            successors,
            predecessors,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Copy)]
pub struct Edge {
    pub from: ProgramPoint,
    pub to: ProgramPoint,
}

impl Edge {
    pub fn new(from: ProgramPoint, to: ProgramPoint) -> Self {
        Self { from, to }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Copy)]
pub enum EdgeKind {
    Unconditional,
    Conditional(bool),
    Match(usize),
    Exception(ProgramPoint, usize),
    UnhandledException,
    Break,
    Continue,
    Return,
}

impl EdgeKind {
    pub fn is_normal_flow(&self) -> bool {
        !self.is_exception_flow()
    }

    pub fn is_exception_flow(&self) -> bool {
        matches!(self, Self::Exception(_, _) | Self::UnhandledException)
    }
}

#[derive(Default, Debug, Clone)]
pub struct Cfg<'s> {
    entries: HashMap<ProgramPoint, NodeEntry<'s>>,
    edges: HashMap<Edge, BTreeSet<EdgeKind>>,
    cfgs: HashMap<Location, Cfg<'s>>,
}

impl<'s> Cfg<'s> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn empty() -> Self {
        let mut cfg = Cfg::default();
        cfg.insert_edge(
            Edge::new(ProgramPoint::Entry, ProgramPoint::Exit),
            BTreeSet::default(),
        );
        cfg
    }

    pub fn entries(&self) -> &HashMap<ProgramPoint, NodeEntry<'s>> {
        &self.entries
    }

    pub fn edges(&self) -> &HashMap<Edge, BTreeSet<EdgeKind>> {
        &self.edges
    }

    pub fn cfgs(&self) -> &HashMap<Location, Cfg<'s>> {
        &self.cfgs
    }

    pub fn successors(&self, program_point: &ProgramPoint) -> Option<&BTreeSet<ProgramPoint>> {
        self.entries.get(program_point).map(|node| &node.successors)
    }

    pub fn predecessors(&self, program_point: &ProgramPoint) -> Option<&BTreeSet<ProgramPoint>> {
        self.entries
            .get(program_point)
            .map(|node| &node.predecessors)
    }

    fn insert_edge_in_entries(&mut self, edge: Edge) {
        self.entries
            .entry(edge.from)
            .or_default()
            .successors
            .insert(edge.to);
        self.entries
            .entry(edge.to)
            .or_default()
            .predecessors
            .insert(edge.from);
    }

    fn remove_edges_from_entry(&mut self, program_point: ProgramPoint, entry: NodeEntry<'_>) {
        for successor in entry.successors {
            self.edges.remove(&Edge::new(program_point, successor));
        }
        for predecessor in entry.predecessors {
            self.edges.remove(&Edge::new(predecessor, program_point));
        }
    }

    pub fn insert_node(&mut self, program_point: ProgramPoint, node: Option<Node<'s>>) {
        if let Some(previous_entry) = self.entries.insert(
            program_point,
            NodeEntry {
                node,
                ..Default::default()
            },
        ) {
            self.remove_edges_from_entry(program_point, previous_entry);
        }
    }

    pub fn remove_node(&mut self, program_point: &ProgramPoint) {
        if let Some(removed_entry) = self.entries.remove(program_point) {
            self.remove_edges_from_entry(*program_point, removed_entry);
        }
    }

    pub fn insert_edge(&mut self, edge: Edge, kinds: BTreeSet<EdgeKind>) {
        self.insert_edge_in_entries(edge);
        self.edges.insert(edge, kinds);
    }

    pub fn insert_edge_kind(&mut self, edge: Edge, kind: EdgeKind) {
        self.insert_edge_in_entries(edge);
        self.edges.entry(edge).or_default().insert(kind);
    }

    pub fn remove_edge(&mut self, edge: &Edge) {
        self.edges.remove(edge);
        if let Some(entry) = self.entries.get_mut(&edge.from) {
            entry.successors.remove(&edge.to);
        }
        if let Some(entry) = self.entries.get_mut(&edge.to) {
            entry.predecessors.remove(&edge.from);
        }
    }

    pub fn remove_edge_kind(&mut self, edge: &Edge, kind: &EdgeKind) {
        if let Some(kinds) = self.edges.get_mut(edge) {
            kinds.remove(kind);
        }
    }

    pub fn insert_cfg(&mut self, location: Location, cfg: Cfg<'s>) {
        self.cfgs.insert(location, cfg);
    }

    pub fn remove_cfg(&mut self, location: Location) {
        self.cfgs.remove(&location);
    }
}

impl<'s> Dot for Cfg<'s> {
    fn fmt(&self, f: &mut Formatter<'_>, name: &str) -> std::fmt::Result {
        let entries = self.entries.iter().collect::<BTreeMap<_, _>>();
        let edges = self.edges.iter().collect::<BTreeMap<_, _>>();

        write!(f, "digraph \"{}\" {{\n", name)?;
        for (program_point, entry) in entries {
            write!(f, "    \"{}\"", program_point)?;

            if let Some(node) = &entry.node {
                let label = match node {
                    Node::FunctionDef(_) => "function_def",
                    Node::ClassDef(_) => "class_def",
                    Node::Return(_) => "return",
                    Node::Delete(_) => "delete",
                    Node::Assign(_) => "assign",
                    Node::AugAssign(_) => "aug_assign",
                    Node::AnnAssign(_) => "ann_assign",
                    Node::TypeAlias(_) => "type_alias",
                    Node::For(_) => "for",
                    Node::While(_) => "while",
                    Node::If(_) => "if",
                    Node::Elif(_) => "elif",
                    Node::With(_) => "with",
                    Node::Match(_) => "match",
                    Node::Raise(_) => "raise",
                    Node::Try(_) => "try",
                    Node::Assert(_) => "assert",
                    Node::Import(_) => "import",
                    Node::ImportFrom(_) => "import_from",
                    Node::Global(_) => "global",
                    Node::Nonlocal(_) => "nonlocal",
                    Node::Expr(_) => "expr",
                    Node::Pass(_) => "pass",
                    Node::Break(_) => "break",
                    Node::Continue(_) => "continue",
                    Node::IpyEscapeCommand(_) => "ipy_escape_command",
                };
                write!(f, " [label=\"{}\"]", label)?;
            }

            f.write_str(";\n")?;
        }

        for (edge, edge_kinds) in edges {
            for edge_kind in edge_kinds {
                write!(f, "    \"{}\" -> \"{}\"", edge.from, edge.to)?;

                match edge_kind {
                    EdgeKind::Unconditional => {}
                    EdgeKind::Conditional(cond) => {
                        write!(f, " [label=\"{}\"]", cond)?;
                    }
                    EdgeKind::Match(index) => {
                        write!(f, " [label=\"match({})\"]", index)?;
                    }
                    EdgeKind::Exception(point, index) => {
                        write!(f, " [label=\"except({}, {})\"]", point, index)?
                    }
                    EdgeKind::UnhandledException => {
                        write!(f, " [label=\"except\"]")?;
                    }
                    EdgeKind::Break => {
                        write!(f, " [label=\"break\"]")?;
                    }
                    EdgeKind::Continue => {
                        write!(f, " [label=\"continue\"]")?;
                    }
                    EdgeKind::Return => {
                        write!(f, " [label=\"return\"]")?;
                    }
                };
                f.write_str(";\n")?;
            }
        }

        f.write_str("}\n")
    }
}
