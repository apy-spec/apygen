pub mod builder;

pub use apygen_graph as graph;
pub use apygen_identifiers as identifiers;
use ast::{
    ElifElseClause, Stmt, StmtAnnAssign, StmtAssert, StmtAssign, StmtAugAssign, StmtBreak,
    StmtClassDef, StmtContinue, StmtDelete, StmtExpr, StmtFor, StmtFunctionDef, StmtGlobal, StmtIf,
    StmtImport, StmtImportFrom, StmtIpyEscapeCommand, StmtMatch, StmtNonlocal, StmtPass, StmtRaise,
    StmtReturn, StmtTry, StmtTypeAlias, StmtWhile, StmtWith,
};
pub use builder::{BuildCfgError, build_cfg};
use graph::Graph;
use graph::dot::DiGraphDot;
pub use identifiers::Location;
pub use ruff_python_ast as ast;
pub use ruff_python_parser as parser;
pub use ruff_source_file as source_file;
pub use ruff_text_size as text_size;
use source_file::LineIndex;
use std::collections::{BTreeSet, HashMap};
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use text_size::TextSize;
use thiserror::Error;

#[derive(Debug, Error)]
#[error("failed to convert text size {0:?} to a location in the source code")]
pub struct ConvertTextSizeError(TextSize);

pub fn convert_text_size_to_location(
    line_index: &LineIndex,
    text_size: TextSize,
) -> Result<Location, ConvertTextSizeError> {
    let line = line_index.line_index(text_size).get();
    let Some(line_size) = line_index.line_starts().get(line - 1) else {
        return Err(ConvertTextSizeError(text_size));
    };
    let offset_size = text_size - line_size;
    Ok(Location::new(line, offset_size.to_usize()))
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
pub enum CfgNode<'s> {
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

impl<'s> From<&'s Stmt> for CfgNode<'s> {
    fn from(value: &'s Stmt) -> Self {
        match value {
            Stmt::FunctionDef(stmt_function_def) => CfgNode::FunctionDef(stmt_function_def),
            Stmt::ClassDef(stmt_class_def) => CfgNode::ClassDef(stmt_class_def),
            Stmt::Return(stmt_return) => CfgNode::Return(stmt_return),
            Stmt::Delete(stmt_delete) => CfgNode::Delete(stmt_delete),
            Stmt::Assign(stmt_assign) => CfgNode::Assign(stmt_assign),
            Stmt::AugAssign(stmt_aug_assign) => CfgNode::AugAssign(stmt_aug_assign),
            Stmt::AnnAssign(stmt_ann_assign) => CfgNode::AnnAssign(stmt_ann_assign),
            Stmt::TypeAlias(stmt_type_alias) => CfgNode::TypeAlias(stmt_type_alias),
            Stmt::For(stmt_for) => CfgNode::For(stmt_for),
            Stmt::While(stmt_while) => CfgNode::While(stmt_while),
            Stmt::If(stmt_if) => CfgNode::If(stmt_if),
            Stmt::With(stmt_with) => CfgNode::With(stmt_with),
            Stmt::Match(stmt_match) => CfgNode::Match(stmt_match),
            Stmt::Raise(stmt_raise) => CfgNode::Raise(stmt_raise),
            Stmt::Try(stmt_try) => CfgNode::Try(stmt_try),
            Stmt::Assert(stmt_assert) => CfgNode::Assert(stmt_assert),
            Stmt::Import(stmt_import) => CfgNode::Import(stmt_import),
            Stmt::ImportFrom(stmt_import_from) => CfgNode::ImportFrom(stmt_import_from),
            Stmt::Global(stmt_global) => CfgNode::Global(stmt_global),
            Stmt::Nonlocal(stmt_non_local) => CfgNode::Nonlocal(stmt_non_local),
            Stmt::Expr(stmt_expr) => CfgNode::Expr(stmt_expr),
            Stmt::Pass(stmt_pass) => CfgNode::Pass(stmt_pass),
            Stmt::Break(stmt_break) => CfgNode::Break(stmt_break),
            Stmt::Continue(stmt_continue) => CfgNode::Continue(stmt_continue),
            Stmt::IpyEscapeCommand(stmt_ipy_escape_command) => {
                CfgNode::IpyEscapeCommand(stmt_ipy_escape_command)
            }
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct CfgNodeEntry<'s> {
    pub node: Option<CfgNode<'s>>,
    pub successors: BTreeSet<ProgramPoint>,
    pub predecessors: BTreeSet<ProgramPoint>,
}

impl<'s> CfgNodeEntry<'s> {
    pub fn new(
        node: Option<CfgNode<'s>>,
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
pub struct CfgEdge {
    pub from: ProgramPoint,
    pub to: ProgramPoint,
}

impl CfgEdge {
    pub fn new(from: ProgramPoint, to: ProgramPoint) -> Self {
        Self { from, to }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Copy)]
pub enum CfgEdgeKind {
    Unconditional,
    Conditional(bool),
    Match(usize),
    Exception(ProgramPoint, usize),
    UnhandledException,
    Break,
    Continue,
    Return,
}

impl CfgEdgeKind {
    pub fn is_normal_flow(&self) -> bool {
        !self.is_exception_flow()
    }

    pub fn is_exception_flow(&self) -> bool {
        matches!(self, Self::Exception(_, _) | Self::UnhandledException)
    }
}

#[derive(Default, Debug, Clone)]
pub struct Cfg<'s> {
    entries: HashMap<ProgramPoint, CfgNodeEntry<'s>>,
    edges: HashMap<CfgEdge, BTreeSet<CfgEdgeKind>>,
    cfgs: HashMap<Location, Cfg<'s>>,
}

impl<'s> Cfg<'s> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn empty() -> Self {
        let mut cfg = Cfg::default();
        cfg.insert_edge(
            CfgEdge::new(ProgramPoint::Entry, ProgramPoint::Exit),
            BTreeSet::default(),
        );
        cfg
    }

    pub fn entries(&self) -> &HashMap<ProgramPoint, CfgNodeEntry<'s>> {
        &self.entries
    }

    pub fn edges(&self) -> &HashMap<CfgEdge, BTreeSet<CfgEdgeKind>> {
        &self.edges
    }

    pub fn cfgs(&self) -> &HashMap<Location, Cfg<'s>> {
        &self.cfgs
    }

    fn insert_edge_in_entries(&mut self, edge: CfgEdge) {
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

    fn remove_edges_from_entry(&mut self, program_point: ProgramPoint, entry: CfgNodeEntry<'_>) {
        for successor in entry.successors {
            self.edges.remove(&CfgEdge::new(program_point, successor));
        }
        for predecessor in entry.predecessors {
            self.edges.remove(&CfgEdge::new(predecessor, program_point));
        }
    }

    pub fn insert_node(&mut self, program_point: ProgramPoint, node: Option<CfgNode<'s>>) {
        if let Some(previous_entry) = self.entries.insert(
            program_point,
            CfgNodeEntry {
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

    pub fn insert_edge(&mut self, edge: CfgEdge, kinds: BTreeSet<CfgEdgeKind>) {
        self.insert_edge_in_entries(edge);
        self.edges.insert(edge, kinds);
    }

    pub fn insert_edge_kind(&mut self, edge: CfgEdge, kind: CfgEdgeKind) {
        self.insert_edge_in_entries(edge);
        self.edges.entry(edge).or_default().insert(kind);
    }

    pub fn remove_edge(&mut self, edge: &CfgEdge) {
        self.edges.remove(edge);
        if let Some(entry) = self.entries.get_mut(&edge.from) {
            entry.successors.remove(&edge.to);
        }
        if let Some(entry) = self.entries.get_mut(&edge.to) {
            entry.predecessors.remove(&edge.from);
        }
    }

    pub fn remove_edge_kind(&mut self, edge: &CfgEdge, kind: &CfgEdgeKind) {
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

impl<'s> Graph for Cfg<'s> {
    type Node = ProgramPoint;
    type NodeData = Option<CfgNode<'s>>;
    type EdgeData = BTreeSet<CfgEdgeKind>;

    fn node_data_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)> {
        self.entries.iter().map(|(node, entry)| (node, &entry.node))
    }
    fn edge_data_iter(
        &self,
    ) -> impl Iterator<Item = ((&Self::Node, &Self::Node), &Self::EdgeData)> {
        self.edges
            .iter()
            .map(|(edge, kinds)| ((&edge.from, &edge.to), kinds))
    }
    fn node_iter(&self) -> impl Iterator<Item = &Self::Node> {
        self.entries.keys()
    }

    fn edge_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::Node)> {
        self.edges.keys().map(|edge| (&edge.from, &edge.to))
    }

    fn get_node_data(&self, node: &Self::Node) -> Option<&Self::NodeData> {
        self.entries.get(node).map(|entry| &entry.node)
    }

    fn get_edge_data(&self, (from, to): (&Self::Node, &Self::Node)) -> Option<&Self::EdgeData> {
        self.edges
            .get(&CfgEdge::new(*from, *to))
            .map(|edge_kinds| edge_kinds)
    }

    fn successor_iter(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.entries
            .get(node)
            .into_iter()
            .flat_map(|node| &node.successors)
    }

    fn predecessor_iter(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.entries
            .get(node)
            .into_iter()
            .flat_map(|node| &node.predecessors)
    }
}

impl<'s> DiGraphDot for Cfg<'s> {
    fn fmt_node(
        &self,
        f: &mut Formatter<'_>,
        node: &Self::Node,
        node_data: &Self::NodeData,
    ) -> std::fmt::Result {
        write!(f, "    \"{}\"", node)?;

        if let Some(cfg_node) = &node_data {
            let label = match cfg_node {
                CfgNode::FunctionDef(_) => "function_def",
                CfgNode::ClassDef(_) => "class_def",
                CfgNode::Return(_) => "return",
                CfgNode::Delete(_) => "delete",
                CfgNode::Assign(_) => "assign",
                CfgNode::AugAssign(_) => "aug_assign",
                CfgNode::AnnAssign(_) => "ann_assign",
                CfgNode::TypeAlias(_) => "type_alias",
                CfgNode::For(_) => "for",
                CfgNode::While(_) => "while",
                CfgNode::If(_) => "if",
                CfgNode::Elif(_) => "elif",
                CfgNode::With(_) => "with",
                CfgNode::Match(_) => "match",
                CfgNode::Raise(_) => "raise",
                CfgNode::Try(_) => "try",
                CfgNode::Assert(_) => "assert",
                CfgNode::Import(_) => "import",
                CfgNode::ImportFrom(_) => "import_from",
                CfgNode::Global(_) => "global",
                CfgNode::Nonlocal(_) => "nonlocal",
                CfgNode::Expr(_) => "expr",
                CfgNode::Pass(_) => "pass",
                CfgNode::Break(_) => "break",
                CfgNode::Continue(_) => "continue",
                CfgNode::IpyEscapeCommand(_) => "ipy_escape_command",
            };
            write!(f, " [label=\"{}\"]", label)?;
        }

        f.write_str(";\n")
    }

    fn fmt_edge(
        &self,
        f: &mut Formatter<'_>,
        (from, to): (&Self::Node, &Self::Node),
        edge_data: &Self::EdgeData,
    ) -> std::fmt::Result {
        for edge_kind in edge_data {
            write!(f, "    \"{}\" -> \"{}\"", from, to)?;

            match edge_kind {
                CfgEdgeKind::Unconditional => {}
                CfgEdgeKind::Conditional(cond) => {
                    write!(f, " [label=\"{}\"]", cond)?;
                }
                CfgEdgeKind::Match(index) => {
                    write!(f, " [label=\"match({})\"]", index)?;
                }
                CfgEdgeKind::Exception(point, index) => {
                    write!(f, " [label=\"except({}, {})\"]", point, index)?
                }
                CfgEdgeKind::UnhandledException => {
                    write!(f, " [label=\"except\"]")?;
                }
                CfgEdgeKind::Break => {
                    write!(f, " [label=\"break\"]")?;
                }
                CfgEdgeKind::Continue => {
                    write!(f, " [label=\"continue\"]")?;
                }
                CfgEdgeKind::Return => {
                    write!(f, " [label=\"return\"]")?;
                }
            };
            f.write_str(";\n")?;
        }

        Ok(())
    }
}
