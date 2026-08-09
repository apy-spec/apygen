use crate::graph::dot::{
    Dot, fmt_digraph, fmt_display_edge, fmt_display_labelled_node, fmt_display_node,
    fmt_labelled_edge,
};
use crate::graph::{Graph, HashGraph};
use ast::{
    ElifElseClause, Stmt, StmtAnnAssign, StmtAssert, StmtAssign, StmtAugAssign, StmtBreak,
    StmtClassDef, StmtContinue, StmtDelete, StmtExpr, StmtFor, StmtFunctionDef, StmtGlobal, StmtIf,
    StmtImport, StmtImportFrom, StmtIpyEscapeCommand, StmtMatch, StmtNonlocal, StmtPass, StmtRaise,
    StmtReturn, StmtTry, StmtTypeAlias, StmtWhile, StmtWith,
};
use source_file::LineIndex;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use text_size::TextSize;
use thiserror::Error;

pub use apygen_graph as graph;
use apygen_graph::Edge;
pub use apygen_identifiers as identifiers;
pub use builder::{BuildCfgError, build_cfg};
pub use identifiers::Location;
pub use ruff_python_ast as ast;
pub use ruff_python_parser as parser;
pub use ruff_source_file as source_file;
pub use ruff_text_size as text_size;

pub mod builder;

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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
    pub graph: HashGraph<ProgramPoint, Option<CfgNode<'s>>, BTreeSet<CfgEdgeKind>>,
    pub cfgs: HashMap<Location, Cfg<'s>>,
}

impl<'s> Cfg<'s> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn empty() -> Self {
        let mut cfg = Cfg::default();
        cfg.graph.insert_node(ProgramPoint::Entry, None);
        cfg.graph.insert_node(ProgramPoint::Exit, None);
        cfg.graph
            .edge_entry((ProgramPoint::Entry, ProgramPoint::Exit))
            .expect("Edge should be inserted successfully")
            .insert_entry(BTreeSet::default());
        cfg
    }
}

impl Dot for Cfg<'_> {
    fn fmt(&self, f: &mut Formatter<'_>, name: &str) -> fmt::Result {
        fmt_digraph(f, &name, |f| {
            for (node, cfg_node) in self.graph.nodes().collect::<BTreeMap<_, _>>() {
                if let Some(cfg_node) = cfg_node {
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
                    fmt_display_labelled_node(f, node, &label)?;
                } else {
                    fmt_display_node(f, node)?;
                }
            }
            for (edge, edge_kinds) in self.graph.edges().collect::<BTreeMap<_, _>>() {
                for edge_kind in edge_kinds {
                    if let CfgEdgeKind::Unconditional = edge_kind {
                        fmt_display_edge(f, edge)?;
                    } else {
                        fmt_labelled_edge(
                            f,
                            |f| write!(f, "{}", edge.from()),
                            |f| write!(f, "{}", edge.to()),
                            |f| match edge_kind {
                                CfgEdgeKind::Unconditional => Ok(()),
                                CfgEdgeKind::Conditional(cond) => {
                                    write!(f, "{}", cond)
                                }
                                CfgEdgeKind::Match(index) => {
                                    write!(f, "match({})", index)
                                }
                                CfgEdgeKind::Exception(point, index) => {
                                    write!(f, "except({}, {})", point, index)
                                }
                                CfgEdgeKind::UnhandledException => {
                                    write!(f, "except")
                                }
                                CfgEdgeKind::Break => {
                                    write!(f, "break")
                                }
                                CfgEdgeKind::Continue => {
                                    write!(f, "continue")
                                }
                                CfgEdgeKind::Return => {
                                    write!(f, "return")
                                }
                            },
                        )?;
                    }
                }
            }
            Ok(())
        })
    }
}
