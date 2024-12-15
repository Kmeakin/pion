use core::fmt;

use pretty::{docs, DocAllocator as _};

use crate::env::{DeBruijnIndex, UniqueEnv};
use crate::syntax::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prec {
    Atom,
    Call,
    Match,
    Fun,
}

impl Prec {
    pub const MAX: Self = Self::Fun;

    pub fn of_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Error
            | Expr::Lit(_)
            | Expr::PrimVar(_)
            | Expr::LocalVar(_)
            | Expr::MetaVar(_)
            | Expr::Do(..)
            | Expr::RecordType(..)
            | Expr::RecordLit(..) => Self::Atom,
            Expr::FunApp(..) | Expr::RecordProj(..) => Self::Call,
            Expr::FunType(..) | Expr::FunLit(..) => Self::Fun,
            Expr::MatchBool(..) | Expr::MatchInt(..) => Self::Match,
        }
    }
}

const INDENT: isize = 4;

#[derive(Debug, Copy, Clone)]
pub struct Printer<'bump> {
    bump: &'bump bumpalo::Bump,
}

impl<'bump, A: 'bump> pretty::DocAllocator<'bump, A> for Printer<'bump> {
    type Doc = pretty::RefDoc<'bump, A>;

    fn alloc(&'bump self, doc: pretty::Doc<'bump, Self::Doc, A>) -> Self::Doc {
        pretty::RefDoc(self.bump.alloc(doc))
    }

    fn alloc_column_fn(
        &'bump self,
        f: impl Fn(usize) -> Self::Doc + 'bump,
    ) -> <Self::Doc as pretty::DocPtr<'bump, A>>::ColumnFn {
        self.bump.alloc(f)
    }

    fn alloc_width_fn(
        &'bump self,
        f: impl Fn(isize) -> Self::Doc + 'bump,
    ) -> <Self::Doc as pretty::DocPtr<'bump, A>>::WidthFn {
        self.bump.alloc(f)
    }
}

pub type DocBuilder<'bump> = pretty::DocBuilder<'bump, Printer<'bump>>;
pub type Names<'core> = UniqueEnv<Name<'core>>;

impl<'bump> Printer<'bump> {
    pub fn new(bump: &'bump bumpalo::Bump) -> Self { Self { bump } }

    pub fn type_ann_expr<'core>(
        &'bump self,
        expr: &Expr<'core>,
        r#type: &Expr<'core>,
        names: &mut Names<'core>,
    ) -> DocBuilder<'bump> {
        let expr = self.expr_prec(expr, Prec::Call, names);
        let r#type = self.expr_prec(r#type, Prec::Fun, names);
        docs![self, expr, " : ", r#type]
    }

    pub fn expr_prec<'core>(
        &'bump self,
        expr: &Expr<'core>,
        prec: Prec,
        names: &mut Names<'core>,
    ) -> DocBuilder<'bump> {
        let inner = match expr {
            Expr::Error => self.text("#error"),
            Expr::Lit(lit) => self.lit(*lit),
            Expr::PrimVar(var) => self.text(var.name()),
            Expr::LocalVar(var) => match names.get(var.de_bruijn) {
                None => panic!("Unbound local variable: {var:?}"),
                Some(Some(name)) => self.text(format!("{name}")),
                Some(None) => self.text(format!("#var({:?})", var.de_bruijn)),
            },
            Expr::MetaVar(var) => self.text(format!("?{}", var.de_bruijn)),
            Expr::FunType(param, body) if !body.binds_local(DeBruijnIndex::new(0)) => {
                let plicity = self.plicity(param.plicity);
                let param_type = self.expr_prec(param.r#type, Prec::Call, names);
                names.push(param.name);
                let ret_type = self.expr_prec(body, Prec::MAX, names);
                names.pop();
                docs![self, plicity, param_type, " -> ", ret_type]
            }
            Expr::FunType(..) => {
                let len = names.len();
                let mut expr = expr;
                let params = std::iter::from_fn(|| match expr {
                    Expr::FunType(param, body) if body.binds_local(DeBruijnIndex::new(0)) => {
                        expr = body;
                        let ret = self.fun_param(param, names);
                        names.push(param.name);
                        Some(ret)
                    }
                    body => {
                        expr = body;
                        None
                    }
                });
                let params = self.intersperse(params, docs![self, ", "]);
                let body = self.expr_prec(expr, Prec::MAX, names);
                names.truncate(len);
                docs![self, "forall(", params, ") -> ", body]
            }
            Expr::FunLit(..) => {
                let len = names.len();
                let mut expr = expr;
                let params = std::iter::from_fn(|| match expr {
                    Expr::FunLit(param, body) => {
                        expr = body;
                        let ret = self.fun_param(param, names);
                        names.push(param.name);
                        Some(ret)
                    }
                    body => {
                        expr = body;
                        None
                    }
                });
                let params = self.intersperse(params, docs![self, ", "]);
                let body = self.expr_prec(expr, Prec::MAX, names);
                names.truncate(len);
                docs![self, "fun(", params, ") => ", body]
            }
            Expr::FunApp(..) => {
                let mut args = Vec::new();
                let mut callee = expr;
                while let Expr::FunApp(head, arg) = callee {
                    callee = head;
                    args.push(arg);
                }

                let callee = self.expr_prec(callee, Prec::Call, names);
                let args = args.into_iter().rev().map(|arg| self.fun_arg(arg, names));
                let args = self.intersperse(args, docs![self, ", "]);
                docs![self, callee, "(", args, ")"]
            }
            Expr::Do([], None) => docs![self, "do {}"],
            Expr::Do([], Some(trailing_expr)) => {
                let trailing_expr = self.expr_prec(trailing_expr, Prec::MAX, names);
                docs![
                    self,
                    "do {",
                    docs![self, self.line(), trailing_expr, self.line()].nest(INDENT),
                    "}"
                ]
                .group()
            }
            Expr::Do(stmts, trailing_expr) => {
                let len = names.len();
                let stmts = stmts.iter().map(|stmt| self.stmt(stmt, names));
                let stmts = self.intersperse(stmts, self.hardline());
                let trailing_expr =
                    trailing_expr.map(|expr| self.expr_prec(expr, Prec::MAX, names));
                names.truncate(len);
                docs![
                    self,
                    "do {",
                    docs![
                        self,
                        self.hardline(),
                        stmts,
                        self.hardline(),
                        trailing_expr,
                        self.hardline(),
                    ]
                    .nest(INDENT),
                    "}"
                ]
            }
            Expr::MatchBool(cond, then, r#else) => {
                let cond = self.expr_prec(cond, Prec::MAX, names);
                let then = self.expr_prec(then, Prec::MAX, names);
                let r#else = self.expr_prec(r#else, Prec::MAX, names);
                docs![self, "if ", cond, " then ", then, " else ", r#else]
            }
            Expr::MatchInt(scrut, cases, default) => {
                let scrut = self.expr_prec(scrut, Prec::MAX, names);
                let cases = cases.iter().map(|(n, expr)| {
                    let expr = self.expr_prec(expr, Prec::MAX, names);
                    docs![self, self.lit(Lit::Int(*n)), " => ", expr, ","]
                });
                let cases = self.intersperse(cases, self.hardline());
                let default = {
                    let expr = self.expr_prec(default, Prec::MAX, names);
                    docs![self, "_ => ", expr, ","]
                };
                docs![
                    self,
                    "match ",
                    scrut,
                    " {",
                    docs![
                        self,
                        self.hardline(),
                        cases,
                        self.hardline(),
                        default,
                        self.hardline()
                    ]
                    .nest(INDENT),
                    "}"
                ]
            }
            Expr::RecordType(fields) => {
                let len = names.len();
                let fields = fields.iter().map(|(label, expr)| {
                    let expr = self.expr_prec(expr, Prec::MAX, names);
                    names.push(Some(*label));
                    docs![self, format!("{label}"), " : ", expr]
                });
                let fields = self.intersperse(fields, docs![self, ", "]);
                names.truncate(len);
                docs![self, "{", fields, "}"]
            }
            Expr::RecordLit(fields) => {
                let fields = fields.iter().map(|(label, expr)| {
                    let expr = self.expr_prec(expr, Prec::MAX, names);
                    docs![self, format!("{label}"), " = ", expr]
                });
                let fields = self.intersperse(fields, docs![self, ", "]);
                docs![self, "{", fields, "}"]
            }
            Expr::RecordProj(scrut, label) => {
                let scrut = self.expr_prec(scrut, Prec::Call, names);
                docs![self, scrut, ".", format!("{label}")]
            }
        };
        match Prec::of_expr(expr) > prec {
            true => docs![self, "(", inner, ")"],
            false => inner,
        }
    }

    fn stmt<'core>(&'bump self, stmt: &Stmt<'core>, names: &mut Names<'core>) -> DocBuilder<'bump> {
        match stmt {
            Stmt::Expr(expr) => {
                let expr = self.expr_prec(expr, Prec::MAX, names);
                docs![self, expr, ";"]
            }
            Stmt::Let(binding) => {
                let LetBinding { name, r#type, init } = binding;
                let r#type = self.expr_prec(r#type, Prec::MAX, names);
                let init = self.expr_prec(init, Prec::MAX, names);
                names.push(*name);
                docs![
                    self,
                    "let ",
                    self.name(*name),
                    " : ",
                    r#type,
                    " = ",
                    init,
                    ";"
                ]
            }
        }
    }

    pub fn let_stmt<'core>(
        &'bump self,
        binding: &LetBinding<'core, Expr<'core>>,
        names: &mut Names<'core>,
    ) -> DocBuilder<'bump> {
        let LetBinding { name, r#type, init } = binding;
        let name = self.name(*name);
        let r#type = self.expr_prec(r#type, Prec::MAX, names);
        let init = self.expr_prec(init, Prec::MAX, names);
        docs![self, "let ", name, " : ", r#type, " = ", init, ";"]
    }

    fn lit(&'bump self, lit: Lit<'_>) -> DocBuilder<'bump> {
        match lit {
            Lit::Bool(true) => self.text("true"),
            Lit::Bool(false) => self.text("false"),
            Lit::Int(n) => self.text(format!("{n:?}")),
            Lit::Char(c) => self.text(format!("{c:?}")),
            Lit::String(s) => self.text(format!("{s:?}")),
        }
    }

    fn plicity(&'bump self, plicity: Plicity) -> DocBuilder<'bump> {
        match plicity {
            Plicity::Implicit => self.text("@"),
            Plicity::Explicit => self.nil(),
        }
    }

    fn fun_param<'core>(
        &'bump self,
        param: &FunParam<'core, &Expr<'core>>,
        names: &mut Names<'core>,
    ) -> DocBuilder<'bump> {
        let FunParam {
            plicity,
            name,
            r#type,
        } = param;
        let plicity = self.plicity(*plicity);
        let name = self.name(*name);
        let r#type = self.expr_prec(r#type, Prec::MAX, names);
        docs![self, plicity, name, " : ", r#type]
    }

    fn fun_arg<'core>(
        &'bump self,
        arg: &FunArg<&Expr<'core>>,
        names: &mut Names<'core>,
    ) -> DocBuilder<'bump> {
        let FunArg { plicity, expr } = arg;
        let plicity = self.plicity(*plicity);
        let expr = self.expr_prec(expr, Prec::MAX, names);
        docs![self, plicity, expr]
    }

    fn name(&'bump self, name: Name<'_>) -> DocBuilder<'bump> {
        match name {
            None => self.text("_"),
            Some(name) => self.text(format!("{name}")),
        }
    }
}

impl fmt::Display for Lit<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Bool(true) => write!(f, "true"),
            Lit::Bool(false) => write!(f, "false"),
            Lit::Int(n) => write!(f, "{n}"),
            Lit::Char(c) => write!(f, "{c:?}"),
            Lit::String(s) => write!(f, "{s:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::*;

    use super::*;
    use crate::env::{DeBruijnIndex, DeBruijnLevel};

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_print_expr(expr: &Expr, expected: Expect) {
        let mut names = UniqueEnv::new();
        let bump = bumpalo::Bump::new();
        let printer = Printer::new(&bump);
        let doc = printer.expr_prec(expr, Prec::MAX, &mut names).into_doc();
        let actual = format!("{}", doc.pretty(80));
        expected.assert_eq(&actual);
    }

    #[test]
    fn print_expr_bool() {
        assert_print_expr(&Expr::bool(true), expect!["true"]);
        assert_print_expr(&Expr::bool(false), expect!["false"]);
    }

    #[test]
    fn print_expr_int() { assert_print_expr(&Expr::int(42), expect!["42"]); }

    #[test]
    fn print_expr_char() { assert_print_expr(&Expr::char('a'), expect!["'a'"]); }

    #[test]
    fn print_expr_string() { assert_print_expr(&Expr::string("hello"), expect![[r#""hello""#]]); }

    #[test]
    fn print_expr_prim_var() {
        let expr = Expr::BOOL;
        assert_print_expr(&expr, expect!["Bool"]);
    }

    #[test]
    fn print_expr_meta_var() {
        let expr = Expr::MetaVar(MetaVar::new(DeBruijnLevel::new(0)));
        assert_print_expr(&expr, expect!["?0"]);
    }

    #[test]
    fn print_expr_fun_type() {
        let expr = Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["Int -> Bool"]);

        let expr = Expr::FunType(FunParam::implicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["@Int -> Bool"]);

        let expr = Expr::FunType(
            FunParam::explicit(None, &Expr::INT),
            &const { Expr::FunType(FunParam::explicit(None, &Expr::BOOL), &Expr::CHAR) },
        );
        assert_print_expr(&expr, expect!["Int -> Bool -> Char"]);

        let expr = Expr::FunType(
            FunParam::explicit(
                None,
                &const { Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL) },
            ),
            &Expr::CHAR,
        );
        assert_print_expr(&expr, expect!["(Int -> Bool) -> Char"]);
    }

    #[test]
    fn print_expr_fun_lit() {
        let int = Expr::int(5);
        let expr = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &int);
        assert_print_expr(&expr, expect!["fun(_ : Int) => 5"]);

        let expr = Expr::FunLit(FunParam::implicit(None, &Expr::INT), &int);
        assert_print_expr(&expr, expect!["fun(@_ : Int) => 5"]);

        let expr = Expr::FunLit(
            FunParam::explicit(None, &Expr::INT),
            &const {
                Expr::FunLit(
                    FunParam::explicit(None, &Expr::BOOL),
                    &const { Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0))) },
                )
            },
        );
        assert_print_expr(
            &expr,
            expect!["fun(_ : Int, _ : Bool) => #var(DeBruijnIndex(0))"],
        );
    }

    #[test]
    fn print_expr_fun_app() {
        let int = Expr::int(1);
        let expr = Expr::FunApp(&Expr::INT, FunArg::explicit(&int));
        assert_print_expr(&expr, expect!["Int(1)"]);

        let expr = Expr::FunApp(&Expr::INT, FunArg::implicit(&int));
        assert_print_expr(&expr, expect!["Int(@1)"]);

        let b = Expr::bool(true);
        let fun = Expr::FunApp(&Expr::BOOL, FunArg::explicit(&b));
        let expr = Expr::FunApp(&fun, FunArg::explicit(&int));
        assert_print_expr(&expr, expect!["Bool(true, 1)"]);

        let expr = Expr::FunApp(
            &const {
                Expr::FunLit(
                    FunParam::explicit(None, &Expr::INT),
                    &const { Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0))) },
                )
            },
            FunArg::explicit(&int),
        );
        assert_print_expr(
            &expr,
            expect!["(fun(_ : Int) => #var(DeBruijnIndex(0)))(1)"],
        );
    }

    #[test]
    fn print_expr_do() {
        let expr = Expr::Do(
            &const {
                [
                    Stmt::Let(LetBinding::new(None, Expr::INT, Expr::int(1))),
                    Stmt::Let(LetBinding::new(None, Expr::BOOL, Expr::bool(true))),
                ]
            },
            Some(&const { Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0))) }),
        );
        assert_print_expr(
            &expr,
            expect![[r"
                do {
                    let _ : Int = 1;
                    let _ : Bool = true;
                    #var(DeBruijnIndex(0))
                }"]],
        );
    }

    #[test]
    fn print_expr_if() {
        let expr = Expr::MatchBool(
            &const { Expr::bool(true) },
            &const { Expr::int(1) },
            &const { Expr::int(2) },
        );
        assert_print_expr(&expr, expect!["if true then 1 else 2"]);
    }
}
