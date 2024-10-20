use std::fmt::{self, Display, Write};

use crate::syntax::*;

pub struct Printer<W: Write> {
    out: W,
    indent: usize,
    at_line_start: bool,
}

impl<W: Write> Write for Printer<W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if self.at_line_start {
            for _ in 0..self.indent {
                self.out.write_str(" ")?;
            }
        }
        self.out.write_str(s)?;
        self.at_line_start = s.ends_with('\n');
        Ok(())
    }
}

impl<W: Write> Printer<W> {
    pub fn new(out: W) -> Self {
        Self {
            out,
            indent: 0,
            at_line_start: true,
        }
    }

    pub fn finish(self) -> W { self.out }

    fn indent(&mut self) { self.indent += 1; }

    fn dedent(&mut self) { self.indent -= 1; }

    fn with_indent(&mut self, mut f: impl FnMut(&mut Self) -> fmt::Result) -> fmt::Result {
        self.indent();
        f(self)?;
        self.dedent();
        Ok(())
    }

    fn located<T: Display>(&mut self, it: &Located<T>) -> fmt::Result {
        write!(self, "{:?} @ {}", it.range, it.data)
    }

    fn expr(&mut self, expr: &Expr) -> fmt::Result {
        match expr {
            Expr::Error => writeln!(self, "Expr::Error"),
            Expr::Hole => writeln!(self, "Expr::Hole"),
            Expr::Var(name) => writeln!(self, "Expr::Var({name:?})"),
            Expr::Lit(lit) => writeln!(self, "Expr::Lit({lit:?})"),
            Expr::Paren(expr) => {
                writeln!(self, "Expr::Paren")?;
                self.with_indent(|this| this.located(expr))
            }
            Expr::TypeAnnotation(expr, r#type) => {
                writeln!(self, "Expr::TypeAnnotation")?;
                self.with_indent(|this| {
                    this.located(expr)?;
                    this.located(r#type)
                })
            }
            Expr::FunCall(callee, args) => {
                writeln!(self, "Expr::FunCall")?;
                self.with_indent(|this| {
                    this.located(callee)?;
                    for arg in *args {
                        this.located(arg)?;
                    }
                    Ok(())
                })
            }
            Expr::FunExpr(params, body) => {
                writeln!(self, "Expr::FunExpr")?;
                self.with_indent(|this| {
                    for param in *params {
                        this.located(param)?;
                    }
                    this.located(body)?;
                    Ok(())
                })
            }
            Expr::FunType(params, body) => {
                writeln!(self, "Expr::FunType")?;
                self.with_indent(|this| {
                    for param in *params {
                        this.located(param)?;
                    }
                    this.located(body)?;
                    Ok(())
                })
            }
            Expr::FunArrow(domain, codomain) => {
                writeln!(self, "Expr::FunArrow")?;
                self.with_indent(|this| {
                    this.located(domain)?;
                    this.located(codomain)
                })
            }
            Expr::Do(stmts, expr) => {
                writeln!(self, "Expr::Do")?;
                self.with_indent(|this| {
                    for stmt in *stmts {
                        this.stmt(stmt)?;
                    }
                    if let Some(expr) = expr {
                        this.located(expr)?;
                    }
                    Ok(())
                })
            }
            Expr::If(cond, then, r#else) => {
                writeln!(self, "Expr::If")?;
                self.with_indent(|this| {
                    this.located(cond)?;
                    this.located(then)?;
                    this.located(r#else)
                })
            }
            Expr::Match(scrut, cases) => {
                writeln!(self, "Expr::Match")?;
                self.with_indent(|this| {
                    this.located(scrut)?;
                    for case in *cases {
                        this.located(case)?;
                    }
                    Ok(())
                })
            }
        }
    }

    fn match_case(&mut self, case: &MatchCase) -> fmt::Result {
        writeln!(self, "MatchCase")?;
        let MatchCase { pat, expr } = case;
        self.with_indent(|this| {
            this.located(pat)?;
            this.located(expr)
        })
    }

    fn stmt(&mut self, stmt: &Stmt) -> fmt::Result {
        match stmt {
            Stmt::Let(binding) => {
                writeln!(self, "Stmt::Let")?;
                self.with_indent(|this| this.located(binding))
            }
            Stmt::Expr(expr) => {
                writeln!(self, "Stmt::Expr")?;
                self.with_indent(|this| this.located(expr))
            }
            Stmt::Command(command) => {
                writeln!(self, "Stmt::Command")?;
                self.with_indent(|this| this.command(command))
            }
        }
    }

    fn command(&mut self, command: &Command) -> fmt::Result {
        match command {
            Command::Check(expr) => {
                writeln!(self, "Stmt::Check")?;
                self.with_indent(|this| this.located(expr))
            }
            Command::Eval(expr) => {
                writeln!(self, "Stmt::Eval")?;
                self.with_indent(|this| this.located(expr))
            }
        }
    }

    fn pat(&mut self, pat: &Pat) -> fmt::Result {
        match pat {
            Pat::Error => writeln!(self, "Pat::Error"),
            Pat::Underscore => writeln!(self, "Pat::Underscore"),
            Pat::Var(name) => writeln!(self, "Pat::Var({name:?})"),
            Pat::Lit(lit) => writeln!(self, "Pat::Lit({lit:?})"),
            Pat::Paren(pat) => {
                writeln!(self, "Pat::Paren")?;
                self.with_indent(|this| this.located(pat))
            }
            Pat::TypeAnnotation(pat, r#type) => {
                writeln!(self, "Pat::TypeAnnotation")?;
                self.with_indent(|this| {
                    this.located(pat)?;
                    this.located(r#type)
                })
            }
        }
    }

    fn fun_param(&mut self, param: &FunParam) -> fmt::Result {
        let FunParam { plicity, pat } = param;
        writeln!(self, "FunParam({plicity:?})")?;
        self.with_indent(|this| this.located(pat))
    }

    fn fun_arg(&mut self, arg: &FunArg) -> fmt::Result {
        let FunArg { plicity, expr } = arg;
        writeln!(self, "FunArg({plicity:?})")?;
        self.with_indent(|this| this.located(expr))
    }

    fn let_binding(&mut self, binding: &LetBinding) -> fmt::Result {
        writeln!(self, "LetBinding")?;
        let LetBinding { pat, init } = binding;
        self.with_indent(|this| {
            this.located(pat)?;
            this.located(init)
        })
    }

    fn file(&mut self, file: &File) -> fmt::Result {
        writeln!(self, "File")?;
        self.with_indent(|this| {
            for stmt in file.stmts {
                this.stmt(stmt)?;
            }
            Ok(())
        })
    }
}

impl<T: Display> Display for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} @ {}", self.range, self.data)
    }
}

impl Display for File<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).file(self) }
}

impl Display for Expr<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).expr(self) }
}

impl Display for MatchCase<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).match_case(self) }
}

impl Display for Stmt<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).stmt(self) }
}

impl Display for Command<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).command(self) }
}

impl Display for LetBinding<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).let_binding(self) }
}

impl Display for Pat<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).pat(self) }
}

impl Display for FunArg<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).fun_arg(self) }
}

impl Display for FunParam<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).fun_param(self) }
}
