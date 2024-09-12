use std::fmt;
use std::fmt::Write;

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

    pub fn expr(&mut self, expr: Located<&Expr>) -> fmt::Result {
        write!(self, "{:?} @ ", expr.range)?;
        match expr.data {
            Expr::Error => writeln!(self, "Expr::Error"),
            Expr::Var(name) => writeln!(self, "Expr::Var({name:?})"),
            Expr::Bool(b) => writeln!(self, "Expr::Bool({b:?})"),
            Expr::Number(n) => writeln!(self, "Expr::Number({n:?})"),
            Expr::Char(c) => writeln!(self, "Expr::Char({c:?})"),
            Expr::String(s) => writeln!(self, "Expr::String({s:?})"),
            Expr::Paren(expr) => {
                writeln!(self, "Expr::Paren")?;
                self.with_indent(|this| this.expr(*expr))
            }
            Expr::FunCall { callee, args } => {
                writeln!(self, "Expr::FunCall")?;
                self.with_indent(|this| {
                    this.expr(*callee)?;
                    for arg in *args {
                        this.fun_arg(arg.as_ref())?;
                    }
                    Ok(())
                })
            }
            Expr::FunExpr { params, body } => {
                writeln!(self, "Expr::FunExpr")?;
                self.with_indent(|this| {
                    for param in *params {
                        this.fun_param(param.as_ref())?;
                    }
                    this.expr(*body)?;
                    Ok(())
                })
            }
            Expr::FunType { params, body } => {
                writeln!(self, "Expr::FunType")?;
                self.with_indent(|this| {
                    for param in *params {
                        this.fun_param(param.as_ref())?;
                    }
                    this.expr(*body)?;
                    Ok(())
                })
            }
            Expr::FunArrow { domain, codomain } => {
                writeln!(self, "Expr::FunArrow")?;
                self.with_indent(|this| {
                    this.expr(*domain)?;
                    this.expr(*codomain)
                })
            }
            Expr::Let { binding, body } => {
                writeln!(self, "Expr::Let")?;
                self.with_indent(|this| {
                    this.let_binding(*binding)?;
                    this.expr(*body)
                })
            }
        }
    }

    pub fn pat(&mut self, pat: Located<&Pat>) -> fmt::Result {
        write!(self, "{:?} @ ", pat.range)?;
        match pat.data {
            Pat::Error => writeln!(self, "Pat::Error"),
            Pat::Underscore => writeln!(self, "Pat::Underscore"),
            Pat::Var(name) => writeln!(self, "Pat::Var({name:?})"),
            Pat::Paren(pat) => {
                writeln!(self, "Pat::Paren")?;
                self.with_indent(|this| this.pat(*pat))
            }
        }
    }

    fn fun_param(&mut self, param: Located<&FunParam>) -> fmt::Result {
        write!(self, "{:?} @ ", param.range)?;
        writeln!(self, "FunParam")?;
        self.with_indent(|this| {
            this.pat(param.data.pat.as_ref())?;
            if let Some(ty) = &param.data.r#type {
                this.expr(ty.as_ref())?;
            }
            Ok(())
        })
    }

    fn fun_arg(&mut self, arg: Located<&FunArg>) -> fmt::Result {
        write!(self, "{:?} @ ", arg.range)?;
        writeln!(self, "FunArg")?;
        self.with_indent(|this| this.expr(arg.data.expr.as_ref()))?;
        Ok(())
    }

    fn let_binding(&mut self, binding: Located<&LetBinding>) -> fmt::Result {
        write!(self, "{:?} @ ", binding.range)?;
        writeln!(self, "LetBinding")?;
        self.with_indent(|this| {
            this.pat(binding.data.pat.as_ref())?;
            if let Some(ty) = &binding.data.r#type {
                this.expr(ty.as_ref())?;
            }
            this.expr(binding.data.expr.as_ref())
        })
    }
}

impl<'text, 'surface> fmt::Debug for Located<Expr<'text, 'surface>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).expr(self.as_ref()) }
}

impl<'text, 'surface> fmt::Debug for Located<Pat<'text, 'surface>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Printer::new(f).pat(self.as_ref()) }
}
