use std::io::{IsTerminal, Read};
use std::str::FromStr;

use camino::Utf8PathBuf;
use clap::Parser;
use codespan_reporting::files::Files;

#[derive(Debug, Parser)]
#[command(version)]
pub enum Command {
    Check { path: PathOrStdin },
}

#[derive(Clone, Debug)]
pub enum PathOrStdin {
    File(Utf8PathBuf),
    Stdin,
}

impl PathOrStdin {
    fn read(&self) -> std::io::Result<String> {
        let text = match self {
            Self::File(path) => std::fs::read_to_string(path)?,
            Self::Stdin => {
                let mut buf = String::new();
                std::io::stdin().read_to_string(&mut buf)?;
                buf
            }
        };

        #[allow(
            clippy::as_conversions,
            reason = "usize <= u128, so no truncation occurs"
        )]
        if text.len() as u128 > u128::from(u32::MAX) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "input files must be less than 4 GiB",
            ));
        }

        Ok(text)
    }

    fn name(&self) -> &str {
        match self {
            Self::File(path) => path.as_str(),
            Self::Stdin => "<stdin>",
        }
    }
}

impl FromStr for PathOrStdin {
    type Err = <Utf8PathBuf as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "-" => Ok(Self::Stdin),
            _ => Ok(Self::File(Utf8PathBuf::from(s))),
        }
    }
}

fn check(path: &PathOrStdin) {
    let stderr = std::io::stderr();

    let color = match stderr.is_terminal() {
        true => codespan_reporting::term::termcolor::ColorChoice::Auto,
        false => codespan_reporting::term::termcolor::ColorChoice::Never,
    };

    let mut stderr = codespan_reporting::term::termcolor::StandardStream::stderr(color);

    let mut files = codespan_reporting::files::SimpleFiles::new();
    let config = codespan_reporting::term::Config::default();

    let file_id = match path.read() {
        Ok(text) => files.add(path.name(), text),
        Err(err) => {
            eprintln!("Error reading {}: {}", path.name(), err);
            return;
        }
    };

    let mut emit = |diagnostic| {
        codespan_reporting::term::emit(&mut stderr, &config, &files, &diagnostic)
            .expect("Unable to emit diagnostic");
    };

    let bump = bumpalo::Bump::new();
    let text = files.source(file_id).unwrap();
    let tokens = pion_surface::lex::lex(text);
    let (file, diagnostics) = pion_surface::parse::parse_file(file_id, tokens, &bump);

    for diagnostic in diagnostics {
        emit(diagnostic);
    }

    let mut interner = pion_interner::Interner::default();
    let mut elab = pion_elab::Elaborator::new(&bump, &mut interner, file_id);
    elab.stmts(file.stmts);
    elab.report_unsolved_metas();
    let (diagnostics, command_output) = elab.finish();

    for diagnostic in diagnostics {
        emit(diagnostic);
    }

    for command_output in command_output {
        println!("{command_output}");
    }
}

fn main() {
    let cmd = Command::parse();
    match cmd {
        Command::Check { path } => check(&path),
    }
}
