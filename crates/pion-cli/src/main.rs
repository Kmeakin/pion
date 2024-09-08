use std::io::Read;
use std::str::FromStr;

use camino::Utf8PathBuf;
use clap::Parser;
use codespan_reporting::files::Files;

#[derive(Debug, Parser)]
#[command(version)]
pub enum Command {
    Check { paths: Vec<PathOrStdin> },
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

fn check(paths: &[PathOrStdin]) {
    let mut diagnostics = Vec::new();
    let mut writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        codespan_reporting::term::termcolor::ColorChoice::Auto,
    );
    let mut files = codespan_reporting::files::SimpleFiles::new();
    let mut file_ids = Vec::new();
    let config = codespan_reporting::term::Config::default();

    for path in paths {
        match path.read() {
            Ok(text) => {
                let file_id = files.add(path.name(), text);
                file_ids.push(file_id);
            }
            Err(err) => eprintln!("Error reading {}: {}", path.name(), err),
        }
    }

    let bump = bumpalo::Bump::new();

    for file in file_ids {
        let text = files.source(file).unwrap();
        let tokens = pion_lexer::lex(text);
        let (_expr, diags) = pion_parser::parse_expr(file, tokens, &bump);
        diagnostics.extend(diags);
    }

    for diagnostic in diagnostics {
        codespan_reporting::term::emit(&mut writer, &config, &files, &diagnostic)
            .expect("Unable to emit diagnostic");
    }
}

fn main() {
    let cmd = Command::parse();
    match cmd {
        Command::Check { paths } => check(&paths),
    }
}
