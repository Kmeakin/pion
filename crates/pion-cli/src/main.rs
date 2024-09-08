use clap::Parser;

#[derive(Debug, Parser)]
pub enum Command {
    Check {},
}

fn main() {
    let cmd = Command::parse();
    match cmd {
        Command::Check {} => todo!(),
    }
}
