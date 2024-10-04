check:
    cargo clippy
    typos

build:
    cargo build

test:
    cargo test

fuzz target:
    cargo fuzz run -O -a {{target}}
