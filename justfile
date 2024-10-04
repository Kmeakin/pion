check:
    cargo check
    typos

build:
    cargo build

test:
    cargo test

fuzz target:
    cargo fuzz run -O -a {{target}}
