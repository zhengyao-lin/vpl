TARGET = libvest.rlib
SOURCE = $(wildcard src/*.rs) $(wildcard src/regular/*.rs) $(wildcard src/secret/*.rs)
MAIN = src/lib.rs

CARGO_DEPS =
VERUS_DEPS =

include ../dep.mk

# all:
# 	verus --crate-type=lib src/lib.rs --multiple-errors 5 --compile -o vest.rlib --export vest.verusdata

# clean:
# 	rm vest.verusdata
# 	rm libvest.rlib
# 	cargo clean
