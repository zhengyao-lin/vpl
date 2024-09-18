TARGET = x509
SOURCE = $(wildcard src/*.rs) $(wildcard src/asn1/*.rs)
MAIN = src/main.rs

CARGO_DEPS = der
VERUS_DEPS = vest polyfill
VERUS_FLAGS = --rlimit 50

include ../dep.mk
