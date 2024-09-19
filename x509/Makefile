TARGET = x509
SOURCE = $(wildcard src/*.rs) $(wildcard src/common/*.rs) $(wildcard src/asn1/*.rs) $(wildcard src/x509/*.rs)
MAIN = src/main.rs

CARGO_DEPS = der macros
VERUS_DEPS = vest polyfill
VERUS_FLAGS = --rlimit 50

include ../dep.mk
