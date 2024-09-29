NAME = parser
TARGET = libparser.rlib
SOURCE = $(wildcard src/*.rs) $(wildcard src/common/*.rs) $(wildcard src/asn1/*.rs) $(wildcard src/x509/*.rs)
MAIN = src/lib.rs

CARGO_DEPS = der base64 paste macros
VERUS_DEPS = vest polyfill
VERUS_FLAGS =

include ../dep.mk

# Same as debug but with parser trace enabled
debug-trace: VERUS_FLAGS += --cfg parser_trace
debug-trace: debug
