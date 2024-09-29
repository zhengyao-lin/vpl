NAME = chain
TARGET = chain
SOURCE = $(wildcard src/*.rs)
MAIN = src/main.rs

CARGO_DEPS = base64
VERUS_DEPS = parser polyfill vest
VERUS_FLAGS = --no-lifetime # Temporary fix for https://github.com/verus-lang/verus/issues/1288

include ../dep.mk
