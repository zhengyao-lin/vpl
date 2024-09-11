##########################################################################
### Makefile to compile Verus project with external cargo dependencies ###
##########################################################################

TARGET = vpl
SOURCE = $(wildcard src/*.rs) $(wildcard src/*.pl)
MAIN = src/main.rs

CARGO_DEPS = peg clap thiserror tempfile
VERUS_DEPS = polyfill

include ../dep.mk

.PHONY: test
test: debug
	@for test in tests/*.pl; do \
		printf "%s: " $$test; \
        target/debug/vpl $$test go || exit 1; \
    done

.PHONY: test-hammurabi
test-hammurabi: debug
	@for test in tests/hammurabi/*.pl; do \
		printf "%s: " $$test; \
        target/debug/vpl $$test go || exit 1; \
    done
