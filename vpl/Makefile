NAME = vpl
TARGETS = vpl libvpl.rlib

CARGO_DEPS = peg clap thiserror tempfile
VERUS_DEPS = polyfill
TEST_TARGETS = test-features test-hammurabi

include ../dep.mk

.PHONY: test
test-features: target/debug/vpl
	@for test in tests/*.pl; do \
		printf "%s: " $$test; \
        target/debug/vpl $$test go || exit 1; \
    done

.PHONY: test-hammurabi
test-hammurabi: target/debug/vpl
	@for test in tests/hammurabi/*.pl; do \
		printf "%s: " $$test; \
        target/debug/vpl $$test go || exit 1; \
    done
