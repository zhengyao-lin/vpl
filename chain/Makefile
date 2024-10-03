NAME = chain
TARGETS = chain

CARGO_DEPS = macros base64 clap thiserror libcrux
VERUS_DEPS = parser polyfill vest vpl

# Temporary fix for https://github.com/verus-lang/verus/issues/1288
# TODO: this skips the lifetime check for proof-mode code
VERUS_FLAGS = --no-lifetime

include ../dep.mk
