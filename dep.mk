##########################################################################
### Makefile to compile Verus project with external cargo dependencies ###
##########################################################################

# Uses these variables (for example):
#   NAME = Name of the crate (e.g. vpl, parser)
#   TARGET = Target executable name (e.g. vpl, libparser.rlib)
#   SOURCE = All source files used for monitoring changes (e.g. $(wildcard src/*.rs) $(wildcard src/*.pl))
#   MAIN = Main file passed to Verus (e.g. src/main.rs)
#   CARGO_DEPS = Rust dependencies added with `cargo add` (e.g. peg clap thiserror tempfile)
#   VERUS_DEPS = Verus dependency paths (e.g. vest). For each dep in VERUS_DEPS, we expect $(dep).rlib and $(dep).verusdata to exist
#   TEST_TARGETS = List of custom test targets

# Recursive wildcard from https://stackoverflow.com/questions/2483182/recursive-wildcards-in-gnu-make/18258352#18258352
rwildcard=$(foreach d,$(wildcard $(1:=/*)),$(call rwildcard,$d,$2) $(filter $(subst *,%,$2),$d))

SOURCE = $(call rwildcard,src,*.rs)
# Append sources of VERUS_DEPS to SOURCE
SOURCE += $(foreach dep,$(VERUS_DEPS),$(call rwildcard,../$(dep)/src,*.rs))

# If $(TARGET) ends in rlib, pass some additional flags to Verus
ifeq ($(suffix $(TARGET)),.rlib)
	LIB_FLAGS = --crate-type=lib
else
	LIB_FLAGS =
endif

.PHONY: debug
debug: target/debug/$(TARGET)

.PHONY: release
release: target/release/$(TARGET)

# Build each dependency in CARGO_DEPS
.PHONY: rust_deps-%
rust_deps-%: $(foreach dep,$(CARGO_DEPS),force-target/%/lib$(dep).rlib)
	@mkdir -p target/$*

# Bulid each dependency in VERUS_DEPS
.PHONY: verus-deps-%
verus-deps-%:
	@for dep in $(VERUS_DEPS); do \
		pushd ../$$dep; \
		echo "Building Verus dependency $$dep"; \
		rlib=target/$*/lib$$dep.rlib; \
		make $* || (echo "Fail to compile dependency $$dep"; exit 1) && \
		if [ ! -f $$rlib ] || [ ! -f $$rlib.verusdata ]; then \
			echo "Cannot find external Verus library $$rlib (or $$rlib.verusdata)"; \
			exit 1; \
		fi && \
		popd; \
    done

# The main verus command to run for TARGET
# Should be used in a context where $* is bound to either "debug" or "release"
# Each dependency <dep> in CARGO_DEPS is mapped to verus argument --extern <dep>=target/<release/debug>/deps/lib<dep>-*.<rlib|dylib>
# Each dependency <dep> in VERUS_DEPS is mapped to verus argument
#     --extern <dep>=../<dep>/target/<release/debug>/lib<dep>.rlib
#     --import <dep>=../<dep>/target/<release/debug>/lib<dep>.rlib.verusdata
VERUS_COMMAND = \
	verus $(MAIN) $(LIB_FLAGS) --crate-name $(NAME) \
		-L dependency=target/$*/deps \
		$(foreach dep,$(CARGO_DEPS),--extern $(dep)=$(firstword $(wildcard target/$*/deps/lib$(dep)-*.rlib) $(wildcard target/$*/deps/lib$(dep)-*.dylib))) \
		$(foreach dep,$(VERUS_DEPS),-L dependency=../$(dep)/target/$*/deps) \
		$(foreach dep,$(VERUS_DEPS),-L dependency=../$(dep)/target/$*) \
		$(foreach dep,$(VERUS_DEPS),--extern $(dep)=../$(dep)/target/$*/lib$(dep).rlib --import $(dep)=../$(dep)/target/$*/lib$(dep).rlib.verusdata) \
		--compile $(if $(filter release,$*),-C opt-level=3) \
		-o $@ --export $@.verusdata \
		$(VERUS_FLAGS)

# Build the main target
target/%/$(TARGET): rust_deps-% verus-deps-% $(SOURCE)
	$(VERUS_COMMAND)

# Build a test binary
target/%/test-$(TARGET): rust_deps-% verus-deps-% $(SOURCE)
	$(VERUS_COMMAND) --test

.PHONY: test
test: target/debug/test-$(TARGET) $(TEST_TARGETS)
	target/debug/test-$(TARGET)

# Named this way to avoid overlapping with the main target
force-target/debug/lib%.rlib: Cargo.toml
	cargo build --package=$*

force-target/release/lib%.rlib: Cargo.toml
	cargo build --package=$* --release

.PHONY: clean
clean:
	cargo clean
