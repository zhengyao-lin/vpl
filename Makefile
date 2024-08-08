# Add external dependencies here
DEPS = peg clap thiserror

.PHONY: debug
debug: target/debug/vpl

.PHONY: release
release: target/release/vpl

# Each dependency <dep> is mapped to verus argument --extern <dep>=target/<release/debug>/deps/lib<dep>-*.rlib
target/%/vpl: $(foreach dep,$(DEPS),target/%/lib$(dep).rlib) src/*.rs
	verus src/main.rs \
		-L dependency=target/$*/deps \
		$(foreach dep,$(DEPS),--extern $(dep)=$(firstword $(wildcard target/$*/deps/lib$(dep)-*.rlib))) \
		--compile -o target/$*/vpl

target/debug/lib%.rlib: Cargo.toml
	cargo build --package=$*

target/release/lib%.rlib: Cargo.toml
	cargo build --package=$* --release

.PHONY: test
test: debug
	for test in tests/*.pl; do \
		echo $$test; \
        target/debug/vpl $$test go || exit 1; \
    done

.PHONY: clean
clean:
	cargo clean
