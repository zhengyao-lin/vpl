target/debug/vpl: cargo src/*.rs
	verus src/main.rs \
		-L dependency=target/debug/deps \
		--extern peg="$(wildcard target/debug/deps/libpeg-*.rlib)" \
		--extern clap="$(wildcard target/debug/deps/libclap-*.rlib)" \
		--extern thiserror="$(wildcard target/debug/deps/libthiserror-*.rlib)" \
		--compile -o target/debug/vpl

.PHONY: cargo
cargo: Cargo.toml
	cargo build --package=peg --package=clap --package=thiserror

.PHONY: clean
clean:
	cargo clean
