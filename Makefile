target/debug/vpl: target/debug/libpeg.rlib src/*.rs
	verus src/main.rs -L dependency=target/debug/deps --extern peg=target/debug/libpeg.rlib --compile -o target/debug/vpl

target/debug/libpeg.rlib:
	cargo build --package=peg

.PHONY: clean
clean:
	cargo clean
