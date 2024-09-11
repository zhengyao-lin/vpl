.PHONY: debug
debug:
	cd vest && make debug
	cd x509 && make debug
	cd vpl && make debug

.PHONY: release
release:
	cd vest && make release
	cd x509 && make release
	cd vpl && make release

.PHONY: clean
clean:
	cd vest && make clean
	cd x509 && make clean
	cd vpl && make clean
