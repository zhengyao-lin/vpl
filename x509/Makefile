all:
	verus src/main.rs \
		--import vest=../vest/vest.verusdata \
		--extern vest=../vest/libvest.rlib \
		--compile -o x509

src/asn1.rs: src/asn1.vest
	../vest-dsl/target/release/vest-dsl src/asn1.vest
