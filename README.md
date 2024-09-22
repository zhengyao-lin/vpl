Verified X.509 Certificate Validation
---

Work in progress.

## Verified X.509 Parser

Run `make` in `x509`. `target/debug/x509` will parse a PEM file read from stdin.

## Certified Prolog

Run `make` in `vpl`. Usage:
```
target/debug/vpl <Prolog source file> <entry query>
```

This will produce a list of intermediate goals that have been validated in the verified kernel.
For example, consider the following Prolog program:
```
node(n0).
node(n1).
node(n2).
node(n3).
node(n4).
edge(n3, n4).
edge(n2, n3).
edge(n1, n2).
edge(n0, n1).
connected(X, Y) :- edge(X, Y).
connected(A, B) :- edge(A, M), connected(M, B).
go :- connected(n0, n4).
```

The output of `vpl` is:
```
validated: edge(n0, n1)
validated: edge(n1, n2)
validated: edge(n2, n3)
validated: edge(n3, n4)
validated: connected(n3, n4)
validated: connected(n2, n4)
validated: connected(n1, n4)
validated: connected(n0, n4)
validated: go
```
Each line `validated: <Goal>` indicates that a proof of `<Goal>` has been validated in the verified kernel.
