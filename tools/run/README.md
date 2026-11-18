# Compiled runs of the certified checker

Some certified terms are too large for Agda's typecheck-time normaliser (it
has no sharing, and the builders duplicate subterms). For those, this folder
runs the *same* certified checker (`CaTTExp.Check`, via
`CaTTExp.Free.Builders.checks`) compiled with GHC. A `true` means the
checker returned a typing derivation at run time. This is weaker than a
typecheck-time certificate only in that it trusts the MAlonzo compiler and
GHC; the checker, the builders and the terms are the ones in `src/`.

These files are not part of the `--safe` library: they postulate two IO
primitives (`putStrLn`, `>>`) and are compiled outside it.

## `RunAssoc.agda`

The depth-2 naturality 3-cell of the associator
(`src/CaTTExp/Free/AssociatorDepth2.agda`). From the repository root:

```
LC_ALL=C.UTF-8 agda --no-libraries --guardedness -i src -i tools/run \
  --compile-dir=/tmp/cattexp-build --compile tools/run/RunAssoc.agda
LC_ALL=C.UTF-8 /tmp/cattexp-build/RunAssoc
```

Expected output (2026-11-18, Agda 2.6.3, GHC 9.4.7; under a second):

```
size of K-α (syntax nodes): 364219
L well typed: true
R well typed: true
step 1: true
...
step 7: true
all steps done
K-α checks with its computed type: true
computed type is L → R: true
negative control, reversed type R → L: false
consistency control, left unitor K-λ: true
```
