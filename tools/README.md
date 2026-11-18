# tools/: term generators for machine checks

These Python scripts *generate* CaTT terms, which are then checked by the certified Agda checker (`src/CaTTExp/Check.agda`). The Python side is not trusted. Each generated module asks the Agda checker to infer the term's type, and asserts by `refl` that the inferred type is the stated one. If Agda typechecks the module, the term is a genuine CaTT derivation of that type.

- `catt.py`: a small CaTT kernel. It uses the same de Bruijn-level syntax as `Syntax.agda` and provides pasting contexts from trees, unbiased composites, binary composites and whiskerings, and substitutions found by unification. Its `infer` mirrors the Agda checker and is used to fail fast.
- `rc2.py`: Theorem A of `notes/relative-coherence.md` (RC(2)) as an algorithm. It covers contexts whose 1-skeleton is acyclic. It implements sequentialization, the normal form of whiskered generators (Lemma G), canonical path cells (Lemma P), and exchange moves (Lemma E).
  - *Not implemented:* positional pull-back for 1-skeleta with cycles. The proof covers them; the tool does not. So the Eckmann–Hilton example is not generated.
- `ladder.py`: the cylinder `L(Q)` of a chain, BMOSV-style lifts of binary composites, and the associator's naturality 3-cell (C1b).
- `unitor.py`, `exch_test.py`: the other generated checks.
- `rc3_square.py`, `rc3_pair.py`: checks for RC(3) on the lax square (`notes/relative-coherence.md` §7.4–7.5) and the generalised active-column factorisation on the composable-pair cylinder.
- `rc3_wedge.py`: the cut-vertex reduction for Y = {x, f, g} on x → y → z (§7.6). `rc3_chain.py`: the round-5 chain-cylinder constructors for x₀ → ⋯ → x₃ (§7.7). Run either with `emit` to write its module, or with `neg` to write a negative control (`NegWedge.agda`, `NegChain.agda`, not committed) that Agda must reject.
- `rc3_grid.py`: RC(3) on the 2 × 2 grid (`notes/relative-coherence.md` §7.8): the strict-cell classification, head shapes, normal forms, every multiplication μ (with block merges), the exchange, the raw law (12) and a mixed interchange 4-cell. `rc3_d2d2.py`: the 2-skeleton of the D² ∗₀ D² cylinder (§7.9): the factorisation lemma, normal forms, every multiplication (with the exchange χ_M), transfers, and (36) on the full cylinder. `rc3_r6.py`: constructions from three verified round-4/6 answers (§7.10). Each takes `emit` or `neg` like `rc3_wedge.py`.
- `emit_agda.py`: writes a module with hash-consed definitions (one Agda definition per distinct subterm).

Generated modules (`src/CaTTExp/Generated/`, entry point `All.agda`). They are not imported by `Everything.agda`, because they take minutes to check.

| Module | Statement checked | Agda time |
|---|---|---|
| `UnitorNaturality` | Left unitor's naturality 3-cell at depth 2 over the lax square | ~50 s |
| `ExchangeTwoBigons` | Theorem A with one exchange move: `(a ∗₀ g) ∗₁ (f′ ∗₀ b) ⇛ (f ∗₀ b) ∗₁ (a ∗₀ g′)` | ~3 min |
| `AssociatorNaturality` | Associator's naturality 3-cell over the fully selected 3-chain (the ladder theorem's example) | ~17 min, about 10 GB (`+RTS -M12G`) |
| `LaxSquareRC3` | Checks toward RC(3) on the lax square: active-column factorisations, an exchange 4-term, the mixed law (11); generalised factorisations on the composable-pair cylinder (`rc3_square.py`, `rc3_pair.py`) | ~11 s |
| `WedgeRC3` | Y = {x, f, g} on x → y → z: two-column factorisations, frame normalisers, exchange coherences and a 4-term between the exchange routes, horizontal fold (`rc3_wedge.py`) | ~13 s |
| `ChainCylinderRC3` | Full cylinder of x₀ → ⋯ → x₃: letters, normal forms N_w, μ for every split, fold 4-cells, frame factorisations (`rc3_chain.py`) | ~36 s |
| `GridRC3` | 2 × 2 grid: 20 normal forms, 50 multiplications (8 block merges), exchange and its compatibility 4-term, raw law (12), Z₃, ζ, an interchange 4-cell, 61 frames (`rc3_grid.py`) | ~3 min |
| `TwoDiscCylinderRC3` | D² ∗₀ D² cylinder 2-skeleton: 67 normal forms, 203 multiplications (4 through χ_M), χ_M, transfers, 64 frames; (36) on the full cylinder (`rc3_d2d2.py`) | ~10 min |
| `RoundSixChecks` | cone r4 (2), (14); gray-contexts r6 (3), (6), (11), (24); naturality r6 (11), (14), (18), (20), routes of (19) (`rc3_r6.py`) | ~18 s |

Negative control: swapping source and target in `expected` of `UnitorNaturality` makes Agda reject the module (`3 != 1 of type Nat … refl`).

To regenerate and check:

```
cd tools && python3 -c "import rc3_square; rc3_square.emit_module()" && python3 unitor.py && python3 exch_test.py && python3 ladder.py && python3 -c "import ladder; ladder.emit_assoc()"
cd ../src && LC_ALL=C.UTF-8 agda +RTS -M12G -RTS CaTTExp/Generated/All.agda
```
