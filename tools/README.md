# tools/: term generators for machine checks

These Python scripts *generate* CaTT terms, which are then checked by the certified Agda checker (`src/CaTTExp/Check.agda`). The Python side is not trusted. Each generated module asks the Agda checker to infer the term's type, and asserts by `refl` that the inferred type is the stated one. If Agda typechecks the module, the term is a genuine CaTT derivation of that type.

- `catt.py`: a small CaTT kernel. It uses the same de Bruijn-level syntax as `Syntax.agda` and provides pasting contexts from trees, unbiased composites, binary composites and whiskerings, and substitutions found by unification. Its `infer` mirrors the Agda checker and is used to fail fast.
- `rc2.py`: Theorem A of `notes/relative-coherence.md` (RC(2)) as an algorithm. It covers contexts whose 1-skeleton is acyclic. It implements sequentialization, the normal form of whiskered generators (Lemma G), canonical path cells (Lemma P), and exchange moves (Lemma E).
  - *Not implemented:* positional pull-back for 1-skeleta with cycles. The proof covers them; the tool does not. So the Eckmann–Hilton example is not generated.
- `rc_oracle.py`: the relative-coherence oracle `rc(G, A, t, u)` (`notes/rc-generator.md`). Strict images by Steiner tableaux; identity; one-coherence answers on globular supports in every dimension (r9 Response 2); RC(1) in every context; Theorem A through `rc2.py`. `write_table` writes `src/CaTTExp/Generated/<T>.agda` (an `Oracle` for `CaTTExp.RCOracle`) and `<T>Check.agda`, whose `all-certified : certified? entries ≡ true` runs the certified checker on every answer.
- `agda_bridge.py`: normalizes a closed Agda expression with `agda --interaction` and parses the printed normal form into `catt.py` values (contexts, types, terms, lists, `Query`, `Maybe Query`). `rc_loop.py`: answers the rc calls of a construction whose later calls contain earlier answers (`ConeRC.firstMiss`), by rounds of normalize, answer, extend the table. Example: `CATT_SRC=<src> RC_WORKDIR=<dir> python3 tools/rc_loop.py RCCone2 "map (λ Γ → ConeRC.firstMiss (TBL orRC rc1) Γ) TermCones2.twoTerm" CaTTExp.Cones CaTTExp.ConeRC CaTTExp.ConesExamples`.
- `steiner.py`: the strict layer of the r9 Response 15 descent: Steiner complex of a context, the strong-Steiner test, cells of ν(K), Steiner's cut formula and strict words (r9 Response 2). `rc_lift.py`: word lifting at prescribed raw poles, given lower-rank comparisons. `steiner.Sd` enumerates Sd(c). `rc_heur.py`: local rank ≥ 3 reductions for `rc` on nonglobular supports (top-slot congruence, identity slots, distribution, rebracketing, abstraction to a pasting context); see `notes/rc-generator.md` §3.
- `ladder.py`: the cylinder `L(Q)` of a chain, BMOSV-style lifts of binary composites, and the associator's naturality 3-cell (C1b).
- `unitor.py`, `exch_test.py`: the other generated checks.
- `rc3_square.py`, `rc3_pair.py`: checks for RC(3) on the lax square (`notes/relative-coherence.md` §7.4–7.5) and the generalised active-column factorisation on the composable-pair cylinder.
- `rc3_wedge.py`: the cut-vertex reduction for Y = {x, f, g} on x → y → z (§7.6). `rc3_chain.py`: the round-5 chain-cylinder constructors for x₀ → ⋯ → x₃ (§7.7). Run either with `emit` to write its module, or with `neg` to write a negative control (`NegWedge.agda`, `NegChain.agda`, not committed) that Agda must reject.
- `rc3_grid.py`: RC(3) on the 2 × 2 grid (`notes/relative-coherence.md` §7.8): the strict-cell classification, head shapes, normal forms, every multiplication μ (with block merges), the exchange, the raw law (12) and a mixed interchange 4-cell. `rc3_d2d2.py`: the 2-skeleton of the D² ∗₀ D² cylinder (§7.9): the factorisation lemma, normal forms, every multiplication (with the exchange χ_M), transfers, and (36) on the full cylinder. `rc3_r6.py`: constructions from three verified round-4/6 answers (§7.10). `rc3_exch.py`: general exchange in dimension 2 (§7.11): event posets and the square/hexagon homotopy basis checked fibre by fibre on grids up to 3 × 3 and other small contexts, plus the block-form hexagon and square coherences. Each takes `emit` or `neg` like `rc3_wedge.py`.
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
| `ExchangeLaws` | block-form hexagon and square 4-coherences; `rc3_exch.py` also checks event posets and the square/hexagon homotopy basis on grids up to 3 × 3 (§7.11) | ~4 s |
| `GrayIntervalDisc` | CT for I ⊗ Dⁿ, n ≤ 4, by the suspension construction of `notes/conjectures/answered/canonical-gray-terms-2026-11-19.md`: Fam(I ⊗ Dⁿ) is a well-formed context and all 536 cells of dimension ≤ n + 2 (identity towers included) have T(c) : T(∂⁻c) → T(∂⁺c) literally (`ct_suspension.py`; `neg` writes a control that swaps one boundary and is rejected) | ~15 min on first run (including the core library) |
| `GrayDiscDiscTransfer` | CT(D² ⊗ D²) by transfer from the Gray cube: the substitution σ realising Φ : I⊗I⊗I → (D²⊗D²)((0,0),(1,1)), with the two endpoint panels sent to the D² ∨₀ D² exchange coherence; Γ′ (25 variables) well formed and all 49 non-identity cube cells transferred (`ct_transfer_d2d2.py`; `neg` writes a rejected control) | ~2.5 min |
| `RoundSixChecks` | cone r4 (2), (14); gray-contexts r6 (3), (6), (11), (24); naturality r6 (11), (14), (18), (20), routes of (19) (`rc3_r6.py`) | ~21 s |

Negative control: swapping source and target in `expected` of `UnitorNaturality` makes Agda reject the module (`3 != 1 of type Nat … refl`).

To regenerate and check:

```
cd tools && python3 -c "import rc3_square; rc3_square.emit_module()" && python3 unitor.py && python3 exch_test.py && python3 ladder.py && python3 -c "import ladder; ladder.emit_assoc()"
cd ../src && LC_ALL=C.UTF-8 agda +RTS -M12G -RTS CaTTExp/Generated/All.agda
```

`tensor_atom_tableau.py` checks the tensor-atom tableau formula (4) of `notes/conjectures/answered/gray-tensor-of-contexts-rule-2026-11-18.md` for p, q ≤ 4 (Steiner sign convention). Run `python3 tools/tensor_atom_tableau.py`; it prints the number of mismatches (0).

`fibration_pentagon_counterexample.py` re-checks the base-dimension-4 counterexample to the relative Gray-generator presentation (`notes/conjectures/answered/fibration-presentations-all-dimensions-2026-11-19.md`, Followup §1): it enumerates the 2-cells gt⁴ ⇒ t (18 paths, 8 cells modulo interchange), every contextual 3-generator instance (8 edges), and shows that no positive 3-cell starting at R lies over the short side of the pentagon. Run `python3 tools/fibration_pentagon_counterexample.py`.

`partial_cylinder_steiner.py` re-checks `notes/conjectures/answered/relative-coherence-all-dimensions-2026-11-19.md`, Followup 3 §1: for every globular pasting diagram with at most N edges (default 5) and every up-closed Y, the partial-cylinder complex K_Y satisfies ∂∂ = 0, is strongly loop-free and unital, and its atoms ⟨Ix⟩ have the iterated boundaries (3)–(5). Run `python3 tools/partial_cylinder_steiner.py 6` (197 diagrams, 25,378 pairs, about 7 s).

`tier_complex_check.py` re-checks the combinatorial core of `notes/conjectures/answered/homotopy-polygraphs-2026-11-19.md`, Followup 2 §2: for random progressive one-colour string diagrams whose components all meet the boundary, every connected component of the complex of tier encodings (products of permutohedra) has the Z/2 homology of a point; two floating scalars give a circle. Run `python3 tools/tier_complex_check.py <seed>` (about 2,000 boundary-connected diagrams per run, 0 failures).

`order_partition_dismantle.py` checks Lemma D of `notes/hpol-obligations.md`: for a random finite poset P and a maximal element m, the poset Π(P) of compatible ordered antichain partitions dismantles onto Π(P − m) by the stated beat-point order and partners. Run `python3 tools/order_partition_dismantle.py <seed> <trials> [maxn]` (600 posets with at most 5 elements, 0 failures).

`layering3_check.py` tests the dimension-3 analogue (`notes/homotopy-polygraphs.md` §4): for random marked 3-dimensional diagrams (planar diagram plus 3-steps, including identity sources and targets) it enumerates the poset of layerings with one regular slice between 3-tiers, checks it is a partial order, and computes Z/2 homology after removing beat points. Run `python3 tools/layering3_check.py <seed> <trials> [p|a]` (`p`: 3-positive steps only). `fibre_analysis` checks the Quillen fibres over 3-tier sequences; `meshes_k`/`analyse_k` add interchange slices and show that bounded truncations are not homotopy-correct.

## Sharing-aware certificates (`dag_cert.py`)

`dag_cert.py` exports a typing problem Γ ⊢ w : A as a certificate for the DAG checker of `src/CaTTExp/Dag/` (design and soundness argument in `notes/dag-certificates.md`): a hash-consed item table plus untrusted typing and free-variable claims, each checked once by `refl` without unfolding any term. It is for answers too large to check as trees. `gen_dag_trie.py` and `gen_dag_natmap.py` generate `Dag/Trie.agda` and `Dag/NatMap.agda`.

`dag_horiz3_q2.py ANSWER.pkl OUTDIR [N PREFIX]` certifies the relative-coherence answer to Horiz3 query (2) (`fixtures/rc_horiz3_query2.txt.gz`; the answer pickle is kept by the cone thread, not in git). The full certificate (779,079 items) is about 82 MB of data, so it is not committed. With `N PREFIX` it certifies a subterm with at most N distinct subterms instead; the committed tests `DagSmall` (N = 164) and `DagMid` (N = 20000) were made this way and are checked from `CaTTExp/Generated/All.agda`.
