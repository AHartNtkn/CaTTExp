# An executable relative-coherence generator

*Thread "Make the relative-coherence construction executable" (RCGEN, `cmsg_018pe2CvdFGDdsWgn8Tjn5gbR69G9NBUpWh76aBRV4TJg2`), started 2026-11-21. Ledger row C1c.*

The goal is a program that, given a context Δ, a type A and parallel terms t, u : A with equal strict images, returns a term w : t → u. The source is the search-free construction of r9 Response 15 (`conjectures/answered/relative-coherence-all-dimensions-r9-2026-11-20.md`, verified; independent check and the U_{k−2} repair in `relative-coherence.md` §7.14–7.15). Consumers: the rc-parametric cone module `src/CaTTExp/ConeRC.agda` (B19, N^cone), and later cylinders (C1, Conjecture N) and the Gray templates (D3).

This is internal tooling (project rule 8). It makes no surface or ergonomic decisions.

## 1. Trust model

The generator is untrusted. Correctness of every answer comes from the certified checker `CaTTExp.Check`:
- `tools/rc_oracle.py` re-checks each answer with the Python kernel `tools/catt.py` before returning it.
- The answers reach Agda as a table. `CaTTExp.RCOracle.certified?` runs the certified checker on every entry, and each generated table has a companion module `<Table>Check` with `all-certified : certified? entries ≡ true` proved by `refl`.
- `CaTTExp.RCOracle.certify` turns any oracle into one that returns typing derivations, `Maybe (Σ Tm λ w → Γ ⊢tm w ∶ arr A t u)`, by running the checker on the answer.

So a bug in the generator can only make an answer missing, never wrong.

*Note (2026-11-22, ledger S19, S20).* Re-checking each answer is how this research tool establishes finite instances. It is not the design for the system. There, an extension is trusted through a formalized proof of its correctness, without a re-check. The target here is a formalized RC procedure (spec §5.1) proved to return well-typed terms.

*Formalized procedure (S20 (i)).* `CaTTExp.RCProc` defines `rcP : Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Σ w. Γ ⊢tm w ∶ arr A t u)`. Each answer carries a derivation built by a proved lemma; nothing is run through the checker. Plan and state:
1. Done (2026-11-22). Identities (the globular filler on the disk `Dsk (dim A)`, pulled back along `dskSub t A`), dimension 1 between variables (`GraphFillerTotal.total`), and globular contexts (`FillTotal.fill-total`, after deciding `Glob Γ` and comparing normal forms). Totality is proved for identities (`rcP-id`), dimension 1 (`rcP-1`: equal paths give an answer) and, since 2026-11-23, globular contexts (`rcP-glob`: on a globular Γ, typed t, u with the same normal form at any fuels are answered; from completeness of `glob?` and fuel independence of `sameNf?` via `NfFuel.nf-det`). Stages 2–3 are owned by the thread "Prove the RC generator correct in Agda" (from 2026-11-23).
2. Done (2026-11-23). Support restriction, `CaTTExp.RCProc.Support` (any signature and side condition). For a keep-predicate closed under dependencies it builds the restricted context Γ′, a renaming ρ and an inclusion ι with Γ ⊢sub ι ∶ Γ′, and proves the partial substitution lemma `ptm[]` (only the variables a term uses need typed images), so t[ρ], u[ρ] are typed in Γ′, and `pull`: an answer w in Γ′ gives w[ι] : t → u in Γ (renaming then including fixes kept syntax, `idOn-*`). The support is the dependency closure `close` of the variables of A, t, u, proved down-closed (`dc-close`). `RCProc.rcS` answers on the support and falls back to `rcP`; it keeps rcP's totality (`rcS-id`, `rcS-1`, `rcS-glob`) and answers every query whose support is globular with one normal form (`rcS-globSupp`), the "globular support, every n" row of §3. `RCProc.SupportExamples` checks by evaluation that the interchange query, asked in a non-globular context, is refused by `rcP` and answered by `rcS`.
3. The local reductions of §3 (congruence, identity slots, distribution, rebracketing, loop cancellation, abstraction) as proved constructions. *Partial (2026-11-23):* Lemma P of Theorem A (Step 1), in every dimension: `rcP` has a graph-context case (`viaGraph`, the higher chain filler `GraphFillerTotal.Higher.totalN`, total by `rcP-graph` after proving `isGraph` complete), so through support restriction every query of dimension ≥ 2 whose support has no variable of dimension ≥ 2 is answered (`rcS-graphSupp`; checked by evaluation in `RCProc.SupportExamples`).
4. Theorem A (dimension 2), then the descent.
   *Stage 3 plan (thread "Prove the RC generator correct in Agda", 2026-11-23).* Each step is a construction with its typing proved once, for all inputs; totality comes last.
   - 3a. Glue, `CaTTExp.RCProc.Glue`: `transA` (vertical composite of two answers, by `DerivedBoundary.rwT` at j = 0) and `pullA` (an answer over P pulled back along a typed θ : Δ → P). Done.
   - 3b. Top-slot congruence (local reduction (a), and the functoriality cells of Step 2): a coh over `ctxOf T` whose top 2-variables carry 3-cells, as one coh over the raised tree; needs ⊢ps of raised trees and ∂± of the raised tree equal to the two inclusions of T. Shared with GCTX (S20 (ii) step 4, which reuses it). *In progress (2026-11-23):* `CaTTExp.PsRaise`, stated for `GrayCtx.Lift.raiseT` itself, simulates the two runs of the pasting-context builder (original tree and raised tree) and proves, for every tree with at least one child and every flag list, that both inclusions incl∓ are typed substitutions (`inclM-wf`, `inclP-wf`), and that, when every flagged leaf has dimension k (`TopOK`), `srcVars k` and `tgtVars k` of the raised context are the images of those of the original under incl⁻ and incl⁺, as lists (`src-incl`, `tgt-incl`); checked by evaluation on the 2-disc (`PsRaiseExamples`). Further, when τ has dimension ≤ k and some leaf is flagged, the raised context has dimension k + 1 (`dim-raise`), and ∂⁻/∂⁺ of the raised context are exactly the images of all of τ's levels under incl⁻/incl⁺ (`src-raise`, `tgt-raise`, via `full-src`/`full-tgt`: at or above a pasting context's dimension, srcVars/tgtVars are all its levels). For arbitrary flags (a flagged leaf below the top dimension, where the coh over the raised tree is a full coherence; needed by GCTX's lift engine), incl∓ are variable substitutions (`inclM-var`, `inclP-var`), a term using every level of τ has images using every level in the image of incl∓ (`fv-inclM`, `fv-inclP`, from the generic `CaTTExp.VarSubFv`), and every level of the raised context is in one of the two images or is a new cell incl⁻ w → incl⁺ w (`cover-incl`); checked on a 2-cell followed by a raised 1-cell. *Congruence cell done (2026-11-23),* `CaTTExp.PsRaiseCongr`: for c = coh P (arr B s u) id over P = ctxOf τ, with flags at dimension k ≥ dim P and some leaf flagged, if incl∓ agree on the variables of arr B s u then R ⊢ty arr A^ c⁻ c⁺ with A^ = A[incl⁻], c∓ = c[incl∓] (`cong-ty`), and coh R (arr A^ c⁻ c⁺) is an operation (`cong-side`), so `cong-cell` types the cell c[incl⁻ ∘ σ^] → c[incl⁺ ∘ σ^] for every Γ ⊢sub σ^ ∶ R. For an operation c the agreement holds by proof (`agree-op`: incl∓ differ only at flagged leaves, `PsRaise.diff-incl`, and an operation's type uses only ∂⁻P ∪ ∂⁺P, whose cells have dimension < dim P, `src-small`/`tgt-small`), giving `cong-cell-op` with no extra hypothesis. Checked on the unary composite over D² (`PsRaiseCongrExamples`). For a coherence c (full type), incl∓ do not agree and the congruence is not a cell between c⁻ and c⁺; that case is GCTX's lifted-type construction.
   - 3c. Sequentialization (Step 2), from 3b and associators over vertical chains.
   - 3d. Lemma G normal forms (column contexts P_g, H_g), using Lemma P (already total via `rcS-graphSupp`).
   - 3e. Lemma E (the exchange cell over E) and sorting a 2-path by exchange moves.
   - 3f. Totality of Theorem A: equal strict images (the free 2-category on the 2-polygraph) imply exchange-equivalent 2-paths, stated against `CaTTExp.Strict`.
   - 3g. The remaining local reductions of §3 ((b)–(e)) as constructions with typing proofs; abstraction (e) is `pullA` along the abstracting substitution.
Until a case is proved, its answers still come from the certified tables above.

Reproducing the checks:

```
python3 tools/rc_selftest.py emit      # Python checks, writes Generated/RCSelfTest{,Check}.agda
cd src && LC_ALL=C.UTF-8 agda CaTTExp/Generated/RCSelfTestCheck.agda          # accepted (about 20 s)
cd .. && python3 tools/rc_selftest.py neg   # negative control: first entry's ends swapped
cd src && LC_ALL=C.UTF-8 agda CaTTExp/Generated/RCSelfTestNegCheck.agda       # must fail with
#   false != true of type Bool
#   when checking that the expression refl has type certified? entries ≡ true
```

The Neg modules are not committed. `entryOK` and `certify` check the answer's typing in the given Γ but not `Γ ⊢ctx` itself; consumers check their whole contexts (ConeRC runs `checkCtx`), so this is harmless there, and a consumer that does not should check Γ separately. *Totality* (an answer for every well-typed equal-image query on a strong-Steiner context) is a separate theorem. For the dimensions covered below it is the cited theorem, provided the implementation follows the proof; it is not machine-checked.

## 2. Interface

Agda (`src/CaTTExp/RCOracle.agda`):

```
Oracle = Ctx → Ty → Tm → Tm → Maybe Tm          -- = ConeRC.RC
record Query : Set   -- query Γ A t u
record Entry : Set   -- entry Γ A t u w
fromTable : List Entry → Oracle
certify   : Oracle → (Γ : Ctx) (A : Ty) (t u : Tm) → Maybe (Σ Tm (λ w → Γ ⊢tm w ∶ arr A t u))
certified? : List Entry → Bool
```

Python (`tools/rc_oracle.py`): `rc(G, A, t, u)` with the same meaning, over `catt.py`'s de Bruijn-level syntax (identical to `CaTTExp.Syntax`). The context is passed plain: the oracle recomputes strict images itself, so consumers pass no extra structure (no marker for the cone vertex).

Bridge (`tools/agda_bridge.py`, `tools/rc_loop.py`): normalize a closed Agda expression with `agda --interaction`, parse the printed normal form into `catt.py` values, answer, and write `src/CaTTExp/Generated/<Table>.agda`. `rc_loop.py` iterates for constructions whose later calls contain earlier answers (ConeRC's `firstMiss`): normalize the list of first misses, answer them, extend the table, repeat.

## 3. What is implemented

| Case | Construction | Status |
|---|---|---|
| strict images | Steiner tableau of π(t): top chain plus the images of the two faces (`strict_image`). Exact on strong-Steiner contexts. | done |
| t ≡ u | identity coherence over the disc | done |
| support | every query is answered on the dependency-closed support of (A, t, u) and pulled back along the inclusion | done |
| globular support, every n | r9 Response 2, "comparisons on a globular support": if the support is a pasting context up to renumbering (positions totally ordered by s(x) < x < t(x)), one coherence head t → u | done |
| n = 1, every context | RC(1): the coherence over the chain context of the common path (`relative-coherence.md` §1) | done |
| common factors, every n | if t and u share a literal prefix or suffix of top-cut factors (flattened through composition coherences over column contexts), compare the middles recursively and whisker; each rebracketing is one coherence over a column context (`peel`) | done |
| n = 2, every context with acyclic 1-skeleton | Theorem A (`relative-coherence.md` §2): `tools/rc_dim2.py`, which reuses `tools/rc2.py` but puts the two Lemma E windows in canonical form item by item (Lemma G(ii) per column coherence, Lemma P per run) and whiskers bare 2-variables directly (Lemma G(i)) instead of normalizing through functoriality cells | done; on the exchange of two bigons the answer drops from 421,593 to about 98,000 nodes (unshared) |
| strict words | Steiner's cut formula (`steiner-nu-freeness` answer §1.2) at the decomposition index, atoms sorted by a linear extension with ties broken by variable index (`steiner.strict_word`) | done; evaluates back to the input cell on every cell of the test contexts |
| word lifting | r9 Response 2: lift a strict word at prescribed raw poles by whiskering comparisons of lower rank (`rc_lift.lift_at`) | done |
| identity towers | r9 Response 2: attach a fresh n-globe at the final vertex, compare u ∗₀ z with v ∗₀ z, collapse, and strip the padding with the disc terms P_j, L_j, M_j (`rc_lift.via_globe`, `rc_lift.PLM`) | done; used once the intrinsic case (§4 step 3) exists |
| n ≥ 3, nonglobular support: local reductions | `tools/rc_heur.py`, not part of Response 15 and not complete. (a) Top-slot congruence: in a composition head of dimension N, the arguments at N-dimensional positions are normalized recursively, all changes carried by one coherence over the pasting context with each changed top variable a given a copy a′ and a cell a → a′. (b) Identity slots: an argument with identity strict image and equal ends is compared with the identity coherence. (c) Distribution: H(c₁ ∗ … ∗ c_k) → H(c₁) ∗ … ∗ H(c_k) when the slot is the only top position of H, one coherence over H's context with that leaf split into k siblings. (c′) Interchange: the same for a head with several top slots, no two composable along N−1, each split into k factors. (d) Rebracketing of equal factor lists over a column context. (d′) Loop cancellation: H(f₁) ∗ … ∗ H(f_k) against the identity, when the slot composite has identity value and equal ends: regroup into H(f₁ ∗ … ∗ f_k), compare the slot with the identity, then H(1) with the identity. (d″) Event interchange: after a common prefix, t has [f, g] and u has [g′, f′] with f′ = f[y := Z] for a context cell e : y → Z; the answer is the naturality square of f along e at y (`rc_nat.square`), whiskered by the rest of t, with its ends compared to t and u recursively; then the cap sweep `rc_nat.sweep_rc`. (f) Event steps (2026-11-23, toward Response 3): change of writing for an event factor, several events at once, with a marker per composite source (faces rebuilt from the types); sorting by naturality squares in both directions; splitting factors with several events (nested or mixed with coherences); dropping identity top slots; separating a loop y : p → p into p → p′; distributing a head over nested vertical composites. A step that raises fails alone. (e) Abstraction: maximal coherence subterms of dimension ≤ d become fresh variables (subterms that a head's type computes are kept), and the query is answered on the smaller context, by one coherence if it is a pasting context. Budget of 400 calls per outermost query, shared by nested calls (`rc_nat` fillers call `rc`), with answers memoized within it. | done; closes the cones of the 3-dimensional unitor and vertical-composite shapes (§8) |
| n ≥ 3, the descent | r9 Response 15 | not yet (§4); the horizontal composite of two 3-globes needs it (event sorting, Response 3) |
| Sd(c) | nontrivial embedded pasting arities of total c, deduplicated by generated subcategory, ordered by inclusion (`steiner.Sd`); descent step 6, strict side | done; partial order checked on two bigons (3 elements), a 2 × 2 grid (29) and 3-dimensional pastings |

## 4. The descent for n ≥ 3: plan

Response 15 is a lexicographic induction on (n, n − l, h, |S|). The pieces, in the order they will be built, each tested on its own before the next:

1. **Strict layer.** Steiner complex of a context, the strong-Steiner test, cells of ν(K) in a closed support, cut decompositions, intrinsic rank h, and the strict expression of r9 Response 2 (tableau cut formula).
2. **Word lifting** (Response 2): lift a strict word at prescribed raw poles, given comparisons of lower rank (the oracle itself, recursively). Together with the marked-globe reduction and the padding terms P_j, L_j, M_j this reduces identity towers to intrinsic values.
3. **Base case h = n** (Response 3): intrinsic events, elementary arrows, change of writing, sorting by swaps of incomparable events. This generalizes the exchange step of Theorem A.
4. **Staircases** (Responses 6 and 15 step 1): partial cylinders of pasting arities with an up-closed marking, the collapsed interval cell, and its lift at the two staircases; specialization to evaluated terms by rank-then-subterm recursion.
5. **Transfer and inverses** (Response 15 step 2, Response 4): transport a comparison between two interpretations with equal strict projection; serialization of inverses inside a piece.
6. **Sd(c) and the cut projections.** The poset of nontrivial embedded pasting arities containing c, carriers p_x, the pieces V_θ, Campion's projections U_{k−2} and U′_{k−1} with least extensions, the single-cut chain poset with Arone's coreflection. The order-theoretic bookkeeping is already machine-checked in `CaTTExp.CarrierGluing`; this step computes the actual finite data.
7. **Piece lifts and gluing**: J, R and the bridges JR ⇒ id in U_θ; the three gluing rules D(P); the low-variable refinement R_l, M_l.

Each step adds cases to `rc`; earlier cases are not replaced, since they give smaller terms.

## 5. Answer size

Agda pays for the *unshared* size of a term: the certified checker and `==Tm` traverse trees, and Agda's printed normal forms (which the bridge reads) unfold every shared subterm. Two consequences.

- **Bridge rounds use placeholders.** While `rc_loop.py` iterates, the table it gives Agda answers query i with the fresh variable `var (1000000 + i)`. ConeRC treats answers as opaque (`raw w a b` takes its type from a, b), so the printed queries stay small, and substituting the real answers back gives exactly the queries the real table meets. The real table is written at the end.
- **Theorem A answers are large.** On the 12 queries of the 2-dimensional cone shapes the answers range from 422 to about 500,000 nodes. The cost is in sequentialization (nested functoriality cells), not in exchange. Reducing it is follow-up work in this thread (§6).

## 6. Open items (owned by RCGEN, ledger C1c)

1. The descent for n ≥ 3 on nonglobular supports (§4 steps 3–5, 7; step 6 has its strict side). The first query that needs it: the cone over `ConeShapesThree.Horiz3` (θ : A ∗₀ B ⇛ C over two 3-globes), whose round-4 query moves the 3-cell composite past old caps (Response 3 event sorting with change of writing). The local reductions return nothing on it.
4. Certification time grows with unshared answer size: the 7-entry table that included the Horiz3 rounds (four Theorem A answers of 106,371 nodes) had not finished `RCConeThreeCheck` after 60 min, while the 3 answers for the two closed shapes certify in 6 s.
2. Smaller RC(2) answers: sequentialize without nesting functoriality cells (one cell per level, canonical runs merged at every level).
3. Agda time for large tables: measure, and if needed emit tables whose entries share definitions across answers (they already do within one module).

## 7. Generators with composite faces (S20 stage 4, 2026-11-23)

Query (2) of Horiz3 (the coherence-only cap-block comparison of round 21) is a rank-3 comparison of two coherence-only tracks (22 and 25 top-cut factors) in a 15-variable context with two generators whose targets are composites: `x12 : x11 ⇒ x10 ∗₀ x2` and `x14 : x13 ⇒ x11 ∗₀ x6`. The context is strong Steiner, checked in Python (`steiner.Complex.is_strong_steiner`), not yet certified in Agda.

**The marker step, stated.** Let g : s → c be a generator whose face c is a composite term of type B. Put Γ_g = Γ with g replaced by C : B and g′ : s → C, and σ_g : Γ_g → Γ the substitution C ↦ c, g′ ↦ g.
- *Claim (correctness).* If t = σ_g(t′) and u = σ_g(u′) with t′, u′ parallel in Γ_g, and w′ : t′ → u′ in Γ_g, then σ_g(w′) : t → u in Γ. This holds because substitution preserves typing.
- *Claim (termination).* Γ_g has one fewer generator with a composite face, so iterating the step terminates.
- *Normalization.* To apply the step to a track t = f₁ ⋯ f_p with boundaries B₀, …, B_p, choose bundled forms B̂ᵢ = σ_g(B̂′ᵢ) with comparisons Jᵢ : Bᵢ → B̂ᵢ (rank n − 1, by induction on rank). Then compare each conjugate Jᵢ₋₁⁻¹ fᵢ Jᵢ with σ_g of a track in Γ_g.

**Why it does not reach query (2).** The normalization needs every boundary Bᵢ to have a bundled form, meaning a rank-(n − 1) term of Γ_g whose image is comparable to Bᵢ. That fails as soon as another generator acts on a proper part of c:
- in query (2), x4 : x2 ⇒ x3 acts on x2 inside c = x10 ∗₀ x2, and x8 : x6 ⇒ x7 acts on x6 inside x11 ∗₀ x6;
- both endpoints of query (2) whisker x4 and x8 inside those composites;
- in Γ_g the marker C is free, so no 2-cell relates C ∗₀ y to x10 ∗₀ x3. The endpoints therefore have no bundled form at all. Checked with `rc_heur._rebuilder`: none of the four endpoint lifts typechecks.

So the marker step, though correct and terminating, applies only under the hypothesis that **no generator acts on a proper part of a marked face** (otherwise no bundled forms exist). Query (2) violates it. This is the same obstruction that made r9 Response 4 fold free faces instead (§7.12 of `relative-coherence.md`). The fold route was tried on query (2) (`tools/rc_fold.py`). Its squares recurse into cylinder contexts of 35 to 87 variables, and each level shows new shapes:
- several simultaneous events with decomposed composite sources;
- identity slots, loops, and nested vertical composites.

Steps were added for each (`rc_heur`). All captured sub-queries answer, some in 15 to 45 minutes, but the inner fold's squares still stop at a composition filler. Adding a step per shape is not a method.

**The general step is the descent, not a new heuristic.** Response 15 (`conjectures/answered/relative-coherence-all-dimensions-r10-2026-11-21.md`, verified) constructs comparisons of parallel raw terms with equal strict value by structural recursion in every finite strong-Steiner context. Its well-founded measure is (n, n − l, h, |S|), so it is terminating and correct on paper. Query (2)'s context is strong Steiner, so Response 15 answers it, with no fold and no marker. No open question is involved, so no new prompt is needed. What is missing is the implementation of §4 steps 4, 5 and 7 (staircases, transfer and inverses, piece lifts and gluing). Step 6 has its strict side (`steiner.Sd`). Stage 4 now implements those steps directly from Response 15. The fold code and the shape steps stay as fast paths for the cases they already answer; they are not part of the general argument.

**Single-piece step, implemented (2026-11-23, `tools/rc_descent.py`).** When both inputs lie in one piece U_θ (the literal expansion of Response 15: heads whose substitution entries all have labels in θ are expanded, every other subterm is a generator with a label of proper support), `piece` does the following:
- builds W, the pasting context of the globular arity θ, with a strict label on every variable;
- builds J : W → Γ, choosing literal generators of the inputs where they fit (the target face first), otherwise word lifts;
- builds R : U_θ → W, lifting the unique W-cell over each label (unique because arities are monic);
- compares R(t) with R(u) in W, where the comparison is globular;
- transfers the result back along bridges x↑ for the generators with JR(x) ≠ x. The bridges are recursive equal-image calls on the proper supports. The lax and oplax squares come from `rc_nat`, and moved faces are stripped at the top cut and at the cut below it (`strip_right`, `strip_lower`, which use inverses and cancellations from `rc_inverse` and generic interchange coherences).

Results:
- On query (2) no gluing is needed: all 47 factors lie in the piece of the order 14, 12, 4, 8, one of the 15 elements of Sd(c).
- The comparison in W (11 variables) answers in 0.6 s.
- On the self-test it answers `rank3-cancel-loop`.
- The step sits in the `rc_heur` dispatch behind `DESCENT` (off by default).

**What still blocks query (2).** The inputs contain many rank-3 generators: whiskerings of inner coherences by raw 1-cells such as x10, x11 and x6, whose labels are outside θ. Their bridges are rank-4 equal-image calls on supports that still contain x12. Two ways of computing them both fail:
- Plain `rc` gives up on the first one after 54 s.
- The step itself, applied recursively, meets two obstacles. First, a wedge arity whose composite 1-pole moves, which the strips handle. Second, naturality fillers K(Q, B, Y′) for coherence heads with 40 to 70 variables, where Y′ contains moved lower-dimensional variables. The filler query in the cylinder Q↑Y′ (about 90 variables, h = n) did not finish in 15 minutes.

In Response 15 these fillers are themselves calls of the induction (step 1: the cylinder has G_{s+1}, so l′ > l), and the low variables are kept stationary by the adapted pieces R_l, M_l. Neither is implemented. So the missing piece is now precise: the l-component of the induction (adapted subdivisions, and staircases as recursive calls in partial cylinders).

## 8. Log

- 2026-11-23. `tools/rc_descent.py`: the single-piece step of Response 15 (§7). Query (2) is committed as `tools/fixtures/rc_horiz3_query2.txt.gz` with the driver `tools/rc_query2.py` (pieces holding both inputs, and the in-arity comparison time; `full` runs the whole step, which does not finish yet). It answers the self-test's `rank3-cancel-loop` and the in-arity comparison of query (2) (0.6 s). Query (2) itself is still open: the bridges of its whiskered rank-3 generators need the l-component of the induction (adapted pieces, cylinder staircases as recursive calls), which is not implemented.
- 2026-11-23. Stage 4, query (2): new `rc_heur` steps (change of writing for several simultaneous events with markers built from the factors' types, sorting in both directions, splitting nested and mixed events, identity-slot removal, loop separation, distribution over nested vertical composites); identity-keyed memos for `infer`, free variables and strict images, sharing-preserving substitution, one call budget and one answer memo per outermost query (a slow sub-query went from 91 s to 11 s, and a run that exhausted 15 GB now stays under 5 GB). Query (2) is still unanswered. The marker step cannot reach it, and the fold route does not converge (§7). Next: implement the descent proper (§4 steps 4, 5, 7) from Response 15.
- 2026-11-23. `rc_heur` dispatches to (d″), the event-interchange step, and to the cone thread's cap sweep (`rc_nat.sweep_rc`) before abstraction. Horiz3 round 21's interchange comparison ([Eτ, Eb] against [Ec, (σc₁)↑]) is answered in 0.1 s, and 15 s inside its whole factor list. The full round-21 query is still unanswered (464 s, 58 calls): the remaining piece is a coherence-only comparison of two different cap blocks with the same boundary, which needs the descent (S20 stage 4). All `rc_selftest.py` cases pass.
- 2026-11-22. Two more reductions in `rc_heur.py`: interchange over several top slots, and loop cancellation. With them, the cone thread's sequentialized horizontal split (`ConeRCS`, branch `claude/project-thread-b03ys3`) gets past its round-16 query (7 s). That query had the two events adjacent on both sides, t a literal prefix of u, and u ending in a whiskered coherence followed by its inverse. In the unsplit `ConeRC` query, and in the first version of the split (stuck at round 17), an event action is separated from the other event by 25 old caps (whiskered Theorem A answers). Matching that needs depth-one naturality of those caps (§6 item 1), so the cone side reorders instead. Self-test case `rank3-cancel-loop` added.
- 2026-11-21. First 3-dimensional cones. `src/CaTTExp/ConeShapesThree.agda` has three shapes ending in a 4-cell: the unitor θ : A ⇛ A ∗₂ 1 over D³ (`Unit3`, B19's smallest open case), the vertical composite (`VComp3`) and the horizontal composite (`Horiz3`). With the rank-3 reductions of `rc_heur.py`, `Unit3` and `VComp3` close in 3 rounds with 3 answers (729, 1,609 and 3,746 nodes): `Generated/RCConeThree` is certified by `RCConeThreeCheck` (6 s) and `Generated/RCThreeCones` checks `all (λ Γ → okM (ConeRC.cone (RCConeThree.rc orRC rc1) Γ)) closedThree ≡ true` by `refl` (9 s). `Horiz3` stops at round 4 (§6 item 1). Also: `catt.infer` memoizes by object identity instead of hashing whole terms (the round-4 query, 107,191 nodes unshared, went from minutes to about 1 s), and a failing rank ≥ 3 call returns `None` instead of raising.
- 2026-11-21. Cocones: `Generated/RCCoconeTwo` (12 answers for `CoconeRC.firstMiss` on the same shapes, 4 rounds) is certified by `RCCoconeTwoCheck` (4.7 min). `Generated/RCTwoCones` checks by `refl` that every cone and every cocone context of `TermCones2.twoTerm`, built with the tables over `rc1`, passes the certified checker (15 min including loading both tables; in `Generated/All.agda`, not in `Everything.agda`).
- 2026-11-21. The cone table `Generated/RCConeTwo` (12 answers, 1.2 MB, made with `rc_dim2.py`) is certified: `RCConeTwoCheck` passes in 5.5 min. With it layered over `rc1`, `all (λ Γ → okM (ConeRC.cone (RCConeTwo.rc orRC rc1) Γ)) TermCones2.twoTerm ≡ true` passes by `refl` on the PR #373 branch in 5.8 min, so every 2-dimensional cone context goes through the certified checker. Loading the table alone takes 4.7 min.
- 2026-11-21. Against the cone thread's `ConeRC.firstMiss` (branch of PR #373), all 8 shapes of `TermCones2.twoTerm` close in 4 rounds with 12 answers (8, 3, 1, 0 misses), every answer from the cases above.
- 2026-11-21. Steps 0 (interface, trust model, bridge) and the n ≤ 2 and globular cases. A round trip (Python → query module → Agda normal form → Python → table → certified checker) passes; the checker accepts all answers of the test table at their queried types (`RCTestCheck`-style module, about 4 min for three answers of rank 2 and 1).
