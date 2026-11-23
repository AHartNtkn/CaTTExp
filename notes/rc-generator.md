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
1. Done (2026-11-22). Identities (the globular filler on the disk `Dsk (dim A)`, pulled back along `dskSub t A`), dimension 1 between variables (`GraphFillerTotal.total`), and globular contexts (`FillTotal.fill-total`, after deciding `Glob Γ` and comparing normal forms). Totality is proved for identities (`rcP-id`) and dimension 1 (`rcP-1`: equal paths give an answer). Totality on globular contexts needs completeness of `glob?` and fuel independence of `sameNf?`, still to do.
2. Support restriction (a strengthening lemma), so that a query is answered in the context its support generates.
3. The local reductions of §3 (congruence, identity slots, distribution, rebracketing, loop cancellation, abstraction) as proved constructions.
4. Theorem A (dimension 2), then the descent.
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
| n ≥ 3, nonglobular support: local reductions | `tools/rc_heur.py`, not part of Response 15 and not complete. (a) Top-slot congruence: in a composition head of dimension N, the arguments at N-dimensional positions are normalized recursively, all changes carried by one coherence over the pasting context with each changed top variable a given a copy a′ and a cell a → a′. (b) Identity slots: an argument with identity strict image and equal ends is compared with the identity coherence. (c) Distribution: H(c₁ ∗ … ∗ c_k) → H(c₁) ∗ … ∗ H(c_k) when the slot is the only top position of H, one coherence over H's context with that leaf split into k siblings. (c′) Interchange: the same for a head with several top slots, no two composable along N−1, each split into k factors. (d) Rebracketing of equal factor lists over a column context. (d′) Loop cancellation: H(f₁) ∗ … ∗ H(f_k) against the identity, when the slot composite has identity value and equal ends: regroup into H(f₁ ∗ … ∗ f_k), compare the slot with the identity, then H(1) with the identity. (e) Abstraction: maximal coherence subterms of dimension ≤ d become fresh variables (subterms that a head's type computes are kept), and the query is answered on the smaller context, by one coherence if it is a pasting context. Budget of 400 calls per query. | done; closes the cones of the 3-dimensional unitor and vertical-composite shapes (§7) |
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

## 7. Log

- 2026-11-22. Two more reductions in `rc_heur.py`: interchange over several top slots, and loop cancellation. With them, the cone thread's sequentialized horizontal split (`ConeRCS`, branch `claude/project-thread-b03ys3`) gets past its round-16 query (7 s). That query had the two events adjacent on both sides, t a literal prefix of u, and u ending in a whiskered coherence followed by its inverse. In the unsplit `ConeRC` query, and in the first version of the split (stuck at round 17), an event action is separated from the other event by 25 old caps (whiskered Theorem A answers). Matching that needs depth-one naturality of those caps (§6 item 1), so the cone side reorders instead. Self-test case `rank3-cancel-loop` added.
- 2026-11-21. First 3-dimensional cones. `src/CaTTExp/ConeShapesThree.agda` has three shapes ending in a 4-cell: the unitor θ : A ⇛ A ∗₂ 1 over D³ (`Unit3`, B19's smallest open case), the vertical composite (`VComp3`) and the horizontal composite (`Horiz3`). With the rank-3 reductions of `rc_heur.py`, `Unit3` and `VComp3` close in 3 rounds with 3 answers (729, 1,609 and 3,746 nodes): `Generated/RCConeThree` is certified by `RCConeThreeCheck` (6 s) and `Generated/RCThreeCones` checks `all (λ Γ → okM (ConeRC.cone (RCConeThree.rc orRC rc1) Γ)) closedThree ≡ true` by `refl` (9 s). `Horiz3` stops at round 4 (§6 item 1). Also: `catt.infer` memoizes by object identity instead of hashing whole terms (the round-4 query, 107,191 nodes unshared, went from minutes to about 1 s), and a failing rank ≥ 3 call returns `None` instead of raising.
- 2026-11-21. Cocones: `Generated/RCCoconeTwo` (12 answers for `CoconeRC.firstMiss` on the same shapes, 4 rounds) is certified by `RCCoconeTwoCheck` (4.7 min). `Generated/RCTwoCones` checks by `refl` that every cone and every cocone context of `TermCones2.twoTerm`, built with the tables over `rc1`, passes the certified checker (15 min including loading both tables; in `Generated/All.agda`, not in `Everything.agda`).
- 2026-11-21. The cone table `Generated/RCConeTwo` (12 answers, 1.2 MB, made with `rc_dim2.py`) is certified: `RCConeTwoCheck` passes in 5.5 min. With it layered over `rc1`, `all (λ Γ → okM (ConeRC.cone (RCConeTwo.rc orRC rc1) Γ)) TermCones2.twoTerm ≡ true` passes by `refl` on the PR #373 branch in 5.8 min, so every 2-dimensional cone context goes through the certified checker. Loading the table alone takes 4.7 min.
- 2026-11-21. Against the cone thread's `ConeRC.firstMiss` (branch of PR #373), all 8 shapes of `TermCones2.twoTerm` close in 4 rounds with 12 answers (8, 3, 1, 0 misses), every answer from the cases above.
- 2026-11-21. Steps 0 (interface, trust model, bridge) and the n ≤ 2 and globular cases. A round trip (Python → query module → Agda normal form → Python → table → certified checker) passes; the checker accepts all answers of the test table at their queried types (`RCTestCheck`-style module, about 4 min for three answers of rank 2 and 1).
