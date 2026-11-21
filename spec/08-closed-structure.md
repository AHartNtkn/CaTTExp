# Chapter 8. Closed structure: the Gray biclosed rules

The ambient's Gray tensor and its two internal homs become object formers: A ⊗ B, A\C = Hom_lax(A, C) and C/A = Hom_oplax(A, C), for arbitrary objects. Their universal properties are coherence-style templates over a new **multimap** judgment. Nothing here adds a definitional equation or a universe, and the rules never change L's coherences (§8.6).

Names follow `notes/conventions.md` §3.2: A\C has evaluation (A, A\C ▸ C), taking the argument first; the "lax hom" [Θ, C] of earlier notes is C/⟦Θ⟧.

## 8.1 Judgments

**Rule.**
```
(GB-form)   Γ ⊢ A : ⋆    Γ ⊢ B : ⋆   ⟹   Γ ⊢ A ⊗ B : ⋆,   Γ ⊢ A\B : ⋆,   Γ ⊢ B/A : ⋆
Γ ⊢ t : (X₁, …, Xₙ ▸ Z)        n ≥ 0; a map X₁ ⊗ … ⊗ Xₙ → Z, the list never bracketed
```
- With n = 1 a multimap is an ambient 1-cell. With one representable input it is a diagram: (⟦Δ⟧ ▸ C) is a Δ-shaped diagram in C.
- A **time slot** is an input position holding a representable ⟦Θ⟧. (B, ⟦Dᵏ⟧ ▸ C) is a lax k-cell between maps B → C; (⟦Dᵏ⟧, B ▸ C) is an oplax one; a slot between two data inputs gives mixed cells. Faces are restrictions along ⟦s⟧, ⟦t⟧ : ⟦Dᵏ⁻¹⟧ → ⟦Dᵏ⟧.
- **Invertible cells** are the `inv` mark of chapter 3 at a time slot, realised as an extra slot in the rightmost gap all of whose cells are invertible.
- **Substitution** is planar, as in a planar multicategory. An L substitution σ : Θ′ → Θ restricts a time slot along ⟦σ⟧, so composition inside a one-hole hom is L's coherence with its side condition in V + S.
- **Sort discipline.** Representables are the probe sort. The output of a row, and every object variable in an output position, is non-representable (an atom, ⊗, \ or /). A context entry whose output is representable has only representable inputs.

**Status.** **Agda-checked** (`src/CaTTExp/Gray/Biclosed/Syntax`, `Typing`: formulas, multimap types, cell types with a gap and a mode, a checker; the collar term `glue` has a stated typing rule standing for an L composite not derived in Agda). **Source:** `notes/closed-structure.md` F.7.4 §1.

## 8.2 Corollas

**Rule.**
```
(GB-pair)   (U V : ⋆)  ⊢  m_{U,V} : (U, V ▸ U ⊗ V)
(GB-evℓ)    (A C : ⋆)  ⊢  e^ℓ_{A,C} : (A, A\C ▸ C)
(GB-evr)    (A C : ⋆)  ⊢  e^r_{A,C} : (C/A, A ▸ C)
(GB-probe)  ⊢  p_{Δ,Θ} : (⟦Δ⟧, ⟦Θ⟧ ▸ ⟦Δ ⊗ Θ⟧)      for pasting shapes Δ, Θ
(GB-pt)     ⊢  pt : ( ▸ ⟦D⁰⟧)
```
Δ ⊗ Θ in (GB-probe) is the Gray tensor of contexts (chapter 5, §5.3), and p is its pair of inclusions.

## 8.3 Rows, cuts and directed cuts

**Rows.** Each row is a restriction r : H → B between multimap types, sending x to its composite with the row's distinguished vertex.

| Row | H | B | r(x) |
|---|---|---|---|
| pair at slot i | (L, U⊗V, R ▸ Z) | (L, U, V, R ▸ Z) | x ∘ᵢ m_{U,V} |
| probe pair at slot i | (L, ⟦Δ⊗Θ⟧, R ▸ Z) | (L, ⟦Δ⟧, ⟦Θ⟧, R ▸ Z) | x ∘ᵢ p_{Δ,Θ} |
| unit at slot i | (L, ⟦D⁰⟧, R ▸ Z) | (L, R ▸ Z) | x ∘ᵢ pt |
| left evaluation | (Φ ▸ A\C) | (A, Φ ▸ C) | e^ℓ ∘ (1_A, x) |
| right evaluation | (Φ ▸ C/A) | (Φ, A ▸ C) | e^r ∘ (x, 1_A) |

A time slot in Φ stays in its gap: a cut never moves a directed time past the bound object.

**(GB-cut_{ρ,n}), for a row ρ and n ≥ 0.** The generic context Ctx(ρ, n) has a fresh object variable per formula of the row; b, an invertible n-ball of operations of type B; u, an (n−1)-sphere of type H (empty for n = 0); and a, the collar r(u) ⊨ b|_∂ (empty for n = 0). Admissible goals:
- **c_{ρ,n}**: the n-ball of type H with boundary u;
- **ε_{ρ,n}**: the invertible (n+1)-cell of type B from r(c_{ρ,n}) to b, with the collar adjoined.

At n = 0, c is currying (or factorization) and ε : r(c) ⊨ b. At n = 1 with b constant, the rule connects two lifts of the same b, which is uniqueness.

**(GB-dcut_{ρ,k}), for k ≥ 1 and a time slot ⟦Dᵏ⟧ at a fixed gap.** The generic context has the row's object variables; parallel u⁻, u⁺ of type H at ⟦Dᵏ⁻¹⟧ in that gap; b of type B at ⟦Dᵏ⟧ in the same gap; collars a^± : r(u^±) ⊨ b|_{∂^±} agreeing on the common boundary. Goals: d of type H at ⟦Dᵏ⟧ from u⁻ to u⁺, and an invertible comparison r(d) ⊨ b relative to a^±.

**Orientation.** The only directed goal is d, and its direction is inherited from the hypothesis b. No template has a directed goal oriented otherwise, so the rules admit no reverse cells.

**Side condition and decision procedure.** A goal is admissible iff, up to renaming of context variables, its context and type are one of the templates. Lemma GB-dec: the templates form finitely many families indexed by (row, slot, gap, n or k), bounded by the goal's size; matching is a finite comparison up to a bijection of variables; ε and comparison goals are tested by building r(c), with no search; restrictions along ⟦σ⟧ call L's side condition, decidable in every setting. Deciding whether an arbitrary sequent has *some* derivation is undecidable (r3 item 38), and the kernel never asks it.

**Example.**
- Fun^lax(C, D) for C the walking span is C\D, with evaluation (C, C\D ▸ D). A lax transformation α between F, G : B → C\D is (B, ⟦D¹⟧ ▸ C\D), which corresponds by the left row to (C, B, ⟦D¹⟧ ▸ D).
- The naive bijection (B ⊗ C, ⟦D¹⟧ ▸ D) ≅ (B, ⟦D¹⟧ ▸ C\D) is **not** derivable: the left row keeps the time slot after C. This matches the counterexample at B = C = D¹ that makes the naive all-levels rule unsound.
- In the context (h : (Q, X ▸ Z)), no template has the reverse of a square at a time slot as its goal.

**Semantics.** In Cat_ω, ⊗ is Campion's Gray tensor and \, / are its two closures (arXiv 2311.00205); the probe base is the Gray maps of pasting shapes. Every template is sound by Response 2's extension lemma (a row is an equivalence iff every relative disk lifts). **Exactness:** the free data model is initial among data models over the lax-grid model (Response 2, theorem (3)); naming c and ε is that reflection.

**Status.**
- Soundness and exactness: **proved** (verified researcher answer, `notes/conjectures/answered/gray-biclosed-coherence-r3-2026-11-20.md`, Response 2). Lemma GB-ext (element generators, probes as bound arguments, the L probe base through its interpretation): **proved** at argument level and independently checked (D7c, closed). Soundness of the combination depends on L's soundness in Cat_ω (E11).
- Lemma GB-dec, the templates, `admit?` sound and complete, `no-reverse` and `dir-needs-dir` for the template relation: **Agda-checked** (`Gray/Biclosed/Templates`). Every row, gap, mode and n gives well-formed contexts and goals: **Agda-checked** (`TemplatesTyped`, D7f). Closure under substitution and the sort discipline: **Agda-checked** (`Subst`, `Instances`, `SortDisc`, D7e). Soundness in every model of the abstract interface, with a nontrivial poset model: **Agda-checked** (`Soundness`, `PosetModel`). No reverse cell for the generic directed contexts: **Agda-checked** (`D7g`).
- Open: no reverse cell for directed **instances** in Agda (the instance criterion and the four-cube computation, D7g); the ∞-categorical initiality stays on paper; implementing the multimap judgment in the main checker.

**Source.** `notes/closed-structure.md` F.7.4 §2–4, §7; `notes/design-decisions.md` §3; ledger D7, D7c–D7g.

## 8.4 Derived rules

All of these are derived, none primitive:
- **(lhom):** [Θ, C] := C/⟦Θ⟧. Abstraction restricts φ : (⟦Δ⊗Θ⟧ ▸ C) by the probe-pair row to (⟦Δ⟧, ⟦Θ⟧ ▸ C) and applies c of the right row at n = 0; β is ε at n = 0; η is c at n = 1; naturality in Δ and C are n = 1 instances.
- **B ⊗ ⟦Θ⟧** (the earlier E.2 rule): u_B := c_{right,0}(m_{B,⟦Θ⟧}), h♯ := c_{pair,0}(e^r ∘ (h, 1)), and its uniqueness is the n = 1 pair row. ⟦Δ⟧ ⊗ Θ ≃ ⟦Δ ⊗ Θ⟧ because both represent the same operation space.
- **Probe absorption** and **E.1's warning:** (B⊗C, ⟦Dᵏ⟧ ▸ D) ≃ (B, C, ⟦Dᵏ⟧ ▸ D) by the pair row, and the right row curries C together with the time slot, giving (B ▸ D/(C ⊗ ⟦Dᵏ⟧)).
- **(A\C)/B ≃ A\(C/B):** canonical but not literal; both represent (A, Φ, B ▸ C).
- 2-functoriality of A ⊗ – on lax cells and of – ⊗ B on oplax cells.

## 8.5 Conservativity over L

No biclosed rule enters a derivation of a pure judgment (⟦Δ₁⟧, …, ⟦Δₖ⟧ ▸ ⟦Θ⟧), by the sort discipline. So the pure judgments are those of L + p + pt in every switch setting. The pure fragment is the free planar multicategory on L's substitutions, p and pt, **with no equations between them**: p ∘ (σ, τ) and (σ ⊗ τ) ∘ p are distinct terms. The stronger claim "pure judgments are exactly L's" is not made.

**Status.** **Proved** at argument level (GB-ext step 4, independently checked). **Source:** `notes/closed-structure.md` F.7.4 §4, §6.

## 8.6 What the closed structure does not change

L's coherence rule and its side condition in V + S; the marks of chapter 3; the pseudo hom (cartesian, `notes/internal-hom.md` §5.4–5.5).

## 8.7 Dualities

The object duality (–)^K and the ambient duality D_J act differently on the biclosed rules.

**Rule.** None. The dualities are meta-operations on derivations, not rules.

**Statement.**
- **Ambient dualities with 1 ∈ J do not act.** A multimap (X₁, …, Xₙ ▸ Z) is an ambient 1-cell. Reversing it gives a map from Z to a tensor, which is not a multimap for n ≠ 1.
- **The mirror.** For K ∈ {odd, even}, (X ⊗ Y)^K ≅ Y^K ⊗ X^K. The mirror acts as follows:
  - a multimap (X₁, …, Xₙ ▸ Z) goes to (Xₙ^K, …, X₁^K ▸ Z^K);
  - A\C goes to C^K/A^K, and C/A goes to A^K\C^K;
  - m, e^ℓ, e^r and p_{Δ,Θ} go to m with swapped arguments, e^r, e^ℓ and p_{Θ^K,Δ^K};
  - a time slot at gap g goes to gap n − g, so a lax slot becomes an oplax one;
  - ⟦Dᵏ⟧ keeps its shape, with source and target swapped iff k ∈ K.

  The mirror maps the row table of §8.3 to itself, the vertex types H and B to their mirrors, and the restriction r to its mirror. Directed cuts go to directed cuts. Collars go to collars after inverting the reversed ones.
- **What breaks the symmetry is L.** A probe restriction along ⟦σ⟧ mirrors to the restriction along ⟦D_K σ⟧. That is a kernel restriction for every σ iff D_K is a symmetry of the core.
  - Under uniform L, in every setting, only K = ∅ is a symmetry (chapter 2, §2.7). So no non-trivial duality is a symmetry of L + biclosed rules.
  - The op mirror lands in the biclosed system over the mixed core D_odd(V + S).
  - K = all keeps ⊗'s order and lands over the oplax core, with the inner law and R exchanged.
  - Under two-tier L, op is a core symmetry, so the op mirror is a symmetry of two-tier L + biclosed rules.
- **Other K** turn ⊗ into the twisted tensor ⊗_ε, which is not a formula. They have no action on the biclosed rules.

**Example.** Over two-tier L, the right curry of a lax transformation α : (B, ⟦D¹⟧ ▸ C) mirrors to the left curry of an oplax transformation of opposites, with the same derivation. Over uniform L the rows still mirror. But a restriction along the interchanger of two 2-cells of an object (Σ(ΣD¹ ∨ ΣD¹), chapter 2 §2.3 example (c)) mirrors under op to a restriction along the reversed interchanger, which uniform L rejects.

**Status.** The mirror's action on the rows: **Agda-checked** (`src/CaTTExp/Gray/Biclosed/Mirror.agda`: `mirRow-invol`, `H-mir`, `B-mir`, `rmap-mir`, `rowsOf-mir`, no postulates). The action on directed cuts, collars and probe restrictions: **stated** (argued in the note). The core classification it relies on: chapter 2, §2.7. **Source.** `notes/closed-structure.md` §D.5; ledger D8.

## 8.8 Open surface questions

**Q8.1. How multimaps are written.**
- *Option A: as in the kernel,* `t : (X₁, …, Xₙ ▸ Z)`. Exact; unfamiliar.
- *Option B: curried function types* `X₁ → … → Xₙ → Z`, elaborated by the rows. Familiar; hides that the inputs are tensored, not producted, and that the order of inputs is the order of time.
- *Worked example.* A lax transformation between F, G : B → C is `α : (B, ⟦D¹⟧ ▸ C)` in A, and `α : B → ⟦D¹⟧ → C` in B; in B the user must learn that swapping the two arguments gives an oplax transformation.

**Q8.2. Which residual names the user sees.**
- *Option A: A\C and C/A* (kernel). Short; the side of the slash encodes lax versus oplax, which is easy to misremember (the hazard of `notes/conventions.md` §3.2).
- *Option B: `Fun^lax(A, C)` and `Fun^oplax(A, C)`.* Self-describing; longer.

**Q8.3. Whether currying is explicit.** `c` and `ε` of the rows are explicit terms.
- *Option A: explicit* `curry`, `uncurry`. Every use is visible.
- *Option B: implicit,* inserted by the elaborator at type mismatches between (Φ ▸ A\C) and (A, Φ ▸ C). Convenient; every inserted ε is an invertible cell the user did not write.
