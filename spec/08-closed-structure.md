# Chapter 8. Closed structure: the Gray biclosed rules

The ambient's Gray tensor and its two internal homs become object formers: A ⊗ B, A\C = Hom_lax(A, C) and C/A = Hom_oplax(A, C), for arbitrary objects. Their universal properties are coherence-style templates over a new **multimap** judgment. Nothing here adds a definitional equation or a universe, and the rules never change L's coherences (§8.6).

Names follow `notes/conventions.md` §3.2: A\C has evaluation (A, A\C ▸ C), taking the argument first; the "lax hom" [Θ, C] of earlier notes is C/⟦Θ⟧.

## 8.1 Judgments

**Rule.**
```
(GB-form)   Γ ⊢ A : ⋆    Γ ⊢ B : ⋆   ⟹   Γ ⊢ A ⊗ B : ⋆,   Γ ⊢ A\B : ⋆,   Γ ⊢ B/A : ⋆
Γ ⊢ t : (X₁, …, Xₙ ▸ Z)        n ≥ 0; a map X₁ ⊗ … ⊗ Xₙ → Z, the list never bracketed
```
- With n = 1 a multimap is an ambient 1-cell. With one representable input it is a **probe diagram**: (⟦Δ⟧ ▸ C) is a Δ-shaped diagram in C in the probe sense. By rule GB-shape (§8.8) it is the same as a map out of chapter 7's free object on Δ, and a point ( ▸ C) is the same as an element ⊤ → C of chapter 6. Without that rule neither identification is derivable.
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

**Further rows (§8.8 and chapter 9, §9.6).** Two rows are added to the five above. GB-shape is adopted (§8.8), and L-× is proposed (ledger F8b): GB-shape (chapter 7's free objects ⟦Θ⟧♭ are represented by the probes ⟦Θ⟧, which at Θ = D⁰ is weakening by ⊤), and L-× (contraction: maps out of A × W into a `grpd_2` target are multimaps (A, W ▸ B)). With them, function sets are A\B and F8 is derived. Without them the kernel has no projection out of ⊗ (graded countermodel, `notes/ordinary-math.md` Theorem 6.4).

## 8.4 Derived rules

All of these are derived, none primitive:
- **(lhom):** [Θ, C] := C/⟦Θ⟧, the lax cotensor for **probe** diagrams. `notes/internal-hom.md` §5.1 states (lhom) for maps out of free objects (Δ ⊳ C), and chapter 6, §6.5 defines a lax cotensor as a limit. Both agree with C/⟦Θ⟧ by GB-shape (§8.8), since all three represent the same functor. Abstraction restricts φ : (⟦Δ⊗Θ⟧ ▸ C) by the probe-pair row to (⟦Δ⟧, ⟦Θ⟧ ▸ C) and applies c of the right row at n = 0; β is ε at n = 0; η is c at n = 1; naturality in Δ and C are n = 1 instances.
- **B ⊗ ⟦Θ⟧** (the earlier E.2 rule, read with Θ a probe; E.2 with Θ a free object needs GB-shape): u_B := c_{right,0}(m_{B,⟦Θ⟧}), h♯ := c_{pair,0}(e^r ∘ (h, 1)), and its uniqueness is the n = 1 pair row. ⟦Δ⟧ ⊗ Θ ≃ ⟦Δ ⊗ Θ⟧ because both represent the same operation space.
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

## 8.8 Rule GB-shape: free objects and probes

This was a kernel question, decided by the evidence (standard 3). It was **adopted on 2026-11-21 (option K2)**, after the independent check of its exactness argument passed. **Source:** `notes/design-decisions.md` §4; ledger S13, F8a.

**The gap.** Free objects (chapter 7) and probes (§8.1) are unrelated. So elements ⊤ → C and points ( ▸ C) are unrelated, ⊗ has no projections, and four places in the notes identify the two without a rule. These are (lhom) in data form, E.2's B ⊗ Θ, chapter 6's lax cotensor as a limit, and an earlier version of chapter 7's A1 argument.

**Rule.**
```
(GB-shape)  ⊢ ι_Θ : (⟦Θ⟧ ▸ ⟦Θ⟧♭)        for each pasting shape Θ   (⟦Θ⟧♭ the free object of chapter 7)
            row: H = (L, ⟦Θ⟧♭, R ▸ Z),   B = (L, ⟦Θ⟧, R ▸ Z),      r(x) = x ∘ᵢ ι_Θ
```
- (GB-cut) and (GB-dcut) apply as for every row. GB-dcut puts its time slot at a fixed gap of L or R, as for the pair row. The row adds no slot of its own.
- With Θ = Dᵏ beside a data input, the converted probe reads as a time slot (§8.1).
- **Derived.** With the pair and probe-pair rows, ⟦Δ⟧♭ ⊗ ⟦Θ⟧♭ ≃ ⟦Δ ⊗ Θ⟧♭, since both represent (⟦Δ⟧, ⟦Θ⟧ ▸ –) on data objects. This is true in Cat_ω.

**Options compared.**

| | K0 status quo | K1 GB-shape at D⁰ (weakening) | K2 GB-shape at every Θ | K3 one sort |
|---|---|---|---|---|
| Elements = points | no | yes | yes | yes |
| Shape diagrams = probe diagrams | no | globes only; others unknown | yes | yes |
| Conservative over L (§8.5) | yes | yes | yes | **no** |
| Decidable | yes | yes | yes (one template family per Θ, bounded by the goal) | — |
| Sound in Cat_ω | yes | yes | yes | yes |

**Worked example.** Take two composable arrows of elements x → y → z in C, i.e. a map out of chapter 7's ⟦D¹ ∨ D¹⟧♭. In K2 the shape row turns it into a probe diagram (⟦D¹ ∨ D¹⟧ ▸ C), which C/⟦D¹ ∨ D¹⟧ classifies. In K1 each arrow transfers separately: an arrow of elements is (⊤, ⟦D¹⟧ ▸ C) by the time-slot reading, and the ⊤ row and then the unit row turn it into (⟦D¹⟧ ▸ C). Gluing the two at y as one probe diagram needs a pasting rule for probes, which does not exist. In K0 nothing transfers.

**Decision: K2.** It is the most general option that keeps conservativity (standard 4). K3 loses conservativity, and K0 and K1 derive strictly less. What would overturn it: a failure of exactness for some Θ (K1 would then be the choice). If K1 is shown to derive the shape row at every Θ, K1 is a smaller presentation of the same theory.

**Status.**
- Soundness in Cat_ω: **proved** (ι_Θ is the identity).
- Exactness: **independently checked** at argument level (ledger S13). By the left and right rows, the whole row family is one locality condition: the data atom ⟦Θ⟧♭ represents (⟦Θ⟧ ▸ –) on data through ι_Θ. Steps 3–5 of GB-ext are unchanged, so conservativity over L holds.
- Scope of that check: it treats ⟦Θ⟧♭ as a data atom. Identifying the atom with chapter 7's free object (LIFT) is sound in Cat_ω. Exactness of the combination with chapter 7 lies outside GB-ext, as for every chapter other than this one.
- Weakening row (Θ = D⁰) in Agda over the abstract interface: `Gray/Biclosed/FunSets.agda` (F8d).

## 8.9 Open surface questions

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
