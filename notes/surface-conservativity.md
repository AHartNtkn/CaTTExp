# Surface conservativity: strict associators and unitors over the kernel

*Thread "Prove the strictified surface language conservative", 2026-11-22. Ledger item S19 (a)–(c); Anthony's decisions are recorded in S6 and S19. Agda: `src/CaTTExp/Surface/Conservativity.agda` (type-checked locally with Agda 2.6.3, `--safe`, no postulates or holes). Status tags: **[Agda]** machine-checked; **[proved]** paper proof written out here; **[cited]** a result of another note or paper, with its own status; **[argued]** a short argument that still needs an independent check; **[open]**.*

## 0. Summary

Anthony's decisions (S19): the kernel has no computation rules. The user-facing surface may strictify two of {associators, unitors, interchange} by definitional equality, by default associators and unitors. Every layer above the kernel is trusted because it is proved conservative once, in Agda, not because its output is re-checked by the kernel.

| Result | Status |
|---|---|
| **Definitions.** Three forms of "the surface is conservative over the kernel": inhabitation, elaboration, and relative coherence (§2) | stated here |
| **Theorem A (reduction).** For any kernel and any definitional equality ≈ that is a congruence, is stable under substitution, and leaves the side condition unchanged: if the kernel satisfies *kernel conversion* (KC), then every surface derivation of a kernel type elaborates to a kernel term of exactly that type, ≈-equal to the original. The elaborator is the proof. | **[Agda]** `Conservative.conservative` |
| **Theorem B.** KC in dimension n follows from *relative coherence* EL(k) for k < n: parallel kernel k-terms that are ≈-equal are joined, both ways, by kernel cells that are ≈-identities. The proof uses only whiskering and vertical composites (linear trees), which exist in every kernel, including uniform L. | **[proved]** (§3.2) |
| **Theorem C (converse).** If the surface is conservative in Γ, then EL holds in Γ. So conservativity in Γ through dimension n+1 is *equivalent* to EL(≤ n) in Γ. | **[Agda]** `Converse.necessary`; equivalence **[proved]** |
| **The 2-of-3 surface over L** (≈ = equality in the side condition's own free objects 𝔉 or F_{V+S}, which are strictly associative and unital, with interchange still a directed generator) is conservative over L **in every pasting context, in every dimension**. | **[proved]** modulo Lemma V (§4.2, **[argued]** for two-tier L, open for uniform L) |
| The same surface over L in an **arbitrary** context | **[open]**: equivalent to Gray relative coherence RC_L (Conjecture GRC, §4.3). Sent as `conjectures/outbox/semistrict-surface-conservativity.md` |
| Plain CaTT, fully strict surface (≈ = equality in the free strict ω-category): conservative in every strong-Steiner context, in every dimension, and in every context for types of dimension ≤ 3. **Not** conservative in the context (x, a : 1ₓ → 1ₓ) at dimension 4. | **[proved]** from RC (`relative-coherence.md`, **[cited]**); the failure from the verified RC(3) counterexample |
| **Catt_sua and Catt_su are conservative over Catt** in every strong-Steiner context (pasting contexts included) and in every context for types of dimension ≤ 3 | **[proved]** from the line above, given Lemma 1.2 (**[argued]**). The literature has this only over pasting contexts (FRRV 2020 for Catt_su; Rice's "partial rehydration" for Catt_sua). |
| Rewrite rules (disc, endo-coherence removal, insertion) as an implementation of ≈ over uniform L | disc and endo removal **[proved]**; insertion and pruning need the designated lifts of §2.2 of `spec/02` to commute with insertion **[open]**, new sub-item of S11 |

The short version: **conservativity is exactly relative coherence for the strictified equality.** The reduction (Theorem A) and the existence half of its converse (Theorem C) are machine-checked; Theorem B (EL ⇒ KC), which closes the equivalence, and the "≈ 1" half of EL in Theorem C are paper proofs. What is left is one statement about the kernel, EL, which holds inside every coherence head (pasting contexts) and is open in arbitrary contexts.

## 1. The setting

### 1.1 Kernel

The kernel is any of the CaTT-style theories of `spec/01`–`spec/02`, all instances of `TypingWith 𝕊 side`:

| Kernel | Side condition computed in | Interchange there |
|---|---|---|
| plain CaTT, P | ν(λΓ), the free strict ω-category | strict (an equation) |
| two-tier L | 𝔉(Γ), the free Gray-enriched category | directed across objects |
| uniform L, setting S | F_{V+S}(Γ) | directed at every level |

All three families of free objects are **strictly associative and strictly unital**. That is the whole reason a strict-associator/unitor surface can make sense over L. Write F(Γ) for whichever family the kernel uses and ⟦t⟧ ∈ F(Γ) for the strict image of a term (`spec/02` §2.1). For uniform L the image of an operation-case coherence is its designated lift (`spec/02` §2.2). The image of a coherence-case coherence is an identity in all three.

### 1.2 Surface

The **surface** has the kernel's rules, the kernel's side condition (read off images, Lemma 2.2.1 of `spec/02`), and the conversion rule

```
Γ ⊢ˢ t : A     A ≈ B     Γ ⊢ˢ B
───────────────────────────────── (conv)
          Γ ⊢ˢ t : B
```

for a definitional equality ≈ on raw syntax. The coh rule of the surface is the kernel's with the head's type and the argument substitution typed in the surface. This is the CaTT_R framework of Finster–Rice–Vicary (`icatt-and-rice-rules.md` §4), over an arbitrary kernel.

Two choices of ≈ matter.

- **≡_F (image equality).** t ≈ t′ iff ⟦t⟧ = ⟦t′⟧ in F(Γ) (extended to raw terms by a compositional interpretation with a junk value for ill-formed heads, so that ≈ is a total equivalence; only its restriction to surface-typed terms is ever used).
  - Over **L** this is exactly the 2-of-3 Anthony endorsed: F is strictly associative and unital, so associators and unitors become identities, while an interchanger is a non-identity generator of F, so interchange stays directed. It also makes Gray's own coherence laws (and, in uniform L, the switched laws of the declared setting) definitional, but never an interchanger.
  - Over **P** it strictifies all three, including interchange. It is not a 2-of-3 surface and is included only as a comparison.
- **≡_sua.** The equivalence closure of the rewrite rules of CaTT_sua (disc removal, endo-coherence removal, insertion, which subsumes pruning), restricted to redexes typable in the kernel. `CaTTExp.SU` implements them on raw syntax with a normaliser (D16).

**Lemma 1.1 [proved for P and two-tier L; partly open for uniform L].** ≡_sua ⊆ ≡_F on surface-typed terms.

*Proof.* Each rule replaces a term by one with the same type and the same support (FRV's support and conversion conditions on R). In ν and 𝔉, cells with the same boundary and support are equal (support determines cells: `Strict/Recon.b-supp`; Hadzihasanovic 2404.07273, Prop. 8.3.17), so each step preserves the image. For uniform L: disc removal sends the unary composite, whose image is its argument, to the argument; endo-coherence removal sends a coherence-case cell, whose designated lift is the identity, to the identity. Both preserve the image. Insertion replaces coh(S, A)[σ] by coh(S ≪ T, A[κ])[σ ≪ τ]. Their images are κ_*(c_{S,A}) and c_{S≪T, A[κ]}, both witnessing paths for the same head in F_{V+S}(S ≪ T). They agree if the designated-lift choice commutes with κ. In the coherence case both are identities. In the operation case this is **open**, and is the same kind of question as S11. ∎

**Lemma 1.2 [argued].** For terms typable in Catt_sua over a pasting context, FM's variable condition on a head agrees with the image form of the side condition. So every Catt_sua derivation is a derivation of the ≡_ν surface.

*Argument.* Lemma 2.2.1 of `spec/02` identifies the image form with the support form. FRV's support condition (supp s = supp t for every rule) makes Var invariant under ≡_sua. The remaining step, Var(t) = supp⟦t⟧ for Catt_sua-typed t, is the "supp = Var for derivable terms" fact of `pseudo-vs-gray.md` §3 (paper; not formalized there either).

## 2. What "conservative" means (S19 (a))

Fix a kernel, a relation ≈, a kernel context Γ and a dimension n.

**Definition 2.1 (inhabitation).** The surface is *conservative at Γ through dimension n* if for every kernel type B over Γ with dim B ≤ n: if Γ ⊢ˢ t : B for some t, then Γ ⊢ t′ : B for some t′.

**Definition 2.2 (elaboration).** The same, with t′ ≈ t, and t′ computed from the surface derivation. This is what "trusted by verified conservativity" needs. The theorem is proved once. After that a surface judgment about a kernel type is known to hold in every model of the kernel, and the elaborator never has to be run. It is run only if a kernel term is wanted, for export for instance. Its output does not need re-checking either: the Agda theorem types it.

**Definition 2.3 (relative coherence EL).** EL(k) holds at Γ if for all parallel kernel k-terms u, u′ : A over Γ with u ≈ u′, there are kernel (k+1)-terms e : u → u′ and e′ : u′ → u with e ≈ 1_u and e′ ≈ 1_{u′}.

**Types and contexts.** Every surface type over a kernel context is ≈ to a kernel type (Agda: `elab-ty`). A surface context therefore translates entry by entry to a ≈-equal kernel context. Conservativity is stated over kernel contexts because only those have kernel judgments.

**On the ledger's phrasing.** S19 (a) asked that the surface "derive no kernel judgment the kernel does not". For typing judgments this is Definition 2.1. A surface *equation* u ≈ u′ has no kernel judgment. Its kernel content is EL: a pair of kernel cells. Theorem C shows the two cannot be separated: a surface that is conservative for typing already forces EL.

## 3. The reduction

### 3.1 Theorem A [Agda]

**Theorem A.** Assume:
- **(E)** ≈ is an equivalence on terms and on types, a congruence for `arr` and `coh` (pointwise on substitutions), and stable under substitution (A ≈ A′ ⇒ A[σ] ≈ A′[σ]). The last is FRV's substitution condition on R.
- **(SC)** If Δ ⊢ps, the arrow type B′ is well formed over Δ in the kernel, B ≈ B′, and side(Δ, B) holds, then side(Δ, B′) holds.
- **(KC)** *Kernel conversion.* If Γ ⊢ t : A and Γ ⊢ A′ in the kernel with A ≈ A′, then Γ ⊢ t″ : A′ for some t″ ≈ t.

Then Definition 2.2 holds at every kernel context, in every dimension. Every surface type over a kernel context is ≈ to a kernel type.

*Proof (as in Agda).* By simultaneous induction on surface derivations, with a strengthened statement for terms: given Γ ⊢ˢ t : A and a kernel type B with A ≈ B, produce kernel t′ : B with t′ ≈ t. The target type is a parameter, so substitutions can be built one variable at a time.
- *var, cst:* use KC from the kernel's own typing.
- *conv:* pass the target on, composing the two ≈ steps.
- *coh Δ (arr A t u) σ:* elaborate the head type over Δ to a kernel type B′ ≈ (arr A t u); SC gives side(Δ, B′). Elaborate σ to a kernel σ′ ≈ σ variable by variable, each time with target C[σ′], which is a kernel type by the substitution lemma and ≈ C[σ] by congruence. Then coh Δ B′ σ′ has kernel type B′[σ′] ≈ B′[σ] ≈ (arr A t u)[σ] ≈ B, and KC moves it to B.

`B′[σ′] ≈ B′[σ]` (substitution of ≈-related substitutions) is proved from congruence (`sub-cong-ty`), not assumed. ∎

The Agda statement is `Conservative.conservative` in `CaTTExp.Surface.Conservativity`, for every signature with closed constant types, every side condition, and every ≈ satisfying (E). The module also checks non-vacuity: with ≈ syntactic equality all hypotheses hold and the surface is the kernel (`Trivial`).

Two presentation choices, both harmless. The surface `arr` rule carries Γ ⊢ˢ A as an explicit premise; in the kernel it is derivable, and on the surface it would otherwise need a presupposition lemma through conv. And contexts are kernel contexts (§2).

### 3.2 Theorem B: KC from relative coherence [proved]

**Theorem B.** Suppose the kernel has two-sided whiskering composites (below), ≈ is compatible with them, and EL(k) holds at Γ for every k < n. Then KC holds at Γ for types of dimension n.

*Whiskering.* For a j-level boundary, (j+1)-cells p, q and a cell x whose iterated j-source is the j-target of p and whose iterated j-target is the j-source of q, the composite p ∗_j x ∗_j q is a coherence over the pasting context Σʲ(D¹ ∨ D^{m−j} ∨ D¹). That context's tree has at most one non-leaf child at every node (a *linear* tree), so its total cell has the context's dimension and no interchanger is involved. It is an operation-case coherence in P, two-tier L and every setting of uniform L. *Compatibility:* if p ≈ 1 and q ≈ 1 then p ∗_j x ∗_j q ≈ x. For ≡_F this is strict unitality of F; for ≡_sua it is insertion followed by disc removal.

*Proof.* Let Γ ⊢ t : A and A ≈ A′, both of dimension n. Write sₖ, tₖ and s′ₖ, t′ₖ for the k-dimensional source and target of A and A′. Let j be the least level at which (sⱼ, tⱼ) ≠ (s′ⱼ, t′ⱼ) syntactically. Below j the two types agree, so sⱼ, s′ⱼ are parallel, and so are tⱼ, t′ⱼ. Both pairs are ≈-equal, because ≈ is a congruence and A ≈ A′ (for ≡_F: images are compared level by level). EL(j) gives p : s′ⱼ → sⱼ and q : tⱼ → t′ⱼ with p, q ≈ 1. Replace t by t₁ := p ∗ⱼ t ∗ⱼ q. Its type agrees with A′ up to level j. Its higher boundaries are the whiskered sₖ, tₖ, still ≈ to s′ₖ, t′ₖ, and t₁ ≈ t by compatibility. The first level of disagreement has gone up, so after at most n steps the type is A′. At the last step (j = n − 1) the whiskering is a vertical composite. Only EL(j) for j ≤ n − 1 was used. ∎

So **conservativity through dimension n ⇐ EL(< n)**.

### 3.3 Theorem C: the converse [Agda]

**Theorem C.** If the kernel has identities (a term 1_u : u → u for every u; in every kernel this is the coherence-case coherence over the disc) and its presupposition lemma, then conservativity at Γ implies EL at Γ.

*Proof.* Given parallel kernel u ≈ u′ : A, the surface derives 1_u : u → u, and by (conv) 1_u : u → u′. Conservativity gives a kernel term e : u → u′, with e ≈ 1_u in the elaboration form. ∎

Agda: `Converse.necessary` (for the existence half; the ≈ 1 half is the elaboration form of `conservative`). Together with Theorem B: **conservativity through dimension n+1 ⟺ EL(≤ n)**, at each context separately. Nothing weaker than EL can make the surface conservative, so the open problem below is the right one.

## 4. Where EL holds

### 4.1 Plain CaTT [cited / proved]

For P with ≈ = ≡_ν, EL is the relative coherence RC of `relative-coherence.md` §1 ("parallel terms with equal strict image are connected"). The connecting terms are built from substituted coherences, so their strict images are identities, and both directions exist.

- RC(1) and RC(2) hold in **every** context (Theorem A there; paper proof, its 2-molecule case refereed).
- RC(n) for every n holds in every finite **strong-Steiner** context (RC_id(∞); verified researcher answers r8 Response 18 and r9 Response 15, with the U_{k−2} step closed in §7.15). Every pasting context is strong Steiner (λ(S) is, Ara–Maltsiniotis Prop. 4.13), and so is every Gray product of globes and every cylinder Q↑Y.
- RC(3) **fails** in (x, a : 1ₓ → 1ₓ) (verified counterexample, `conjectures/answered/gray-contexts-r5-2026-11-18.md`).

**Corollary 4.1.** The fully strict surface over P is conservative in every strong-Steiner context, in every dimension, and in every context for types of dimension ≤ 3. By Theorem C it is **not** conservative in (x, a : 1ₓ → 1ₓ) for types of dimension 4. This is the Eckmann–Hilton obstruction, and it is why the full strictification is ruled out.

**Corollary 4.2.** Catt_sua and Catt_su are conservative over Catt (Definition 2.1, and 2.2 up to ≡_ν) in every strong-Steiner context in every dimension, and in every context for types of dimension ≤ 3. *Proof.* By Lemma 1.2, a Catt_sua derivation is a derivation of the ≡_ν surface. Apply Corollary 4.1. ∎ The literature proves conservativity only over pasting contexts: Finster–Reutter–Rice–Vicary (arXiv 2007.08307) for Catt_su, and Rice's thesis (arXiv 2502.17068, Ch. 4, "partial rehydration") for Catt_sua. Rehydration is stronger, since it gives a Catt term that is ≡_sua-equal and not just ≡_ν-equal. Neither proves or conjectures the general-context case, and the thesis records "obstructions to rehydration in a generic context". Corollary 4.2 adds the non-pasting strong-Steiner contexts and the low-dimensional general case, in the weaker inhabitation sense.

For ≡_sua the counterexample of Corollary 4.1 does not apply. The two 3-terms there differ by an Eckmann–Hilton braid, which is built from interchangers, and ≡_sua does not identify them. Whether EL holds for ≡_sua in every context is **open** (Q1 of the outbox prompt).

### 4.2 L in pasting contexts [proved modulo Lemma V]

**Proposition 4.3.** For two-tier L and for uniform L in any setting, with ≈ = ≡_F, EL(k) holds in every pasting context Δ, for every k.

*Proof.* Let u, u′ : A be parallel kernel terms over Δ with ⟦u⟧ = ⟦u′⟧. By Lemma V, Δ′ := Var(u) is a pasting sub-context, Var(u′) = Δ′, u and u′ factor as ũ[ι] and ũ′[ι] through the inclusion ι : Δ′ → Δ, and ⟦ũ⟧ = ⟦ũ′⟧ has full support in F(Δ′). Then coh_{Δ′, ũ → ũ′} is a coherence-case coherence, accepted in every row of `spec/02`'s table, and so is its reverse. Their images are identities. Substituting ι gives e and e′. ∎

**Lemma V [argued for two-tier L; open for uniform L].** For a kernel term u over a pasting context Δ: (i) Var(u) is a pasting context and supp⟦u⟧ = Var(u) (the Gray support projected to variables); (ii) the inclusion of a pasting sub-context induces an injective map F(Δ′) → F(Δ). For two-tier L: (i) is E1's "supp = Var" on a single hom together with the hom-wise form of 𝔉, and (ii) holds because 𝔉's homs are ν of Steiner complexes and sub-complexes include injectively. For F_{V+S}, (ii) is not known.

**Corollary 4.4.** The 2-of-3 surface (≈ = ≡_F) over two-tier L, and over uniform L given Lemma V (ii), is conservative over the kernel in every pasting context in every dimension. In particular, everything a coherence head sees (its type, built over its own pasting context) is safe.

### 4.3 L in arbitrary contexts [open]

The users of the surface work in arbitrary contexts. There, conservativity is equivalent to:

**Conjecture GRC (Gray relative coherence).** For two-tier L (and uniform L in each setting), in every finite context Γ, any two parallel kernel terms with the same image in the free Gray-enriched category on Γ (respectively F_{V+S}(Γ)) are connected, both ways, by kernel terms whose images are identities.

Evidence for it: the obstruction that kills the fully strict surface over P (Corollary 4.1) is an Eckmann–Hilton identification, and ≡_𝔉 does not make it. In 𝔉 the two composites of a : 1ₓ → 1ₓ with itself differ by a directed interchanger, so they are not ≡_𝔉-equal. Gordon–Power–Street prove the semantic statement in dimension 3: every tricategory is triequivalent to a Gray-category. GRC is a syntactic, all-dimensions, directed analogue. Against it: no RC-type theorem for the Gray image in non-Steiner contexts exists yet, and for P such statements fail exactly in non-loop-free contexts. The question is posed in general, with the plain-CaTT ≡_sua case alongside, in `conjectures/outbox/semistrict-surface-conservativity.md`.

## 5. What this means for the surface design (S6, S19)

- **The surface's definitional equality should be ≡_F of the declared setting,** with the CaTT_sua rewrite rules as an implementation of a sound fragment of it (Lemma 1.1). This makes associators and unitors definitional and leaves interchange directed, which is the 2-of-3 in S6. It needs no extra rule class. The relation is read off the same free objects the side condition already uses, and over L it never identifies an interchanger with an identity.
- **Deciding ≈ in an arbitrary context.** ≡_sua is decidable by normalisation (FRV: strongly terminating and confluent). Equality in F(Γ) is decidable on pasting contexts (`spec/02` §2.3). For arbitrary finite contexts it is not established here for 𝔉 or F_{V+S} **[open]**. This bears on implementing the surface, not on the conservativity results.
- **Trust without re-checking.** Theorem A is the guarantee. The surface checker's output is a surface derivation, and `conservative` maps it to a kernel derivation of the same kernel type. The proof obligation for a *new* surface feature is then exactly (E), (SC) and EL in the contexts it is used in.
- **The other pairs of the 2-of-3.** The reduction does not depend on which pair is made strict. Strict unitors plus strict interchange with weak associators is not available over L, because L has no strict interchange to begin with. Strict associators plus strict interchange with weak units (Simpson's choice) would need a kernel whose side condition reads off a free object with strict interchange, which is P, not L. Over L, therefore, associators and unitors are the only pair (S6's default).

## 6. Formalization (S19 (c))

`src/CaTTExp/Surface/Conservativity.agda`, parameterised by a signature with closed constant types and an arbitrary side condition, so it applies to P, two-tier L and uniform L alike:
- `SurfaceEq`: hypothesis (E); `Pw`: pointwise extension to substitutions; `sub-cong-ty/tm/sub`: substitution of ≈-related substitutions, **proved**.
- `_⊢ˢty_`, `_⊢ˢtm_∶_`, `_⊢ˢsub_∶_`: the surface judgments, with (conv).
- `SideResp` (SC), `KernelConv` (KC): the two hypotheses on the kernel.
- `Conservative.elab-ty / elab-arr / elab-tm / elab-sub`: the elaborator; `conservative`, `no-new-inhabitants`: Theorem A.
- `ConservativeAt`, `RelCohAt`, `Converse.necessary`: Theorem C.
- `Trivial`: non-vacuity.

Not formalized yet: Theorem B (it needs the whiskering coherences as typed raw terms; the plan is to build them from `Std`/`PastingTrees` and discharge KC from an EL hypothesis), Lemma 1.1 (strict-image invariance of the `CaTTExp.SU` rules in `Strict/`), and Proposition 4.3. These are listed as open items with owners in the ledger (S19).

## 7. Open items

| Item | Owner |
|---|---|
| Conjecture GRC (§4.3) and EL for ≡_sua over P in arbitrary contexts | outbox prompt `semistrict-surface-conservativity.md`; this thread keeps working on it |
| Lemma V (ii) for F_{V+S}; Lemma V (i) written out | this thread (S19) |
| Insertion vs designated lifts in uniform L (Lemma 1.1, uniform case) | this thread, cross-referenced to S11 |
| Agda: Theorem B (KC ⇐ EL + whiskering) and Lemma 1.1 in the strict model | this thread (S19 (c)) |
| Decidability of ≡_F in arbitrary finite contexts, for the surface checker | this thread (S19) |
| Spec §0.3/§0.5 revision (no kernel re-checking; surface conversion) | spec thread (already listed in S19) |
