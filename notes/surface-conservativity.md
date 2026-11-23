# Surface conservativity: which strictifications are safe over the kernel

*Thread "Prove the strictified surface language conservative", 2026-11-22. Ledger item S19 (a)–(c); Anthony's decisions are recorded in S6 and S19. Agda: `src/CaTTExp/Surface/Conservativity.agda` and `src/CaTTExp/Surface/StrictInterchange.agda`, type-checked locally with Agda 2.6.3 under `--safe`, with no postulates or holes. Status tags: **[Agda]** machine-checked; **[proved]** a paper proof written out here; **[cited]** a result of another note or paper, carrying that source's status; **[argued]** a short argument that still needs an independent check; **[conj]**; **[open]**.*

## 0. Summary

Anthony's decisions (S19):
- The kernel has no computation rules.
- The user-facing surface may strictify some of {associators, unitors, interchange} by definitional equality. The default is associators and unitors.
- Every layer above the kernel is trusted because it is proved conservative once, in Agda, not because its output is re-checked.

| Result | Status |
|---|---|
| **Definitions.** Three forms of "the surface is conservative over the kernel": inhabitation, elaboration, and relative coherence (§2) | stated here |
| **Theorem A (reduction, local).** Fix a kernel and a context-indexed definitional equality ≈. Assume ≈ is a congruence, is stable under kernel substitution, and leaves the side condition unchanged. Then every surface derivation over Γ of a kernel type elaborates to a kernel term of exactly that type, ≈-equal to the original, provided *kernel conversion* (KC) holds at Γ and at every pasting context. The elaborator is the proof. | **[Agda]** `Conservative.conservative` |
| **Theorem B.** KC at Γ for types of dimension n follows from *relative coherence* EL(k) at Γ for k < n. EL(k) says: parallel kernel k-terms that are ≈-equal are joined, in both directions, by kernel cells that are ≈ to identities. The proof uses only whiskering and vertical composites over linear trees, which exist in every kernel, uniform L included. | **[proved]** on paper (§3.2). **[Agda]** in the undimensioned form (EL in every dimension), over a whiskering interface (`Surface/TheoremB.agda`, `kc-from-el`). For **plain CaTT** the interface's typing rule is discharged and all hypotheses are shown jointly satisfiable (`Surface/WhiskerPure.agda`). What is left per ≈ is the unit law `Wh-≈`: a property of ≈ on the fixed kernel term (p ◃ₖ x) ▹ₖ q (strict unitality of ≈), needing no further kernel construction. Two-tier and uniform L are open |
| **Theorem C (converse).** If the surface is conservative at Γ, then EL holds at Γ, including the "≈ identity" half. | **[Agda]** `Converse.necessary` |
| **Corollary 3.4 (equivalence).** Conservativity at Γ through dimension n ⟺ EL(< n) at Γ, given EL at pasting contexts of dimension ≤ n | **[proved]**; the undimensioned form (EL at Γ and at pasting contexts ⇒ conservative at Γ ⇒ EL at Γ) is **[Agda]** for Theorems A and C (`necessary`); the Theorem B half (`conservative-from-el`) is Agda over the whiskering interface, which is discharged for plain CaTT up to the unit law `Wh-≈` for the chosen ≈ |
| **Interchange can never be strictified over L.** Any surface equality that identifies the two layerings of a horizontal pair is not conservative, already over the pasting context ΣD¹ ∨ ΣD¹ in dimension 3. With interchange in its whiskering form (§1.2), every subset of {associators, unitors, interchange} that contains interchange identifies that pair and so fails over L. | **[Agda]** `strict-interchange-not-conservative` (two-tier L); uniform L **[proved]** from requirement 3 |
| **Strict associators and unitors over L** (≈ = equality in 𝔉 or F_{V+S}, the side condition's own free objects) are conservative in every pasting context, in every dimension | **[proved]** given Lemma V (**[argued]** for two-tier L; (ii) **[open]** for uniform L) and Lemma 1.3 (**[argued]**) |
| The same over L in an **arbitrary** context | **[open]**. It is equivalent to Conjecture GRC (§4.3), which is in the outbox |
| **Plain CaTT, by subset.** Every subset is conservative in strong-Steiner contexts in every dimension, and in every context through dimension 3. Full image equality ≡_ν fails in (x, a : 1ₓ → 1ₓ) at dimension 4; any subset containing {unitors, interchange} is expected to fail there too. {associators, interchange} is Simpson's case and is open; so are {associators, unitors} and every smaller subset. | first claim **[proved]** given Lemma 1.3; failure of ≡_ν **[proved]** from a verified counterexample; failure of ≈_{U,I} and ≈_{A,U,I} **[argued]**; rest **[open]** (§4.4) |
| **Catt_sua and Catt_su are conservative over Catt** in every strong-Steiner context (pasting contexts included) and in every context for types of dimension ≤ 3 | **[proved]** given Lemmas 1.2 and 1.3 (**[argued]**). The literature has this only over pasting contexts. |
| Rewrite rules (disc, endo-coherence removal, insertion) as an implementation of ≈ over uniform L | disc and endo removal **[proved]**; insertion and pruning need the designated lifts to commute with insertion **[open]**, a new sub-item of S11 |

The short version: **conservativity is exactly relative coherence for the strictified equality.** The reduction (Theorem A) and the converse (Theorem C) are machine-checked. Theorem B, which closes the equivalence, is proved on paper and in Agda over a whiskering interface. For plain CaTT that interface is built from the derived whiskers, and its typing rule is proved; all hypotheses are shown jointly satisfiable. For a given ≈, the only remaining obligation is the unit law (whiskering by cells ≈ 1 is ≈ the identity). For two-tier and uniform L the interface is not yet built. Over L, interchange is ruled out outright. Associators and unitors are safe inside every coherence head, and in arbitrary contexts they reduce to one open statement, GRC.

## 1. The setting

### 1.1 Kernel

The kernel is any of the CaTT-style theories of `spec/01`–`spec/02`. All are instances of `TypingWith 𝕊 side`:

| Kernel | Side condition computed in | Interchange there |
|---|---|---|
| plain CaTT, P | ν(λΓ), the free strict ω-category | strict (an equation) |
| two-tier L | 𝔉(Γ), the free Gray-enriched category | directed across objects, strict inside a hom |
| uniform L, setting S | F_{V+S}(Γ) | directed at every level |

All three families of free objects are **strictly associative and strictly unital**. This is why a surface with strict associators and unitors can make sense over L at all. Write F(Γ) for whichever family the kernel uses, and ⟦t⟧ ∈ F(Γ) for the strict image of a term (`spec/02` §2.1). For uniform L, the image of an operation-case coherence is its designated lift (`spec/02` §2.2). In all three, the image of a coherence-case coherence is an identity.

### 1.2 Surface

The **surface** has three ingredients:
- the kernel's rules;
- the kernel's side condition, read off images (Lemma 2.2.1 of `spec/02`);
- the conversion rule

```
Γ ⊢ˢ t : A     Γ ∣ A ≈ B     Γ ⊢ˢ B
───────────────────────────────────── (conv)
            Γ ⊢ˢ t : B
```

Here ≈ is a definitional equality on raw syntax, **indexed by the context**: Γ ∣ t ≈ u. The surface coh rule is the kernel's, except that the head's type and the argument substitution are typed in the surface. The head's type is compared over its own pasting context Δ, and the arguments over Γ. This is Finster–Rice–Vicary's CaTT_R framework (`icatt-and-rice-rules.md` §4), over an arbitrary kernel.

The relations that matter:

- **≡_F (image equality).** Γ ∣ t ≈ t′ iff ⟦t⟧ = ⟦t′⟧ in F(Γ). The interpretation is extended to raw terms compositionally, with a junk value for ill-formed heads, so that ≈ is a total equivalence. Only its restriction to surface-typed terms is ever used.
  - Over **L**: F is strictly associative and unital, so associators and unitors become identities. Interchangers across objects (and, in uniform L, at every level) are non-identity generators of F, so they stay directed.
  - Over **P**: ≡_ν strictifies all three, interchange included (§4.1).
- **≈_S for S ⊆ {A, U, I}** (associativity, units, interchange). This is the smallest congruence, stable under substitution, that contains (i) w ≈ w′ for every pair of parallel *words* that are equal in the free algebra satisfying exactly the laws in S, and (ii) coh_{Δ, w → w′}[σ] ≈ 1_{w[σ]} for every such pair, whenever that coherence exists (a coherence between S-equal words is an identity; Catt_su/sua get this from endo-coherence removal). Words are terms over a pasting context built from variables, the kernel's binary composites (in L: vertical composites and whiskerings) and identities. The laws: A is associativity of each composite; U is the unit laws; I is the *whiskering form* of interchange, (a ∗ⱼ s b) ∘ (t a ∗ⱼ b) = (s a ∗ⱼ b) ∘ (a ∗ⱼ t b) for j-composable a, b, where s, t are the boundaries one level below the cells and ∘ is composition along them, with its higher analogues (in the presence of U this is equivalent to Godement's law). This is the general form used in §4.4 and in the outbox prompt. For P, ≈_{A,U,I} ⊆ ≡_ν. For L, ≈_{A,U} ⊆ ≡_F.
- **≡_su, ≡_sua.** These are the equivalence closures of the published rewrite rules of Catt_su and Catt_sua: disc removal, endo-coherence removal, and pruning (respectively insertion), restricted to redexes typable in the kernel. `CaTTExp.SU` implements them on raw syntax with a normaliser (D16). Both are context-independent.

**Lemma 1.1 [proved for P and two-tier L; partly open for uniform L].** ≡_sua ⊆ ≡_F on surface-typed terms.

*Proof.* Each rule replaces a term by one with the same type and the same support (FRV's support and conversion conditions on R). In ν and 𝔉, cells with the same boundary and support are equal (support determines cells: `Strict/Recon.b-supp`; Hadzihasanovic 2404.07273, Prop. 8.3.17), so each step preserves the image.

For uniform L:
- *Disc removal* sends the unary composite, whose image is its argument, to that argument.
- *Endo-coherence removal* sends a coherence-case cell, whose designated lift is the identity, to the identity.
- *Insertion* replaces coh(S, A)[σ] by coh(S ≪ T, A[κ])[σ ≪ τ]. Their images are κ_*(c_{S,A}) and c_{S≪T, A[κ]}, two witnessing paths for the same head in F_{V+S}(S ≪ T). They agree if the designated-lift choice commutes with κ. In the coherence case both are identities. In the operation case this is **open**, and it is the same kind of question as S11. ∎

**Lemma 1.2 [argued].** For terms typable in Catt_sua over a pasting context, Finster–Mimram's variable condition on a head agrees with the image form of the side condition. So every Catt_sua derivation is a derivation of the ≡_ν surface.

*Argument.*
- Lemma 2.2.1 of `spec/02` identifies the image form with the support form.
- FRV's support condition (supp s = supp t for every rule) makes Var invariant under ≡_sua.
- The remaining step is Var(t) = supp⟦t⟧ for Catt_sua-typed t. This is the "supp = Var for derivable terms" fact of `pseudo-vs-gray.md` §3, extended from kernel terms to Catt_sua-typed ones. It is paper-only there, and not formalized.

**Lemma 1.3 [argued]. (E) and (SC) hold for ≡_F.**
- *Equivalence:* immediate.
- *Congruence for `arr` and `coh`:* the interpretation is compositional. The image of coh_{Δ,A}[σ] is σ_*(c), where c depends only on the images of A's terms in F(Δ). For uniform L the designated lift is a function of the head's images, `spec/02` §2.2.
- *Stability under a kernel substitution σ : Γ → Δ:* ⟦A[σ]⟧ = σ_*⟦A⟧, the substitution lemma for the strict interpretation (for two-tier L, `Strict/Subst.agda`), so equal images stay equal.
- *(SC):* the surface side condition is *defined* on images, and the kernel's side condition equals its image form. For P this needs Lemma 1.2's "supp = Var" step. For L it is Lemma 2.2.1 of `spec/02`.

None of this is formalized yet.

## 2. What "conservative" means (S19 (a))

Fix a kernel, a relation ≈, a kernel context Γ and a dimension n.

**Definition 2.1 (inhabitation).** The surface is *conservative at Γ through dimension n* if the following holds for every kernel type B over Γ with dim B ≤ n: if Γ ⊢ˢ t : B for some t, then Γ ⊢ t′ : B for some t′.

**Definition 2.2 (elaboration).** The same as Definition 2.1, but with Γ ∣ t′ ≈ t, and with t′ computed from the surface derivation.
- This is what "trusted by verified conservativity" needs. The theorem is proved once. After that, a surface judgment about a kernel type is known to hold in every model of the kernel, and the elaborator never has to run.
- The elaborator runs only if a kernel term is actually wanted, for instance for export. Its output needs no re-checking either, because the Agda theorem types it.

**Definition 2.3 (relative coherence EL).** EL(k) holds at Γ if the following holds for all parallel kernel k-terms u, u′ : A over Γ with Γ ∣ u ≈ u′: there are kernel (k+1)-terms e : u → u′ and e′ : u′ → u with e ≈ 1_u and e′ ≈ 1_{u′}. EL(0) is automatic for every relation used here, because parallel 0-terms are variables, and ≈-equal variables are equal.

**Types and contexts.** Every surface type over a kernel context is ≈ to a kernel type (Agda: `elab-ty`). A surface context therefore translates, entry by entry, to a ≈-equal kernel context. Conservativity is stated over kernel contexts because only those have kernel judgments.

**On the ledger's phrasing.** S19 (a) asked that the surface "derive no kernel judgment the kernel does not".
- For typing judgments this is Definition 2.1.
- A surface *equation* u ≈ u′ has no kernel judgment. Its kernel content is EL, a pair of kernel cells.
- Theorem C shows the two cannot be separated: a surface that is conservative for typing already forces EL.

**The formal surface.**
- Its `arr` rule carries Γ ⊢ˢ A as an explicit premise. The bare system leaves that premise out and would need a presupposition lemma through (conv).
- So the formal surface is a priori a subsystem of the bare one. They agree given a surface presupposition lemma, which needs a surface substitution lemma. Both are standard for CaTT_R (FRV) but **not formalized** here.

## 3. The reduction

### 3.1 Theorem A [Agda]

**Theorem A.** Assume:
- **(E)** In each context, ≈ is an equivalence on terms and on types. It is a congruence for `arr`, and for `coh` (the head is compared over its own Δ, and arguments pointwise over Γ). It is stable under kernel substitution: Γ ⊢ σ : Δ and Δ ∣ A ≈ A′ imply Γ ∣ A[σ] ≈ A′[σ]. The last condition is FRV's substitution condition on R.
- **(SC)** If Δ ⊢ps, the arrow type B′ is well formed over Δ in the kernel, Δ ∣ B ≈ B′, and side(Δ, B) holds, then side(Δ, B′) holds.
- **(KC) at Γ** (*kernel conversion*). If Γ ⊢ t : A and Γ ⊢ A′ in the kernel, with Γ ∣ A ≈ A′, then Γ ⊢ t″ : A′ for some t″ with Γ ∣ t″ ≈ t.

Suppose (KC) holds at Γ and at every pasting context. Then Definition 2.2 holds at Γ in every dimension, and every surface type over Γ is ≈ to a kernel type.

*Proof (as in Agda).* By simultaneous induction on surface derivations. The statement for terms is strengthened: given Γ ⊢ˢ t : A and a kernel type B with Γ ∣ A ≈ B, produce a kernel t′ : B with Γ ∣ t′ ≈ t. The target type is a parameter, so substitutions can be built one variable at a time.
- *var, cst:* use (KC) at Γ on the kernel's own typing.
- *conv:* pass the target on, composing the two ≈ steps.
- *coh Δ (arr A t u) σ:*
  - Elaborate the head type over Δ, using (KC) at Δ, to a kernel type B′ with Δ ∣ B′ ≈ (arr A t u). (SC) then gives side(Δ, B′).
  - Elaborate σ to a kernel σ′ with Γ ∣ σ′ ≈ σ, one variable at a time. The target for each variable is C[σ′]. This is a kernel type by the substitution lemma, and it is ≈ C[σ] by congruence.
  - Then coh Δ B′ σ′ has kernel type B′[σ′]. Stability gives B′[σ′] ≈ (arr A t u)[σ′], and congruence gives (arr A t u)[σ′] ≈ (arr A t u)[σ] ≈ B. (KC) at Γ moves the term to B.

The congruence step for substitutions (Γ ∣ σ ≈ σ′ implies Γ ∣ A[σ] ≈ A[σ′]) is proved from congruence (`sub-cong-ty`), not assumed. ∎

The Agda statement is `Conservative.conservative`. It quantifies over every signature with closed constant types, every side condition, and every ≈ satisfying (E). It takes (KC) at Γ as an argument and (KC) at pasting contexts as a module parameter. `conservative-everywhere` is the global form. The module also checks non-vacuity: with ≈ syntactic equality, every hypothesis holds and the surface is the kernel (`Trivial`).

### 3.2 Theorem B: KC from relative coherence [proved]

**Hypotheses.** Beyond (E):
- **(Inv) arr-inversion.** Γ ∣ arr A t u ≈ arr A′ t′ u′ implies Γ ∣ A ≈ A′, Γ ∣ t ≈ t′ and Γ ∣ u ≈ u′. Congruence gives only the converse.
- **(Dim)** ≈ preserves dimension.
- **(W) whiskering, compatible with ≈.**
  - Take a level j, (j+1)-cells p, q, and a cell x with these boundaries: the iterated j-source of x is the j-target of p, and the iterated j-target of x is the j-source of q. Then the composite p ∗_j x ∗_j q is a kernel coherence over Σʲ(D¹ ∨ D^{m−j} ∨ D¹).
  - That context's tree has at most one non-leaf child at every node, a *linear* tree. So its total cell has the context's dimension and involves no interchanger, and the composite is an operation-case coherence in P, in two-tier L and in every setting of uniform L.
  - *Compatibility:* if p ≈ 1 and q ≈ 1, then p ∗_j x ∗_j q ≈ x.

All three hold for ≡_F. (Inv) and (Dim) hold because images are compared level by level. (W) holds by strict unitality of F. For ≡_sua, (W) is insertion followed by disc removal, and (Inv) and (Dim) are syntactic.

**Theorem B.** Under (E), (Inv), (Dim) and (W), if EL(k) holds at Γ for every k < n, then (KC) holds at Γ for types of dimension n.

*Proof.* Let Γ ⊢ t : A with Γ ∣ A ≈ A′, both of dimension n (Dim). Write sₖ, tₖ and s′ₖ, t′ₖ for the k-dimensional sources and targets of A and A′. Let j be the least level at which (sⱼ, tⱼ) ≠ (s′ⱼ, t′ⱼ) syntactically.
1. Below level j the two types agree. So sⱼ, s′ⱼ are parallel, and so are tⱼ, t′ⱼ.
2. Both pairs are ≈-equal, by (Inv) applied repeatedly.
3. EL(j) gives p : s′ⱼ → sⱼ and q : tⱼ → t′ⱼ with p, q ≈ 1.
4. Replace t by t₁ := p ∗ⱼ t ∗ⱼ q.
   - The type of t₁ agrees with A′ up to level j.
   - The higher boundaries of t₁ are the whiskered sₖ, tₖ. These are still ≈ to s′ₖ, t′ₖ, by (W) and transitivity.
   - t₁ ≈ t, by (W).
5. The first level of disagreement has gone up. So after at most n steps the type is A′.

At the last step (j = n − 1) the whiskering is a vertical composite. Only EL(j) for j ≤ n − 1 was used. ∎

### 3.3 Theorem C: the converse [Agda]

**Theorem C.** Suppose the kernel has its presupposition lemma and identities: a term 1_u : u → u for every u. In every kernel considered here, 1_u is the coherence-case coherence over the disc. Then conservativity at Γ implies EL at Γ, including e ≈ 1_u.

*Proof.* Let u ≈ u′ be parallel kernel terms of type A. The surface derives 1_u : u → u, and by (conv) also 1_u : u → u′. Conservativity gives a kernel term e : u → u′ with e ≈ 1_u. ∎

Agda: `Converse.necessary`. The same argument, applied to a kernel cell c : u → u′ instead of an identity, gives `Embed.reverse-breaks`: if u ≈ u′ but the kernel type u′ → u is empty, then the surface is not conservative at Γ.

### 3.4 The equivalence, localised

**Corollary 3.4 [proved].** Assume (E), (SC), (Inv), (Dim) and (W). Assume also that the kernel's side condition forces dim Δ ≤ dim A for every accepted head (Δ, A). This holds in all three kernels: in the operation case A has the dimension of the total cell, which is ≥ dim Δ (equal in P; larger for interchangers in L), and in the coherence case A's terms are full, so dim A ≥ dim Δ. Suppose EL(k) holds for all k < n at every pasting context of dimension ≤ n. Then the following are equivalent:
- the surface is conservative at Γ through dimension n;
- EL(k) holds at Γ for all k < n.

*Proof.*
- ⇐: Run Theorem A with (KC) restricted to dimension ≤ n. In a derivation of a type of dimension ≤ n, every (KC) call has dimension ≤ n:
  - conversion preserves dimension (Dim);
  - the arguments of a coh of dimension m have dimension ≤ dim Δ ≤ m;
  - the head's type has dimension m.

  The calls happen at Γ and at the pasting contexts of the heads, whose dimension is ≤ n. Theorem B supplies (KC) at both from EL(< n).
- ⇒: Theorem C, applied to types of dimension ≤ n, gives EL(< n) at Γ. ∎

The dimension-bounded form of Theorem A is not separately formalized. The Agda proves Theorem A with (KC) at Γ and at all pasting contexts, without a dimension bound.

## 4. Where EL holds, and the classification by subsets

### 4.1 Plain CaTT [cited / proved]

For P with ≈ = ≡_ν, EL is the relative coherence RC of `relative-coherence.md` §1: parallel terms with equal strict image are connected. The connecting terms there are built from substituted coherences, so their strict images are identities, and both directions exist.
- RC(1) and RC(2) hold in **every** context. This is Theorem A of `relative-coherence.md`: a paper proof whose 2-molecule case was refereed.
- RC(n) holds for every n in every finite **strong-Steiner** context (RC_id(∞); verified researcher answers r8 Response 18 and r9 Response 15, with the U_{k−2} step closed in §7.15).
  - Every pasting context is strong Steiner: λ(S) is, by Ara–Maltsiniotis Prop. 4.13.
  - So is every Gray product of globes, and every cylinder Q↑Y.
- RC(3) **fails** in (x, a : 1ₓ → 1ₓ). This is a verified counterexample, `conjectures/answered/gray-contexts-r5-2026-11-18.md`.

**Corollary 4.1.** Assume Lemma 1.3. Then the fully strict surface over P is conservative:
- in every strong-Steiner context, in every dimension;
- in every context for types of dimension ≤ 3. This uses EL(0), which is automatic, together with RC(1) and RC(2).

By Theorem C it is **not** conservative in (x, a : 1ₓ → 1ₓ) for types of dimension 4. This is the Eckmann–Hilton obstruction.

**Corollary 4.2.** Assume Lemmas 1.2 and 1.3. Then Catt_sua and Catt_su are conservative over Catt in the following cases:
- in every strong-Steiner context, in every dimension;
- in every context, for types of dimension ≤ 3.

The conservativity holds in the sense of Definition 2.1, and of Definition 2.2 up to ≡_ν.

*Proof.* By Lemma 1.2, a Catt_sua derivation is a derivation of the ≡_ν surface. Apply Corollary 4.1. ∎

The literature proves conservativity only over pasting contexts:
- Finster–Reutter–Rice–Vicary (arXiv 2007.08307) for Catt_su;
- Rice's thesis (arXiv 2502.17068, Ch. 4, "partial rehydration") for Catt_sua.

Rehydration is stronger, since it gives a Catt term that is ≡_sua-equal and not just ≡_ν-equal. Neither source proves or conjectures the general-context case, and the thesis records "obstructions to rehydration in a generic context".

**Whether the obstruction survives ≡_sua.** The pair of 3-terms in the counterexample is the Eckmann–Hilton braid of a with itself against an identity. The braid is a composite of unitors and interchangers.
- **[argued]** ≡_sua does not identify the two, because ≡_sua makes no interchanger trivial. Not checked with the SU normaliser.
- **[argued]** ≈_{U,I} does identify them. Each constituent cell is a coherence between ≈_{U,I}-equal words, hence ≈ 1 by clause (ii) of the definition of ≈_S, and a composite of identities is an identity under U.

Whether EL holds for ≡_sua in every context is **open** (Q1 of the outbox prompt).

### 4.2 L in pasting contexts [proved modulo Lemma V]

**Proposition 4.3.** For two-tier L, and for uniform L in any setting, with ≈ = ≡_F, EL(k) holds in every pasting context Δ, for every k.

*Proof.* Let u, u′ : A be parallel kernel terms over Δ with ⟦u⟧ = ⟦u′⟧. By Lemma V:
- Δ′ := Var(u) is a pasting sub-context, and Var(u′) = Δ′;
- u and u′ factor as ũ[ι] and ũ′[ι] through the inclusion ι : Δ′ → Δ;
- ⟦ũ⟧ = ⟦ũ′⟧ has full support in F(Δ′).

So coh_{Δ′, ũ → ũ′} is a coherence-case coherence, accepted in every row of `spec/02`'s table, and so is its reverse. Their images are identities. Substituting ι gives e and e′. ∎

**Lemma V [argued for two-tier L; (ii) open for uniform L].** Let u be a kernel term over a pasting context Δ.
- (i) Var(u) is a pasting context, and supp⟦u⟧ = Var(u), where the support is the Gray support projected to variables.
- (ii) The inclusion of a pasting sub-context induces an injective map F(Δ′) → F(Δ).

For two-tier L:
- (i) is E1's "supp = Var" on a single hom, together with the hom-wise form of 𝔉;
- (ii) holds because 𝔉's homs are ν of Steiner complexes, and sub-complexes include injectively.

For F_{V+S}, (ii) is not known.

**Corollary 4.4.** Strict associators and unitors (≈ = ≡_F) over two-tier L are conservative in every pasting context in every dimension, given Lemma 1.3. The same holds over uniform L given also Lemma V (ii). In particular, everything a coherence head sees is safe: its type is built over its own pasting context.

### 4.3 L in arbitrary contexts [open]

The users of the surface work in arbitrary contexts. There, by Corollary 3.4, conservativity is equivalent to the following.

**Conjecture GRC (Gray relative coherence).** Let the kernel be two-tier L, or uniform L in each setting. In every finite context Γ, any two parallel kernel terms with the same image in the free Gray-enriched category on Γ (respectively F_{V+S}(Γ)) are connected, in both directions, by kernel terms whose images are identities.

Evidence for it:
- The obstruction that kills full strictness over P (Corollary 4.1) is an Eckmann–Hilton identification, and ≡_𝔉 does not make it. In 𝔉, the two composites of a : 1ₓ → 1ₓ with itself differ by a directed interchanger, so they are not ≡_𝔉-equal.
- Gordon–Power–Street prove the semantic statement in dimension 3: every tricategory is triequivalent to a Gray-category. GRC is a syntactic, all-dimensions, directed analogue.

Against it: no RC-type theorem for the Gray image exists yet outside pasting contexts. For P, such statements fail exactly in contexts that are not loop-free.

### 4.4 Classification by subsets of {associators, unitors, interchange} (Anthony, 2026-11-22)

Write S ⊆ {A, U, I} for the laws made definitional, with ≈_S as in §1.2. Conservativity (Definition 2.1) is **downward closed** in S: if S′ ⊆ S, then ≈_{S′} ⊆ ≈_S. So every S′-surface derivation is an S-surface derivation, and conservativity for S gives it for S′. The classification is therefore determined by the maximal conservative subsets.

**Over L.**

**Proposition 4.6 [Agda for two-tier L; proved for uniform L].** Let the surface identify the two layerings (f◁β);(α▷g′) and (α▷g);(f′◁β) in ΣD¹ ∨ ΣD¹. Then it is not conservative at that pasting context, in dimension 3. ≈_S does this for every S ∋ I, since the identification is an instance of the whiskering form of I (§1.2); so does any other surface equality that strictifies interchange across objects.

*Proof.* The interchanger converts to the reverse type, which the kernel leaves empty. For two-tier L this is `no-reverse-interchanger`. For uniform L it is requirement 3 in every admissible theory, `spec/02` §2.4. Apply `Embed.reverse-breaks`. Agda: `Surface/StrictInterchange.agda`, `strict-interchange-not-conservative`, for every surface equality whatsoever that identifies the pair. ∎

Consequences:
- Over L, **every S containing I fails**: {I}, {A, I}, {U, I} and {A, U, I}, with I in its whiskering form. This is a theorem, not a design choice. (With I only in Godement's horizontal form, I cannot even be stated over L, which has no horizontal composite of positive-dimensional cells in adjacent homs; the whiskering form is the one that means "strict interchange" there.)
- The reason is that interchange in L is directed. Strictifying it equates two cells that the kernel joins in one direction only. By Theorem C, conservativity needs both directions.
- What remains is S ⊆ {A, U}. By downward closure, everything there follows from {A, U}, which is §4.2–4.3: conservative in pasting contexts, and GRC in general.
- Interchange *inside* a hom of two-tier L is already strict in 𝔉. It is part of ≡_𝔉 and is not an extra choice.

**Over P (for comparison; this is the setting of Simpson's conjecture).**

| S | Status |
|---|---|
| any S | conservative in every strong-Steiner context in every dimension, and in every context through dimension 3 (≈_S ⊆ ≡_ν and Corollary 4.1) **[proved]** given Lemma 1.3 |
| ≡_ν (all of image equality) | fails in (x, a : 1ₓ → 1ₓ) at dimension 4 **[proved]** (Corollary 4.1) |
| {A, U, I}, {U, I} | fail at the same place **[argued]**: the braid/identity pair is ≈_{U,I}-equal, because each constituent cell is a coherence between ≈_{U,I}-equal words, hence ≈ 1 by clause (ii) of §1.2, and a composite of identities is an identity under U. This is Simpson's Eckmann–Hilton argument in type-theoretic form. Not yet written out cell by cell |
| {A, I} (weak units) | **[open]**. This is the type-theoretic form of Simpson's conjecture that weak units suffice; Joyal–Kock prove the semantic version for one object and one arrow in dimension 3 |
| {A, U}, {U} (contained in ≡_sua, ≡_su) | **[open]** in general contexts (§4.1) |
| {A}, {I} | **[open]**; they follow from {A, I}. {I} alone may be conservative for a cheap reason: without U, the whiskering law identifies few terms |

**Conjecture SC-P [conj].** S-strictification is conservative over CaTT in every context if and only if S ⊉ {U, I}. Equivalently, {A, I} and {A, U} are both conservative. Evidence: the failing cases are exactly the Eckmann–Hilton ones, and the semantic analogues are Simpson's conjecture and Gordon–Power–Street.

The outbox prompt asks for both classifications, over L and over CaTT, as one question.

## 5. What this means for the surface design (S6, S19)

- **Over L, the only strictifiable pair is associators and unitors** (Proposition 4.6). S6's "two of three" is not a free choice over L: any pair that includes interchange is not conservative.
- **The surface's definitional equality should be ≡_F of the declared setting.** The CaTT_sua rewrite rules are an implementation of a sound fragment of it (Lemma 1.1). This makes associators and unitors definitional and leaves interchange directed. It needs no extra rule class: it is read off the same free objects the side condition already uses.
- **Deciding ≈ in an arbitrary context.**
  - ≡_sua is decidable by normalisation (FRV: strongly terminating and confluent).
  - Equality in F(Γ) is decidable on pasting contexts (`spec/02` §2.3).
  - For arbitrary finite contexts, decidability is not established here for 𝔉 or F_{V+S} **[open]**. This bears on implementing the surface, not on the conservativity results.
- **Trust without re-checking.** Theorem A is the guarantee. The proof obligation for a *new* surface feature is exactly (E), (SC) and EL in the contexts where it is used.

## 6. Formalization (S19 (c))

`src/CaTTExp/Surface/Conservativity.agda` is parameterised by a signature with closed constant types and an arbitrary side condition, so it applies to P, two-tier L and uniform L alike. Contents:
- `SurfaceEq`: hypothesis (E), with ≈ indexed by the context. `Pw` is the pointwise extension to substitutions. `sub-cong-ty/tm/sub` (substitution of ≈-related substitutions) are **proved**.
- `_⊢ˢty_`, `_⊢ˢtm_∶_`, `_⊢ˢsub_∶_`: the surface judgments, with (conv).
- `SideResp` is (SC). `KCAt Γ` is (KC) at Γ.
- `Conservative.elab-ty / elab-arr / elab-tm / elab-sub` is the elaborator. `conservative`, `conservative-everywhere` and `no-new-inhabitants` give Theorem A, local in Γ.
- `Embed.emb-*` embed kernel derivations in the surface. `Embed.reverse-breaks` is the obstruction.
- `ConservativeAt`, `Converse.RelCohAt` (with the ≈ 1 half) and `Converse.necessary` give Theorem C.
- `Trivial` checks non-vacuity.

`src/CaTTExp/Surface/StrictInterchange.agda` contains `strict-interchange-not-conservative` (Proposition 4.6, two-tier L).

`src/CaTTExp/Surface/TheoremB.agda`: Theorem B. By recursion on a kernel type B ≈ B′ it builds a transport map on all cells over B (transport over the base, then whisker with the EL-cells), so a term of type A goes to a term of type exactly A′ (`kc-from-el`); `conservative-from-el` combines it with Theorem A. Hypotheses, all explicit module parameters: arr-inversion, dimension preservation, presupposition, an abstract predicate `Unit` ("≈ an identity"), and a whiskering operation `wh Γ j p x q`, which sees the context Γ, with its typing rule (`Wh-wf`, stated with the explicit type transformer `whTy`) and unit law (`Wh-≈`). An earlier version gave `wh` no context; independent review showed that `Wh-wf` was then unsatisfiable, because a variable's dimension depends on Γ. `ELAt` is undimensioned.

`src/CaTTExp/Surface/WhiskerPure.agda` instantiates the interface for plain CaTT.
- `wh Γ k p x q = (p ◃ₖ x) ▹ₖ q` is built from the derived whiskers `lwT` and `rwT` of `Derived`/`DerivedBoundary`. It reads the types of its arguments off Γ (`tyOf`).
- `Wh-wf-pure` proves TheoremB's `Wh-wf` for every E. The type equality is syntactic, as `Wh-wf` demands: the boundaries of (p ◃ₖ x) ▹ₖ q are literally the whiskers of the boundaries of x.
- `Consistent` instantiates every hypothesis of `Hyp`/`Thm` at once: a coarse E (types related iff of equal dimension, all terms related) with `Unit = ⊤`. So the module parameters are jointly satisfiable. There `Wh-≈` and `Unit` hold trivially, since all terms are related; that `Wh-≈` holds together with `Wh-wf` for a non-trivial ≈ is part of the open item. That E is not the instance of interest; for it, `ELAt` fails in most contexts (already at D¹: x ≈ y, but there is no cell y → x).
- Not proved: `Wh-≈` for the ≈ of interest (≡_F or ≡_sua), which needs that ≈ formalized; and the interface for two-tier and uniform L.

Not formalized yet:
- The whiskering interface for two-tier and uniform L: derived whiskers in the Gray kernels, with their side condition for all k, j (plain CaTT is done in `WhiskerPure`).
- `Wh-≈` for the ≈ of interest, once that ≈ (≡_F or ≡_sua) is formalized.
- The dimensioned form of `ELAt` (EL below dim B only).
- The dimension-bounded form of Theorem A.
- Lemmas 1.1, 1.3 and V.
- The surface presupposition lemma (§2).
- Proposition 4.3.

## 7. Open items

| Item | Owner |
|---|---|
| Conjecture GRC (§4.3); EL for ≡_sua over P in arbitrary contexts; the classification Conjecture SC-P | outbox prompt `semistrict-surface-conservativity.md`; this thread keeps working on it |
| Lemmas 1.2, 1.3 and V written out; Lemma V (ii) for F_{V+S} | this thread (S19) |
| Insertion vs designated lifts in uniform L (Lemma 1.1, uniform case) | this thread, cross-referenced to S11 |
| Agda: the whiskering interface of `TheoremB` for two-tier and uniform L (plain CaTT done); `Wh-≈` for the ≈ of interest once ≡_F/≡_sua is formalized; the dimension-bounded Theorem A; Lemma 1.1 in the strict model; the surface presupposition lemma | this thread (S19 (c)) |
| Check with the SU normaliser that the Eckmann–Hilton pair is not ≡_sua-equal | this thread |
| Decidability of ≡_F in arbitrary finite contexts, for the surface checker | this thread (S19) |
