# Unifying the engine's mechanisms (ledger S37)

*Thread "Unify the engine's disparate mechanisms", 2026-11-25. Anthony (project chat, 2026-11-25): "I suspect there's been a lack of thought around the coherence of the overall engine design. I suspect it would be possible to replace some of the existing commitments with more general infrastructure that would unify and simplify and allow the disparate systems to properly talk to and collaborate with each other." Agda: `src/CaTTExp/Binder/FreeModelMark*.agda`. Coordinated with the markings thread (MKL), which owns S36 (object marks on object terms, PR #627); nothing here redoes S36.*

## 0. Summary

The engine grew one mechanism per problem. Surveying all of chapters 1–9, most of these mechanisms are instances of four general principles. Each principle is stated below with what it replaces, what is proved, and what is open.

- **U1. One mark judgment, read in the free model of the marked context (§2).** Every rule that concludes a mark on a coherence reads only the head (Δ, A) and the marks of the arguments. The general rule is: coh_{Δ,A}[γ] has mark m when the head's forced value has m in **F(Δ, μ_γ)**, the free model of Δ with the marking μ_γ pulled back from γ. The fifteen propagation rules of spec chapter 3 ((COH-inv), (OP-inv), (INV-fac), (INV-obj), (PS-fac), (OBJ-k) on coherences, (INV-fac_V), (PS-fac_V), (ORD), (INN-fac_S), (OP-inv_S′), (OP-ps_S′), the marks of (COH-ord)) become sound **decidable fragments** of that one predicate.
  - [proved] Soundness of the general rule, by one factorization argument, in every model class the spec uses (§2.3).
  - [proved] For plain CaTT (P), the two clauses (COH-inv) and (OP-inv) compute the predicate **exactly** (§2.5).
  - [Agda] Any rule of this shape whose conclusion is monotone in the argument marks is substitution-stable, with renaming, substitution and the kernel checker for free. Positive clause lists are monotone by construction. The binder kernel's two existing mark judgments (`varMark`, `headMark`, used by UNI-inv) are proved to be instances (§2.4).
  - [conjecture, outbox] Over pasting contexts the predicate is decidable in V + S. The non-r.e. result of the certificates line is about non-pasting computads and does not apply (§2.6).
- **U2. Object marks act on acceptance through the same free model (§3).** The side condition of (coh) computes in F(Δ, μ_Δ), the free model of the head's own marked context. (COH-ord), the split marks and the open mixed case E15 are instances of this one rule. Soundness is the same factorization. Decidability of the mixed case is E15 (MKL) and is not settled here.
- **U3. Marks are locality classes (§4).** Read semantically, every mark is right orthogonality to a set of maps between finite computads: `inv`, `ps`, `grpd_k`, `trunc n`, `⋆^{≤n}`, the marks of partially lax limits, INIT's `inv` marks, and L-×'s hypothesis. Closure of marks under limits, INIT's mark condition and the entailment relation then follow from one argument each. For the inner marks (`ord`, `iord`, the splits) this reading holds **exactly when** MKL's hypothesis (PW) does, which explains where (PW) comes from and reduces S36(b) to S36(a).
- **U4. One representability schema for object formers (§5).** Every object former in chapters 6–9 states that some functor of a test object is represented, by filler heads of the same shape. INIT is the covariant form. Its dual restricted to contexts in which X occurs only as a source (REP) is the contravariant form. Colimits, free objects, ATTACH, truncations and higher inductive objects are INIT instances. Limits, ⊤, cotensors, commas and hom objects are REP instances. With multimap entries in contexts (chapter 8 already has them), ⊗ is an INIT instance and \, / are REP instances.
  - [sketch] colim_Γ[γ] ≃ μ(Cocone(Γ; X)[γ]) at every level. FREE is INIT of the generic-diagram context, which closes S23 by definition.
  - [proved] A Morita lemma: two positive contexts with equivalent models have equivalent initial models. This turns §7.4 (free objects as lax colimits of the point, open from dimension 3) into a context-equivalence construction that RC supplies.
- **U5. Naming cells that are not forced (§6).** The forced lift (D), the native letter heads (E) and chapter 9's lax-functor rule dcoh_S are one principle: a head is a context, a type and an intrinsic name, and the name is empty exactly when the filler is forced. dcoh_S is already an (E)-style rule in the kernel, named by support. That is evidence for S11's open question (i′), sent to its owner.

Every open item is listed with its owner in §8 and in the ledger (S37).

## 1. Inventory: what the engine has, grouped by the job each piece does

| Job | Mechanisms today | Where |
|---|---|---|
| **Say a term has a property** | `inv`, `ps`, `ps*` on cells; `grpd_k`, `iord`, `ord`, `lsplit`, `rsplit`, `trunc n`, `⋆^{≤n}` on objects; marked diagram variables of partially lax limits; INIT's `inv` marks; mark schemes | ch. 3, §6.1, §9.1, §9.3, §3.9 |
| **Propagate a property** | 15 propagation rules, each with its own soundness lemma; (DES-inv); (UNI-inv); INIT's invertible conclusions; LIFT's and GB-cut's invertible comparisons; T-inv, T-fill, T-ctr; per-former rules for object marks (S36) | ch. 3, §6.2, §7.1, §8.3, §9.1–9.3 |
| **Decide which coherences exist** | SC_𝕋 in ν, 𝔉, F_{V+S(Δ)}; (COH-ord) in 𝔉; split marks via S(Δ); E15 (mixed) open; forced lift | ch. 2, §3.6 |
| **State a universal property** | lim/λ/uni_n (horn form, every n); colim/couni (separate instance); FREE/GEN/LIFT_k; GB-cut_{ρ,n}, GB-dcut; INIT-J1/J2 (higher derived via cotensors); DESC-glue/uni; DJ; L-× row; GB-shape row | ch. 6–9 |
| **Name a cell whose filler is not unique** | forced lift (D) with letter heads (E) as fallback; dcoh_S carries its support; RC terms; canonical Gray terms | §2.2, §9.8, ch. 5 |
| **Check a context class** | ⊢ps; positivity (INIT); sort discipline (ch. 8); ⊢hpol (above the kernel) | ch. 1, 4, 8, 9 |

**The formalization shows the same fragmentation.** The mark rules are encoded at least eight times, and no two share the judgment: `Gray/Marks` (two-tier rules), `Gray/MarksB*` (with destructors), `Uniform/Marks` (superseded), `Uniform/MarksRepaired`, `Uniform/SplitMarks`, `Uniform/InnerInv`, `Binder/Mark` + `HeadMark` + `UniMark` (the kernel's own), `Uniform/ObjectMarks` (S36), and `Gray/MarkSchemes`. Each proves its own substitution lemma, or none. The kernel with binders, where everything is meant to meet, sees only `varMark` and one `inv` axiom per head.

## 2. U1. One mark judgment

### 2.1 The rule

Fix the kernel's syntax with binders (`CaTTExp.Binder`). A **marking** of a context Δ assigns to each variable a set of marks. For a term judgment Γ ⊢ coh_{Δ,A}[γ], the **pulled-back marking** is

```
μ_γ(x) := { m : Γ ⊢ x[γ] m }        for each variable x of Δ.
```

The mark judgment Γ ⊢ t m has four rules, one per kind of term:

```
(VAR)   (x : A)^{…, a, …} ∈ Γ,   a ⊑ m                         ⟹  Γ ⊢ x m
(CST)   m ∈ cstHas(c)                                          ⟹  Γ ⊢ c m
(HEAD)  m ∈ headHas(h, y)                                      ⟹  Γ ⊢ h_y[σ] m
(COH)   the forced value c_{Δ,A} has m in F(Δ, μ_γ)              ⟹  Γ ⊢ coh_{Δ,A}[γ] m
```

- ⊑ is S36's entailment between marks.
- (HEAD) covers every head whose conclusion carries a mark: (DES-inv) on t⁻ˡ, t⁻ʳ, λ_t, ρ_t; J2's (UNI-inv); INIT's invertible rec_y, uni, uni_y; LIFT's β; GB-cut's ε; T-fill's fill(u, v). The head's arity may itself be marked (DES needs `(t)^inv`), which the kernel already checks through `marksOK`.
- **F(Δ, μ)** is the algebra presented by the free model F_{V+S(Δ)}(Δ) (chapter 2) together with, for each variable x and each mark in μ(x), the mark's **relations**:
  - x `inv`: a new cell x⁻ with reversed boundary and the equations x ∗ x⁻ = 1 and x⁻ ∗ x = 1;
  - an object a marked `grpd_k`: the same, for every cell of hom-dimension ≥ k whose hom lands in a;
  - a marked `iord`: the same, for every inner letter landing in a;
  - a marked `ord`: every inner letter landing in a set equal to an identity;
  - a marked `lsplit` (`rsplit`): already in V + S(Δ).
  
  Write q_μ : F(Δ) → F(Δ, μ) for the quotient map. "c has `inv` in F(Δ, μ)" means q_μ(c) has a two-sided inverse.

`ps` is the ∀-mark "y ⊗ t is invertible for every positive y composed before t". For it, (COH) reads the same predicate on the generic extension Δ_y^k = ΣDᵏ ∨ Δ, one k at a time. A uniform-in-k test is what (OP-ps_S′) supplies, so ps stays with its current clauses (§2.6).

### 2.2 What it replaces

Each current rule is a sufficient condition for (COH) in one model class. The table gives the reading.

| Current rule | Its condition, read in F(Δ, μ_γ) |
|---|---|
| (COH-inv) | the value is an identity, so it is invertible in every quotient |
| (OP-inv), (OP-inv_S′) | the value is a path whose top letters are invertible in F(Δ, μ_γ) (cases (i)–(iii)) |
| (INV-fac), (INV-fac_V) | a Gray cell with an invertible factor is invertible in F(Δ, μ_γ) along criterion (1) |
| (INV-obj) | a Gray cell with all factors objects and all `inv` |
| (PS-fac), (PS-fac_V) | the definition of ps*, applied to an argument |
| (OBJ-k) on coherences | the value lands in a hom into a `grpd_k` object, inverted by the relations |
| (ORD) | the value is an inner coherence, and inner letters into an `ord`/`iord` target are inverted or trivial |
| (INN-fac_S) | the split relation plus an invertible input inverts the inner interchanger (M6) |
| the marks of (COH-ord) | F(Δ, μ) factors through 𝔉 when all objects are `ord`, so the two-tier rules apply |

So the chapter-3 rules are **derived**: each is a lemma of the form "in F(Δ, μ), the value is invertible whenever …", and each soundness proof in `uniform-marks.md` §8 and `invertibility-markings.md` §2 is exactly that lemma. What is new is that the kernel rule is the predicate itself, and the lemmas become a decision procedure for it.

### 2.3 Soundness

**Theorem U1.1 [proved].** Let M be a model in any of the spec's classes: algebras of an admissible theory E ⊇ V + S with strict inverses (chapter 3, §3.6 semantics), strict Gray-enriched categories (§3.3), or strict ω-categories (P). Suppose every argument's marks are sound in M: for every x of Δ and m ∈ μ_γ(x), the cell ⟦x[γ]⟧ has the property m. Then ⟦coh_{Δ,A}[γ]⟧ has every mark (COH) gives it.

*Proof.* ⟦coh_{Δ,A}[γ]⟧ = ⟦γ⟧_*(c_{Δ,A}), where ⟦γ⟧_* : F(Δ) → M is the algebra map induced by γ (requirement 5, spec §2.2). Each relation of F(Δ, μ_γ) holds in M under ⟦γ⟧_*:
- an `inv` relation at x: M has a chosen strict inverse for ⟦x[γ]⟧, and the image of x⁻ is sent to it;
- a `grpd_k`, `iord` or `ord` relation at an object a: a cell whose hom lands in a is sent to a cell whose hom lands in ⟦a[γ]⟧, where the mark holds by hypothesis;
- the split relations are part of S(Δ) and hold by the same argument as (coh)'s own soundness (spec §2.3, Semantics).

So ⟦γ⟧_* factors as φ ∘ q_{μ_γ} by the universal property of the presentation. Algebra maps preserve inverses, and an identity or the equations above are preserved, so φ(q(c)) has every mark q(c) has. ∎

Soundness of the whole judgment follows by induction on terms: (VAR) by certification of substitutions, (CST) and (HEAD) by the soundness of each head's rule, (COH) by Theorem U1.1.

The proof uses nothing specific to any mark beyond "its relations hold in M at the denoted cell". That is the single argument behind all the per-rule soundness lemmas.

### 2.4 Substitution and decidability, once [Agda]

`CaTTExp.Binder.FreeModelMark` builds the judgment of §2.1 for the binder kernel from four parameters: an entailment ⊑, the constants' marks, the heads' marks and an **oracle** `cohHas Δ A f m` for (COH), where f is the pulled-back marking. It proves the kernel's three hypotheses on a mark judgment:
- `markVar` (MarkVar): a variable has the marks of its entry;
- `markRen` (MarkRen) and `markSub` (MarkSub): renaming and substitution preserve marks, by one induction on typing (`mark-map`, `pull-map`);
- `up`: the judgment is closed upward under ⊑.

The hypotheses are reflexivity and transitivity of ⊑, upward closure of the three data, and **one structural hypothesis**, `coh-mono`: more marks on the arguments never remove a mark from the coherence. With these, substitution (`Binder.Subst`), presupposition and the certified checker (`Binder.CheckWith`) hold for the kernel with this mark judgment, as they do for any mark judgment satisfying MarkVar, MarkRen and MarkSub.

`CaTTExp.Binder.FreeModelMarkPos` shows that monotonicity is a property of the **form** of the rules. A clause concludes a mark when a condition on the head holds and a **positive** Boolean formula over atoms "argument i has mark m" holds. Every rule of chapter 3 has this form. `evalP-mono`, `cohC-mono` and `cohC-up` prove the hypotheses for every clause list. So any clause list, sound or not, inherits renaming, substitution and decidability, and only its soundness remains to be proved.

`CaTTExp.Binder.FreeModelMarkInstances` proves that the kernel's existing judgments are instances, pointwise on every context, mark and term:
- `varMark-is-markTm`: rule (MARK) alone is the judgment with no clauses;
- `headMark-is-markTm`: `HeadMark` (used by `UniMark` for UNI-inv) is the judgment with headHas b y m = (m is inv) ∧ inv? b y.

`CaTTExp.Binder.FreeModelMarkCatt` instantiates the judgment for plain CaTT with the two clauses of §2.5, on the binder kernel's `cattSide`, and checks by evaluation:
- the composite of two `inv`-marked arrows is `inv`, and with one argument unmarked it is not;
- the identity coherence on an object is `inv` with no marks;
- substituting `inv`-marked variables into an unmarked composite creates the mark.

What the Agda does not contain: the free model F(Δ, μ) itself, and Theorem U1.1. The oracle is a parameter. Its soundness is §2.3 on paper, and for the uniform core it depends on the free-model layers that S3a has not yet built.

### 2.5 In plain CaTT the two clauses are exact [proved]

**Proposition U1.2.** Let Δ be a pasting context of dimension n, M a set of its variables, and coh_{Δ,A} a head of plain CaTT. Its value is invertible in F_ν(Δ)[M⁻¹] iff the head is in the coherence case, or it is in the operation case and every variable of Δ of dimension n is in M.

*Proof.* (⇐) Coherence case: Benjamin–Markakis (arXiv 2406.12127, Prop. 16). Operation case: the value is the composite τ_Δ, a pasting of the top generators whiskered by lower cells. Whiskering preserves invertibility and composites of invertible n-cells are invertible (BM Thm 33 in the weak case, immediate in the strict case).

(⇒) Suppose the head is in the operation case and the top variable x is not in M. Let N be the strict ω-category with one cell in each dimension below n, the monoid (ℕ, +) as its n-cells (every composition along k < n is addition, which is well defined and commutative by Eckmann–Hilton for n ≥ 2), and identities above n. Define a strict functor Φ : F_ν(Δ) → N on generators: every variable of dimension below n goes to the unique cell, x goes to 1, and the other top variables go to 0. Every variable in M goes to an invertible cell (a unique cell or 0), so Φ factors through F_ν(Δ)[M⁻¹]. The top-dimensional part of τ_Δ contains each top generator once (it is the total cell of the Steiner complex), so Φ(τ_Δ) = 1, which is not invertible in ℕ. So τ_Δ is not invertible in the localization. ∎

The weak and strict localizations give the same answer: (⇐) holds in the weak free model by BM, and a cell invertible in the weak localization stays invertible in the strict one, so (⇒) transfers. So in P the kernel's two clauses compute the free-model predicate exactly, and (COH) adds nothing new there. The Agda instance `FreeModelMarkCatt` is that clause list.

### 2.6 In uniform L: decidable fragments, and one conjecture

In V + S the current clause list is sound and not complete:
- E13's verified answer and the r2 answer (`uniform-marks.md` §8.6) computed the predicate on **single Gray cells** over principal disk trees: criterion (1) is exact there. That is the predicate of §2.1 on the arities ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}.
- Nothing yet computes it on an arbitrary forced value over an arbitrary pasting context.

**What the certificates line does and does not show.** Invertibility in free L-models is not recursively enumerable, even for one fixed finite marked computad (`marking-alternatives.md` §10). The computad there is built from a Turing machine and has loops: it is not a pasting context. The r2 undecidability result for letters on composite operands likewise uses matching contexts with group relators. Over a **pasting** context Δ with a set of marked generators, nothing is known either way. Free algebras on pasting diagrams have no non-identity invertible cells (positivity, (M5)), and the question is how much the localization at M adds.

**Conjecture U1.3 (outbox `conjectures/outbox/free-model-invertibility.md`).** For every admissible theory E between V and T₁₂, invertibility of a cell in F_E(Δ)[M⁻¹] is decidable, uniformly in the pasting diagram Δ, the marked set M and the cell.

If U1.3 holds, (COH) is a kernel rule that is complete for heads in the sense of §2.5, and the chapter-3 rule list becomes its decision procedure. If it fails, the clause list stays the kernel's rule, as a decidable sufficient criterion, exactly as principle 0.6 allows. Either way the judgment's form, its metatheory (§2.4) and its soundness (§2.3) are the same, so nothing has to wait on the answer.

**What U1 does not change.** No rule of chapter 3 is withdrawn, and no judgment is lost. The saturation theorem (§3.7) is about closure under inv-intro on raw terms, which (COH) does not ask for. ps is not certified from data (§3.7): (COH) only ever reads ps from argument marks.

## 3. U2. Object marks act on acceptance through the same free model

The side condition of (coh) is a test in the free object of the head's theory. Today that theory is chosen three ways: V + S(Δ) from the split marks, 𝔉 by the separate rule (COH-ord) when every object is `ord`, and nothing yet for mixed heads (E15). Under U2 there is one rule:

```
Δ ⊢ps     Δ ⊢ t →_A u     SC_{F(Δ, μ_Δ^{eq})}(Δ, t →_A u)     Γ ⊢ σ : Δ
────────────────────────────────────────────────────────────────────── (coh)
            Γ ⊢ coh_{Δ, t →_A u}[σ] : (t →_A u)[σ]
```

where μ_Δ^{eq} keeps only the **equational** object marks of Δ (`ord` and the splits). Invertibility marks (`inv`, `iord`, `grpd_k`) do not enter acceptance. They act only through U1. The reason is that inverting a generator of a pasting diagram can create loops: inverting f in the 2-disk α : f ⇒ g makes g a loop up to equivalence. Pasting contexts are required for coherences precisely because loop-free free objects are the ones whose strict and weak versions agree (spec §4.1).

- **All objects `ord`.** The inner letters are identities, so F(Δ, μ) = 𝔉(Δ). This is (COH-ord), now an instance rather than a separate rule.
- **Split marks.** F(Δ, μ) = F_{V+S(Δ)}(Δ), as now.
- **Mixed `ord` (E15).** F(Δ, μ) is F_{V+S(Δ)}(Δ) with the inner letters into the `ord` objects set to identities. This is E15's F_m(Γ). Its soundness is Theorem U1.1's factorization, as E15 already notes.

**What U2 settles and what it does not.** It fixes the form of the mixed rule, so that E15 is a question about a decision procedure, not about which rule to adopt. It does not settle E15's open points, which stay with MKL: (a) decidability of SC in F_m(Γ), and (b) whether target-only `ord` suffices (MKL expects it to fail through binary outer letters with inner content in their operands). The forced-lift condition reads the same free object, so it needs no separate treatment.

## 4. U3. Marks are locality classes

### 4.1 The reading

Each mark m comes with a set J_m of maps between finite computads (or between Gray tensors of them with test objects), and means **right orthogonality** to J_m:
- a cell t has m iff its classifying map extends uniquely (up to contractible choice) along every j ∈ J_m;
- an object C has m iff C is J_m-local: Map(B, C) → Map(A, C) is an equivalence for every (j : A → B) ∈ J_m, tensored with every test object.

| Mark | J_m |
|---|---|
| `inv` on an n-cell | Dⁿ → J_n, the walking n-equivalence |
| `grpd_k` on C | Dⁿ → J_n for n ≥ k, on the homs into C |
| `trunc n` on C | the boundary inclusions ∂Dᵐ → Dᵐ for m ≥ n + 2 (fillers) together with grpd_{n+1} |
| `⋆^{≤n}` in INIT | the same as `trunc n` |
| `iord` on C | for each inner letter ℓ on its arity Θ_ℓ: F(Θ_ℓ) → F(Θ_ℓ)[ℓ⁻¹], on the homs into C |
| `ord` on C | F(Θ_ℓ) → F(Θ_ℓ)/(ℓ = 1), on the homs into C |
| `lsplit`, `rsplit` | F(C_{2,1}) → F(C_{2,1})/(split equation), on the homs into C |
| marked diagram variable of a partially lax limit | the comparison transfor's components over it: Dⁿ → J_n |
| `ps` on t | the adjunct of t inverts the mixed cells (spec §3.4, C1″) |
| L-×'s hypothesis on B | κ_{A,W} : A ⊗ W → A × W, for all A, W |

### 4.2 What follows uniformly

**Proposition U3.1 [proved for representable marks].** If m is a locality class, then:
1. **Limits.** A limit of m-local objects is m-local, for every finite diagram and every marking of it, since Map(A, lim Dᵢ) = lim Map(A, Dᵢ) and a limit of equivalences is an equivalence. This is S36's (O-lim) for every such m at once.
2. **INIT.** If J_m is a set of maps between compact objects, the m-local objects form an accessible reflective subcategory closed under limits and filtered colimits. That is exactly INIT's condition on a mark of X (spec §9.3), so INIT with X marked m is sound, by the verified INIT answer for any presentable carrier category.
3. **Entailment.** m ⊑ m′ holds when J_{m′} lies in the saturation of J_m. For example, J_{grpd_k} ⊆ J_{iord} after saturation for k ≤ 2, because inner letters have hom-dimension ≥ 2 (S36, Lemma 2.1).
4. **One filler rule per mark.** A marked object is local, so the restriction along each j ∈ J_m has fillers. T-fill, T-inv and T-ctr (for `trunc n`), (OBJ-k) on variables and heads (for `grpd_k`), and L-× (for `grpd_2`, by Campion) are each this one statement at their mark.

**The inner marks and (PW).** For `iord`, `ord` and the splits, the table's J_m is a set of maps of hom-algebras, and the mark says something about Map(X, C) for every X. Reading it as locality for maps out of a fixed finite computad needs inner letters to be natural in X: precomposition with a 1-cell p : X′ → X must send the letter ℓ(A, B) of Map(X, C) to the letter ℓ(p ▷ A, p ▷ B) of Map(X′, C). That is exactly MKL's hypothesis (PW) (`object-marks.md` §3.4). So:

**Proposition U3.2 [sketch].** Under (PW), `iord`, `ord`, `lsplit` and `rsplit` are locality classes for sets of maps between compact objects. Then Proposition U3.1 gives both (O-lim) for the inner marks (S36(a)) and INIT with X marked `iord` or `ord` (S36(b)). So S36(b) is not a separate problem: it follows from (PW).

Without (PW) the reading fails in the expected way. If precomposition does not preserve inner letters, "C has trivial inner letters" is not stable under the limit's legs, which is the failure S36(a) records. MKL's caution stands: (PW) equates two parallel cells with the same Gray image, and E13 shows such pairs need not be equal in V + S, so (PW) needs its own argument. U3 does not supply it. It shows that (PW) is the only input.

## 5. U4. One representability schema for object formers

### 5.1 The pattern

Every object former of chapters 6–9 says that, for a fixed context Δ of "generic data" with a distinguished object X, the functor sending a test object to the Δ-data on it is represented. Covariantly, maps μΔ → A correspond to models of Δ with carrier A. Contravariantly, maps c → νΔ correspond to models with carrier c. In each case the kernel states the correspondence by filler heads of one shape: a structure map, a filler for each boundary datum, and an invertible comparison.

| Former | Variance | Δ | Today's filler heads |
|---|---|---|---|
| colim_Γ[γ] | covariant | Cocone(Γ; X)[γ] | couni over cocone transfors, every n |
| ⟦Γ⟧ (FREE) | covariant | X with Γ placed in 𝒦(⊤, X) | LIFT_k, every k |
| C[x : a → b] (ATTACH) | covariant | derived already | — |
| μΔ (INIT), ‖A‖_n, HITs | covariant | Δ | J1, J2; higher derived through cotensors |
| U ⊗ V | covariant | (X, m : (U, V ▸ X)) | GB-cut pair row |
| lim_Γ[γ] | contravariant | Cone(Γ; X)[γ] | uni over Horn_n, every n |
| ⊤, A × B, comma, Hom_C(a, b), cotensors | contravariant | instances of the cone context | via lim |
| A\C, C/A | contravariant | (X, e : (A, X ▸ C)), (X, e : (X, A ▸ C)) | GB-cut left and right rows |

Three conventions for higher levels coexist: lim, LIFT and GB-cut state a filler at every n; INIT states n ≤ 1 and derives the rest through cotensors. The cell shapes are built separately: Tr_n and Horn_n for limits, cylinders Γ ⊗ Dᵏ for Diag, the arrow context Δ^→ for INIT, time slots for GB.

### 5.2 The proposal

- **INIT** (spec §9.3) as the one covariant former, unchanged.
- **REP**, the contravariant former, for contexts Δ in which X occurs only bare (or as X ⊗ B, B ⊗ X) in the **sources** of operations and never in a target. Its models in c are then a finite limit of representables in c, which is why REP is sound wherever finite limits exist and needs none of the exponentiability that sinks general final models (`universe-free-principles.md` §4.2). REP is lim read through its cone context. It adds no derivability. It makes the internal homs \ and / instances of the same schema.
- **One cell-shape construction.** The level-n data of a representability is Δ-data on the test object tensored with Dⁿ, relative to ∂Dⁿ. Tr_n, Horn_n, the Diag cylinders, INIT's cotensor levels and GB's time slots are instances of this one construction, which chapter 5 builds from RC.

### 5.3 What is proved

**Proposition U4.1 [sketch].** colim_Γ[γ] and μ(Cocone(Γ; X)[γ]) have the same universal property at every level.

*Argument.*
- The cocone context is positive. Each leg q_x : γ(x) → X has an X-free source and target X. Each higher q_t is a cell between composites of earlier operations, with target X. A marked diagram variable gives an `inv` mark on its q_t, which INIT allows.
- Level 0: INIT-J1 gives, for a cocone σ with apex A, a map μ → A with an invertible comparison, which is couni at n = 0 with J2's invertible components.
- Level 1: INIT's derived level is a model morphism into the cotensor [⟦D¹⟧, A]. A model in that cotensor is a cocone whose cells may be non-invertible (Δ's cell variables carry no `inv` unless marked), so it is a lax cocone transfor. The model morphism's comparisons are invertible. That is couni at n = 1: a filler with an invertible comparison over a lax transfor.
- Level n: the same with [⟦Dⁿ⟧, A], given that Tr_n(Γ; c) is the context of cocone models in that cotensor. Chapter 5 defines Tr_n as the iterated cylinder of the cone, so this identification is the open step. It needs the orientation conventions of `conventions.md` §4 checked against the cotensor's.

**Corollary U4.2 (S23) [by definition].** Define ⟦Γ⟧ := μ(X, Γ placed in 𝒦(⊤, X)). The context is positive: each object variable becomes an element ⊤ → X, each cell a cell between composites with target X. FREE, GEN and LIFT_0 are INIT-form and INIT-J1. LIFT_1 at strong cells is INIT-J2, and at lax cells it is INIT's derived level through [⟦D¹⟧, C]. So S23's question, whether every free object is an INIT instance, is answered yes by taking this as the definition. The comparison with chapter 7's computad reading uses Hom(⊤, C) ≃ C (spec §6.6).

**Lemma U4.3 (Morita) [proved].** Let Δ, Δ′ be positive in X, and suppose there are context morphisms F : Δ → Δ′ and G : Δ′ → Δ over X whose composites are related to the identities by invertible cells, naturally in the carrier. Then μΔ ≃ μΔ′.

*Proof.* Precomposition with F and G gives an equivalence between the model ω-categories Mod_Δ(A) and Mod_{Δ′}(A), natural in A. Both initial models represent their model functors (INIT-J1, J2 and the derived levels). Representing objects of equivalent functors are equivalent (Yoneda). ∎

**Consequence for §7.4 [reduction].** "⟦Γ⟧ ≃ laxcolim_Γ(const ⊤)" is open from dimension 3 (B6, B20, B21), including higher cocone morphisms. Under U4 both sides are INIT instances: μ(Γ placed in 𝒦(⊤, X)) and μ(Cocone(Γ; X)[const ⊤]). A lax cocone over the constant point has legs q_x : ⊤ → X and cells q_f : q_x → 1_⊤ ∗ q_y, so the two contexts agree up to unitors. By Lemma U4.3 the theorem reduces to a context equivalence whose cells are unitor coherences. RC (§5.1) supplies those in every dimension. The higher cocone morphisms disappear: they are INIT's derived levels on both sides.

### 5.4 What U4 does not cover

- **DESC** is about families p : E → X, not about a represented object. It states its gluing and uniqueness by the same filler pattern, but over a category of fibrations, which is not an object of the theory. It stays a rule (F12 shows it is independent of INIT).
- **GB-shape** identifies two kinds of context entries, a probe and a diagram of its shape. It is the axiom that makes Lemma U4.3 apply across the two sorts. It stays a rule.
- **L-×** becomes a locality statement (§4.2 item 4), not a representability.

## 6. U5. Naming cells that are not forced

Three parts of the kernel name a cell of a decision device:
- (coh) with the forced lift (D): a head names a cell only when its type has a single filler after loop removal (spec §2.2);
- the fallback (E): forced heads, plus a head for each native letter of V, named by its tag (`design-decisions.md` §5.8);
- dcoh_S (spec §9.8): a cell between parallel lax-functor images, named by its support S, a set of simplices of the nerve. In O₃ there are two distinct 2-cells f₀₁ ; f₁₂ ; f₂₃ ⇒ f₀₃, so this type has two fillers, and dcoh_S names both.

These are one principle: **a head is a context, a type and an intrinsic name, and the name is empty exactly when the filler is forced.** The name must be determined by the free model, not by an enumeration. A native letter's tag is such a name. So is a support in a loop-free Steiner complex, where a cell is determined by its support. (C) in `design-decisions.md` §5.3 (the lift as part of the term) is rejected because a path of letters is not intrinsic. Neither a tag nor a support is a path.

**Finding [for S11].** The kernel already contains an (E)-style rule, dcoh_S. It names non-forced fillers because lax functors need them: the two composites of O₃ are both required, and neither is forced. That is a case in the kernel where (D) alone would lose a type inhabitant the semantics has. It bears on S11's open question (i′), which asks whether (D) loses inhabitation of a formable type, although dcoh_S's types live over lax-functor contexts and not over pasting contexts. It suggests that if (E) is adopted for V + S, dcoh_S and the letter heads should be stated as one rule. The decision stays with S11's owner.

## 7. Context classes

The kernel checks four classes of contexts: pasting contexts (⊢ps), positive contexts (INIT), the sort discipline of chapter 8, and, above the kernel, ⊢hpol. Under U4 the second and third are both the variance check of the representability schema: INIT asks X to be covariant, REP asks it to be contravariant, and chapter 8's sort discipline is the same check for multimap entries. ⊢ps and ⊢hpol are about something else, which free objects are combinatorially describable, and stay as they are.

## 8. Open items and owners

| Item | What | Owner |
|---|---|---|
| S37(a) | Conjecture U1.3: decidability of invertibility in F_E(Δ)[M⁻¹] for pasting Δ. Outbox `conjectures/outbox/free-model-invertibility.md`; in-house attempt continues (first step: the 2-dimensional pasting diagrams in V, where the letters are known) | this thread |
| S37(b) | Spec: restate chapter 3's propagation rules as clauses of (COH), and §3.6/(COH-ord) as U2. Unblocked: PR #627 (S36) merged 2026-11-25 | this thread |
| S37(c) | Agda: re-express the separate mark encodings (`Gray/Marks`, `Uniform/MarksRepaired`, `Uniform/SplitMarks`) as clause lists over `FreeModelMark`, so that one substitution proof covers them; then honesty review | this thread |
| S37(d) | (PW) is the single input for S36(a) and S36(b) (Proposition U3.2) | MKL (S36), notified |
| S37(e) | U4: write out REP's soundness, Proposition U4.1 at level n (the Tr_n / cotensor identification), and the §7.4 reduction as a construction | this thread |
| S37(f) | dcoh_S as an (E)-style rule: evidence for S11 (i′) | S11 owner ("Settle the designated-lift choice"), notified |
| S37(g) | U4 for the Agda binder kernel: lim, colim and ⟦Γ⟧ as INIT/REP instances instead of separate head families (relevant to S26g, S26k, S26m) | proposal to COLIM and HEADS, via the coordinator |

## 9. Sources

- Spec chapters 1–9; `invertibility-markings.md` §2; `uniform-marks.md` §8; `marking-alternatives.md` §§3, 9–10; `mark-schemes.md` §4; `design-decisions.md` §5; `universe-free-principles.md` §4; `object-marks.md` (PR #627).
- Researcher answers: `invertibility-in-directed-interchange-2026-11-21.md` and `-r2-2026-11-25.md`; `invertibility-certificates-r3-2026-11-23.md`; `forced-lift-generation-2026-11-25.md`.
- Benjamin–Markakis, *Invertible cells in ω-categories*, arXiv 2406.12127 (Prop. 16, Thm 33).
- Campion, arXiv 2311.00205 (Gray tensor on Cat_n, used for L-×).
- Adámek–Rosický, *Locally presentable and accessible categories* (orthogonality classes of maps between presentable objects are reflective, accessible, and closed under limits and filtered colimits).
