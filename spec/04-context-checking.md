# Chapter 4. Context checking

Two kinds of context appear in the kernel.
- The context of a **coherence** must be a pasting context. That is decidable and is the only shape check `coh` makes (chapter 1, §1.3).
- Every other well-formed context is a finite computad: variables whose boundaries may be arbitrary terms. Such contexts are the **bases** of diagrams, weights and limits (chapter 6). The kernel reads them **weakly** and checks nothing beyond well-formedness.

The question this chapter settles is whether a base must be *homotopical* (its free strict ω-category F(Γ) agreeing with its free weak one Free(Γ)). It need not. Homotopicality enters only as an optional, decidable judgment `⊢hpol` that makes presentations smaller.

## 4.1 Coherence contexts

**Rule.** (coh) has the premise Δ ⊢ps (chapter 1, §1.4).

**Side condition and decision procedure.** Δ ⊢ps is decided by the deterministic pasting checker (chapter 1, §1.3).

**Example.** The composable pair is accepted; the 2-sphere is rejected (chapter 1, §1.3). The parallel pair `(x, y : ⋆, f, g : x → y)` is rejected as a coherence context.

**Semantics.** Coherences are only ever generated over pasting diagrams, whose free strict and free weak ω-categories agree, and whose free objects in every row of chapter 2 have the combinatorial descriptions that side conditions compute in.

**Status.** **Agda-checked** (`CaTTExp.PastingCheck`). **Source:** chapter 1.

## 4.2 Bases are read weakly

**Rule.** For a well-formed context Γ (Γ ⊢, chapter 1, §1.2), a diagram over Γ in an object or hom is a substitution out of Γ. The kernel interprets it as a functor out of **Free(Γ)**, the free weak ω-category on the computad Γ, never out of the free strict ω-category F(Γ). No kernel rule has homotopicality of Γ as a premise.

**Side condition and decision procedure.** None beyond Γ ⊢, which is decidable (chapter 1, §1.5).

**Example.**

| Base | Accepted? | Meaning |
|---|---|---|
| parallel pair x ⇉ y (equalizers) | yes | homotopical; the optional fast path applies (§4.4) |
| μ : a · a ⇒ a on a loop a | yes | homotopical (positive 2-polygraph); fast path applies |
| bubble σ : 1_x ⇒ 1_x | yes | weak meaning, presented over a resolution; F(σ) = B²ℕ is never used |
| A : α₀g ⇛ α₁g, B : gβ₀ ⇛ gβ₁ (positive, bubble-free, not homotopical: it has a circle fibre) | yes | weak meaning, over a resolution |
| the semi-Thue family G(T, w, v) of HPOL r4 | yes | weak meaning, over a resolution; no decidable test could sort these |

**Semantics.** A CaTT diagram over Γ is a context morphism out of Γ, i.e. a functor out of Free(Γ). Over a homotopical base this agrees with the strict reading. Over a non-homotopical base the strict reading is not expressible in CaTT at all, so nothing expressible is lost.

**Why nothing is checked.** Homotopicality of finite polygraphs is co-r.e.-complete already on positive 3-polygraphs (HPOL r4). So no decidable test is exact, and no sound and complete r.e. certificate system exists. Bubble-freeness, the obvious candidate, is undecidable in dimension 2 and unsound in dimension 3 (the circle-fibre example above is bubble-free). Any check would reject some homotopical bases, and no extension could close that gap.

**Status.** The undecidability results that rule out a complete check are **proved** (verified researcher answers). The weak reading itself is a design decision, and what would overturn it is a weight over a non-homotopical base with no finite presentation, which Proposition W (§4.3) excludes. **Source:** `notes/design-decisions.md` §2.1–2.4, §2.7; ledger B24, B25.

## 4.3 Finite presentations over every base

The weak reading needs the finite-presentation theorems for totals of weights to hold over arbitrary bases.

**Proposition W.** Let Γ be any finite n-polygraph and T : Free(Γ) → ω a coherent weight whose values are Free(Π_b)[W_b⁻¹] with dim Π_b ≤ m. Then the total ∫T has a finite marked presentation of dimension ≤ n + m.

*Proof outline.*
1. *Resolve the base.* Free(Γ) is an iterated homotopy pushout of globes along their boundaries, by the definition of Free. The bounded-model calculus gives a finite complicial model of dimension ≤ n, and its conversion gives a finite **homotopical** polygraph Γ′ (an oriental of a semisimplicial set, Chanavat Thm 3.35) with a finite set W′ of generators such that Free(Γ′)[W′⁻¹] ≃ Free(Γ).
2. *Pull back and present.* T composed with the localisation is a weight over the homotopical base Γ′; the uniform presentation gives (Ω′, S′) of dimension ≤ n + m.
3. *Localise the total.* By Lemma Loc-total, ∫T is ∫(T∘ℓ) localised at the cartesian lifts of W′. Localising adds no generators.

**Lemma Loc-total.** For B an (∞,ω)-category, S a set of cells, ℓ : B → B[S⁻¹] and T : B[S⁻¹] → ω, the map ∫(T∘ℓ) → ∫T exhibits ∫T as the localisation of ∫(T∘ℓ) at the cartesian lifts of S.

**Decision procedure.** A resolution (Γ′, W′) always exists and is found by a terminating search; a finite equivalence certificate is checkable. The certificate is trivial (Γ′ = Γ, W′ = ∅) exactly when Γ has a `⊢hpol` derivation (§4.4).

**Status.** Proposition W and Lemma Loc-total: **proved** (verified researcher answer, `notes/conjectures/answered/fibration-presentations-characterization-r4-2026-11-20.md`, Response 1). **Source:** `notes/design-decisions.md` §2.5; ledger B14, B25.

## 4.4 The optional judgment ⊢hpol

**Rule.** An inductive judgment Γ ⊢hpol in the style of ⊢ps.

Base rules, one per decidable homotopical class:
- pasting contexts and their Gray tensors;
- graphs (all 1-polygraphs, loops allowed);
- positive 2-polygraphs (Chanavat Cor. 3.39);
- positive-to-one polygraphs and their duals;
- positive 3-polygraphs without matching idle overlaps (relative-coherence r6 Responses 4–5);
- orientals of finite semisimplicial sets (Chanavat Thm 3.35);
- top weight ≤ 2 in any dimension, finite strict cells with abelian tests, one-resource semaphores (homotopy-polygraphs r5);
- the partition test.

Closure rules, each a proved closure theorem:
- suspension;
- adjoining 1-generators in dimension 2;
- adjoining fresh globes along two vertices (vertex-attachment lemma).

**Its only effect.** When Γ ⊢hpol, a weight presentation over Γ may use Γ itself instead of a resolution (§4.3). It is never a premise of a kernel rule, so failing to derive it never makes anything underivable.

**Side condition and decision procedure.** Each base rule is a decidable test on the context; derivations are syntax-directed. The judgment is necessarily incomplete (§4.2) and grows as closure theorems arrive.

**Example.** The parallel pair and μ : a · a ⇒ a have ⊢hpol derivations (graph; positive path 2-polygraph). The bubble has none, and is still accepted as a base.

**Semantics.** Γ ⊢hpol implies F(Γ) ≃ Free(Γ).

**Status.** First base rule (positive path 2-polygraphs) **Agda-checked** as a decision procedure (`src/CaTTExp/Lim/Hpol.agda`); its homotopicality is cited from Chanavat, not formalised, and that the test selects exactly that class is argued informally there. Remaining base rules and suspension closure: **open**, ledger B25 (former owner DSGN). **Source:** `notes/design-decisions.md` §2.2, §2.7.

## 4.5 What the limit rules actually need from a base

The encoded cone-recognition rules accept the lax cone over the bubble σ : 1_x ⇒ 1_x, so nothing in them requires homotopicality (`src/CaTTExp/Lim/WeakBase.agda`). The specified cone construction `coneC` is undefined on the bubble and also on the homotopical base μ : a · a ⇒ a, because it handles only generators of dimension ≤ 2 with variable boundaries. So the restriction in the current limit rules is "variable boundaries, dimension ≤ 2", which is the cone-over-coherences problem (ledger B5), not homotopicality. That problem belongs to chapters 5 and 6.

**Status.** **Agda-checked** for the two instances (`Lim/WeakBase.agda`, independently reviewed). **Source:** `notes/design-decisions.md` §2.6.

## 4.6 Open surface questions

**Q4.1. Whether the user sees ⊢hpol.**
- *Option A: never.* The elaborator tries the base rules, and if they fail it builds a resolution silently. Nothing to learn; presentation sizes can jump without explanation.
- *Option B: as an optional annotation* the user can write to assert the fast path, with an error if it does not derive. Lets an author pin presentation size; one more concept.
- *Option C: as a report only.* The elaborator states which path it took for each limit. Explains sizes without adding syntax.

**Q4.2. How bases are written.** The kernel takes any well-formed context.
- *Option A: as contexts.* Uniform with the rest of the kernel; a base such as μ : a · a ⇒ a needs the composite a · a written as a coherence term.
- *Option B: as polygraph presentations* (generators with source and target words), elaborated to contexts. Closer to how ordinary diagrams are drawn; needs a word-to-term elaborator that chooses bracketings, and different bracketings give different (equivalent) contexts.
