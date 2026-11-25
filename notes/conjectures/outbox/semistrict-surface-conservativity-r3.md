# Which semistrict definitional equalities are conservative over CaTT-style theories? (round 3)

*A self-contained problem. Standard higher category theory is the only background assumed. This is the third round. The earlier prompts and their responses are reproduced in two repository files:*
- *`notes/conjectures/answered/semistrict-surface-conservativity-2026-11-24.md` (round 1, "R1.n");*
- *`notes/conjectures/answered/semistrict-surface-conservativity-r2-2026-11-25.md` (round 2, "R2.n").*

*§2 summarises what is settled. Those results are taken as known and are not re-asked.*

**What we are asking for.** Three conservativity statements remain open. Each is now known in low degrees, or on special classes of contexts. We want each one **in every finite context and every degree**, by a uniform argument, or a counterexample:
- **(a)** associativity and units over every theory with directed interchange at every level;
- **(b)** the binary surfaces containing interchange over ordinary CaTT;
- **(c)** Catt_sua over ordinary CaTT.

Round 2 produced several hundred results for particular classes of computads, particular degrees, or particular presentations. Results of that shape are **not** what we want now. We especially do not want further degree-by-degree bounds, results on a single class of presentations, or complexity of per-context recognition. §3 says what a useful partial answer looks like.

## 1. Setting

### 1.1 CaTT and its strict images

**CaTT** is Finster–Mimram's type theory for weak ω-categories (arXiv 1706.02866).
- Contexts are finite computads, written as lists of typed variables.
- Types are ⋆ or `t →_A u`.
- Terms are variables or `coh_{Δ, A}[σ]`. Here Δ is a pasting context (`Δ ⊢ps`), A = `t →_B u` is a type over Δ, and σ : Γ → Δ is a substitution.
- The rule for `coh` has a side condition on (Δ, A) alone.
- There is no definitional equality: types are compared syntactically.

**Kernels.** A *kernel* 𝕋 assigns to each finite computad Γ a strict higher-categorical structure F_𝕋(Γ), free on Γ. It is functorial for substitutions of cells for generators, and it comes with a projection π : F_𝕋(Γ) → ν(λΓ) to the free strict ω-category on Γ, read as a polygraph (Steiner, *Omega-categories and chain complexes*, HHA 2004). In every kernel below, composition is strictly associative and strictly unital. Every well-typed term t over Γ has a strict image ⟦t⟧ ∈ F_𝕋(Γ):
- a variable goes to its generator;
- `coh_{Δ, A}[σ]` goes to σ_*(c), where c is the cell of F_𝕋(Δ) supplied by the side condition (below).

The theory **CaTT_𝕋** has the syntax and rules of CaTT. Its `coh` side condition is:

```
SC_𝕋(Δ, t →_A u)  :⟺  F_𝕋(Δ) has a cell c : ⟦t⟧ → ⟦u⟧ (an identity allowed)
                       whose projection has full support.
```

Support is measured in the Steiner bases of the relevant Gray-enriched or strict quotient (below). The coherence is in the *coherence case* if ⟦t⟧ = ⟦u⟧, and in the *operation case* otherwise. Three kernels are in play:

| Kernel | F(Γ) | Interchange |
|---|---|---|
| ν (ordinary **CaTT**) | ν(λΓ), the free strict ω-category | strict at every level |
| 𝔉 (the **Gray variant CaTT_G**) | the free category enriched in strict ω-categories with the lax Gray tensor | strict inside each hom; directed across objects |
| E (**CaTT_E**), for admissible E (§1.3) | F_E(Γ) | directed at every level |

For ν and 𝔉, c is unique when it exists. The operation case is then exactly "⟦t⟧ = ∂⁻τ_Δ and ⟦u⟧ = ∂⁺τ_Δ" for the total cell τ_Δ, and the coherence case is exactly "⟦t⟧ = ⟦u⟧ with full support".

**Two forms of the coherence case.** The rule above is the *full-support form*. Round 1 used it throughout. A second, *variable form* (written CaTT_𝕋^V) replaces the coherence case by:

```
⟦t⟧ = ⟦u⟧, and every variable of Δ occurs in t : A and in u : A.
```

The operation case is unchanged. For ν the two forms agree. For 𝔉 and F_E the variable form accepts strictly more coherences; §1.2 gives an example. The variable form is the one we intend to use. Answers for the full-support form are also wanted. Please say which form an answer concerns.

### 1.2 The Gray kernel

Every pasting context decomposes uniquely as Δ = ΣΘ₁ ∨ … ∨ ΣΘₙ, with objects a₀, …, aₙ. The homs of 𝔉(Δ) are

```
𝔉(Δ)(aᵢ, aⱼ) = ν(λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ),
```

with ⊗ the Steiner–Ara–Maltsiniotis tensor and factors in execution order. For a general finite computad Γ, 𝔉(Γ) is the free such enriched category on Γ. The total cell τ_Δ is the tensor of the composites of the Θᵢ. Support is measured in the Steiner bases.

Example: over Δ = ΣD¹ ∨ ΣD¹, with α : f ⇒ f′ and β : g ⇒ g′, the coherence of type (f ◁ β) ; (α ▷ g′) → (α ▷ g) ; (f′ ◁ β) is accepted. Its reverse is not, and no term at all has the reverse type.

The coherence case needs full support in the Steiner bases, not only that every variable occurs. Over the same Δ, βα = (f ◁ β) ; (α ▷ g′) and βα₂ = (1_{f;g} ; (f ◁ β)) ; (α ▷ g′) are parallel, have equal images and together use every variable. Their images miss the basis element α ⊗ β, so no single coherence has type βα → βα₂ (either way). A composite of two coherences, a unitor whiskered by α ▷ g′, does have that type. So in CaTT_G with the full-support form, parallel terms with equal images over a pasting context cannot in general be joined by one coherence-case coherence over the variables they use. In the variable form CaTT_G^V, coh(βα → βα₂) is accepted.

### 1.3 Kernels with directed interchange at every level

These kernels direct interchange along k-cells for every k, including inside homs. They are strict theories on the following signature:
- strictly associative and unital composition ∗ₖ in every dimension;
- an elementary interchanger χ for every pair of levels k < l;
- one naturality cell per varying argument, with Leibniz-signed orientation;
- higher cells between routes.

Such a theory E is **admissible** if its free objects on finite pasting diagrams satisfy five requirements:

1. They have an explicit combinatorial description by generators with explicit boundaries.
2. Two cells of the same dimension that use the same generators, counted in the expanded basis, are equal.
3. Every elementary interchanger exists, and its reverse does not.
4. Making every interchanger along a k-cell with k ≥ 1 an identity gives 𝔉(Γ). Making every interchanger an identity gives ν(λΓ).
5. They are closed under substitution of cells for generators.

The projection of §1.1 is the composite of requirement 4. For E, π denotes the first map, to 𝔉(Γ), and support is measured there. The expanded basis of F_E(Γ) is infinite already on Σ[2] ∨ Σ[2].

**Known facts about these theories** (proved elsewhere; full constructions in the repository files `notes/conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`, `-r9-2026-11-20.md` and `-r10-2026-11-20.md`):
- **The least theory V.** On finite pasting diagrams there is a least admissible theory V: F_V(Γ) maps generator-preservingly into F_E(Γ) for every admissible E.
- **Settings.** Two further laws change free objects on pasting diagrams: the *inner law* (crossing a composite A₁ ∗ A₂ past B equals the paste of the two crossings) and its mirror *R*. All four of V, V + R, V + inner law and V + both are admissible and pairwise distinct.
- **Decidability.** Equality and reachability in F_{V+S′}(Γ) are decidable for each of the four settings S′, in every dimension.
- **Loops.** Some free objects have non-identity endo-paths, for example a degree-4 loop H on the 2 × 2 grid with pairwise distinct powers. So c in SC_E need not be unique. The image of an operation-case coherence is a chosen lift: the first shortest witnessing path in a fixed enumeration.
- **Comparison with CaTT_G.** Every CaTT_E derivation projects to a CaTT_G derivation.
- **Interchange inside a hom.** Inside a hom, for 2-cells a, b of one object composable along a 1-cell, there are directed interchangers b ∗ a ⇛ a ∗ b and a ∗ b ⇛ b ∗ a. They are not inverse to each other. The Eckmann–Hilton cells are therefore non-invertible.

The question in (a) concerns only inhabitation. It does not depend on the choice of lift, since ≈_S below is syntactic.

### 1.4 Semistrict equalities

Write A, U and I for the associativity, unit and interchange laws:
- A: (x ∗ₖ y) ∗ₖ z = x ∗ₖ (y ∗ₖ z);
- U: 1 ∗ₖ x = x = x ∗ₖ 1, and 1_{a ∗ⱼ b} = 1_a ∗ⱼ 1_b;
- I, in whiskering form: for j-composable cells a, b of dimension > j, (a ∗ⱼ s b) ∘ (t a ∗ⱼ b) = (s a ∗ⱼ b) ∘ (a ∗ⱼ t b), together with the analogous laws for cells of unequal dimension. Here s and t are the source and target one dimension below the cells, and ∘ is composition along them. With U this is equivalent to Godement's law.

For a kernel 𝕋:
- **Words** over a pasting context Δ are terms built from variables, identities, and the binary composites that exist in CaTT_𝕋. In CaTT these are all ∗ₖ. In CaTT_G and CaTT_E they are vertical composites and whiskerings, since a horizontal composite of positive-dimensional cells across a directed interchange does not exist.
- For S ⊆ {A, U, I}, **≈_S** is the smallest congruence on terms, stable under substitution, that contains:
  - (i) w ≈ w′ for all raw-parallel words w, w′ over a pasting context that are equal in the free algebra satisfying exactly the laws in S;
  - (ii) coh_{Δ, w → w′}[σ] ≈ 1_{w[σ]} for every such pair whose coherence exists in CaTT_𝕋.
- **Published closed forms.**
  - ≡_su is Catt_su (Finster–Reutter–Rice–Vicary, arXiv 2007.08307: disc removal, endo-coherence removal, pruning).
  - ≡_sua is Catt_sua (Finster–Rice–Vicary, arXiv 2302.05303: the same with insertion).
  - They contain ≈_{U} and ≈_{A,U} respectively.

**Conservativity.** T_≈ is T plus the conversion rule: from Γ ⊢ t : A and A ≈ B, conclude Γ ⊢ t : B. T_≈ is **conservative over T in Γ** if every T-type over Γ that is inhabited in T_≈ is inhabited in T. This is the inhabitation form. We do **not** ask for T-terms ≈-equal to the given ones (see §2, item 1).

## 2. What is known (proved or checked; not re-asked)

**1. Forms of conservativity.** Relative coherence (EL) fails for every binary surface already on a point (R1.43), so proofs must be model-theoretic or use rank induction (item 6). Over CaTT_G and over CaTT, every S without I is conservative in every finite context and dimension (R1.3, R1.16, R1.50, R1.51, R1.222). Every S ∋ I fails over CaTT_G and over every CaTT_E, already at ΣD¹ ∨ ΣD¹ in dimension 3.

**2. (a): A, U over CaTT_E.**
- *Low degrees.* Through degree 4, in every finite context, for every admissible E, both coherence forms and every S ⊆ {A, U} (R2.99). In the full-support form, through degree 3 for every interchange-free surface (R2.2).
- *Pasting contexts.* In the variable form, every interchange-free binary surface is conservative on every finite globular pasting context in every dimension (R2.3). The proof uses relative coherence for strict-image equality on trees.
- *Further classes.*
  - All degrees when every declaration below degree h has variable faces, up to degree h (R2.5).
  - Degree 5 on every finite computad with a globular 3-skeleton, in the variable form (R2.102).
  - Further cases in R2.41, R2.43, R2.96 and R2.225.
- *A candidate route.* In the variable form, the site of arities with free temporal composition used by the CaTT_G proof (R1.222) exists for every admissible E: raw syntax is a cellular resolution of the operad of realisable directed values, with lifting at every prescribed globular boundary (R2.9). The comparison with models on an arbitrary finite computad, the last step of R1.222, was not carried out.
- *The forms differ.* The full-support and variable forms first give different inhabitation answers in degree 5 on a pasting tree. This holds for V, for the two single-switch kernels, and for V plus one equation (R2.83, R2.85, R2.113). In the full-support form even strict-image equality is not conservative on pasting trees. For both forms, raw terms on a pasting tree do not reach every strict cell of F_E in degree 4 (R2.13).

**3. (b): interchange surfaces over CaTT.**
- *Through degree 5, every finite context:* all four surfaces containing interchange are conservative (R2.233).
- *Reductions.*
  - Every type inhabited in a binary surface (even with disc and endo-coherence removal) has an inhabitant using only the word equations of clause (i) (R2.227).
  - For the maximal surface, equations between equal-dimensional operands suffice in every context and degree (R2.230). Through degree 5 these are 15 explicit generic equations, through degree 6 they are 24.
  - In degree 6, ten of the 15 rank-≤3 equations are conservative in every degree. A degree-6 failure therefore needs one of five laws: the three rank-3 temporal laws (associativity and the two units of composition along 2-cells, at rank 3) and the two rank-3 grid laws (a lower-cut product of equal-dimensional cells preserves temporal composition and identities) (R2.233).
- *The Eckmann–Hilton pair is not identified* by any binary surface (R1.1, R1.4). No counterexample is known in any class studied so far. Every binary surface is conservative on every finite 2-computad (R1.10). The same holds on bubble-free planar substitutions and on many probe presentations (R2.17, R2.40, R2.190 and others).

**4. (c): Catt_sua over CaTT.**
- *Through degree 5, every finite context:* conservative (R2.235). In degree 6, insertion's generating equations through degree 3 suffice for inhabitation (R2.235).
- *The join is settled, negatively.* Let J be the join of ≡_sua with ≈_{A,U,I}. J is conservative on a finite 2-computad iff its free strict 2-category has no nonidentity cell from an empty path to itself (R2.1, R2.28). A positive raw bubble rules out every finite extension (R2.4). Recognition is Π⁰₂-complete (R2.37). J is not asked again.

**5. Limits of finite methods.** Some finite one-object computads have a 4-type that is empty in every theory here, yet inhabited in every model with finitely many 1-cells (R2.68). Per-context recognition ranges from P-complete to Π⁰₂-complete, and can have any c.e. Turing degree (R2.37, R2.169, R2.202, R2.241). One fixed finite 3-computad tests uniform conservativity on all finite 3-computads (R2.101). The per-degree question reduces to the globular context T_{n−1}, with one generator in each degree below n (R2.109, R2.114).

**6. The rank induction behind items 3 and 4.** Write D_r for the theory whose equations of the surface have output rank ≤ r (R2.230 for (b), the bounded published theory B_r for (c)). R2.233 and R2.235 prove:

```
for r ≥ 1, D_r reflects inhabitation into D_{r−1} at every old boundary through degree r + 2.
```

The proof works at rank r. Each generating equation is oriented as a reduction on rank-r expressions. Each reduction is represented by a *track*, the comparison on its own globular arity carried through its context, with tracks taken up to mutual existence of cells one degree higher. Then every local confluence peak is shown to close **with equal track classes**. The bound r + 2 arises because track classes are compared only up to one further degree. The all-degree statements (b) and (c) follow if, for every r, the track comparisons are coherent in all higher degrees. Concretely, the comparisons between tracks around each peak must themselves be comparable, and so on.

**7. Semantic background.**
- Gordon–Power–Street: every tricategory is triequivalent to a Gray-category.
- Simpson conjectures that strict associativity and interchange with weak units model all homotopy types.
- Joyal–Kock prove the one-object, one-arrow case semantically.

## 3. Questions

**Q1 (main).** Prove or refute each of the following, in every finite context and every degree. A single argument covering more than one is preferred.
- **(a)** For every admissible E, ≈_{A,U} is conservative over CaTT_E^V, the variable form. One possible route is to finish the model construction of R1.222 on the site of R2.9: compare the free model on an arbitrary finite computad with its rigidification. The full-support form is also wanted, but it is known to behave worse (item 2).
- **(b)** ≈_{A,U,I} is conservative over CaTT. It is enough to treat the 24 equal-rank equations of R2.230 and their higher analogues, or to show that the rank induction of item 6 holds without the degree bound. If it fails, the first failure involves one of the five rank-3 laws of R2.233 in degree 6. Then give the context and the type.
- **(c)** Catt_sua is conservative over CaTT. The same rank-induction formulation applies (R2.235).

A useful partial answer is any of the following:
- the rank induction of item 6 without the bound r + 2, for (b) or (c), even for a single rank r;
- a counterexample in degree 6, together with the invariant that certifies it;
- for (a), the missing comparison step on an arbitrary finite computad, even for one setting.

**Q2.** If any part of Q1 fails, characterise the contexts where it holds as a class closed under finite extension, or prove that no such class exists. This mirrors what R2.4 shows for the join.

## 4. What counts as a solution

For each of (a), (b) and (c): a proof valid in every finite context and every degree, or a counterexample. A counterexample is a context Γ and an old type over Γ, inhabited after conversion but not before. Its non-inhabitation should be certified by an invariant (a model of the kernel) that can be checked by hand or by a short program. A proof may cover a class of kernels instead of one kernel; in that case, say which admissibility requirements it uses.

## 5. Literature (searched 2026-11-22, 2026-11-24 and 2026-11-25)

- Finster–Reutter–Rice–Vicary (arXiv 2007.08307) prove Catt_su conservative for terms over pasting diagrams. Finster–Rice–Vicary (arXiv 2302.05303) define Catt_sua. Rice's thesis (arXiv 2502.17068, Ch. 4) gives partial rehydration over pasting contexts. None of these proves conservativity in arbitrary contexts.
- Chanavat–Hadzihasanovic (arXiv 2507.00146) use top associativity in globular operations.
- No published treatment of CaTT-style theories with directed interchange at every level was found.
