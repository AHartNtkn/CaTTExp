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

## Researcher Response 1

### Finite extensions (Q2)

Fix one of the surfaces in Q1 and its raw kernel, using either coherence rule in (a). If it has a counterexample in degree \(n\), **every finite context has a finite extension with a counterexample in that same degree**. Consequently, if Q1 fails for this surface, no nonempty class of conservative contexts is closed under all finite extensions.

**Proof.** Let \((\Gamma,A)\) be a counterexample and let \(X\) be any finite context. Append a fresh, disjoint copy of \(\Gamma\) to \(X\), carrying its attaching terms along the renaming. Call the result \(X\sqcup\Gamma\). The surface inhabitant of \(A\) weakens to this extension.

To see that \(A\) is still empty in the kernel, take the disjoint union of the underlying globular sets of the two raw term models \(H_X\) and \(H_\Gamma\). Interpret the raw constructors on this union as follows. A tuple for a coherence head labels a nonempty globular pasting diagram. Its initial vertex selects a summand. At each pasting-context extension, the new cell and its two faces belong to the same summand, since both face maps preserve the summand. One of these faces was already labelled. Induction shows that the entire tuple belongs to the chosen summand. Evaluate the head in that raw model. This gives the required faces and respects substitution, because both assertions hold in each summand and every generic head test is made on its own arity. In particular the construction works for an operation with a chosen lift. It uses no comparison of lifts chosen on different arities.

Interpret the generators of \(X\sqcup\Gamma\) by their own generators in this model. On each half of the telescope, induction on declarations and terms gives its original interpretation followed by the summand inclusion. The empty context has no surface terms. Indeed a variable needs a declaration, a head needs at least one argument, and a conversion needs a term premise. Every nonempty context already has a raw object. A failing \(A\) must therefore have positive degree. Any cell at its weakened type has its source in \(H_\Gamma\), and hence belongs to \(H_\Gamma\) itself. By the definition of the raw term model it would give a raw inhabitant at the original written type \(A\). This contradiction proves the assertion. Taking \(X\) in a proposed nonempty extension-closed class proves the conclusion about classes. The extension exhibited here adjoins a disjoint context. The argument leaves open what adjoining a generator directly at \(A\) does to other judgments.

There is also a short proof of the exact closure criterion asked for in Q2. The empty context is conservative by the empty-context argument. Every finite well-formed context is obtained from it by successive one-declaration extensions. Thus the class of *all* conservative contexts is closed under finite extension if and only if the surface is conservative everywhere.

**Validation.** The following Agda check proves both implications of this last equivalence for the repository's surface typing judgments, with an arbitrary head test and surface equality on the empty signature. In particular the empty-context step covers conversion and heads with surface-typed arguments. The disjoint-extension strengthening follows from the two-summand model above. To reproduce the check from the repository root, run

```sh
checkdir=$(mktemp -d)
note=notes/conjectures/outbox/semistrict-surface-conservativity-r3.md
awk '/^```$/ {inside=0} inside {print} /^```agda$/ {inside=1}' "$note" > "$checkdir/ExtensionClosure.agda"
agda --safe --no-libraries -i src -i "$checkdir" "$checkdir/ExtensionClosure.agda"
```

```agda
module ExtensionClosure where

open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅)
open import CaTTExp.Signature
open Signature ∅
open import CaTTExp.Pasting ∅
import CaTTExp.TypingWith as Raw
import CaTTExp.Surface.Conservativity as Surface

private
  nonempty : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Γ ≡ ε → ⊥
  nonempty pss ()
  nonempty (pse p) ()
  nonempty (psd p) = nonempty p

module _ (side : Ctx → Ty → Tm → Tm → Bool) where
  open Raw ∅ side
  open Surface ∅ side (λ ())

  module _ (E : SurfaceEq) where
    no-closed-term : ∀ {t A} → _⊢ˢtm_∶_ E ε t A → ⊥
    no-closed-term (varˢ _ ())
    no-closed-term (cohˢ (ps p) _ _ _ (⟨⟩ˢ _)) = nonempty p refl
    no-closed-term (cohˢ _ _ _ _ (,ˢ _ d)) = no-closed-term d
    no-closed-term (cstˢ {k = ()} _ _)
    no-closed-term (convˢ d _ _) = no-closed-term d

    Reflects : Ctx → Set
    Reflects Γ = ∀ {t A} → Γ ⊢ty A → _⊢ˢtm_∶_ E Γ t A →
                 ∃ λ u → Γ ⊢tm u ∶ A

    ClosedUnderExtension : Set
    ClosedUnderExtension =
      ∀ {Γ A} → Γ ⊢ctx → Γ ⊢ty A → Reflects Γ → Reflects (Γ ▸ A)

    global : ClosedUnderExtension → ∀ {Γ} → Γ ⊢ctx → Reflects Γ
    global step ε-wf _ d = ⊥-elim (no-closed-term d)
    global step (▸-wf w a) = step w a (global step w)

    closure : (∀ {Γ} → Γ ⊢ctx → Reflects Γ) → ClosedUnderExtension
    closure all-contexts w a _ = all-contexts (▸-wf w a)
```

### What the reductions imply for Q1

**Globular generators and compound attachments in (a).** R2.109 and R2.114 quantify over finite globular sets of generators. There is an obstruction even to presenting a general computad as a retract of such a context by raw substitutions. Take
\[
 S=(x:\star,\ a:1_x\to 1_x).
\]
Suppose substitutions interpreted the generators of \(S\) in a globular context \(Z\) and those of \(Z\) back in \(S\), with composite the identity on \(S\). Pass to ordinary strict values. In the free strict category on \(Z\), a generating 2-cell replaces a single edge by a single edge. In a whiskered step its source path therefore has positive length. Every strict 2-cell is a vertical string of such steps, by ordinary interchange, and higher generators impose no equations on the 2-truncation. Hence the only strict 2-cell on an empty path is its identity. The first substitution must send \(a\) to that identity, which the second substitution preserves. But \(a\) has nonidentity ordinary strict value in \(S\). For a separating strict model take one object, one arrow and natural-number 2-cells with both compositions given by addition. Interpret \(a\) as 1. Interchange holds by commutativity, and the identity is 0. This contradicts the proposed retraction. The same argument applies to the directed syntax by ordinary projection. It rules out this way of extending the globular reduction. A different comparison at written boundaries, as required in R2.9, remains possible. [R2.9](../answered/semistrict-surface-conservativity-r2-2026-11-25.md#researcher-response-9) · [R2.114](../answered/semistrict-surface-conservativity-r2-2026-11-25.md#researcher-response-114)

Here it matters which strict category one uses for an arbitrary computad in §1.1. On the one-object graph with loop edges \(f,g\), the free strict category distinguishes the words \(fg\) and \(gf\). In Steiner's chain complex both have 1-chain \([f]+[g]\) and the same two 0-faces, so they define the same 1-cell of \(\nu\lambda\). Thus the notation \(\nu(\lambda\Gamma)\) in §1.1 cannot in general compute the free strict category on arbitrary attachments. The free monoid on \(f,g\), viewed as a one-object strict category with only identity higher cells, therefore separates the two faces of the old type \(fg\to gf\). The raw head tests still take place on pasting arities, where the Steiner comparison applies. [Steiner, *Omega-categories and chain complexes*](https://arxiv.org/abs/math/0403237)

**Location of a possible failure in (b) or (c).** Write \(V_r=D_r\) for (b) and \(V_r=B_r\) for (c), with rank zero the raw theory. If a raw degree-\(n\) boundary witnesses a failure, there is a least \(r\) at which that *same* boundary becomes inhabited. For (b), R2.227 and R2.230 give a witness using the equal-rank generators. For (c), take a finite published derivation. In either case the finite derivation uses only finitely many generating equation ranks. The least such \(r\) satisfies
\[
                         3\le r\le n-3 .
\]
Indeed, all generators of \(V_2\) have arity of dimension at most two, so R1.26 reflects any such inhabitant at the old boundary to raw CaTT. For the other inequality, if \(n\le r+2\), §2.6 gives a \(V_{r-1}\)-inhabitant at that very boundary, contradicting minimality. In particular a degree-six failure must first appear at rank three. This implication leaves open the possibility that the least failing degree is larger than six. [R1.26](../answered/semistrict-surface-conservativity-2026-11-24.md#researcher-response-26) · [R2.233](../answered/semistrict-surface-conservativity-r2-2026-11-25.md#researcher-response-233) · [R2.235](../answered/semistrict-surface-conservativity-r2-2026-11-25.md#researcher-response-235)

One can test the scope of an argument using only reflection on arities against the join \(J\) of §2.4. On a pasting arity \(P\), a \(J\)-inhabitant of an old type gives a strict cell by strict soundness of both sets of equations. Ordinary raw lifting on \(P\) returns a term at the prescribed old faces with that strict value. Thus \(J\) reflects at *every* old type on *every* pasting arity. Nevertheless it fails on \(S\) by §2.4. To obtain (b) or (c) from arity calculations one must use a property distinguishing the respective equation system from the join when passing to compound attachments. For the rank route, the outstanding step is realizing the higher comparisons in the preceding theory after substitution at those attachments. Published rehydration supplies the pasting-context comparison for (c). [Ordinary arity lifting](../answered/semistrict-surface-conservativity-r2-2026-11-25.md#researcher-response-227) · [Scalar obstruction for the join](../answered/semistrict-surface-conservativity-r2-2026-11-25.md#researcher-response-1) · [Rice, Theorem 4.5.3 and §4.5.2](https://arxiv.org/abs/2502.17068)

Q2 is settled conditionally for each surface. Q1(a) for both coherence forms, Q1(b), and Q1(c) remain open in arbitrary finite contexts and all degrees.

## Researcher Response 2

### Temporal factorization at arbitrary rank in Q1(b)

Fix an old finite context \(X\), a rank \(r\ge2\), and the equal-rank presentation \(D_r\) of Q1(b). Let \(C\) be the ordinary category of rank-\(r\) arrows in the free \(D_r\)-model on \(X\), under temporal composition. Its objects are the rank-\((r-1)\) cells. **There is a simplicial subset \(K\subseteq NC\), made of cubes of independent occurrences, whose inclusion is inner anodyne.** Thus for any quasicategory \(T\) and any prescribed map \(K\to T\), the space of coherent extensions to all temporal factorizations is a contractible Kan complex. Both the allowed cubes and the prescription on their common faces matter.

**Which factorizations occur.** Use the unique reduced reading of an arrow \(f\). Give each variable or opaque factor one event, keeping its entire normalized label, including its arguments. Give an empty row no events. For a lower product \(F_j(a,b)\) take the disjoint union of the event posets of the two components. For a temporal row take their ordinal sum, so every event of an earlier factor precedes every event of a later one. Write \(E(f)\) for the resulting finite poset of occurrences and \(J(E(f))\) for its order ideals. The labelled reading retains the stationary objects of empty components. [R2.233, reductions on rows](../answered/semistrict-surface-conservativity-r2-2026-11-25.md#researcher-response-233)

The factorizations of the *given arrow* \(f=f_1\cdots f_k\) correspond bijectively to flags
\[
     \varnothing=I_0\subseteq I_1\subseteq\cdots\subseteq I_k=E(f).
\]
To prove this, first consider a single cut. On concatenating two nonempty reduced rows only their touching factors can merge. This happens precisely for two boxes with the same cut index and matching seams in *both* components, where equality of seams is taken in \(D_{r-1}\). Their components then concatenate recursively. A merged box retains the component sources of the first box, the component targets of the last, and every event. Consequently neither of its outside neighbours can newly merge with it. Equality of the outer composite objects alone causes no merge.

It follows that every cut is between row factors or inside one factor. Inside a nontrivially split box it consists of a cut in each component. An opaque factor has only its two endpoint cuts. Conversely, split a row at an ideal. An ideal of an ordinal sum ends at a block boundary or meets precisely one block in a nonempty proper ideal after taking all earlier blocks. An ideal of a disjoint union specifies one ideal per component. Apply the component cuts and take the two indicated products, using the identity at its actual object for an empty part. When the cut is internal to a box, its two resulting boxes are nonempty and retain the exterior component faces, so they fit their respective outside neighbours in reduced form. Concatenation reconstructs the original reading. Conversely, reading the unique touching merge of any proposed prefix and suffix recovers the internal split recursively. Without a touching merge their cut is the displayed row boundary. This proves uniqueness, including repeated labels and loops. The suffix has the order induced on the complementary events, by the same row and component descriptions. Iterating the binary cut proves the flag assertion. In particular the factor on an interval of ideals has the induced event order there. Refining a flag splits that factor and forgetting an interior ideal composes the adjacent factors.

**The attachment argument.** Each arrow gives a simplicial map \(NJ(E(f))\to NC\) by taking interval factors. Let \(L_f\) be the subcomplex of chains missing the empty ideal or the full ideal. For nonidentity \(f\), it maps into arrows of strictly smaller weight, where the weight of a simplex is the event count of its total composite. At each positive weight the nerve is obtained from smaller weights by attaching one such lattice nerve along \(L_f\) per arrow of that weight. Indeed every nondegenerate new simplex determines its arrow by composition and then its unique strict flag by factorization. This is a pushout description even when the characteristic map identifies boundary faces.

Take \(K\) to consist of simplices whose total has antichain event order, including the objects. The interval formula makes this a simplicial subset. For an antichain of size \(m\), the lattice nerve is \((\Delta^1)^m\), and for \(m>0\) the subcomplex \(L_f\) is its cubical boundary. A chain missing the bottom has a coordinate constantly one, and a chain missing the top has a coordinate constantly zero. This describes the cubes with their actual face identifications in \(NC\).

For every other order \(E\), choose a minimal event \(u\) with a strict successor. The nerve of the poset of nonempty proper ideals collapses to the vertex \(\{u\}\). To see this, process the ideals \(I\) missing \(u\) in decreasing size. At the step for \(I\), its least remaining strict upper bound is \(I\cup\{u\}\). This ideal is proper because any successor of \(u\) is absent from \(I\). Pair each chain through \(I\) missing this upper bound with the chain obtained by inserting it. In decreasing chain size these are elementary free-face collapses. The surviving poset has least element \(\{u\}\), so its nerve collapses to that vertex by the same cone pairing.

Now start from \(L_f\). Attach the long edge and the triangle through \(\{u\}\) by an inner 2-horn. Undo each elementary collapse of the proper-ideal nerve in reverse order. For the restored free face and simplex, adjoin the bottom and top to both chains. This attaches the larger simplex along its horn missing the smaller one. The missing vertex is interior, the endpoint faces belong to \(L_f\), and the other interior faces are present by the collapse order. This constructs \(L_f\hookrightarrow NJ(E)\) from inner horns. Starting instead with all of \(K\), apply these attachments for non-antichain arrows in increasing weight. The flag bijection gives precisely \(NC\). Exponentiating any quasicategory by this inclusion gives the asserted trivial Kan fibration \(T^{NC}\to T^K\). [Kerodon, Proposition 4.1.4.4](https://kerodon.net/tag/01BW)

There is an explicit way to supply the cube map whenever lower products have already been realized by simplicial bifunctors. Assign the objects of \(C\) to vertices of \(T\) and each normalized opaque factor or variable to an edge at its assigned endpoints. Suppose that, on each pair of composable sorts, a simplicial map from the product of the two target quasicategories to the output quasicategory realizes \(F_j\) on objects. An antichain reading has at most one nonempty factor at each temporal row. Its cube is therefore obtained recursively from the assigned edges and vertices by taking the product of the two component cubes and applying the indicated simplicial map. On a cubical face this evaluates the interval reading, since a stationary component gives its assigned vertex and a pair of stationary components gives the assigned product vertex. Induction on the boxes proves face compatibility, even if two faces have the same image in \(NC\). The pushout description for antichains now glues the cubes to a map on \(K\). The extension theorem applies with those data fixed.

**Substitution on the factorization lattices.** There is a canonical order map
\[
               p_{f,\sigma}:E(f\sigma)\longrightarrow E(f)
\]
for every substitution between old contexts (also for a well-typed \(D_r\)-substitution between them). On ideals its inverse-image map sends the cut \((a,b)\) of \(f\) to the cut \((a\sigma,b\sigma)\) of \(f\sigma\). To construct it, substitute into each opaque factor or variable of the labelled reading and mark each event in the resulting arrow by that factor's original position. Empty images contribute no marks. Reassemble the row and product nodes, carrying these marks through the touching merges. A merge of two boxes pairs their *components* and concatenates each pair. It preserves every marked occurrence and can only relax the order between the two boxes. Inductively the new event order therefore maps monotonically to the old one. In particular different original positions with equal labels still have their own marks. For the cut at an ideal \(I\), all marks in the substituted prefix lie over \(I\), and those in the suffix lie over its complement. The seam calculation identifies these with the two parts of the normalized composite. This proves the inverse-image formula. It also makes the map intrinsic and functorial. Indeed ideals distinguish points of a finite poset, and iterated substitution acts on the two cut factors by ordinary composition. Thus the entire square of lattice nerves and temporal nerves commutes under substitution, including a substitution that makes two formerly distinct component seams equal.

**What this leaves for the rank induction.** This theorem concerns temporal factorization inside a fixed free model. A comparison with the preceding theory must supply the cube data there, compatibly with substitution and at the written higher faces. For example, substitution can send a rank-\(r\) variable to a row of two successive variables. Its edge lies in \(K\) before substitution and its image has two comparable events. Thus restricting to \(K\) is not itself an operation on the whole substitution site. Contractibility of extensions of a given cubical map addresses the temporal choices after those data have been supplied. It does not construct the required \(D_{r-1}\)-inhabitant.

**Validation.** The checker enumerates all composable paths of the specified lengths in two alphabets with folded component objects. It compares their actual cuts with all ideals of the normalized arrow and the number of serial orders with the count of linear extensions. For each resulting arrow it independently recovers the map on occurrences from its factor pairs after a substitution that folds both objects together and sends atoms to identities, serial pairs, parallel pairs, or single events. It checks monotonicity and the inverse-image formula on every ideal. It also verifies the free-face and horn conditions on mixed event orders. Run `python3 -B tools/semistrict_surface_temporal_ideals.py` from the repository root. The two enumerations give 11,664 paths on 10,512 arrows and 5,000 paths on 4,520 arrows. The horn check verifies 110 attachments. The arbitrary-rank result follows from the flag and attachment proofs above. [Factorization checker](../../../tools/semistrict_surface_temporal_ideals.py)
