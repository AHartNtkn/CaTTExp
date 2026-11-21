# Chapter 7. Free objects

A free object makes a context into an object: ⟦Γ⟧ is the free ω-category on the computad Γ, and maps ⟦Γ⟧ → C are the same as Γ-shaped diagrams in C. The universal property is an equivalence stated as filler rules, one per dimension, with no definitional β or η.

**Notation.** Free objects are data objects. Chapter 8's probes are a different sort, also written ⟦Θ⟧ there. Where both appear (chapter 9, §9.6, and `notes/design-decisions.md` §4), the free object is written ⟦Θ⟧♭. No current rule relates the two (§7.5).

## 7.1 How a universal property is stated

**Schema (LIFT).** A restriction R : X → Y between ω-categories is an equivalence when
```
 y an object of Y
──────────────────────────────────────────────    (LIFT₀)
 an object x of X,  and an invertible cell  R x ≅ y  in Y

 u, u′ parallel k-cells of X,   θ : R u → R u′  in Y
──────────────────────────────────────────────    (LIFT_{k+1})
 a cell v : u → u′ of X,  and an invertible cell  R v ≅ θ  in Y
```
This is the coinductive definition of equivalence written as filler rules, the same pattern as `uni` (chapter 6). No side conditions beyond well-typedness, and no equations.

**Source.** `notes/free-objects.md` §1.3.

## 7.2 The free object on a context (A1 = R-A)

**Rule.**
```
 Γ ⊢          (Γ a closed context)                Γ ⊢
───────────────────── (FREE)               ─────────────────────── (GEN)
 Θ ⊢ ⟦Γ⟧ : ⋆                                Θ ⊢ η_Γ : Γ ⇒ ⟦Γ⟧
```
η_Γ is the **generic diagram**: η_Γ(x) is the generator x, a cell of ⟦Γ⟧. The universal property is LIFT for the restriction
```
R : Hom(⟦Γ⟧, C) → Diag(Γ, C),    F ↦ η_Γ ; F
```
At dimension 0:
```
 Θ ⊢ σ : Γ ⇒ C
─────────────────────────────────────────────    (LIFT₀)
 Θ ⊢ ⟨σ⟩ : ⟦Γ⟧ → C
 Θ ⊢ β_σ : η_Γ ; ⟨σ⟩ ≅ σ      (invertible 1-cell of Diag(Γ, C))
```
At dimension 1: given F, G : ⟦Γ⟧ → C and a lax transformation of diagrams θ between their restrictions, a transformation ⟨θ⟩ : F → G with an invertible cell relating its restriction to θ. Higher dimensions follow the pattern, with Diag(Γ, C)'s higher cells shaped by the cylinders Γ ⊗ Dᵏ of chapter 5.

**Side condition and decision procedure.** Γ ⊢ (decidable, chapter 1). No free-variable condition: the rule asserts nothing about Γ, it names its free object.

**Example.**
- ⟦Dⁿ⟧ is the n-disk, and its source and target maps ⟦Dⁿ⁻¹⟧ → ⟦Dⁿ⟧ are ⟦τ⟧ for the two face substitutions.
- A substitution Δ ⊢ τ : Γ gives ⟦τ⟧ := ⟨τ[η_Δ]⟩ : ⟦Γ⟧ → ⟦Δ⟧. For composable substitutions, ⟦τ⟧ ; ⟦τ′⟧ and ⟦τ′ ∘ τ⟧ are related by an invertible cell from LIFT₁, not by an equation.
- A CaTT operation over Γ becomes a map between free objects, and applying it to cells of C is precomposition.

**Semantics.** Strict model: the free strict ω-category on the polygraph Γ. Weak model: the free Grothendieck–Maltsiniotis ω-category on the computad Γ, i.e. Free(Γ) of chapter 4.

**Status.**
- **Decomposition of diagrams** (C3), Diag((Γ, x : A), C) ≃ Diag(Γ, C) ×_{Diag(∂D, C)} Diag(D, C): **proved** as an isomorphism onto the strict pullback at every level, given the cylinder contexts (unconditional for globular Γ; for all Γ now by chapter 5). Strict ≃ pseudo pullback **proved** at level 0 and in the strict model at all levels. Remaining: compatibility with Diag's composition (C3a) and boundary restriction as an ω-equifibration (C3b), owner FOBJ (former).
- **Lifting** (C3 (L)): unconditional at level 0, at argument level for n + k ≤ 3, and given N on Dⁿ ⊗ Dᵏ beyond that, which chapter 5 §5.2 supplies.
- **Invertibility of the lift** (C3 (I)): depends on C3a, then on one simultaneous recursion (inverse, comparisons, unit, counit), **open**.
- **Conservativity** (C5), cells of ⟦Γ⟧ between CaTT terms are exactly CaTT terms: non-collapse half **proved** under P (strict cartesian model) and under L (strict Gray model 𝔖, Prop. 5L, argument level, independently checked); weak half reduced to a sound weak interpretation (C5a, blocked on E11).
- Agda: cylinder contexts for globular Γ and the depth-2 left-unitor naturality cell (C7).

**Source.** `notes/free-objects.md` §2; `notes/free-objects-proofs.md`; `notes/limits-representables.md` §5.2 (R-A); ledger C3, C5, C7.

## 7.3 Attaching a cell (A2), derived

**Rule (derived from 7.2 and the colimit rules of chapter 6).**
```
 Θ ⊢ C : ⋆      Θ ⊢ (a, b) : ∂Dⁿ ⇒ C
──────────────────────────────────────────    (ATTACH)
 Θ ⊢ C[x : a → b] : ⋆,   ι : C → C[x : a → b],   x : ι a → ι b
```
C[x : a → b] is the pseudo pushout of C ← ⟦∂Dⁿ⟧ → ⟦Dⁿ⟧, the left map being ⟨(a, b)⟩. Its universal property: maps out of C[x : a → b] are maps F out of C together with a cell F a → F b, i.e. LIFT for
```
R : Hom(C[x : a → b], D)  →  Hom(C, D) ×_{Diag(∂Dⁿ, D)} Diag(Dⁿ, D)
```
The initial object 0 is ⟦ε⟧.

**Why A1 is the primitive.** The notes compare A1 (one object per context) and A2 (initial object plus one-cell attachment) and leave both open (`notes/free-objects.md` §4.4). The comparison there turns on one structural fact: **A2 = A1 + pushouts along boundary inclusions**, and with general pseudo pushouts the two are interderivable, A1 being the smaller addition. The kernel has pseudo pushouts: the all-marked colimit of a span (chapter 6, §6.3). R-A in ordinary mathematics (chapter 9) also uses A1's form. So the spec takes A1 as primitive and derives ATTACH. (An earlier version of this paragraph also cited chapter 8's probes ⟦Δ⟧ as A1's form. They are not free objects; see §7.5.) This is **stated here**, by that argument; ledger S10 asks for it to be recorded in `notes/free-objects.md`.

**Example.** ℤ in chapter 9 is a localisation of the loop ⟦x, s : x → x⟧, a finite pushout. Under A1 + pushouts it needs no further primitive.

**Status.** The interderivability: **proved** (`notes/free-objects.md` §4.1, §3.3, with the decomposition property C3). The choice of primitive: **stated here** (S10).

## 7.4 Free object as a lax colimit of the point

**Statement.** ⟦Γ⟧ ≃ laxcolim_Γ(const ⊤). This would make (FREE) derivable from the colimit rules.

**Status.** Semantically **proved** (`notes/limits-representables.md` §10.3). Syntactically, with the specified cocone: φ (family ⇒ cocone) exists in every dimension; the full equivalence is **proved** for graphs (machine-checked on 6 graphs) and in dimension 2 (ψ and one homotopy machine-checked on 9 shapes, the other on paper); dimension ≥ 3 and higher cocone morphisms are open (B6, B20, B21, owner CONE). Until it is proved, (FREE) stays a primitive. **Source:** `notes/specified-cones.md` §6.

## 7.5 Free objects and chapter 8's probes

**Rule.** GB-shape (chapter 8, §8.8) relates the free object ⟦Θ⟧ of this chapter (data sort) to the probe ⟦Θ⟧ of chapter 8 (probe sort). It gives a corolla ι_Θ from the probe to the free object, and a row that makes maps out of the free object the same as probe diagrams. In particular, an element ⊤ → C (⊤ ≃ ⟦D⁰⟧) is the same as a point ( ▸ C) of chapter 8.

**Why a rule is needed.** Without GB-shape, a graded countermodel satisfies every other rule and separates elements from points (`notes/ordinary-math.md` Theorem 6.4 (a)).

**Status.** Adopted 2026-11-21 (`notes/design-decisions.md` §4; ledger S13). Sound in Cat_ω. Exactness has been checked with ⟦Θ⟧♭ as a data atom. Its identification with the free object of §7.2 is sound in Cat_ω, and its exactness together with LIFT is outside that check.

## 7.6 Open surface questions

**Q7.1. How free objects are named.**
- *Option A: by their context*, `⟦x : ⋆, s : x → x⟧`. Exactly the kernel; long names for common objects.
- *Option B: by declarations*, `object N := free (x : ⋆, s : x → x)`, elaborated to ⟦…⟧ and the generic diagram. Readable; the user must know that two declarations of the same context are equivalent but not equal objects.

**Q7.2. How lifts are written.** LIFT₀ produces ⟨σ⟩ and β_σ; higher LIFT produces cells with invertible comparisons.
- *Option A: explicit* `lift σ` and `lift-cell σ`. Nothing hidden; every use of a universal property writes both.
- *Option B: pattern-matching notation* (define a map out of ⟦Γ⟧ by giving its values on generators), elaborated to ⟨σ⟩, with β_σ inserted where a computation needs it. Reads like recursion; every elaborated β_σ is an invertible cell the user did not write, which matters when lax and pseudo comparisons are mixed.
