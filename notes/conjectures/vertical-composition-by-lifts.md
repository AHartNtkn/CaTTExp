# Vertical composition of lax transformations by naturality lifts

**Status:** open. Dimension 3 is checked by computation (a compiled run of the certified checker). Dimension 4 is checked at the level of raw types.
**Owner of the follow-up:** GCTX (ledger D15).

## Background

We work in CaTT, the type theory for weak ω-categories (Finster–Mimram, *A type-theoretical definition of weak ω-categories*, LICS 2017).
- A **context** lists variables with their globular types.
- A **pasting scheme** is a context with a unique composite.
- A **coherence** coh_P(A)[σ] is a term formed from a pasting scheme P, a type A over P that is *full*, and a substitution σ.
- Fullness: either both sides of A use all variables of P (an invertible coherence), or the source uses exactly the variables of ∂⁻P and the target those of ∂⁺P (a composite).
- Definitional equality is syntactic.

**Gray cylinders.** For a globular context Γ, the context Γ ⊗ D¹ has three blocks of variables:
- copies x₀ and x₁ of every variable x of Γ;
- a generator x⊗e of dimension dim x + 1.

The type of x⊗e is a whiskered square:
- for x : a → b of dimension n, its source and target are binary composites along dimension n;
- one of these composites involves x₀ whiskered by the generators of lower dimension, the other x₁;
- the orientation alternates with the dimension for Γ ⊗ D¹ and is fixed for D¹ ⊗ Γ.

A map Γ ⊗ D¹ → C is a lax transformation (Ara–Maltsiniotis), and D¹ ⊗ Γ gives an oplax one. The explicit types are `TsE` in `src/CaTTExp/GrayCtx/NaturalExplicit.agda`. They are proved well formed for every globular Γ and every dimension.

**Vertical composition.** Γ ⊗ (D¹ ∨ D¹) has:
- copies 0, 1 and 2 of Γ;
- two generator blocks, x⊗i between copies 0 and 1 and x⊗j between copies 1 and 2.

Vertical composition of lax transformations is a substitution

  Γ ⊗ (D¹ ∨ D¹) ⊢ comp : Γ ⊗ D¹.

It sends copy 0 to copy 0 and copy 1 to copy 2. It sends x⊗e to a term img(x) of type TsE[comp], which is a composite of x⊗i and x⊗j. It is proved (`GrayCtx/VCompAll.agda`) that comp is well typed for every globular Γ of dimension ≤ k, provided the image of the top cell of each disk D^m, m ≤ k, is well typed in D^m ⊗ (D¹ ∨ D¹). So everything rests on the disks.

## The construction

Let x : a → b be the top cell of D^{n+1}. The image img(a) is a term in:
- the five copies of a (a₀, a₁, a₂, a⊗i, a⊗j);
- generators of lower dimension.

The **lift** of img(a) along x moves each copy of a to the corresponding copy of b, with these lifts:
- **derivatives:** x₀, x₁, x₂, each a cell a_k → b_k;
- **squares:** x⊗i and x⊗j, whose boundaries themselves move.

The lift L is defined on coherence terms in three cases (`src/CaTTExp/GrayCtx/Lift.agda`):
1. **Every moving argument has a derivative lift.** L is a single coherence over P with those arguments raised by one dimension. Its type is computed by L inside the raised scheme.
2. **A vertical chain of squares.** L is the pasting of the squares, with regroupings.
3. **A whiskering of one square.** L is the whiskered square, between two functoriality coherences.

Iterating from the dimension-2 images gives img(x) for every disk (`src/CaTTExp/GrayCtx/VCompLift.agda`, `imgN`).

## Statement

**Conjecture (VL).** For every n ≥ 3 and both orientations, the lift is defined (no case fails), and

  D^n ⊗ (D¹ ∨ D¹) ⊢ imgN(n) : TsE_n[comp].

Hence vertical composition of lax (and oplax) transformations is well typed for every globular context, of every dimension.

## What is known

- **n ≤ 2.** Proved in Agda (`Checks/VCompAll.agda`), with the elaborator's images.
- **n = 3, both orientations.** The certified checker accepts the judgement in a compiled run (`tools/vcomp-check`). Agda's type checker does not finish the same evaluation: the term is about 110 MB without sharing. The conditional theorem `Checks/VCompLift.vcomp3-wf` (Agda-checked) turns that judgement into vertical composition for every globular Γ of dimension ≤ 3.
- **n = 4, both orientations.** The lift is defined and its raw type is exactly TsE_4[comp]. The certified checker ran out of memory (15 GB).
- **Why the cases close up.** At each stage, square-type arguments occur only:
  - in whiskerings (inside the functoriality coherences of case 3, each square appears as a single top cell of a pasting scheme);
  - in vertical chains (case 2).

  Every other coherence (associators, regroupings, naturality and functoriality coherences) takes only arguments with derivative lifts. A square produced at stage n is again a whiskering or a chain at stage n + 1, so the case analysis repeats.
- **Contrast with the general naturality problem.** The general problem asks for naturality cells of every coherence along a cylinder: RC(n) in `naturality-arbitrary-depth.md` and `outbox/relative-coherence-all-dimensions.md`. The construction here avoids it. The cylinder direction is a disk extension, and P with a raised variable is again a pasting scheme, so case 1 is an ordinary coherence.

## Why it matters

Vertical composition of lax transformations is the first operation needed to treat transformations as cells of a hom (the lax internal hom [D¹, C]). In CaTT it must be a substitution between explicit contexts, because definitional equality is syntactic. A construction for every dimension, with a typing proof, makes the lax hom available in every dimension.

## What would count as a solution

Either of the following:
- a **typing theorem for the lift engine**: under the case hypotheses, if the inputs are well typed then the lift is well typed with the stated type, together with the invariant that the case hypotheses hold at every stage;
- a counterexample dimension where a case fails or the checker rejects the term.

An Agda proof is preferred: the repository's style is `--safe` Agda with a certified checker.

## Literature search

Not yet done for this specific construction. Related:
- Benjamin–Markakis study cylinders and their composition in CaTT-style computads (their paper on hom ω-categories of computads); whether it gives this construction has not been checked.
- Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*, for lax transformations as maps out of Γ ⊗ D¹.
