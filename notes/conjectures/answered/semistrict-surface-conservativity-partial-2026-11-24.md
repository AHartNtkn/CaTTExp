# Semistrict surface conservativity: partial researcher responses, filed and checked (2026-11-24)

The responses themselves (Responses 1–267, about 3 MB) are appended to the round-1 prompt in
[`semistrict-surface-conservativity-2026-11-24.md`](semistrict-surface-conservativity-2026-11-24.md).
The follow-up prompt for what remains open is
[`semistrict-surface-conservativity-r2-2026-11-25.md`](semistrict-surface-conservativity-r2-2026-11-25.md) (round 2, answered 2026-11-25).
They are partial: Q1 is settled for every subset over the Gray kernel and for the subsets without
interchange over CaTT, but not for the CaTT subsets containing interchange, nor for insertion
(≡_sua) in arbitrary contexts. This file records what each headline result says, how far it was
checked here, and what it changes in `notes/surface-conservativity.md` (S19).

Notation as in the prompt: ≈_S is the binary word surface for S ⊆ {A, U, I} (clauses (i) and (ii));
"the Gray kernel" CaTT_G is our two-tier L; ≡_𝔉 is full equality of images in the free
Gray-enriched category; "conservative" means inhabitation of old types (Definition 2.1 of the note).

## Headline results

| # | Claim | Check here |
|---|---|---|
| R1 | **The sharper Gray conjecture (our Conjecture GRC) is false.** In Σ(x, a : 1ₓ → 1ₓ) the suspended diagonal Eckmann–Hilton braid ΣB = ΣE(a,a) and ΣJ = Σ1_{a∗a} have equal 𝔉-images, but no Gray 5-cell joins them in either direction. So conversion by ≡_𝔉 newly inhabits an old 5-type. Also: B ≉_{A,U,I} J and B ≢_sua J in CaTT (weight model; distinct Catt_sua normal forms). | **Checked** (argument reconstructed). The weight model (3-cells in (ℕ, +), +1 for the five-disc string arity) is sound for clauses (i) and (ii), and B has weight ≥ 1 while J has 0. The equal-image claim is immediate: every coherence has identity image in F. The no-5-cell half reduces, via lifting of suspended CaTT heads, to the two-colour list-model argument of `relative-coherence-all-dimensions-r10` item 20, which was verified on 2026-11-21. The Catt_sua normal forms were not recomputed here. |
| R2 | Through dimension 3 the Gray surface is conservative in every context iff I ∉ S. For one context with I ∈ S the exact test is "every exchange edge has a directed return path", which is undecidable. On globular pasting contexts, in all dimensions: conservative iff I ∉ S or at most one column is active. | Read. The pasting-context statement agrees with our Proposition 4.6 (failure at ΣD¹ ∨ ΣD¹) and Corollary 4.4. |
| R3, R16, R50, R51 | ∅ and {A} are conservative over both kernels; Catt_su (hence {U}) over CaTT; {U} over CaTT_G. All in every finite context and every dimension. | Read, **not independently verified**. These are model-theoretic proofs (raw algebras, globular trivial fibrations, cylinder lifting). |
| R6 | Q3: through dimension 4, ordinary CaTT is conservative for every subset in every finite context; the Gray kernel exactly for the four subsets omitting I. | Read, not independently verified. |
| R43 | **EL fails for every binary surface ≈_S, already on a point, in both kernels.** EL_S(k) at X holds iff surface-equal raw-parallel k-terms are literally equal. The first failing rank is 1 if A or U ∈ S, and 2 otherwise (S = ∅ included). | **Checked.** The argument was read (marked-disc multiset M and the grade-zero induction (8)). The checker `tools/semistrict_surface_identity_classes.py` was run: 11 point pairs in ranks 1–4, and the emitted `OrdinaryIdentityClasses.agda` and `GrayIdentityClasses.agda` type-check with `--safe` against `src/`. This is consistent with our Agda: `Converse.necessary` derives EL from *elaboration-form* conservativity (`ConservativeAt`, Definition 2.2, t′ ≈ t). So for ≈_S the elaboration form fails even where inhabitation holds. |
| R222 | **{A, U} is conservative over both kernels in every finite context and every dimension** (also binary A joined with the three published strict-unit rules over CaTT). So Q1(i) is exactly I ∉ S. One may also add all strict-image equalities on temporal arities of every height. | Read in full, **not independently verified**. It depends on R3, R4, R50, R51, R170 and R183. The construction is a model whose cell spaces have strictly associative and unital temporal products and Kan fibrations at globular boundaries (simplicial presheaves on a site C of arities with free temporal composition; Bergner–Rezk Reedy/injective comparison; fixed-object rigidification). The researcher's Agda witnesses need Rice's binary and were not rerun. |
| R13, R29, R105, R185, R218 | Gray with I: there is no uniform first-failure bound. One scalar fails in every degree ≥ 4. Individual-context conservativity is Π⁰₂-complete in general, and r.e.-complete on positive 3-computads. | Read, not verified. |
| R4, R10, R14, R26, R31, R33, … | Ordinary CaTT with interchange: conservative on many classes (finite 2-computads, all eight surfaces and ≡_sua; through degree 5 in several classes). The full binary surface still separates the diagonal braid. No counterexample is known for {U, I} or {A, U, I}. | Read (headlines only). |
| R44, R217, R202 | Conversion for ≈_{A,U,I} is decidable over every finite computad. So is strict units with binary {A, U}, and each finite insertion width. | Read (headlines only). |

## What this changes in the note (applied 2026-11-24)

1. **Conjecture GRC is refuted** (R1). Full image equality ≡_𝔉 is not conservative over two-tier L in
   arbitrary contexts; the first failure is at the suspended scalar in dimension 5. The note's design
   advice "use ≡_F as the surface's definitional equality" is withdrawn for arbitrary contexts.
2. **Strict associators and unitors over two-tier L are conservative in every context** for the binary
   surface ≈_{A,U} (R222; researcher's proof, not verified here). This is the positive answer to
   S19 (b) for two-tier L. Uniform L (F_{V+S}) is not addressed by the responses.
3. **The note's "[argued]" failure of {U, I} and {A, U, I} over CaTT at the Eckmann–Hilton pair is
   wrong** (R1): the braid and the identity are not ≈_{A,U,I}-equal. Over CaTT, every subset containing
   I is now open in arbitrary contexts, and conservative through dimension 4 (R6).
4. **Elaboration form and inhabitation form separate** (R43). Theorem C (Agda) is about the elaboration
   form; for the binary surfaces only the inhabitation form can hold. So "conservativity ⟺ EL" is a
   statement about Definition 2.2. The route through EL cannot prove the binary classification, and
   R222 does not go through it.

## Still open after these responses

- Over CaTT: {I}, {A, I}, {U, I}, {A, U, I} in arbitrary contexts (Simpson's case {A, I} included), and
  ≡_sua in arbitrary contexts.
- Uniform L (V + S) for {A, U}: not addressed.
- Independent verification of R3, R16, R50, R51, R170, R183 and R222. These carry the positive answers.
