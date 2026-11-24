# Which operations propagate invertibility in algebras with directed interchange at every level? (round 2)

*A self-contained problem. Background: standard higher category theory, and the previous rounds listed below. This is the second round of this line. The first round's prompt, its response and the verification are in the repository file `notes/conjectures/answered/invertibility-in-directed-interchange-2026-11-21.md`, cited below as "round 1". The definitions of the theories V and V + S, the letters, and the operations h, W, K, J are those of round 1 and of the rounds it cites (`lax-interchange-every-dimension-r5` … `-r10` in the same folder). Everything round 1 settled is taken as known and is not re-asked.*

**What we are asking for.** We want one general statement that decides, for every operation of V and every setting S ⊆ {left split, right split}, whether the operation sends invertible operands to invertible cells in **every** algebra of V + S, not only in free algebras over pasting diagrams. The cases below are the ones a proof assistant's rules depend on. They should come out as instances of that statement, not be settled one at a time.

## 1. Setting (summary of round 1)

- V is the least admissible theory: the forced base B (structural operations, P, the face and unit declarations, the outer unary subdivisions in both variables, and their vertex transports) plus the guarded round-5 equations. V + S adds the unguarded left split and/or right split of the inner interchanger.
- Every d-cell of a free algebra F_{V+S}(Γ) is a ∗_{d−1}-path of contextual letters. The Gray projection π sends a letter to a whiskered generator of the free Gray-enriched category 𝔉(Γ) (an **outer** letter) or to an identity (an **inner** letter).
- Free algebras on pasting diagrams have no non-identity invertible cells (positivity, (M5)).
- For cells x₁, …, xₙ in consecutive homs, of hom-dimensions d₁, …, dₙ, the **Gray cell** G(x₁, …, xₙ) is the image of the top-atom lift over the wedge ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}. On ΣD² ∨ ΣD² this lift is W.
- **Known in every algebra:**
  - an outer cylinder (one factor of positive dimension, the other an edge) with an invertible moving input is invertible, from the outer unary subdivisions and the unit declarations;
  - an inner interchanger with an invertible left (right) input is invertible exactly when the left (right) split holds;
  - the join h(A, B) is invertible when A is and the inner interchanger ῑ₋ of the factorization r̄₁ = h · ῑ₋ is.
- **Known to fail:** the binary subdivision W(A₁ ∗ A₂, B) = paste of W(A₁, B) and W(A₂, B) fails in every setting, even after localization (round 1, the outer W-strip, with a label table).

## 2. The questions

**Q1 (factor rule for Gray cells).** Fix (d₁, …, dₙ) with at least two dᵢ ≥ 1, an index i with dᵢ ≥ 1, and a setting S. Is G(x₁, …, xₙ) invertible in every algebra of V + S whenever xᵢ is invertible? We expect the answer to depend on (d₁, …, dₙ), on i and on S. We would like the exact list.
- Is the case d = (1, 1) (the cut-0 crossing of two 2-cells) positive in every algebra, because its outer square subdivisions are unguarded?
- Is d = (2, 2), with W as the lift, negative?

**Candidate countermodel for (2, 2).** Start from round 1's outer W-strip table, keeping the long hom through degree 4: 3-values in ℤ, inner squares labelled xy, joins −ab, r, t and χ labelled 0. Then change three things:
- the short hom carrying A is replaced by one in which A has a two-sided inverse, with advance counts A ↦ 1 and A⁻¹ ↦ −1;
- 5-labels are taken in (ℕ, +);
- W(A, B) is labelled 1, and every other disk pair is labelled 0, including (A⁻¹, B) and (1, B).

Here A is invertible and W(A, B) is not. Is this an algebra of V + S? Round 1's check used two facts that change here: the short homs were chains, so two positive short advances are never spatially adjacent, and advance counts were positive, so every guard test ab was nonzero. If some guarded equation of V links W(A, B) to W(A⁻¹, B) through A ∗ A⁻¹ = 1, please give it. In that case the factor rule may hold after all.

**Q2 (pseudo factor).** Call a cell x **ps\*** if every mixed cell G(y, x′), for x′ x or a face of x of positive dimension and y of positive dimension composed before it, is invertible. If xⱼ is ps\* and some i < j has dᵢ ≥ 1, is G(x₁, …, xₙ) invertible in every algebra of V + S? This is the uniform analogue of the strict lemma "y ⊗ β is invertible when β is pseudo". Its strict proof uses the same binary subdivisions as Q1.

**Q3 (other outer letters).** Which further outer letters propagate invertibility from an operand in every algebra of V + S, and under which hypotheses on the inner letters of the target hom? The letters we have in mind are:
- W on composite operands;
- the auxiliary K and J;
- shifted joins;
- higher naturality and route cells.

The hypotheses on inner letters range from "all inner letters into the target object invertible" to none. A criterion stated in terms of which subdivision and factorization laws each letter satisfies would answer this.

**What would help most.** A characterization of the form: an outer letter propagates invertibility from an operand position in every algebra of V + S if and only if [a syntactic condition on the letter, the position and S], with the positive direction proved from the laws and the negative direction by explicit algebras. Round 1's per-letter semi-decision procedure certifies single positive instances. We want the general dividing line.
