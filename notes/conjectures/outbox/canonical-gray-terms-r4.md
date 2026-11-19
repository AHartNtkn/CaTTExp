# Canonical CaTT terms for the cells of Gray tensors of pasting diagrams: general pairs and iterated tensors

*A self-contained problem. It assumes familiarity with the type theory CaTT, strict ω-categories and Steiner's directed complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** The most general theorem: a construction for **all** pairs and all finite families of globular pasting diagrams, compatible with associativity, or a proof that none exists for some pair together with the equations such a counterexample forces. The cylinder case I ⊗ P is now settled for every globular P (items 6–8), so what is asked is the case where both factors are non-trivial. The question is purely syntactic: whether chosen terms can match their boundaries on the nose in a theory with no definitional equalities.

## 1. Setting

**CaTT** (Finster–Mimram, LICS 2017, arXiv 1706.02866). Types are `⋆` or `u →_A v`. Terms are variables or `coh_{P, u →_A v}[σ]`, where P is a context presenting a globular pasting diagram, σ is a substitution into P, and either (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`. The type of `coh_{P, u→_A v}[σ]` is `u[σ] →_{A[σ]} v[σ]`. **Definitional equality is syntactic identity.** A context is well formed when, for each variable `x : u →_A v`, the terms u and v have type A syntactically.

**Gray tensors.** For globular pasting diagrams Θ, Δ, let λΘ, λΔ be their Steiner complexes and ν(λΘ ⊗ λΔ) the strict ω-category of the tensor (Steiner, *Omega-categories and chain complexes*, HHA 2004). Its generators are the pairs y ⊗ x of cells, of dimension dim y + dim x, with boundary given by the Leibniz formula. Its cells are molecules (Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273) and are determined by their sets of generators.

**The family context.** Fam(Θ ⊗ Δ) has one variable v_g per generator g, typed `T(∂⁻g) → T(∂⁺g)`, where T(c) is a CaTT term over the earlier variables denoting the cell c.

## 2. Statement

> **Conjecture CT.** For all finite globular pasting diagrams Θ, Δ there is an assignment T from cells c of ν(λΘ ⊗ λΔ) of dimension ≥ 1 to CaTT terms over Fam(Θ ⊗ Δ) such that
> - (a) T(g) = v_g for every generator g;
> - (b) T(c) is built from the variables by coh terms, and its strict interpretation (v_g ↦ g) is c;
> - (c) `T(c) : T(∂⁻c) → T(∂⁺c)` holds **syntactically** for every cell c. In particular Fam(Θ ⊗ Δ) is well formed.

The same question for iterated tensors λΘ₁ ⊗ ⋯ ⊗ λΘ_k.

## 3. What is known

1. **Low dimensions.** For Θ, Δ of dimension ≤ 1, binary composites can be chosen consistently by hand. CT holds for D² ⊗ D¹.
2. **Layered terms fail for D¹ ⊗ D¹ ⊗ D¹.** "Layered" means T(c) is the vertical composite, along a layering of the molecule c, of whiskered generators. The source hexagon of the top cell has a unique layering whose first two layers are a square whiskered on the right and a square whiskered on the left, meeting at a 3-edge path. The first layer's target contains a subterm denoting the 2-edge path bc, and no subterm of the second layer's source denotes bc (in CaTT every term uses exactly the variables of its strict image). So the two sides bracket the 3-edge path differently and (c) fails. Non-layered terms are not ruled out.
3. **The weak form holds through dimension 4.** With (c′) — T(c) has a type u → v with u, v connected to T(∂⁻c), T(∂⁺c) by invertible coherence cells, inserted into the variables' types — CT holds for generators of dimension ≤ 4.
4. **Single coherence heads do not avoid the problem directly.** Taking T(c) to be one composition coherence coh_{P, u→v}[σ] requires T(∂^±c) to be literally u[σ], v[σ]; this fails when the boundary is a composite of lower cells that are not among σ's arguments.
5. **Semantics is settled.** The (∞,ω) Gray tensor of pasting diagrams is the free (∞,ω)-category on the Steiner tensor (Campion, arXiv 2311.00205, Cor. 3.5; Chanavat, arXiv 2603.22242, Thm 3.29). CT is only about syntax.
6. **Suspension closure (all dimensions).** With I = D¹ and P a finite globular pasting diagram, CT(I ⊗ P) ⇒ CT(I ⊗ ΣP). Proof: the hom (I ⊗ ΣP)(A, D) between the two extreme vertices is strictly isomorphic to I ⊗ P (checked on chains, f_r bijective on bases for r > 0, degree 0 giving the two kinds of A → D paths); every other hom is globular. Whiskerings R_r, L_r over D^r ∨₀ D¹ and D¹ ∨₀ D^r with recursively chosen types satisfy the composition-case support condition. In a globular pasting diagram every positive-dimensional generator has generators as source and target, so the endpoint declarations of Fam(I ⊗ P) have variable boundaries; a context Γ′ with a substitution σ : Γ′ → Σ_{A,D} Fam(I ⊗ P) then declares the mixed variables by σ-substituted suspended types, and T′(c) = (ΣT(c̄))[σ] satisfies (c) by stability of typing under suspension and substitution. Consequences: CT holds for I ⊗ Dⁿ, Dⁿ ⊗ I (via the odd-dimensional opposite) and I ⊗ Σ^r[m], for every n, r, m.
7. **Wedge closure for cylinders (all dimensions).** For finite globular P, Q: CT(I ⊗ P) ∧ CT(I ⊗ Q) ⇒ CT(I ⊗ (P ∨ Q)). Write z for the wedge point, u : z₀ → z₁ for the seam, a ∈ P₀∖{z}, b ∈ Q₀∖{z}, U = P(a,z), V = Q(z,b), L = (I⊗P)(a₀,z₁), R = (I⊗Q)(z₀,b₁).
   - *Strict part.* i : U → L (p ↦ p₀ # u) is a full sieve and j : V → R (q ↦ u # q₁) a full cosieve. This follows from the sign test: a nonzero positive chain of positive degree in a strongly loop-free unital basis has a differential with both signs.
   - The crossing hom (I⊗(P∨Q))(a₀,b₁) is the full sub-ω-category of L × R on the vertices (l, r) with l ∈ iU₀ or r ∈ jV₀. On Steiner tableaux the inverse is l + r − E_u, with E_u the tableau of u.
   - Every crossing cell from (ip, r) to (l, jq) factors strictly as (1_p, β) # (α, 1_q) through d = (p, q). Crucially, d depends only on the cell's 0-endpoints, so it is unchanged under higher faces.
   - *Terms.* Horizontal composites of the given terms on X = L × V and Y = U × R. One 2-coherence γ_d : S_Y(d) → S_X(d) per vertex d of U × V, over the generic path context, with identity image. Composition heads A_m (∗₀), V_m (∗₁) and W_m (∗₁ with a 2-term) whose types are prescribed recursively, so that ∂A_m(a,b) = A_{m−1}(∂a, ∂b) etc. literally.
   - The four endpoint cases are assigned S_X, S_Y, W_m(S_Y(h), γ_d) and V_m(W_m(S_Y(h_Y), γ_d), S_X(h_X)). Literal boundary agreement then holds in every dimension.
   With item 6 and the Batanin-tree decomposition P = ⋁ ΣP_j, this gives **CT(I ⊗ P) and CT(P ⊗ I) for every finite globular P**.
8. **The three-interval cube.** CT holds for I ⊗ I ⊗ I, the same terms serving both parenthesizations. Choose right-associated composites for paths. Declare each square with its two path terms. For a 2-cell (a sequence of adjacent swaps), whisker each square and pre- and post-compose with path coherences (identity image) so that consecutive steps share the same path term, then compose vertically. Declare the top cell between the two corrected full routes 321 → … → 123. All nonidentity cells (30 paths, 18 2-cells, 1 top cell) have been machine-checked against a certified CaTT checker. So the failure of *layered* terms (item 2) is a failure of that particular choice only.
9. **Where the cylinder argument stops.** For a general first factor Θ in place of I, reconstructing a cell across a wedge of the second factor subtracts a varying cell of the common copy of Θ, not the fixed seam tableau E_u. Positivity conditions then occur in degrees above one, and the intermediate vertex d of item 7 is no longer determined by the 0-endpoints, so a single 2-coherence per vertex no longer suffices.

10. **A strict comparison for the diagonal hom of two suspensions (all dimensions).** For finite globular P and Q, write ΣP and ΣQ for their suspensions, with vertices 0 and 1, and Sp for the suspended basis element of p. Let ε be the augmentation, extended by 0 in positive degree. The degree-+1 chain map
    - F(p ⊗ e ⊗ q) = Sp ⊗ Sq,
    - F(p ⊗ v ⊗ q) = ε(q) Sp ⊗ (1 − v) + ε(p) v ⊗ Sq (v = 0, 1),
    
    has nonnegative coefficients and commutes with ∂ in positive degree. Here e is the arrow of I, and at total degree 0 the image is one of the two directed paths from (0,0) to (1,1). Prefixing the row ((0,0),(1,1)) to the image of each tableau row gives a strict functor **Φ : P ⊗ I ⊗ Q → (ΣP ⊗ ΣQ)((0,0),(1,1))**. Φ sends the atom p ⊗ e ⊗ q to the atom Sp ⊗ Sq, so every mixed atom of ΣP ⊗ ΣQ has a source of one lower dimension. Φ is not injective. For P = D^{m−1} and Q = D^{n−1} with 1 ≤ m, n ≤ 4, Φ has a section of underlying globular sets that preserves identities and sends each mixed atom to its specified preimage (checked by machine). Transfer along Φ does not by itself give CT. It also needs a section for all P and Q, CT for the iterated tensor P ⊗ I ⊗ Q, and CaTT terms comparing the different representatives of the endpoint panels: for P = Q = I, the two edge orders around an endpoint square have the same strict image and need a well-typed comparison.

11. **Transfer works for D² ⊗ D² (P = Q = I).** Φ can be realized as a CaTT substitution σ from a context Γ′ into the suspension of Fam(I ⊗ I ⊗ I), whose CT terms are those of item 8. Γ′ has 25 variables, and its 9 mixed generators are declared with σ-substituted suspended types. Each endpoint panel e ⊗ v ⊗ e is sent to the exchange coherence over D² ∨₀ D² between the two transferred edge orders. That is a coherence-case coh whose type is literally the σ-substituted panel type, so the endpoint comparison is a single coherence head. A certified CaTT checker accepts Γ′, both panel coherences and all 49 transferred non-identity cells, and rejects a control with the panel reversed. Together with the strict section of item 10 for m = n = 2, this gives CT(D² ⊗ D²).

## 4. Questions

**Q1 (main).** Decide CT for **all** pairs Θ, Δ of finite globular pasting diagrams and for all iterated tensors Θ₁ ⊗ ⋯ ⊗ Θ_k, compatibly with associativity (the assignments for (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) agree up to renaming). A positive answer may use any terms (non-layered composites, single coherence heads over chosen pasting diagrams, globally chosen bracketings, correction coherences as in items 7–8, simultaneous inductive choices). A negative answer should give a pair or family with a proof that no assignment satisfies (a)–(c).

A natural inductive route, via the Batanin-tree decomposition of both factors:
- (i) wedge closure in the second factor for an arbitrary first factor: CT(Θ ⊗ P) ∧ CT(Θ ⊗ Q) ⇒ CT(Θ ⊗ (P ∨ Q)), which needs a replacement for the fixed intermediate vertex of item 7 (item 9);
- (ii) suspension of the first factor: CT(Θ ⊗ P) ⇒ CT(ΣΘ ⊗ P), generalising item 6;
- (iii) for iterated tensors, the same with the second factor a Gray product, i.e. a non-globular molecule, as item 8 does for I ⊗ (I ⊗ I).
- (iv) **simultaneous suspension by transfer along Φ** (item 10): CT(P ⊗ I ⊗ Q) ⇒ CT(ΣP ⊗ ΣQ). This needs a section of Φ for all P and Q that is compatible with faces, and an all-dimensional rule for the comparison coherences of the endpoint panels, so that boundaries match on the nose. Item 11 does the case P = Q = I, where the panel comparison is the exchange coherence over D² ∨₀ D². In general a panel p ⊗ v ⊗ q with higher-dimensional p and q has as strict image a whiskered identity over a larger wedge D^a ∨₀ D^b, and the natural candidate is the coherence case over that wedge, provided its type can be matched literally. Together with (i) on both sides, (iv) would reduce CT for all pairs to iterated tensors of the form P ⊗ I ⊗ Q, which is (iii).

**Q2 (fallback, still every dimension).** If Q1 is out of reach, prove CT for every Gray cube I^{⊗n} (all n, compatibly with every parenthesization), or for every pair Dᵐ ⊗ Dⁿ of globes, by a construction uniform in the dimensions. For globes, item 10 reduces Dᵐ ⊗ Dⁿ to D^{m−1} ⊗ I ⊗ D^{n−1} plus the endpoint-panel comparisons, so a uniform treatment of those comparisons together with a section of Φ for all pairs of globes would be enough.

**Q3 (if CT fails).** If CT fails for some pair or family, prove that no assignment satisfies (a)–(c) and identify the minimal extra rule that makes the family contexts well formed (for example a typing rule for generators whose boundaries are molecules, or a definitional equation between bracketings). A precise description of the forced equations is the useful answer.

## 5. What counts as a solution

An explicit construction of T for all pairs and iterated tensors; the inductive steps (i)–(iii) with proof; a uniform construction for all cubes or all pairs of globes; an impossibility proof with the forced equations; or a published reference.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Steiner, *Simple omega-categories and chain complexes*, arXiv math/0403237 (tableaux and the tensor product, used for item 10).

- Steiner, HHA 2004; Hadzihasanovic, arXiv 2404.07273 (molecules, layerings, Prop. 8.3.17 on supports).
- Campion, arXiv 2311.00205; Chanavat, arXiv 2603.22242.
- Finster–Mimram, arXiv 1706.02866; Benjamin–Markakis, arXiv 2406.12127 (invertibility of coherences).
- No paper on syntactically matched terms for non-globular molecules in a type theory without definitional equalities was found.

# Researcher Response 1

**CT holds for D² ⊗ D², including all identity towers.** More generally, the strict comparison in Known 10 gives the following transfer theorem. Put B = P ⊗ I ⊗ Q, C = ΣP ⊗ ΣQ, A = (0,0), Z = (1,1) and H = C(A,Z). Suppose B has a CT assignment U and Φ has a section s of underlying globular sets with

$$
s(\langle Sp⊗Sq\rangle)=\langle p⊗e⊗q\rangle
$$

for every pair of basis elements. Then C has a CT assignment. Here the target atom in the formula is viewed as a cell of H. The section needs to commute with the two face maps. Composition preservation is unnecessary.

**Interpreting the endpoint panels.** Start the context of C with its four vertices and its four pure sides, giving each side the usual suspended globular context. The two routes from A to Z through a third corner give pasting subcontexts R₀ = ΣQ ∨₀ ΣP and R₁ = ΣP ∨₀ ΣQ. Each is the wedge of two globular pasting diagrams at their consecutive endpoints. The formula for F in Known 10 puts the entire strict image of P ⊗ {v} ⊗ Q in the corresponding route Rᵥ. We use two facts here. A term has the support of its strict image, with dependent boundaries included, and strict interpretation on a globular pasting context lifts strict cells with prescribed parallel term boundaries. [Support and globular boundary lifting, Known 2](../answered/relative-coherence-all-dimensions-r4-2026-11-19.md)

Construct a substitution ρ from the context being built to the suspended family context Σ Fam(B), in order of generator dimension. Send the two suspension vertices to A and Z. For a variable of Fam(B) indexed by b, let E be its suspended type with all earlier entries of ρ substituted. If b belongs to the v-panel, the endpoints in E involve only variables from Rᵥ. Indeed, U on either face of b uses only variables in that panel by the support lemma. Their suspended images are already in Rᵥ by induction. For a vertex b the endpoints are just A and Z. Moreover the two terms have the same type by substitution, and by induction their strict images are the two faces of Φ(b), with the dimension shifted back to C. Apply boundary lifting *in Rᵥ* to this particular strict cell and these literal endpoints. Use the resulting term of type E as the entry of ρ. This includes panel cells whose image is an identity. It supplies the comparison between the two substituted edge orders in the endpoint square example in Known 10.

For b = p ⊗ e ⊗ q, declare the new variable for g = Sp ⊗ Sq with type E and take that variable as the entry of ρ. This gives exactly one declaration for each mixed generator. The atom calculation in Known 10 identifies its strict cell and both faces. Suspension and substitution preserve typing, so the induction constructs a well-formed context and substitution. By induction on terms, strictly interpreting a suspended term after ρ applies Φ to the original strict cell, viewed one dimension higher in C. This holds on the variables by construction and on strict composites and identities because Φ is a strict functor.

**The section.** For a cell c from A to Z, write c̄ for the corresponding cell of H and set

$$
T(c)=(Σ U(s\bar c))[ρ].
$$

Its strict value is c by the section equation. If c has dimension one, its endpoints are literally A and Z. In higher dimensions the two substituted boundary terms are precisely T on its two faces, since s commutes with both faces. At a mixed atom the displayed formula reduces to its declared variable by the pinning condition and CT(a) for U. Every arrow outside this diagonal either stays at a vertex or lies on a single pure side. This follows by projecting its directed edge path to the two vertex coordinates. Higher cells with such endpoints stay there as well, since each mixed atom has A and Z as its 0-faces, and composition cannot reverse a coordinate. On each pure side use globular boundary lifting successively, selecting each generator variable and taking identities on vertex towers. The sides share just those vertex towers. This finishes all three CT conditions.

**The two-disc calculation.** For P = Q = I, Known 8 gives U, and Known 10 provides the pinned section. There is also a direct term check of the resulting transfer. For a panel generator p ⊗ v ⊗ q, restrict its substituted type E to the wedge of the two individual globes on Sp and Sq in route order. The implementation builds a coherence with exactly this type over that wedge, substitutes its inclusion, and checks the CaTT support condition. For each target cell it computes the strict tableau of the chosen term, compares the entire tableau to the requested cell, and checks the inferred type against the terms independently selected at the two strict faces. The checks include all 25 generator variables.

| Dimension in D² ⊗ D² | 0 | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|---:|
| Cells checked, including identities | 4 | 20 | 50 | 60 | 61 |
| Objects or nonidentity cells | 4 | 16 | 30 | 10 | 1 |

Above dimension four every cell is the identity on its sole face, so iterating the CaTT identity on the selected term proves the assertion in all higher dimensions. Agda 2.8.0 accepted the prescribed types for all 61 objects and nonidentity cells. Run `python3 tools/canonical_gray_two_discs.py --emit` to check the tableaux and regenerate the certificate. [Term construction](../../../tools/canonical_gray_two_discs.py) · [Agda type checks](../../../src/CaTTExp/Generated/CanonicalGrayTwoDiscs.agda)

For general m,n the transfer requires CT on Dᵐ⁻¹ ⊗ I ⊗ Dⁿ⁻¹ and a pinned globular section in those dimensions. The two-disc result discharges both hypotheses for m=n=2. A uniform construction for Q2 and the general assertion in Q1 remain open here.
