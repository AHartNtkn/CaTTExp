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

## 4. Questions

**Q1 (main).** Decide CT for **all** pairs Θ, Δ of finite globular pasting diagrams and for all iterated tensors Θ₁ ⊗ ⋯ ⊗ Θ_k, compatibly with associativity (the assignments for (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) agree up to renaming). A positive answer may use any terms (non-layered composites, single coherence heads over chosen pasting diagrams, globally chosen bracketings, correction coherences as in items 7–8, simultaneous inductive choices). A negative answer should give a pair or family with a proof that no assignment satisfies (a)–(c).

A natural inductive route, via the Batanin-tree decomposition of both factors:
- (i) wedge closure in the second factor for an arbitrary first factor: CT(Θ ⊗ P) ∧ CT(Θ ⊗ Q) ⇒ CT(Θ ⊗ (P ∨ Q)), which needs a replacement for the fixed intermediate vertex of item 7 (item 9);
- (ii) suspension of the first factor: CT(Θ ⊗ P) ⇒ CT(ΣΘ ⊗ P), generalising item 6;
- (iii) for iterated tensors, the same with the second factor a Gray product, i.e. a non-globular molecule, as item 8 does for I ⊗ (I ⊗ I).

**Q2 (fallback, still every dimension).** If Q1 is out of reach, prove CT for every Gray cube I^{⊗n} (all n, compatibly with every parenthesization), or for every pair Dᵐ ⊗ Dⁿ of globes, by a construction uniform in the dimensions.

**Q3 (if CT fails).** If CT fails for some pair or family, prove that no assignment satisfies (a)–(c) and identify the minimal extra rule that makes the family contexts well formed (for example a typing rule for generators whose boundaries are molecules, or a definitional equation between bracketings). A precise description of the forced equations is the useful answer.

## 5. What counts as a solution

An explicit construction of T for all pairs and iterated tensors; the inductive steps (i)–(iii) with proof; a uniform construction for all cubes or all pairs of globes; an impossibility proof with the forced equations; or a published reference.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Steiner, HHA 2004; Hadzihasanovic, arXiv 2404.07273 (molecules, layerings, Prop. 8.3.17 on supports).
- Campion, arXiv 2311.00205; Chanavat, arXiv 2603.22242.
- Finster–Mimram, arXiv 1706.02866; Benjamin–Markakis, arXiv 2406.12127 (invertibility of coherences).
- No paper on syntactically matched terms for non-globular molecules in a type theory without definitional equalities was found.


# Researcher Response 1

## A strict comparison for the diagonal hom of two suspensions

Write ΣP for the suspension of a finite globular pasting diagram P. Denote its two vertices by 0 and 1, and write Sp for the suspended basis element corresponding to p in λP. For two such diagrams P,Q there is a strict functor

$$
  Φ:P⊗I⊗Q \longrightarrow (ΣP⊗ΣQ)((0,0),(1,1)).
$$

It sends the atom on p⊗e⊗q to the atom on Sp⊗Sq, viewed in the diagonal hom. Here e is the generating arrow of I. In particular this gives a source with one fewer dimension for every mixed atom of a tensor of two globes. Both endpoint copies of P⊗Q are needed.

**Construction.** Extend the augmentation of each complex by zero on positive degrees and denote it by ε. On chains define F, of degree +1, by the formulas

$$
\begin{aligned}
 F(p⊗e⊗q)&=Sp⊗Sq,\\
 F(p⊗v⊗q)&=ε(q)\,Sp⊗(1-v)+ε(p)\,v⊗Sq \qquad(v=0,1).
\end{aligned}
$$

In the second formula the bare vertices in the first and second tensor positions belong to ΣP and ΣQ respectively. At a source vertex this gives one of the two directed paths from (0,0) to (1,1). The path at v=0 first traverses Q, and the path at v=1 first traverses P.

Every formula has nonnegative coefficients. In positive source degree, ∂F = F∂. To verify the middle-edge formula, expand ∂(Sp⊗Sq). The suspended differentials on positive-degree p and q give the first-factor and last-factor contributions to F∂, with signs 1 and (−1)^{|p|+1}. When p or q has degree zero, its suspended differential is the difference of the two vertices. The resulting contributions sum to (−1)^{|p|}(F(p⊗1⊗q) − F(p⊗0⊗q)). On an endpoint panel the identity follows directly from ε∂=0 and the suspended differential, except at total degree zero, where the boundary of the displayed path is (1,1) − (0,0). Thus applying F to each row of a Steiner tableau and prefixing the row ((0,0),(1,1)) gives a tableau. The row formula preserves identities, faces with the dimension shift, and composition by addition above the cut, giving the stated strict functor. [Steiner's tableau construction and tensor product](https://arxiv.org/abs/math/0403237)

**Images of mixed atoms.** In the signed row of degree k of the atom on p⊗e⊗q, a term with middle degree 1 and outer degrees i,j has i+1+j=k. It maps to the (i+1,j+1) term in row k+1 of the atom on Sp⊗Sq. The sign on the q-face is twisted by (−1)^{i+1} on both sides. With middle degree 0, only terms with i=0 or j=0 survive the augmentation. These give respectively the (0,k+1) and (k+1,0) terms. For the latter the endpoint 1−v contributes the extra sign reversal required by (−1)^{k+1}. When i=j=0 both contributions occur, giving exactly the two edges in the appropriate boundary path. These are all terms of the target row. The prefixed row supplies its two vertices, proving the atom assertion in all dimensions. [Tensor-atom row formula (4)](../answered/gray-tensor-of-contexts-rule-2026-11-18.md)

**Finite section check.** For all 16 ordered pairs 1 ≤ m,n ≤ 4, put P=D^{m−1}, Q=D^{n−1}. In each case Φ admits a section of the underlying globular sets that preserves identities and chooses the specified preimage of every mixed atom. The checker enumerates the two strict categories independently by closing their atoms under every admissible composition. It pins each mixed atom and all its faces, then chooses a preimage for each remaining cell with precisely the previously chosen faces. It verifies the section equation and both face equations for every cell. Above the top dimension the section extends by identities. For m=n=4 the target has 1,649 cells in degree seven including iterated identities, and every one has a verified lift. Run `python3 tools/gray_globe_comparison.py 4 4` for that case. [Reproduce the check](../../../tools/gray_globe_comparison.py)

**What remains for CT.** The calculation constructs strict representatives. A proof by transfer would also need CaTT terms for the endpoint panels and their compatibility with the mixed declarations. For example, when P=Q=I, the two edge orders around an endpoint square have the same strict image; their substituted terms need a well-typed comparison. The strict section test does not supply that term. The general section and the all-dimensional CaTT assignment in Q2 remain open here.
