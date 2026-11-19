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

**Interpreting the endpoint panels.** Start the context of C with its four vertices and its four pure sides, giving each side the usual suspended globular context. The two routes from A to Z through a third corner give pasting subcontexts R₀ = ΣQ ∨₀ ΣP and R₁ = ΣP ∨₀ ΣQ. Each is the wedge of two globular pasting diagrams at their consecutive endpoints. The formula for F in Known 10 puts the entire strict image of P ⊗ {v} ⊗ Q in the corresponding route Rᵥ. We use two facts here. A term has the support of its strict image, with dependent boundaries included, and strict interpretation on a globular pasting context lifts strict cells with prescribed parallel term boundaries. [Support and globular boundary lifting, Known 2](relative-coherence-all-dimensions-r4-2026-11-19.md)

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

# Researcher Response 2

CT holds for **every iterated tensor of globes of total dimension at most four**, including the four-cube with the same terms for every parenthesization. It also holds for **D³ ⊗ D² and D² ⊗ D³**. There is a further all-dimensional result about the strict section in Known 10. For arbitrary finite globular P and Q, every prescribed mixed atom and all its iterated faces have compatible prescribed lifts. The proof below reconstructs each such lift from its image alone.

## Choosing the three-skeleton and the top cell

Start with the object variables. In degree d, once terms have been chosen below d, declare each d-generator between the terms already chosen for its strict source and target. Those terms are parallel by globularity. For d ≤ 3 one can then select terms for *every* strict d-cell with exactly its prescribed boundary. Here is the argument, including the role of the dimension bound.

Use the variable on an atom and the CaTT identity on an identity. For any remaining cell choose an expression of minimum size in atoms, identities on lower cells, and binary strict compositions. The operands of its last composition have smaller minimum size. Their selected terms can be composed at the indicated cut since the required faces are literally the terms on the same strict cell. Call the resulting term u. Its strict value is correct. To correct its outside faces, proceed in order of dimension j from 1 to d−1. The object faces already agree. At stage j, the desired j-source and the actual j-source are parallel and have equal strict images, as do the actual and desired j-targets. In the subcontext of dimension at most j choose a (j+1)-term from the desired source to the actual source and one from the actual target to the desired target. This uses RC(1) or RC(2), proved for every context. Their strict values are identities since the subcontext has no (j+1)-generators. Compose u at cut j with the first correction on its left and the second on its right, padding the corrections with identities up to dimension d. The binary composition over two globes glued at j has the outside j-faces of its operands literally. Hence the correction sets both j-faces, preserves all earlier choices, and leaves the strict value of u fixed. This constructs the required section through degree three. [RC(1) and RC(2), Known 1](relative-coherence-all-dimensions-r4-2026-11-19.md) · [Relative lifting, in particular formula (3)](gray-tensor-of-contexts-rule-2026-11-18.md)

If every nonidentity four-cell is an atom and there are no generators above degree four, only the declaration step is needed in degree four. All other selections are iterated identities. For the globe tensors of total dimension four the following exhaustive calculation verifies exactly this hypothesis. Unit factors D⁰ can be omitted. The rows cover all ordered compositions of four. Each strict degree-four cell with nonempty top chain was compared with the full atom as an entire tableau.

| Ordered dimensions | Cells in degree three | Cells in degree four | Nonidentity four-cells |
|---|---:|---:|---:|
| (4) | 8 | 9 | 1 |
| (1,3), (3,1) | 38 | 39 | 1 |
| (2,2) | 60 | 61 | 1 |
| (1,1,2), (2,1,1) | 172 | 173 | 1 |
| (1,2,1) | 166 | 167 | 1 |
| (1,1,1,1) | 520 | 521 | 1 |

To reproduce the last column, for each row take `shape` to be the indicated tuple and run the following with `PYTHONPATH=tools`. The enumeration closes all padded atoms under all compositions at cuts below degree four. Atomic generation of the Steiner tensor gives exhaustiveness. For total dimension below four the three-skeleton construction already covers all nonidentity cells. Fix the choices on the single complex with flattened ordered basis tuples and use them under every tensor associator, which only changes the bracketing of those tuples. This gives literal agreement up to the prescribed renaming.

```python
from gray_globe_comparison import atom, strict_cells

top = atom(tuple((d, 2) for d in shape))
assert {x for x in strict_cells(shape, 4) if x[-1][0]} == {top}
```

Apply Response 1 with (P,Q) = (D²,I) and (I,D²). The needed input tensors have ordered dimensions (2,1,1) and (1,1,2), respectively. The pinned section checks for (m,n) = (3,2) and (2,3) each cover 48, 94, 106 and 107 diagonal cells in hom degrees one through four, as well as all eight vertices. The transfer therefore gives CT for both ordered two-globe tensors of total dimension five with both factors of dimension at least two. [Strict cell enumeration and section checks](../../../tools/gray_globe_comparison.py)

## Recovering the prescribed mixed faces in every dimension

Let X be the globular subset of P ⊗ I ⊗ Q generated by the atoms on p ⊗ e ⊗ q under the two face maps. The restriction of Φ to X is an isomorphism onto the globular subset of the diagonal hom generated under faces by the corresponding mixed atoms. Surjectivity onto this subset follows from the atom formula and preservation of faces. For injectivity it suffices to recover each signed row of a tableau in X. A face truncates the tableau and duplicates the chosen row at the cut, so every row encountered is a row of a mixed atom.

Write α for the sign of such a row, and pᵢᵅ for the i-dimensional α-face generator of p, with the two signs agreeing at the top. Use the same convention for q. In source degree k the summands with middle factor e are visible individually in the target chain. After desuspension of their outer factors these give the pairs

$$
 (p_i^α,q_j^{(-1)^{i+1}α}),\qquad i+j=k-1.
$$

Record them at their bidegrees (i,j). A pair occurs exactly when the two indices are within the dimensions of p and q. Each remaining source summand has middle factor an endpoint v, with outer bidegree (i,j) of sum k. Here v is the endpoint with sign (−1)ⁱα, using 0 for minus and 1 for plus. The following rules only use the visible target row. [Tensor-atom row formula (4)](gray-tensor-of-contexts-rule-2026-11-18.md)

- In degree zero the two edges of the target path determine both outer vertices and the route v.
- For k > 0 and j = 0, the pure P-side term in the image supplies the suspended first factor and endpoint 1−v. The recorded pair at (k−1,0) supplies the missing q-vertex with exactly the required sign (−1)ᵏα. For i = 0 the pure Q-side term gives v and the suspended last factor, and the pair at (0,k−1) supplies the missing p-vertex.
- For i,j > 0, a summand occurs precisely when both (i−1,j) and (i,j−1) are recorded. The former supplies its q-factor and the latter its p-factor. The former also gives pᵢ₋₁ᵅ. This is the α-face of the recovered pᵢᵅ. Its two immediate faces are distinct generators in a globular pasting diagram, so the two visible p-generators determine α and hence v. This determines even the summands that map to zero under the endpoint augmentation.

Thus two prescribed faces with the same image have identical rows in every degree, even if they come from different atoms or different signs of truncation. This proves injectivity and gives a uniform, face-preserving inverse on the stated subset. It extends to the identities on that subset by padding both tableaux with empty rows. The globe implementation of the inverse independently recovered all 3,459 distinct prescribed atoms and faces for D¹⁰ ⊗ D¹¹. [Row reconstruction](../../../tools/gray_globe_comparison.py)

**Extension over the endpoint routes and all diagonal arrows.** Each pure route in the diagonal hom is a copy of P × Q. In fact, a cell in the extreme hom of the wedge of the two suspensions decomposes into its two coordinates by restricting its tableau to each side of the seam. Conversely, horizontal composition of the suspended coordinates gives back the tableau, since in positive degrees the two sides have disjoint bases. For a pair of d-cells (a,b) in these coordinates and d > 0 choose the following lift in the v-panel, writing #₀ in traversal order and identifying vertices with their iterated identities when needed:

$$
(a ⊗ v ⊗ s_0 b)\ \#_0\ (t_0 a ⊗ v ⊗ b).
$$

In this formula fixing the two vertex factors means applying the strict inclusion of the remaining factor. At d = 0 take the vertex (a,v,b). Projection to each coordinate gives a and b respectively. The source and target of the displayed path in degree one are the selected vertices. In higher degrees taking either face commutes with #₀ and preserves the outer 0-endpoints used in the formula. This gives a globular section on both routes in every degree. Their only intersections with the prescribed mixed faces and their identities are vertices and their identity towers, since each positive-dimensional face of a mixed atom goes from route 0 to route 1 at hom level.

Every remaining arrow of the diagonal hom also has a lift with its prescribed vertices. In C it is a strict 2-cell. Expand it as a vertical sequence of generating 2-cells whiskered by edge paths, using strict exchange to expand a horizontal composite. Each intermediate A-to-Z path consists of two edges. A pure step changes one edge and keeps the other vertex label fixed, giving an edge of P or Q in the appropriate panel of B. A mixed step at (p,q) lifts to the edge on p ⊗ e ⊗ q. The endpoint of each lifted step is the unique vertex over the intermediate path, so the lifts compose. Make one choice for each arrow still unassigned, keeping the choices already made on the pure routes and the prescribed faces. This extends the section to the union with the whole one-skeleton, and then to its identity towers.

The remaining strict section problem concerns higher cells outside this union that must fit all the selected faces. Transfer for arbitrary globe dimensions also requires CT on Dᵐ⁻¹ ⊗ I ⊗ Dⁿ⁻¹. The three-skeleton argument uses only established relative coherence in degrees one and two. Extending its correction step to arbitrary d would require further coherence results.

# Researcher Response 3

**CT holds for Σ[r] ⊗ Σ[s] for all r,s ≥ 0.** Here [r] is a directed path of r composable arrows. Thus each factor can have an arbitrarily long vertical string of 2-generators. The proof constructs a pinned globular section on the entire diagonal hom. Its first two degrees also give a section on the two-skeleton of the diagonal hom for *arbitrary* finite globular P,Q.

Write B = P ⊗ I ⊗ Q and H = (ΣP ⊗ ΣQ)(A,Z) as in Known 10. A vertex of H records a vertex of each factor and one of the two route orders. Write P and Q in words for edge moves of the indicated factor, with their actual generator labels understood. Write M for the move along the middle interval of B.

**Choosing the arrows.** An arrow of H is a 2-cell in the tensor. Expand it into whiskered generating 2-cells. A step changes one factor edge on its current route or crosses from route 0 to route 1 at a specified pair of vertices. There is at most one crossing. In each portion on a fixed route the P-steps and Q-steps commute with one another across factors by strict horizontal exchange. Their two ordered subsequences are intrinsic: the strict tableau records their labelled edges separately on that route, and a path in either factor's acyclic generating graph visits each vertex at most once. A crossing step is recorded by its own mixed basis element. Thus there is a well-defined lifted word W with all P-steps followed by all Q-steps in each portion, and M at the crossing, if present. Its image is the given arrow. On a pure route this is exactly the choice in Response 2. The two 1-faces of any pinned mixed atom are Q M P and P M Q with any dimension-zero outer moves omitted, by the tensor-atom formula. Both are already in the chosen form. [Steiner's tableau description](https://arxiv.org/abs/math/0403237)

**Lifting two-cells for general P and Q.** A 2-cell of H is a vertical sequence of elementary 3-generator applications in the tensor. For clarity, this follows by expanding a strict expression in its cuts: composition at the top cut concatenates the sequences, and interchange at any lower cut expresses a composite as applications in the two factors one at a time with the other factor held at an identity. At the cut at a vertex of the tensor, whiskering an application on a pure side by a 2-cell on the other side can likewise be written as whiskering by a 1-edge and composing with an identity on the other side's 2-cell. The extreme path has exactly two edges. Thus a pure application changes a single P- or Q-letter by a 2-generator of that factor, in a word context. A mixed application slides M past one P- or Q-letter, also in a word context. These are all possibilities, by the degree splits 3+0, 0+3, 2+1 and 1+2 of a 3-generator. [Polygraphic generation and interchange](https://arxiv.org/abs/2312.00429)

For a pure application, use the same labelled 2-generator at its place in W. A mixed application has one of the two following lifts, with swaps performed at the indicated adjacent letters.

- For M P → P M, the moving P is the first P on the right of M. Swap M P and then slide that P left across all Q's in the left portion. Each additional swap is Q P → P Q.
- For Q M → M Q, the moving Q is the last Q on the left of M. Swap Q M and then slide that Q right across all P's in the right portion, again by Q P → P Q.

All these swaps are oriented square generators in B, with the surrounding words as whiskers. The additional squares lie in an endpoint panel and have identity image under Φ. The central square has precisely the desired mixed image. The result starts at W of the source and ends at W of the target, so the lifts compose along the entire sequence. For general P,Q choose one sequence per remaining 2-cell, using the prescribed lifts on mixed faces, the pure-route section on pure cells and identities on identities. Their boundaries agree by the arrow calculation. This gives a globular section on the two-skeleton together with both pure routes and all pinned faces in every dimension.

**When both outer factors are paths.** Fix the two vertices in B at the ends of a crossing arrow. Label their outer coordinates (a,b) and (c,d). Such an arrow in H is uniquely determined by the pair (i,j) at which it crosses, with a ≤ i ≤ c and b ≤ j ≤ d. The corresponding W is

$$
 P_{a:i}\,Q_{b:j}\,M\,P_{i:c}\,Q_{j:d},
$$

where subscripts denote path segments. A 2-cell between crossing arrows is exactly a lattice path of moves (i,j) → (i+1,j) or (i,j) → (i,j−1). Indeed, the preceding generation argument leaves only the two mixed applications, since [r] and [s] have no 2-generators. Conversely each move is a whiskered application. The strict top chain in the tensor records each traversed lattice edge with its position and kind. The directed path has no repeated vertices, so its starting point and its edge set recover its order. Pure-route 2-cells are identities. Consequently the lift of a crossing 2-cell can be defined by composing the displayed lifts of its *unique* lattice path. On a pinned 2-face the path involves at most one step of each kind. The two faces of a mixed cube lift to its two three-swap routes, since the two outer factor edges are single generating edges and there are no other letters to pass. Single steps at a pinned atom have just their central square.

**Lifting the cube in a longer word.** The 3-generators at hom level arise from the (2,2)-atoms of the tensor. Each exchanges two consecutive lattice steps around an elementary square. A general 3-cell can be expanded into a sequence of these applications by the same top-cut expansion. Whiskering by a 2-path before or after an application adds a common lattice prefix or suffix. At the object cut in H each additional factor stays on a pure route, whose higher cells are identities on paths in [r] × [s]. Such whiskers extend the fixed outer path segments. Thus it suffices to lift the oriented elementary exchange for *any* lengths of these segments, then compose with identities on the lifted prefixes and suffixes.

At the exchange write the relevant word as L Q M P R, up to fixed outside letters, where L is the block of earlier Q's and R the block of later P's. The lift of “P-step then Q-step” first swaps M P, then Q P, moves P left through L, swaps Q M, and moves Q right through R. The lift of “Q-step then P-step” first swaps Q M, then Q P, moves Q right through R, swaps M P, and moves P left through L. In the first route the moves through L are disjoint from the third central swap. In the second route the moves through R are disjoint from the third central swap. Strict exchange therefore rewrites both 2-cells with all three central swaps first, followed by the *same* two blocks of moves through L and R. Those blocks are disjoint and may be put in the same order. Now whisker the oriented 3-cube on Q M P by L and R and compose with the identity on the common remaining moves. Its two faces are literally the two selected strict 2-cells. Its image under Φ is the requested (2,2)-application with its whiskers, since the central cube maps to that atom and the remaining panel swaps have identity image. This argument uses the direction of the actual cube on its two routes and requires no inverse swaps.

Use the resulting 3-cell on each chosen expansion. On an unwhiskered mixed cube the construction gives the atom itself. Higher cells of H and B are identities, so identity padding completes the pinned globular section. The three-skeleton construction of Response 2 gives CT on [r] ⊗ I ⊗ [s], whose dimension is at most three. The transfer theorem of Response 1 now gives CT on Σ[r] ⊗ Σ[s]. The case of a zero-length factor uses the same construction with the corresponding list of moves empty.

**Independent check.** The checker enumerates both strict categories from their atoms. It constructs the sorted lifts of arrows, builds each 2-lift by the indicated swaps, and forms each 3-lift from its chosen faces and the cubes indexed by its target top chain. These determine the whole three-dimensional tableau, since cubes are the only degree-three source basis elements. The checker tests membership in the independently enumerated source, the section equation, both face equations and every mixed pin. For r=s=3 it checks 32, 600, 1,916 and 3,075 diagonal cells in hom degrees zero through three. The uniform proof above covers all path lengths. [Run the section check](../../../tools/gray_path_section.py)

For higher-dimensional outer factors, a 2-path can include applications of a 2-generator of P or Q, and its strict cell need no longer determine a unique lattice path. The common-boundary argument for arbitrary 3-lifts and the general assertions in Q1 and Q2 remain open here.

# Researcher Response 4

**Simultaneous suspension, step (iv), holds for all finite globular pasting diagrams.** The strict functor Φ of Known 10 has an identity-preserving globular section that sends every mixed atom to its prescribed preimage. Together with Response 1 this proves
$$
  \mathrm{CT}(P\otimes I\otimes Q)\ \Longrightarrow\ \mathrm{CT}(\Sigma P\otimes\Sigma Q).
$$
The strict construction uses the section for two suspended paths from Response 3 at each pair of nodes in the Batanin trees of P and Q. For two globes these local sections amount to four fixed finite tables, independent of the globe dimensions.

### 1. Two operations on tableaux

Use infinite rows, padding with empty rows above the dimension of a cell, and allow the all-empty tableau as a separate value. For a path factor J=[r], write E for augmentation in that factor. It keeps terms with a vertex in the J-position, sums over that vertex, and erases the position. Write Dₑ for the operation that keeps terms with the particular edge e in that position, erases the position, and drops the initial row. Operations on different positions commute as selections and sums of labelled chains. Dₑ lowers the degree by one. In the differential of the remaining tensor, every factor to its right has its differential negated, by the Leibniz sign. A path with negated differential is identified with the usual path by reversing its vertex order, including the corresponding renaming of its edges. No interchange of the two signed tableau rows is made.

Here is the version of D needed for a whole globular pasting diagram. Write a tree as a wedge of suspensions, one segment for each edge of its path of objects. Keeping only the suspended generators in segment e and desuspending gives the complex of its child tree. Iterating along a branch u of length i lowers degrees by i. At the resulting node, project to the path of objects by mapping every generating arrow to its segment edge and all generators of higher degree to zero. These operations respect the row differential in positive remaining degrees. In particular, a 2-generator killed by the path projection has parallel 1-faces on the same edge.

Such a restriction of a genuine tableau gives either a genuine tableau or the all-empty value. To check the augmentation, for each branch of length i there is a positive chain map to the i-globe. At the root use augmentation. For the inductive step collapse everything strictly before and after the chosen segment to its initial and final vertices and suspend the map for the child. The basis elements at depth i in that node map to the unique top generator, and no other elements of degree i do. Tensoring these maps shows that the mass of each prospective bottom signed row is at most one, since it is a single coefficient of a tableau in a tensor of globes. The two masses are equal by the differential and augmentation. If both vanish, every higher row vanishes. Indeed a positive cycle of positive degree in the remaining path tensor must be zero: adjoining twice such a cycle as an equal pair of rows above a vertex, with all intervening rows empty, would otherwise violate the coefficient bound. These facts apply also to a signed path after the indicated vertex renaming. [Steiner, Theorem 6.2(iii)](https://arxiv.org/html/math/0403237)

### 2. Local data on a pair of paths

For a tableau X on J ⊗ I ⊗ K, with J=[r] and K=[s], consider its three arrays
$$
 U=E_K X,\qquad V=E_J X,\qquad W=D_I X .
$$
Here D on the middle interval selects its unique edge. Thus U lives on J ⊗ I, V on I ⊗ K and W, one degree lower, on J ⊗ K with the K differential negated. The three matching conditions are
$$
 E_J U=E_K V,\qquad D_I U=E_K W,\qquad D_I V=E_J W.                 \tag{1}
$$
**Every compatible triple of genuine or empty arrays has a globular choice of X.** To see this, assemble a diagonal tableau for ΣJ ⊗ ΣK. If one of U,V is empty, the first equation forces both to be empty, and the other equations force W empty by its bottom augmentation. Choose the empty X. Otherwise prefix the row A,Z. In the next rows send every panel entry (p,v) of U to Sp ⊗ (1−v), every panel entry (v,q) of V to v ⊗ Sq, and each entry (p,q) of W to Sp ⊗ Sq at its shifted degree. In the first of these rows U,V specify the same route by the first equation, giving paths from A to Z.

For the differential in the remaining rows, the mixed components are exactly the row equations of W: the suspension of p contributes the extra minus sign on the q differential. In the pure P components the mixed terms with q a vertex contribute the middle-edge differential of U, by the second equation in (1) and the endpoint 1−v. The remaining contributions there are the pure P differentials of U. In the pure Q components the mixed terms with p a vertex contribute the middle-edge differential of V by the third equation, and the other terms give its pure Q differentials. This checks all components. Extracting the pure terms and the middle-edge slice recovers the triple, including the middle-edge parts of U and V by (1). In particular the diagram so assembled from X is precisely ΦX. Apply the pinned globular section of Response 3 to the assembled tableau. This gives the asserted local choice, respecting faces and identity padding. Cutting all three input arrays at an absolute degree d cuts W one degree lower, with the empty array below its degree zero.

### 3. Recursion over pairs of nodes

Fix a diagonal cell y and nodes u of P and w of Q of depths i and j. Let J and K be their paths of objects. We construct X(u,w) on J ⊗ I ⊗ K, in order of increasing i+j. Interpret the coordinates in standard path orientations. After the i descents in P, reverse the labels of the middle interval and of the K path if i is odd. No axis lies to the right of Q. The following three inputs to the local construction are consequently in the orientations of (1).

- For W, keep the mixed entries Sp ⊗ Sq of y, desuspend the two outer factors and restrict to u,w and their paths. Its initial row is the row of y in degree i+j+2. The underlying differential on K has the additional minus sign from the middle slice. In particular W is a genuine or empty tableau by the branch restriction argument applied directly to the two factors of y.
- For U when w is the root, project y to P ⊗ I and then restrict P at u. This projection first collapses Q to a point before suspension. Equivalently it reads the pure P terms at endpoint 1−v and the mixed terms with q a vertex, the latter as middle edges. This is the one-point case of Known 10, where Φ is an isomorphism. When w is a child, take D on its segment edge of the K path in X(u,parent(w)). Select that edge in the orientation used in the parent.
- For V when u is the root, use the corresponding projection to I ⊗ Q restricted at w. Otherwise take D on the segment edge for u in X(parent(u),w) and reverse both remaining path axes. The reversal accounts for the extra P descent.

To verify (1), first take the middle slice of U. In the interior this selects exactly the entries of the preceding W whose K-edge is the segment for w. These entries equally result from restricting the original mixed rows to w and augmenting its path: all vertices of the child were represented by that one edge in the parent path. On the boundary the same identity is the mixed-with-q-a-vertex part of the projection formula. Taking the middle slice of V proves the third equality in the same way, now selecting the P segment and changing the two axis orientations. For the first equality at two nonroot nodes, both sides select the P and Q segment edges from X(parent(u),parent(w)) and erase those axes. Indeed each preceding local choice has the required augmented projection by construction. The two edge selections commute, and erasing the Q-axis makes its coordinate reversal immaterial provided its specified edge is renamed with it. On an outer edge of the node grid the same computation uses the projected P ⊗ I or I ⊗ Q tableau; at the two roots it is equality of the middle routes. This proves compatibility at every node without making any assumption about lifts in higher dimensions.

### 4. Assembling the section

Copy all mixed entries of y to their prescribed bidegrees p ⊗ e ⊗ q. In each signed row of source degree i+j take the bottom signed row of X(u,w) for every node pair of depths i,j. If nonempty, it is a single triple of vertices. Undo the orientation renaming. The outer vertices are precisely a degree-i generator p of P and a degree-j generator q of Q at those nodes. Insert p ⊗ v ⊗ q with the indicated middle endpoint v.

The local restrictions of this assembled array are exactly the chosen X(u,w). For mixed entries this is the prescription for W. For panel entries with two local vertices it is the bottom-row construction. For a panel entry with a local P-edge, selecting that edge in X(u,w) gives the augmentation over the P-path in the corresponding child choice, with the stated renaming. This sums exactly the reconstructed labels projecting to that edge. The same verification applies to a local Q-edge. With two edges apply the two adjacent overlap equalities in succession, reaching the pair of children. These four cases exhaust the panel entries because the local outer factors are paths.

Consequently all global row differential equations hold. For the coefficient at particular outer generators p,q, use their two nodes. There p and q are vertices, and every incoming differential along an outer factor comes from a child segment edge. Its coefficient is precisely the sum just verified. The middle differential is read in the same local tableau. The local row equation therefore gives the global equation at that coefficient, with the two sign reversals undone. The root choice supplies the bottom augmentation. No entries occur beyond the dimension of y shifted down by one, since the three input arrays and the local sections respect identity padding. The assembled tableau is a strict cell. Applying Φ returns y: W recovers the mixed entries, while the root-Q and root-P augmented projections recover all pure P and pure Q entries respectively.

Taking a signed face of y commutes with the whole construction. A restriction lowering degree by h takes that face h degrees lower, or is empty if the cut lies below the restriction. Equation (1) and the globularity of the local choices then give this assertion by induction on node depth. Reading the bottom rows gives the required global face, and padding with identities gives global identities.

Finally take the target mixed atom on Sp ⊗ Sq and its specified source atom on p ⊗ e ⊗ q. The local restrictions of the source atom are empty off its branches. On its branches they are the mixed atoms on the restricted outer faces, with identity padding when a higher generator projects to a single path edge. This follows row by row from the tensor-atom formula: dropping i and j outer degrees reindexes the summands, their middle and last signs change by (−1)ⁱ, and projecting to a path retains only its vertex and edge degrees. A cut of the atom gives the corresponding cut of this same restriction. These local cells are among the pinned atoms, their faces and their identities. Their three inputs are the ones in the recursion by the projection and overlap equations. Therefore the local choices return these very restrictions, and the assembled lift is the prescribed atom. This proves the section theorem. [Tensor-atom formula (4)](gray-tensor-of-contexts-rule-2026-11-18.md)

### Finite verification for the globe implementation

For globes every node path is a point or an interval. The independently enumerated local tables have the following sizes, counting the empty value and identifying identity padding.

| Outer path lengths | Source tableaux | Compatible triples |
|---|---:|---:|
| 0,0 | 4 | 4 |
| 0,1 or 1,0 | 12 | 12 |
| 1,1 | 58 | 46 |

The implementation exhausts the three independent path-array sets subject to (1), then verifies a choice on that whole finite domain with the required dimensions, pins and faces. Thus the globe specialization can use these four tables directly. The same tables construct the section for every input dimension; the algorithm does not enumerate a higher-dimensional source fibre. Run `python3 tools/gray_globe_section.py 3 3` to test on every diagonal cell of D⁴ ⊗ D⁴, including the 1,649 cells in hom degree seven. The verifier checks basis degrees, row differentials, normalization, the exact image, both faces and the mixed atoms. [Uniform construction and verifier](../../../tools/gray_globe_section.py)

The general implementation accepts a tree as a JSON list of its child trees. Run `python3 tools/gray_tree_section.py '[[[],[]],[]]' '[[],[[]]]'` for a pair with branching below the root. The checker enumerates the source and target independently and compares the constructed lifts with actual source cells. It verifies 18, 460, 3,892, 9,795, 12,899 and 13,214 diagonal cells in the six hom degrees, as well as every mixed generator. [Construction for arbitrary finite trees](../../../tools/gray_tree_section.py)

This proves the strict section and the implication in (iv). To deduce CT for Dᵐ ⊗ Dⁿ, the antecedent still asks for CaTT terms on Dᵐ⁻¹ ⊗ I ⊗ Dⁿ⁻¹. That is an iterated tensor with three factors. Q2 for arbitrary globe dimensions and Q1 for general families remain open here.

# Verification (2026-11-19)

Status: **verified, partial**. Four responses. Together they prove **CT(P ⊗ I ⊗ Q) ⇒ CT(ΣP ⊗ ΣQ) for all finite globular P and Q** (route (iv)), and CT for several new families. CT for general pairs and families is still open, because the antecedent is a three-factor tensor.

**Response 1 (transfer theorem; CT(D² ⊗ D²)): correct.**
- The endpoint panels are interpreted by boundary lifting inside the route pasting contexts R₀ = ΣQ ∨₀ ΣP and R₁ = ΣP ∨₀ ΣQ. This uses that π is a trivial fibration on pasting contexts, and the support lemma keeps every panel term in its route. This is more general than the single exchange coherence of item 11, and agrees with it at P = Q = I.
- Mixed generators are declared with ρ-substituted suspended types. Diagonal cells get T(c) = (ΣU(s c̄))[ρ], and the face conditions follow from the section commuting with faces. Off-diagonal cells lie on a single pure side, where boundary lifting is used. The argument needs only a pinned globular section; it does not need composition.
- Re-run: `python3 tools/canonical_gray_two_discs.py` checks 4/20/50/60/61 cells in degrees 0–4. `src/CaTTExp/Generated/CanonicalGrayTwoDiscs.agda` type-checks with Agda 2.6.3 in 2 min 27 s, and has no postulates or pragmas. This agrees with MARK's independent certified transfer for D² ⊗ D² (item 11).

**Response 2 (CT for all iterated globe tensors of total dimension ≤ 4, and for D³ ⊗ D² and D² ⊗ D³; faces of mixed atoms recovered): correct.**
- The three-skeleton construction is right. A term is chosen by a minimal composite expression, and its j-faces are corrected for j = 1, …, d−1 by identity-image (j+1)-terms in the ≤ j-dimensional subcontext, composed at cut j. With d ≤ 3, only RC(1) and RC(2) are needed. **The same argument works in every degree d, given RC(j) for the j-skeleta of the family context for j < d.** Those skeleta are strongly loop-free Steiner, so CT for every tensor of globular pasting diagrams follows from RC(∞) on finite strong-Steiner contexts (Q2 of the relative-coherence prompt). I state this as a reduction and do not re-prove it here.
- Re-run of the exhaustive degree-4 check: in all eight ordered shapes the only non-identity 4-cell is the top atom, so in degree 4 only declarations are needed. Associativity holds because the choices are made on flattened ordered basis tuples. The section checks `gray_globe_comparison.py 3 2` and `2 3` were re-run (48/94/106/107).
- Recovery of faces: the restriction of Φ to the face-closure X of the mixed atoms is injective, by reading back each row (the rules for i, j > 0 use the two distinct faces of a generator in a globular pasting diagram). The pure-route lift (a ⊗ v ⊗ s₀b) #₀ (t₀a ⊗ v ⊗ b) and the extension over arrows are correct.

**Response 3 (CT(Σ[r] ⊗ Σ[s]) for all r, s; a section on the 2-skeleton for all P, Q): correct.**
- Arrow lifts W are put in sorted form (P-steps before Q-steps in each portion, with M at the crossing). 2-cells are lifted by sequences of square swaps whose extra squares lie in panels and have identity image. Between crossing arrows of two paths, the 2-cells are lattice paths, unique given the edge set. The 3-lift is the oriented cube, whiskered after strict exchange reorders the disjoint blocks; no inverses are used.
- B = [r] ⊗ I ⊗ [s] has dimension ≤ 3, so Response 2 gives CT(B), and Response 1 transfers it. `python3 tools/gray_path_section.py 3 3` was re-run and gives 32/600/1,916/3,075.

**Response 4 (pinned globular section of Φ for all finite globular P and Q): correct as a proof, checked on globes and one branching pair.**
- The local data (U, V, W) on pairs of node paths, with the compatibility equations (1), are assembled into a diagonal tableau by the inverse of the Known-10 formula. Then Response 3's path section is applied, and the result is recursed over pairs of Batanin-tree nodes in order of depth and assembled from bottom rows. The coefficient bound (mass ≤ 1 per bottom row, via positive chain maps to globes) is what guarantees a single vertex triple per node pair. Each step was read through. The sign and orientation bookkeeping (reversal after an odd number of P-descents) is the only delicate part, and the checkers exercise it.
- Re-run: `gray_globe_section.py 3 3` verifies every diagonal cell of D⁴ ⊗ D⁴ (1,649 in hom degree 7). `gray_tree_section.py '[[[],[]],[]]' '[[],[[]]]'` verifies 18/460/3,892/9,795/12,899/13,214 cells (73 s).

**What is left open.** CT for three-factor tensors P ⊗ I ⊗ Q in general, and hence for all pairs: by (iv), CT for all pairs follows from CT(P ⊗ I ⊗ Q). Iterated tensors and associativity in general are also open, as is a transfer for k ≥ 3 suspended factors. Alternatively, all of CT follows from RC on strong-Steiner skeleta. Follow-up: [`outbox/canonical-gray-terms-r5.md`](../outbox/canonical-gray-terms-r5.md).
