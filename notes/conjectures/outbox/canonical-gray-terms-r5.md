# Canonical CaTT terms for the cells of Gray tensors of pasting diagrams: general pairs and iterated tensors

*A self-contained problem. It assumes familiarity with the type theory CaTT, strict ω-categories and Steiner's directed complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** The most general theorem: a construction for **all** pairs and all finite families of globular pasting diagrams, compatible with associativity, or a proof that none exists for some family together with the equations such a counterexample forces. The cylinders I ⊗ P (items 6–8) are settled. Simultaneous suspension is now settled too: CT(P ⊗ I ⊗ Q) ⇒ CT(ΣP ⊗ ΣQ) for all P and Q (items 10–12). So CT for all pairs reduces to CT for the **three-factor** tensors P ⊗ I ⊗ Q, and what is asked is the iterated case. The question is purely syntactic: whether chosen terms can match their boundaries on the nose in a theory with no definitional equalities.

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
    
    has nonnegative coefficients and commutes with ∂ in positive degree. Here e is the arrow of I, and at total degree 0 the image is one of the two directed paths from (0,0) to (1,1). Prefixing the row ((0,0),(1,1)) to the image of each tableau row gives a strict functor **Φ : P ⊗ I ⊗ Q → (ΣP ⊗ ΣQ)((0,0),(1,1))**. Φ sends the atom p ⊗ e ⊗ q to the atom Sp ⊗ Sq, so every mixed atom of ΣP ⊗ ΣQ has a source of one lower dimension. Φ is not injective.

11. **Φ has a pinned globular section for all finite globular P and Q.** There is a map s of underlying globular sets, commuting with both faces and preserving identities, with Φ s = id and s(Sp ⊗ Sq) = p ⊗ e ⊗ q on every mixed atom. Proof outline:
    - For two paths J = [r] and K = [s], cells of the diagonal hom are lifted directly. Arrows become sorted words (P-moves before Q-moves on each route, with the middle move at the crossing). 2-cells become sequences of oriented square swaps, whose extra squares lie in the endpoint panels and have identity image. 3-cells become whiskered oriented cubes, after strict exchange of disjoint swap blocks.
    - For general P and Q, a diagonal cell y is cut into local data over pairs (u, w) of nodes of the Batanin trees, by restriction to node paths and augmentation. Each local triple (U on J ⊗ I, V on I ⊗ K, W on J ⊗ K one degree lower), subject to three compatibility equations, is lifted by the path case. The bottom rows of the local lifts are then assembled into a tableau of P ⊗ I ⊗ Q. A coefficient bound (each prospective bottom row has mass ≤ 1, by positive chain maps to globes) makes each local bottom row a single vertex triple.
    - Restricted to the faces of the mixed atoms, Φ is injective, and the face-closure of the mixed atoms is recovered row by row from the image.
    
    The section is checked by machine on every diagonal cell of D⁴ ⊗ D⁴ and of a pair of branching trees.
12. **Transfer theorem: CT(P ⊗ I ⊗ Q) ⇒ CT(ΣP ⊗ ΣQ) for all finite globular P, Q.** Let U be a CT assignment for B = P ⊗ I ⊗ Q, and s the section of item 11. Build a substitution ρ from the family context of ΣP ⊗ ΣQ into Σ Fam(B), in order of dimension. Each endpoint-panel generator of B is sent to a boundary lift, inside the route pasting context R_v (R₀ = ΣQ ∨₀ ΣP, R₁ = ΣP ∨₀ ΣQ), of its strict image with the literally prescribed substituted endpoints. This is possible because strict interpretation on a pasting context is a trivial fibration, and the support of a term is that of its strict image. Each mixed generator Sp ⊗ Sq is declared with the ρ-substituted suspended type of p ⊗ e ⊗ q. Then T(c) = (Σ U(s c̄))[ρ] on the diagonal hom, and boundary lifting on the pure sides, satisfies (a)–(c). Composition preservation of s is not needed. For P = Q = I the panel lifts can be taken to be single exchange coherences over D² ∨₀ D²; this case was also checked by a certified CaTT checker.
13. **CT through dimension 3, and in dimension 4 when the top cells are atoms.** For any family context, choose terms degree by degree. Take the variable on a generator and the identity on an identity. For any other cell, compose the terms of a minimal strict expression, then correct its j-faces for j = 1, …, d−1 by composing at cut j with identity-image (j+1)-terms. Those terms live in the ≤ j-dimensional subcontext and exist by RC(j) there. RC(1) and RC(2) hold in every CaTT context, so this gives (a)–(c) for every cell of dimension ≤ 3. In degree 4 only declarations are needed when every non-identity 4-cell is an atom, which holds for all iterated tensors of globes of total dimension 4 (checked exhaustively). Making the choices on flattened basis tuples gives the same terms for every parenthesization. **The same argument works in every dimension given RC(j) for the j-skeleta of the family context.** These skeleta are strongly loop-free Steiner, so relative coherence on finite strong-Steiner contexts (any two parallel n-terms with the same strict image are joined by an (n+1)-term) would give CT for every tensor of globular pasting diagrams.
14. **Consequences.** CT holds for: every iterated tensor of globes of total dimension ≤ 4, including the four-cube I^{⊗4} compatibly with every parenthesization; D² ⊗ D² (with its identity towers), D³ ⊗ D² and D² ⊗ D³; and ΣJ ⊗ ΣK for all paths J = [r], K = [s] (each factor a vertical string of 2-generators of any length), since [r] ⊗ I ⊗ [s] has dimension ≤ 3.

## 4. Questions

**Q1 (main).** Decide CT for **all** pairs Θ, Δ of finite globular pasting diagrams and for all iterated tensors Θ₁ ⊗ ⋯ ⊗ Θ_k, compatibly with associativity (the assignments for (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) agree up to renaming). By item 12, the pairs follow from the three-factor tensors P ⊗ I ⊗ Q. A positive answer may use any terms (single coherence heads over chosen pasting diagrams, boundary lifts in pasting subcontexts, correction coherences as in items 7, 8 and 13, simultaneous inductive choices). A negative answer should give a family with a proof that no assignment satisfies (a)–(c).

Natural routes:
- (i) **Transfer for k suspended factors.** Compare the diagonal hom of ΣP₁ ⊗ ⋯ ⊗ ΣP_k, from the bottom corner to the top corner, with a tensor of P₁, …, P_k and a (k−1)-dimensional shape recording the order in which the factors are traversed (for k = 2 this is the interval I of item 10). Prove a strict comparison with a pinned section and a transfer theorem as in items 11–12. Together with closure under wedges and under interval factors, this would give an induction on total dimension that covers every iterated tensor.
- (ii) **Interval factors in any position.** Generalise the cylinder results (items 6–7) from I ⊗ P to tensors containing I in any position, and to iterated tensors, in particular CT(P ⊗ I ⊗ Q) for all P and Q: suspension and wedge closure in each outer factor of P ⊗ I ⊗ Q, for example CT(P ⊗ I ⊗ Q) ∧ CT(P ⊗ I ⊗ Q′) ⇒ CT(P ⊗ I ⊗ (Q ∨ Q′)). The smallest three-factor tensors not covered by item 14 have total dimension 5 (for example I ⊗ I ⊗ D³ and D² ⊗ I ⊗ D², the antecedent for D³ ⊗ D³). A uniform argument is what is wanted, not these cases one at a time.
- (iii) **Through relative coherence.** Prove RC(n) for all n on the skeleta of the family contexts of Gray tensors (strongly loop-free Steiner complexes), which by item 13 gives CT outright. Or prove the weaker statement that item 13's correction step needs, namely the existence of identity-image (j+1)-terms between parallel j-terms with equal image in those skeleta.

**Q2 (fallback, still every dimension).** If Q1 is out of reach, prove CT for every Gray cube I^{⊗n} (all n, compatibly with every parenthesization), or for every pair Dᵐ ⊗ Dⁿ of globes, by a construction uniform in the dimensions. By item 12, the globe pairs follow from CT(D^{m−1} ⊗ I ⊗ D^{n−1}) for all m and n.

**Q3 (if CT fails).** If CT fails for some pair or family, prove that no assignment satisfies (a)–(c) and identify the minimal extra rule that makes the family contexts well formed (for example a typing rule for generators whose boundaries are molecules, or a definitional equation between bracketings). A precise description of the forced equations is the useful answer.

## 5. What counts as a solution

An explicit construction of T for all pairs and iterated tensors; CT for all three-factor tensors P ⊗ I ⊗ Q; a transfer theorem for k suspended factors; relative coherence on the strong-Steiner skeleta; a uniform construction for all cubes or all pairs of globes; an impossibility proof with the forced equations; or a published reference.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Steiner, *Simple omega-categories and chain complexes*, arXiv math/0403237 (tableaux and the tensor product, used for items 10–12).
- Steiner, HHA 2004; Hadzihasanovic, arXiv 2404.07273 (molecules, layerings, Prop. 8.3.17 on supports).
- Campion, arXiv 2311.00205; Chanavat, arXiv 2603.22242.
- Finster–Mimram, arXiv 1706.02866; Benjamin–Markakis, arXiv 2406.12127 (invertibility of coherences).
- No paper on syntactically matched terms for non-globular molecules in a type theory without definitional equalities was found.

# Researcher Response 1

**Wedge closure with a finite path as the other factor.** For every finite path $J=[r]$ and finite globular pasting diagrams $P,Q$,
$$
  \mathrm{CT}(J\otimes P) \land \mathrm{CT}(J\otimes Q)
  \quad\Longrightarrow\quad
  \mathrm{CT}\bigl(J\otimes(P\vee_0 Q)\bigr).
$$
This gives closure under any finite sequence of such wedges. The proof uses the full sieve and cosieve in the single-interval case of item 7. The new feature for a path is that a cell can cross several time edges at the common vertex. Two cuts determined by its source and target paths suffice in every dimension.

### Reconstructing a crossing cell

Let $z$ be the common vertex. Fix outer endpoints $(i,a),(j,b)$ with $a$ strictly before $z$ in $P$, $b$ strictly after $z$ in $Q$, and $i\le j$. Write $H$ for their hom in the tensor with the wedge. Put
$$
 L=(J\otimes P)((i,a),(j,z)),\qquad R=(J\otimes Q)((i,z),(j,b)).
$$
Collapse $Q$ or $P$ to $z$ to get $H\to L\times R$. Every vertex $l$ of $L$ is a path. Let $A(l)$ be the time of its last $P$-edge. For a vertex $q$ of $R$, let $B(q)$ be the time of its first $Q$-edge. Both times exist by the choice of $a,b$.

**Claim.** The collapse identifies $H$ with the full subcategory of $L\times R$ on the pairs $(l,q)$ with $A(l)\le B(q)$. In global Steiner tableaux the inverse on any admissible pair $(x,y)$ is $x+y-E_{ij}$, where $E_{ij}$ is the identity tower on the path from $(i,z)$ to $(j,z)$. Indeed, augmenting the second tensor factor sends both tableaux to the unique path $i\to j$ and its identities. On chains the two collapses jointly retain each off-seam coefficient once and count the common projection once too many. The displayed formula therefore inverts them, fixes the outer vertices, and satisfies the boundary equations by linearity. Positivity is automatic in degrees above one since there are no seam chains there. In each signed degree-one row the left path contains exactly the seam edges with starting times $A(l),\ldots,j-1$, and the right path those with starting times $i,\ldots,B(q)-1$. Subtracting one copy of every seam edge is possible exactly when these ranges cover the interval. Applying the test to both signed rows proves fullness, including $i=j$.

Along an arrow of $H$, both $A$ and $B$ are nondecreasing. To see this at a threshold $i\le u<j$, collapse the time path to one interval, retaining just the edge at $u$. The resulting left path first traverses $P$ and then the seam edge exactly when $A(l)\le u$. Such paths form the full sieve of item 7, so the condition propagates from target to source. On the right, the path first traverses the seam edge and then $Q$ exactly when $B(q)>u$. The full cosieve propagates this condition from source to target. Taking all thresholds gives both inequalities. [Single-interval sieve and cosieve, §2](../answered/canonical-gray-terms-r2-2026-11-19.md)

For a time $t$, take the full subcategory $G_t$ on pairs with $A(l)\le t\le B(q)$. Every cell $(x,y)$ there splits horizontally at $(t,z)$. Strip the seam suffix from $t$ to $j$ off both degree-one rows of $x$, changing its target vertex to $(t,z)$. Strip the seam prefix from $i$ to $t$ off both degree-one rows of $y$, changing its source to $(t,z)$. Leave all higher rows intact. These are positive tableaux in the respective pieces. The changed vertex accounts for the boundary of each stripped path, and the difference of the two degree-one rows is unchanged. Their horizontal composite restores $x+y-E_{ij}$, since the two stripped segments partition the seam path. At fixed $t$ this split commutes with signed hom faces in every positive hom dimension.

Take a positive-dimensional cell $h=(\alpha,\beta)$ of $H$, with hom endpoints $x_-=(l_-,q_-)$ and $x_+=(l_+,q_+)$. The intermediate vertex $d=(l_-,q_+)$ is admissible since $A(l_-)\le B(q_-)\le B(q_+)$. In the product hom,
$$
 h=h_1\mathbin{\#_0^H}h_2,\qquad
 h_1=(1_{l_-},\beta),\quad h_2=(\alpha,1_{q_+}),
$$
where identities have the dimension of $h$. This is composition at cut 1 in the tensor. The endpoints of $h_1$ belong to $G_{A(l_-)}$, and those of $h_2$ belong to $G_{B(q_+)}$. Fullness puts each factor inside the corresponding subcategory. Thus both factors split horizontally, even if no single time works for $h$. For hom dimension at least two, both immediate faces of $h$ inherit exactly the same $d$ and the same two times.

### Choosing terms with literal boundaries

Glue the two given family contexts on their seam generators. The seam is $J$, whose generator boundaries are object variables. Choose either section on the cells entirely in the seam. On other cells having both object endpoints in one piece keep that piece's section. This is consistent because all positive-dimensional faces retain the pair of object endpoints. A cell with object endpoints in one piece stays there. Its boundary paths cannot leave that piece and return, since all spatial edges are directed forward. For the higher rows, collapse the retained piece to $z$. The resulting tableau has object endpoints in the seam and both paths there. It has only identity higher rows there. Any positive second row would have zero differential, impossible for a nonzero positive chain in the strong Steiner basis by the sign test of item 7. The same argument applies inductively in each higher row. Every generator off the retained piece survives this projection. This also covers endpoints in the seam. Reverse crossings are empty and a wedge with a point is its other component.

Choose a single bracketing $T(w)$ of the edge word of each crossing path $w$. For a cell $g\in G_t$ of global dimension $m\ge 1$, let $S_t(g)$ be the horizontal composition head on the two given terms for its stripped tableaux. Use the heads over $D^m\vee_0 D^m$ with recursively prescribed faces as in item 7. Thus each signed face of $S_t(g)$ above global dimension one is literally $S_t$ of the corresponding face. For every path $w\in G_t$, choose comparison 2-terms in both directions between $T(w)$ and $S_t(w)$. Each is a coherence over the globular context of the directed path $w$, substituted back into the tensor. The two terms can be read in that path context since their strict image is $w$ and their support is precisely its edges and vertices. Both use the full path, so the coherence rule applies. Their strict images are identities because the path context strictly has only identity 2-cells.

For $m\ge 2$, pad $S_t(g)$ on the source side by the comparison from $T(w_-)$ and on the target side by the comparison to $T(w_+)$, where $w_-,w_+$ are its global 1-endpoints. Denote the resulting term by $U_t(g)$. In dimension two use ordinary vertical composition. In higher dimensions use the two composition heads on $D^2\vee_1D^m$ and $D^m\vee_1D^2$, retaining the comparison term when taking either higher face. Their recursive types are admissible by the composition rule because their signed faces use exactly the corresponding boundary of the arity. Consequently $U_t(g)$ strictly denotes $g$, its 1-endpoints are the chosen path terms, and its immediate faces for $m>2$ are literally the padded terms for the two faces. [Composition and whiskering heads, §§4–6](../answered/canonical-gray-terms-r2-2026-11-19.md)

For every crossing cell of global dimension $m\ge 2$, take
$$
 T(h)=V_m\bigl(U_{A(l_-)}(h_1),\,U_{B(q_+)}(h_2)\bigr),
$$
with the cut-1 head $V_m$ on $D^m\vee_1D^m$. The common 1-term at the join is literally $T(d)$. In dimension two its outer faces are precisely the chosen path terms. Above dimension two the recursive type of $V_m$ applies the same construction to both immediate faces, since $d$ and both cuts are fixed. Its strict value is $h$ by the product factorization. Every tensor generator belongs to a piece, where the chosen generator term is its variable. These facts give (a)–(c), including identity towers.

**Finite check.** The checker enumerates the strict tensor and its two pieces independently by composition of atoms. For every crossing hom it compares the reconstructed tableaux with the complete enumeration, checks each stripped factor in its piece, and recovers each positive-dimensional hom cell by the two indicated compositions. For $[3]$ with the branching trees below it checks 819, 28,225, 55,275 and 55,275 crossing cells in global dimensions 1 through 4, including identities. The literal CaTT boundary argument is the recursive construction above. [Tableau checker](../../../tools/gray_path_wedge.py)

```sh
python3 tools/gray_path_wedge.py 3 '[[[],[]],[]]' '[[],[[]]]'
```

This proves the path case of wedge closure in every dimension. In route (ii), the other factor $P\otimes I$ can itself have higher generators. Its overlap then contributes higher rows to the subtracted tableau, and the degree-one cut test above leaves the general three-factor case open.

### Why the same intermediate-path rule fails for three factors

In the three-factor tensor $I_A\otimes I_B\otimes[2]$, write $C,D$ for the successive edges of $[2]$, with shared vertex $z$. Consider paths from the bottom to the top corner. Each path is a word in $A,B,C,D$ with $C$ before $D$. A square swaps an adjacent inversion, keeping the order of $C,D$. Here are two strict 2-cells with the same path boundaries. Each displayed step is a whiskered generating square.

$$
\begin{aligned}
 CDBA&\to CDAB\to CADB\to ACDB\to ACBD\to ABCD,\\
 CDBA&\to CBDA\to BCDA\to BCAD\to BACD\to ABCD.
\end{aligned}
$$

A path performing both clock moves at $z$ must be $CABD$ or $CBAD$. **No one of these paths is a cut-1 intermediate for both cells.** The first cell contains the $BA\to AB$ square at the terminal vertex of $[2]$, after $D$. In any factorization through a seam path this square must precede that path. Indeed, starting at a seam path, both clock letters already precede $D$, and every clock/spatial swap moves the clock letter earlier. Thus the first cell can pass only through $CABD$. The second cell uses the $BA\to AB$ square at the initial vertex, before $C$. Once both letters precede $C$, they remain there, so this square must follow any seam path and the second cell can pass only through $CBAD$.

This argument applies to every strict expression for each cell. A strict 2-cell in this tensor is generated by square swaps, horizontal composites can be serialized by interchange, and its degree-two tableau counts each generating square at its specified vertex. In particular no refactorization can change the position in $[2]$ of the unique $BA\to AB$ event. Both allowed cuts are attained by commuting the two disjoint middle swaps in each displayed route. The example isolates the additional choice that route (ii) needs even when CT itself already holds by item 13.

The two cells are even the faces of **one 3-cell**. Apply the functor $I_A\otimes I_B\otimes I\to I_A\otimes I_B\otimes[2]$ taking the last edge to $CD$ to the generating cube. Its source performs the two spatial swaps past $B$, then the two past $A$, then the $BA$ swap at the initial vertex. This gives the second displayed cell, up to exchange of disjoint swaps. Its target performs the $BA$ swap at the terminal vertex, then the spatial swaps past $A$, then those past $B$. This gives the first cell. Equivalently, the top chain is $e_A\otimes e_B\otimes C+e_A\otimes e_B\otimes D$, whose signed degree-two boundaries give the two displayed square lists. Thus choosing the intermediate path separately for each 2-cell still cannot make that choice constant on the two faces of this 3-cell.

The obstruction persists in $P\otimes I\otimes(Q\vee_0 Q')$ whenever $P,Q,Q'$ each have an edge. Choose one generating edge in $P$, one entering the seam in $Q$, and one leaving it in $Q'$. These choices include the example as a subtensor. It has a strict retraction: in $P$ project every edge over the chosen root segment to the edge of $I$, collapsing the other root segments; use the same two projections on $Q,Q'$, glued at $z$, to reach $[2]$. These are functors because parallel edges have the same image and all higher generators can be sent to identities. A common seam path in the larger tensor would project to one in the example, and any factorizations through it would project to factorizations of the displayed 2-cells. Thus a higher-dimensional treatment of the middle seam is already necessary throughout this family.
