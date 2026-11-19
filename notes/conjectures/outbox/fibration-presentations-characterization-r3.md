# Grothendieck constructions over free bases: recognising when the plain Gray-generator presentation works

*A self-contained problem. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, polygraphs (computads) and Grothendieck constructions, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** The most general theorem about the **unaugmented** relative Gray-generator presentation of §2: an exact criterion, valid in every dimension and checkable by a terminating procedure, for when it is well defined and correct; or a proof that no terminating procedure exists. Existence of presentations, dimension bounds and a uniform presentation with auxiliary generators are now settled (§3 items 12–15), so they are not asked again; one more counterexample or special class is not what we want.

## 1. Setting

### 1.1 Marked (∞,ω)-categories and left cartesian fibrations

Work in Loubaton's model (*Categorical theory of (∞,ω)-categories*, arXiv 2406.05425).
- A **marked** (∞,ω)-category has a chosen class of positive-dimensional cells containing the equivalences and closed under composition. A^♯ marks every cell. D_n^t is the n-globe with its top cell marked. ⊗ is the marked Gray tensor.
- A map p : E → B is a **left cartesian fibration** (Def. 3.2.2.1) when it has the unique right lifting property against `K ⊗ {0} → K ⊗ [1]^♯` for `K ∈ {D_n^♭ : n ≥ 0} ∪ {D_n^t : n ≥ 1}`. Straightening (Thm 4.1.4.2) identifies left cartesian fibrations over B^♯ with functors B → ω (the (∞,ω)-category of (∞,ω)-categories). The fibration classifying T is written ∫T.

### 1.2 Polygraphs and localisation

- For a finite polygraph Ψ, `Free(Ψ)` is the free (∞,ω)-category on Ψ and `F(Ψ)` the free strict ω-category. Ψ is **homotopical** when the comparison Free(Ψ) → F(Ψ) is an equivalence. `F_m(Π)` is the free strict m-category on an m-polygraph Π.
- A marking is a set of generators. `J[S⁻¹]` is the localisation of J at a set S of cells.
- A **presentation** of a fibration p : E → B over a polygraph base Γ is a finite marked polygraph Ψ with a map to Γ and a set S of marked generators such that `Free(Ψ)[S⁻¹] → Free(Γ)` is equivalent to p.

### 1.3 Why it matters

A W-weighted limit of a diagram F is the marked lax limit of F ∘ p over the total space of the fibration p classifying W (Loubaton, Cor. 4.2.2.6, Cor. 4.2.3.18). If p has a finite presentation with a finite correctness certificate, a proof checker can accept the weighted limit as a marked lax limit over a finite index. So a theorem for all dimensions gives checkable weighted limits for every finite weight with free values over every homotopical finite base.

## 2. The expected answer

For a base n-polygraph Γ and a strict weight T : F(Γ) → strict ω-categories with each value T(b) = F_m(Π_b), Π_b finite and homotopical, the expected presentation is the **relative Gray-generator presentation**:
- the generators of every fibre Π_b over the base vertices b;
- for each base k-generator q (k ≥ 1) with source vertex b and each j-generator g of Π_b, one marked generator `q ⊗ g` of dimension k + j, with boundary given by the Leibniz formula `∂(q ⊗ g) = ∂q ⊗ g ± q ⊗ ∂g`, read through T;
- localisation at the generators q ⊗ g with j > 0.

So the presentation has dimension ≤ n + m.

## 3. What is known

1. **Localisation lemma.** If S is a set of marked cells of J and q : J → J[S⁻¹], restriction is an equivalence of (∞,ω)-categories of marked cones, natural in the apex.
2. **Tensor-localisation and mixed localisation.** For any set S of positive-dimensional cells, `X[S⁻¹] ⊗ I ≃ (X ⊗ I)[{s ⊗ 0, s ⊗ 1, s ⊗ i}⁻¹]`. For finite homotopical X and Y there is a finite cellular model 𝓡_Y(X), natural in X, with one generator x ⊗ y per pair of generators, and `𝓡_Y(X)[(x ⊗ y)⁻¹ : dim x, dim y > 0] ≃ X × Y`.
3. **Bases of dimension ≤ 2.** For every finite homotopical 2-polygraph base and fibres F_m(Π_b) with Π_b finite homotopical, the expected presentation is correct. Proof: for a base path p = e₁; …; e_r the map δ_r : I → [r] (0 ↦ 0, 1 ↦ r) and A ⊗ [r] ≃ (A ⊗ I) ∐_A ⋯ ∐_A (A ⊗ I) give a map from the cylinder of T(p) into the **unlocalised** graph presentation; attach a double Gray cylinder block for each base 2-generator along these maps; conclude with Loubaton's theorem that pullback preserves colimits (Thm 3.2.3.15, Cor. 3.2.3.16).
4. **Bases of dimension 3.** For a finite 3-polygraph base Γ such that Γ and its 2-skeleton are homotopical (more precisely: the 2-skeleton is homotopical and attaching the 3-generators is a homotopy pushout), the expected presentation is correct for every fibre dimension m, with generators of dimension ≤ m + 3. The 3-generators of the base are handled by left and right whiskering subdivisions of the outer interval, which reduce each 3-generator to a cylinder over its 2-dimensional boundary data, where item 3 applies.
5. **Suspension bases.** For Q = F_d(Λ) with Λ finite homotopical and base ΣQ, the expected presentation is correct for every fibre dimension, via K = 1^co ⋆ Q and the suspension-base classification (Loubaton, Cor. 4.1.2.19).
6. **The obstacle in base dimension ≥ 4.** Gluing the local totals over the base generators gives the right generators. But the attaching maps are first obtained in the **localised** category Free(Ψ)[S⁻¹], while adjoining generators to Ψ needs attaching maps in Free(Ψ) itself, and such lifts need not exist (in Free(s)[s⁻¹] the inverse of s exists; in Free(s) no arrow goes back). For bases of dimension ≤ 3 the lifts were constructed by hand, by subdividing cylinders along composites in the boundary of each generator. For base dimension ≥ 4 what is missing is a **compatible** choice of such lifts for all higher-dimensional boundary expressions at once.
7. **A finite certificate exists for the proved cases:** homotopicality certificates for the fibres and base attachments, the weight data, the attaching expressions, the generator list indexed by base–fibre pairs, the marking and localisation lists, and face-compatibility checks on the intersections of the cylinders.
8. **Homotopicality of the base is needed.** For the base (x; σ : 1_x ⇒ 1_x), F(Γ) = B²ℕ groupoidifies to K(ℤ,2), while every Free(Ψ)[S⁻¹] with Ψ finite groupoidifies to a finite CW complex. So even the terminal weight has no finite presentation.
9. **The expected presentation fails from base dimension 4.** Base Γ: one vertex b, a : b → b, μ : aa ⇒ a, an associator α : (μ₁;μ₀) ⇛ (μ₀;μ₀) (words in right-to-left order; a subscript is the position of the rewrite), and a pentagon 4-generator P. Fibre Π: x, g : x → x, δ : g ⇒ gg, κ : (δ₀;δ₁) ⇛ (δ₀;δ₀). Weight: T(b) = F₃(Π), T(a) = Z the constant functor at x, T(μ)_x = g, T(α)_x = δ, T(P)_x = κ.
   - Both polygraphs and all their skeleta are homotopical: Π is the oriental polygraph of the semisimplicial set with one simplex in each dimension ≤ 3, and Γ is the even dual of the one for dimension ≤ 4 (Chanavat, arXiv 2603.22242, Thm 3.35).
   - With the fibre-first Leibniz convention ∂(g ⊗ q) = ∂g ⊗ q + (−1)^{|g|} g ⊗ ∂q, the mixed generators are t = a ⊗ x, c : t ⇒ tg, u : gtt ⇒ t, and the 3-generators D = a ⊗ δ, M = μ ⊗ g : (u₀;c₀) ⇛ (c₂;u₀), V = α ⊗ x : (c₁;u₂;u₀) ⇛ (δ₀;u₁;u₀), together with κ.
   - The 2-cells gt⁴ ⇒ t are 8 (18 rewriting paths up to interchange). Every contextual instance of a 3-generator gives exactly 8 edges. Over the short side R → E → L of the pentagon, the only V-step out of the lift of R lands at a vertex with no outgoing edge. So the target face of P ⊗ x does not exist in the unlocalised category: it would need M⁻¹, which exists only after localisation. No weak attaching map can repair this, since it would project to the missing strict 3-cell.
   - Reversing M repairs this pentagon but changes M's Gray boundary.
10. **Finite presentations exist, with auxiliary generators.** For every finite polygraph Γ with homotopical skeleta, and every (∞,ω)-functor T : F(Γ) → ω whose values have finite weak polygraphic presentations (localisations allowed), ∫T has a presentation (Free(Ψ), ⟨Q ∪ S⟩)[S⁻¹] with Ψ finite and homotopical and Q, S finite sets of positive-dimensional generators, keeping the cartesian marking. The proof gives no dimension bound and no control of the generators. It goes through finite complicial models: closure under finite homotopy pushouts and products, and a conversion L_d of a finite stratified simplicial set into a finite semisimplicial set whose oriental polygraph is homotopical. It then inducts over the base cells with Loubaton's pullback–colimit theorem and the suspension classification for globes. For weights whose values are ≃ F(Π_b), the weight can moreover be made strict, since the homs of ω between gaunt strict categories are gaunt.
11. **Homotopicality of the base passes to skeleta.** The inclusion F(Γ_{≤r}) ↪ F(Γ) is discrete Conduché (the generator support of a strict cell is well defined and additive), so pulling back along it preserves colimits (Loubaton Thm 2.2.2.10), and the comparison for Γ_{≤r} is a pullback of the comparison for Γ. Hence Γ is homotopical iff all its skeleta are.
12. **Every pair has a presentation of dimension ≤ n + m, and n + m is optimal.** For Γ of dimension n and weights with values Free(Π_b)[W_b⁻¹], dim Π_b ≤ m, there is a presentation of dimension ≤ n + m. Proof: a bounded relative realization lemma for finite complicial models (thin markings reflected from the fibrant target after each horn stage), a dimension calculus (homotopy pushouts by double mapping cylinders give max{b, c, a + 1}, products add dimensions, globe attachments keep dimension), totals over globes of dimension m + k, and a conversion L_D with (L_D K)_r = K_r × Inj([r], [D]) whose oriental polygraph is homotopical (Chanavat, Thm 3.35). Optimality: Γ = ∂D_{n+1}, Π = ∂D_{m+1}, constant weight; the total groupoidifies to Sⁿ × S^m. In particular item 9's example has a presentation of dimension ≤ 7.
13. **A uniform presentation Ω.** For every finite homotopical Γ and every coherent weight with values Free(Π_b)[W_b⁻¹] there is a finite marked polygraph Ω with dim Ω ≤ n + m and a finite localisation set S_Ω with Free(Ω)[S_Ω⁻¹] ≃ ∫T over B^♯, such that each Π_b is a literal subpolygraph, and each base k-generator q and fibre j-generator g give a designated cartesian-marked generator z_{q,g} of dimension k + j (localised when j > 0) whose 0-endpoints are the original fibre vertices. **The positive-dimensional proper faces of z_{q,g} are auxiliary copies**, related to the required composites by explicitly localised comparison cylinders. Ω need not be homotopical. Key lemma: adjoining fresh globes along two prescribed vertices, with no positive-dimensional identifications, preserves homotopicality.
14. **Coherent weights and non-free values** are covered by item 13, with finite roofs for the transport data.
15. **A positive semi-decision procedure.** Equivalence of two specified finite complicial models (over a fibrant base, preserving and reflecting the cartesian marking) has a finite certificate: finite anodyne extensions L ↪ A, K ↪ U, A ↪ V, maps f : K → A, g : A → U, h : U → V and finite cylinders witnessing gf ≃ i, hg ≃ j. So once attaching expressions for all q ⊗ g in the unlocalised Free(Ψ) are supplied, correctness is certifiable, and enumerating expressions and certificates semi-decides "the unaugmented presentation is well defined and correct". What is missing is a **bound on the positive mixed-generator expressions** to search. Additivity of base-generator support bounds the top base lifts, but not the lower mixed steps. No undecidability reduction is known either.

## 4. Questions

**Question 1 (main: decidability and an exact criterion).** Is it decidable, given a finite homotopical polygraph Γ and a strict weight T with finite homotopical fibres Π_b, whether the relative Gray-generator presentation of §2 is well defined (every q ⊗ g has an attaching map in the unlocalised Free(Ψ), with boundary the Leibniz expression read through T) and correct? Either give a terminating procedure with proof, ideally as an exact criterion on (Γ, T) valid in every dimension (for example a bound on the length of the mixed-generator rewriting paths that must be searched, derived from the dimensions and supports of the base and fibre generators), or prove undecidability by a reduction (for example from reachability in positive rewriting systems, encoded in the base associativity data as in item 9).

**Question 2 (conditions on the base alone).** Is there a condition on Γ alone, checkable on finite data and valid in every dimension, under which the unaugmented presentation is well defined and correct for **every** strict weight with free homotopical values? Item 9 shows that this is not automatic from base dimension 4, even for oriental bases. If such a condition exists, prove necessity and sufficiency; if the only bases that work for every weight are those covered by items 3–5, prove that.

**Question 3 (well defined implies correct?).** When every q ⊗ g has an attaching map in Free(Ψ) with the Leibniz boundary, is the resulting presentation automatically correct (after localising at the q ⊗ g with j > 0), or can a well-defined unaugmented presentation present the wrong fibration? A proof of "well defined ⇒ correct" would reduce Question 1 to a pure existence problem for attaching expressions.

## 5. What counts as a solution

A terminating recognition procedure with proof, or an undecidability proof, for Question 1; an exact base criterion, or a proof that none exists beyond items 3–5, for Question 2; a proof or counterexample for Question 3; or a published reference.

## 6. Literature (searched 2026-11-19)

- Loubaton, arXiv 2406.05425 (left cartesian fibrations, straightening, pullback preserves colimits, discrete Conduché functors); Loubaton, arXiv 2207.08504 (complicial model).
- Campion, arXiv 2311.00205 and 2311.00200; Chanavat, arXiv 2603.22242 (homotopy polygraphs, semisimplicial pasting theorem).
- Ara–Guetta, arXiv 2503.08832, §7 (strict Grothendieck construction with Gray functoriality).
- No published recognition theorem for Gray-generator presentations of Grothendieck constructions over polygraphs was found.

# Researcher Respons 1

**Question 3 has an affirmative answer for the actual globular Leibniz boundaries stipulated in the question.** Once those attaching maps exist in the unlocalised presentation, localisation gives the required Grothendieck construction.

The proof compares each new relative cellular construction **after localising the completed lower base skeleton**. Uniqueness of marked lifts identifies the old boundary data there. The Gray tensor determines the dependence on the new generators, so this comparison does not require a compatible unlocalised map from an entire boundary block.

This resolves Question 3. It does not supply a terminating procedure or an undecidability reduction for Question 1, or an exact base criterion for Question 2.

## Theorem: automatic correctness

Let \(\Gamma\) and \(T\) satisfy the hypotheses of Question 1. Suppose the unaugmented relative Gray-generator presentation \(\Psi\) is well defined: its generators have the **actual globular Gray attaching maps**, read through \(T\), with positive expressions in the previously constructed unlocalised stages.

Let
\[
S=\{q\otimes g:\dim q>0,\ \dim g>0\}.
\]
Then there is an equivalence
\[
\boxed{\operatorname{Free}(\Psi)[S^{-1}]\simeq \int T}
\]
of marked \((\infty,\omega)\)-categories over \(F(\Gamma)^\sharp\), compatible with the prescribed fibre maps.

Consequently, two choices of positive expressions realising the prescribed Gray boundaries give equivalent localised presentations.

Here “actual globular Gray boundary” has its usual map-valued meaning. It specifies the Gray pasting and its attaching map, including the compositions involving previously adjoined pair generators. Equality of signed generator counts, parallelism of the two faces, or equality only after mapping to the *final* total would be weaker conditions. None of those weaker conditions is used below.

## 1. Gauntness of the actual total

We first establish the rigidity needed for the comparison.

### Lemma 1

Let
\[
p:E\longrightarrow B^\sharp
\]
be a left or right cartesian fibration. If \(B\) and every vertex fibre \(E_b\) are gaunt, then \(E\) is gaunt.

### Proof

Prove simultaneously for left and right cartesian fibrations, by induction on \(r\), that the space
\[
\operatorname{Map}(D_r,E)
\]
is \(0\)-truncated.

For \(r=0\), its map to the discrete space \(\operatorname{Map}(D_0,B)\) has fibres
\[
\operatorname{Map}(D_0,E_b),
\]
which are discrete by hypothesis.

For the induction step, fix vertices \(x,y\) of \(E\). The induced map
\[
\operatorname{hom}_E(x,y)
\longrightarrow
\operatorname{hom}_B(px,py)
\tag{1}
\]
is a cartesian fibration of the opposite variance, by Loubaton’s Proposition 3.2.2.6. In the left cartesian case, choose a marked lift
\[
x\longrightarrow f_!x
\]
of a base arrow \(f:px\to py\). The cancellability square for that lift identifies the fibre of (1) over \(f\) with
\[
\operatorname{hom}_{E_{py}}(f_!x,y).
\tag{2}
\]
For a right cartesian fibration, the corresponding fibre is
\[
\operatorname{hom}_{E_{px}}(x,f^*y).
\tag{3}
\]
These identifications follow from Definition 3.2.2.15 and Theorem 3.2.2.24(5). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The base of (1) is gaunt, and its vertex fibres (2) or (3) are gaunt. The induction hypothesis therefore applies to (1). Using \(D_r=\Sigma D_{r-1}\), we obtain
\[
\operatorname{Map}(D_r,E)
\simeq
\coprod_{x,y\in E_0}
\operatorname{Map}
\bigl(D_{r-1},\operatorname{hom}_E(x,y)\bigr),
\]
a discrete space.

All globular evaluations of \(E\) are therefore discrete. The Segal identities then make every globular-sum evaluation discrete, which is precisely the gauntness criterion; compare Loubaton’s Proposition 2.3.3.2.  ∎

In our setting, every free strict base skeleton and every free strict fibre is gaunt. Lemma 1 consequently applies to
\[
E_k:=\int\!\left(T|_{F(\Gamma_{\le k})}\right)
\]
for every \(k\). This conclusion concerns the actual classified fibration and does not assume correctness of the proposed presentation.

### Lemma 2: uniqueness of marked factors

In a gaunt left cartesian fibration \(p:E\to B^\sharp\), a marked \(d\)-cell is determined by:

1. its projection to \(B\);
2. the distinguished \((d-1)\)-face specified by the alternating globular lifting condition.

Indeed, Theorem 3.2.2.24(4) gives the unique lifting property against
\[
i_{d-1}^{\epsilon_d}:D_{d-1}\longrightarrow D_d^t,
\]
where, in Loubaton’s notation, \(\epsilon_d=+\) when \(d-1\) is even and \(\epsilon_d=-\) when \(d-1\) is odd. Gauntness allows the resulting uniqueness to be expressed as equality in a strict model of \(E\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

In particular, two positive expressions for the same prescribed marked factor have equal images in \(E\) once their distinguished faces have equal images.

Apply this only to **marked factors**. A complete weighted face can include unmarked fibre arrows supplied by \(T\). For example, the word \(gtt\) in the stated counterexample need not be marked. Its fibre factor \(g\) is fixed by \(T\); marked-lift uniqueness applies to the relevant cartesian factors.

## 2. What the globular Leibniz rule fixes

The next point ensures that localisation of the old stage does not discard information about the new pair generators.

Use the fibre-first tensor convention, while retaining the question’s label \(q\otimes g\). For \(j,k\geq 0\), put
\[
K_{j,k}
=
(D_j\otimes\partial D_k)
\amalg_{\partial D_j\otimes\partial D_k}
(\partial D_j\otimes D_k).
\tag{4}
\]

The tensor polygraph \(D_j\otimes D_k\) has one generator for each pair of generators of its factors. The only generator absent from (4) is the pair of top generators. Thus it has a specified globular attaching map
\[
\lambda_{j,k}:\partial D_{j+k}\longrightarrow K_{j,k}.
\tag{5}
\]
The pair-generator description is Henry–Loubaton, Proposition 2.13; their construction also supplies tensor functoriality and preservation of colimits. [arxiv.org](https://arxiv.org/pdf/2301.11424?utm_source=chatgpt.com)

We use the corresponding Gray cellular models when interpreting (4)–(5) in \((\infty,\omega)\)-categories. In particular, the gluing in (4) carries its homotopy-pushout meaning and its structural coherence.

Now fix a base \(k\)-generator \(q\) and a fibre \(j\)-generator \(g\). The two terms in (4) have distinct roles.

### The proper-base-face part

Every tensor generator of
\[
D_j\otimes\partial D_k
\]
has a proper base face as its base factor. After reading the boundary of \(q\) through \(T\), its expression uses the completed lower base stage.

The fibre terms introduced by \(T\), including components of \(T(q)\), also belong to that stage: all fibre presentations have already been adjoined.

### The proper-fibre-face part

Write the fibre attachment as
\[
a_g:\partial D_j\longrightarrow
\operatorname{Free}(\Pi_{b,<j}).
\]
The other part of (4) is read through the map
\[
a_g\otimes\operatorname{id}_{D_k}.
\tag{6}
\]

Hence its new-base generators are precisely the already named
\[
q\otimes h,\qquad \dim h<j.
\]
More than their support is specified: (6) determines their compositions and whiskerings. This uses the Gray construction **before** mixed localisation.

Thus the actual globular Leibniz rule has the following triangular form:

> The boundary of \(q\otimes g\) uses old-stage expressions and previously adjoined \(q\otimes h\), with \(\dim h<\dim g\). Its dependence on those new generators is fixed by the fibre attaching map and Gray functoriality.

This is a consequence of (4)–(6), not an additional compatibility assumption.

The intersection
\[
\partial D_j\otimes\partial D_k
\tag{7}
\]
uses only proper base faces. Consequently, the agreement needed to glue the two parts can be established entirely in the completed old stage.

## 3. Independent positive choices become compatible after localisation

Fix \(k>0\). Assume the presentation over \(\Gamma_{\le k-1}\) has already been proved correct, and write
\[
A=\operatorname{Free}(\Psi_{\le k-1}),
\qquad
\varepsilon:A\longrightarrow E_{k-1}
\]
for its comparison map. Thus
\[
A[S_{\le k-1}^{-1}]\simeq E_{k-1}.
\tag{8}
\]

For a new base generator \(q\), let
\[
C_q\longrightarrow L_q
\tag{9}
\]
be the local relative Gray presentation over
\[
\partial D_k\hookrightarrow D_k.
\]
Its correctness is among the accepted globe and suspension cases. Relative to \(C_q\), the generators of \(L_q\) are exactly
\[
q\otimes g,\qquad g\in\Pi_{s_0q}.
\]
There is a canonical marked map
\[
\beta_q:C_q\longrightarrow E_{k-1}
\tag{10}
\]
obtained by restricting the actual fibration along the attaching map of \(q\).

Consider a prescribed old factor in an attaching expression. Different substitutions in different expressions may use different positive representatives. We claim that every such representative has its canonical image under \(\varepsilon\).

Prove this by induction on the dimension of the formal factor.

- A fibre vertex has its prescribed image.
- A pure fibre expression has the image specified by the fibre map and \(T\).
- For a marked factor, its projection is prescribed. Its distinguished face is a composite of lower-dimensional formal factors and prescribed fibre expressions. Their images agree with the canonical images by induction. Lemma 2 therefore identifies the image of the marked factor with its canonical image.

Composition then identifies the images of the complete old expressions, including weighted expressions that are not themselves marked.

This argument applies separately to each substitution. It does **not** require a common choice of positive representative for a formal factor throughout the presentation. Nor does it construct or assume an unlocalised map
\[
C_q\longrightarrow A.
\tag{11}
\]

The compatible map needed for the proof is (10), after localisation.

## 4. Comparing the relative cellular constructions

We now prove the comparison while retaining the previously adjoined generating disks. This prevents an equivalence of completed categories from concealing a change in a later attaching map.

Order the generators over each new base \(k\)-generator by fibre dimension. Suppose the relative stages through fibre dimension \(j-1\) have already been identified after base change along \(\varepsilon\), under \(E_{k-1}\) and compatibly with their generating disks.

For a fibre \(j\)-generator \(g\), compare the attaching map of \(q\otimes g\) with the canonical local attaching map.

On the proper-base-face part of (4), Section 3 identifies all marked factors and all prescribed fibre terms with their canonical values in \(E_{k-1}\).

On the proper-fibre-face part, the map is induced by (6). The induction hypothesis identifies the preceding relative stages compatibly with their generating disks. Gray functoriality therefore identifies this entire face map, including its compositions involving \(q\otimes h\).

Their restrictions to (7) agree through \(E_{k-1}\). The comparison data there have no further ambiguity: mapping spaces into the gaunt category \(E_{k-1}\) are \(0\)-truncated. The homotopy-pushout property of (4) now identifies the maps from \(K_{j,k}\). Precomposing with (5) identifies the two attaching maps.

Adjoining the generating disk extends the identification of relative cellular diagrams. Induction on \(j\) gives
\[
E_{k-1}\amalg_A
\operatorname{Free}(\Psi_{\le k})
\;\simeq\;
E_{k-1}
\amalg_{\coprod_{q\in\Gamma_k}C_q}
\coprod_{q\in\Gamma_k}L_q.
\tag{12}
\]

Equation (12) is the essential step. Its proof never replaces equality in a partially constructed stage by equality in the final total. The new generators remain part of the relative cellular diagram throughout.

A different written expression for a prescribed Gray face causes no problem: a genuine equality or homotopy of attaching maps is preserved by base change, and equivalent attaching diagrams have equivalent pushouts. What matters is that it denotes the prescribed globular face in the relevant relative stage.

## 5. Localisation and the base induction

Let \(S_k^{\mathrm{new}}\) denote the mixed generators belonging to the new base \(k\)-generators. By (8) and the universal property of localisation,
\[
\operatorname{Free}(\Psi_{\le k})
[S_{\le k}^{-1}]
\simeq
\left(
E_{k-1}\amalg_A
\operatorname{Free}(\Psi_{\le k})
\right)
[(S_k^{\mathrm{new}})^{-1}].
\tag{13}
\]

Substitute (12). The map \(C_q\to E_{k-1}\) already inverts the mixed boundary generators. Therefore localisation of the right-hand side of (12) gives
\[
E_{k-1}
\amalg_{\coprod_q E_{\partial q}}
\coprod_q E_q,
\tag{14}
\]
where \(E_{\partial q}\) and \(E_q\) are the actual restricted totals over \(\partial D_k\) and \(D_k\). This uses the accepted correctness of the local presentations in (9).

Homotopicality of the base skeleta identifies the base attachment with the corresponding pushout in \((\infty,\omega)\)-categories:
\[
F(\Gamma_{\le k})
\simeq
F(\Gamma_{\le k-1})
\amalg_{\coprod_q\partial D_k}
\coprod_qD_k.
\tag{15}
\]
Pullback along the classified cartesian fibration preserves this colimit, so (14) is \(E_k\). This is Loubaton’s Theorem 3.2.3.15 and Corollary 3.2.3.16. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Combining (13)–(15),
\[
\operatorname{Free}(\Psi_{\le k})[S_{\le k}^{-1}]
\simeq E_k.
\]

The initial stage \(k=0\) is the coproduct of the fibre presentations, and is correct by homotopicality of the \(\Pi_b\). Induction proves the theorem.

All constructions and comparisons above take place in the category of **marked** \((\infty,\omega)\)-categories over the base. Thus the equivalence includes the cartesian marking. ∎

## 6. The resulting finite certificate

For the unaugmented presentation, a separate equivalence certificate of the kind in item 15 is unnecessary once the prescribed attaching expressions have been supplied and checked.

A certificate consists of:

1. **The input data:** the base and fibre polygraphs, their homotopicality certificates, and the finite strict weight data.
2. **The prescribed generators:** the fibre generators and the pairs \(q\otimes g\), with their dimensions, cartesian markings, and mixed localisation list.
3. **The attaching expressions:** finite positive expressions for both globular faces of each pair generator, ordered by base dimension and then fibre dimension.
4. **The Gray-boundary verification:** finite typed pasting data, or finite derivations, showing that these expressions realise (5) after reading the labels through \(T\). This checks the fibre-boundary map (6), the prescribed projections, markings of the marked factors, and the globular face identifications.

Different substitutions for a proper-base factor may be recorded separately. The checker does not need an additional compatible unlocalised map (11): Section 3 proves the required compatibility after localisation.

The mathematical implication is therefore
\[
\boxed{
\text{well-defined actual globular Gray attachments}
\quad\Longrightarrow\quad
\text{correct unaugmented presentation}.
}
\]

The unresolved recognition issue is the existence of those positive attachments. The proof gives neither a bound on their length nor a terminating negative test, so Questions 1 and 2 remain unresolved here.
