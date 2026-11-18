# Problem: finite presentations of cartesian fibrations over a 2-dimensional base

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and 2-categorical Grothendieck constructions, and nothing else. The questions are in §4, smallest first.*

## 1. Setting

### 1.1 Marked (∞,ω)-categories and left cartesian fibrations

Work in Loubaton's model (F. Loubaton, *Categorical theory of (∞,ω)-categories*, [arXiv 2406.05425](https://arxiv.org/abs/2406.05425)).

- A **marked** (∞,ω)-category has a chosen class of positive-dimensional cells. The class contains the equivalences and is closed under composition.
  - A^♯ marks every cell, and A^♭ marks only the equivalences.
  - D_n^t is the n-globe with its top cell marked.
  - ⊗ is the marked Gray tensor.
- **Left cartesian fibrations** (Def. 3.2.2.1). A map p : E → B is a left cartesian fibration if it has the *unique* right lifting property against

  ```
  K ⊗ {0} → K ⊗ [1]^♯,     K ∈ { D_n^♭ : n ≥ 0 } ∪ { D_n^t : n ≥ 1 }.        (★)
  ```

  Equivalently (Thm 3.2.2.24(5)), three conditions hold:
  1. every 1-cell of B has a marked lift with prescribed source, unique up to a contractible space;
  2. for marked u : x → x′ and every z, `E(x′, z) ≃ E(x, z) ×_{B(px,pz)} B(px′, pz)`;
  3. every hom map `E(x, y) → B(px, py)` is a **right** cartesian fibration (lifts with prescribed *target*).

  So the variance alternates: cocartesian 1-cells, cartesian 2-cells, and so on.
- **Straightening** (Thm 4.1.4.2). Left cartesian fibrations over B^♯ correspond to functors B → ω.

### 1.2 Why finite presentations matter

The W-weighted limit of a diagram F is the marked lax limit of F∘p over the total space of the left cartesian fibration p classifying W (Loubaton Cor. 4.2.2.6, Cor. 4.2.3.18, Thm 4.1.4.2). If p is presented by a map of *finite* computads with a marking, a proof checker can accept the weighted limit as a marked lax limit over the finite index, provided it can check (★) by a finite test.

### 1.3 Computads, markings and localisation

- `Free(Ψ)` is the free (∞,ω)-category on a finite computad Ψ: generators are freely adjoined along their boundaries.
- A **marking** μ is a set of positive-dimensional generators, closed up as in §1.1.
- `J[S⁻¹]` is the coherent localisation of a marked (∞,ω)-category J at a set S of marked cells.

## 2. What is known

1. **Localisation lemma (Loc), proved.** Let S be a set of marked positive-dimensional cells of a marked (∞,ω)-category J, and q : J → J[S⁻¹]. For every diagram F̄ on J[S⁻¹], restriction is an equivalence of whole (∞,ω)-categories of marked cones, natural in the apex: `Cone^m_{J[S⁻¹]}(c, F̄) ≃ Cone^m_J(c, F̄ q)`.
   - *Proof:* q is a pushout of Loubaton's generating trivialisations `D_{k+1}^t → D_k^♭`, so it is initial and final (Def. 3.2.1.6, Prop. 3.2.1.7). Then apply Lemmas 4.2.3.15 and 4.2.3.23.
   - So a marked index cell that every diagram sends to an equivalence may be inverted without changing marked lax limits.
2. **Base a graph: solved.** Let Γ be a finite graph, so `Free(Γ)` is the free category on it. A finite datum **FT₂** consists of:
   - fibre graphs `G_b`, one per vertex b, whose edges are the *vertical* generators (unmarked);
   - for each base edge u : b → c and each vertex e of G_b, a *horizontal* marked generator `u_e : e → T_u(e)`;
   - for each vertical β : e → e′ and each base edge u, a marked 2-generator `θ_{u,β} : β ; u_{e′} ⇒ u_e ; T_u(β)`, where `T_u(β)` is a path in G_c (possibly empty);
   - nothing else.

   With marking μ = horizontals ∪ θ's, `Free(Ψ)^μ[θ⁻¹] → Free(Γ)^♯` is a left cartesian fibration. It is equivalent to the Grothendieck construction of the functor `T : Free(Γ) → Cat` that the data define. Every weight `Free(Γ) → Cat` with values free on finite graphs has such a presentation. By (Loc), weighted limits may be computed over the *unlocalised* computad. Vertical generators must be unmarked: a marked vertical arrow over a point is a counterexample.
3. **What a base 2-generator needs** (proved necessary). Let α : u ⇒ v, with u, v : b → c paths in Γ, and let T send α to a natural transformation `a_α : T_u ⇒ T_v`.
   - For each fibre vertex e over b, there is a vertical path `a_{α,e} : T_u(e) → T_v(e)` with, for each vertical generator β : e → e′, the **path equality**
     ```
     T_u(β) ; a_{α,e′}  =  a_{α,e} ; T_v(β).                               (16)
     ```
   - Let `τ_{u,e}` be the composite of horizontal lifts along the path u, and `θ_{u,β} : β;τ_{u,e′} ⇒ τ_{u,e};T_u(β)` the pasted comparison. The marked cartesian lift of α at e must have **prescribed target**:
     ```
     λ_{α,e} :  τ_{u,e} ; a_{α,e}  ⇒  τ_{v,e}.                              (17)
     ```
     This matches the strict Grothendieck construction (Hörmann, *Six functor formalisms and fibered multiderivators*, Def. 2.14 and Prop. 2.16): a 2-cell `(u, r) ⇒ (v, s)` over α exists iff `r = a_{α,e} ; s`. λ projects to α, so it need not be invertible.
   - Naturality of the lifted 2-cell requires, for each (α, β), the **3-dimensional relation**
     ```
     (θ_{u,β} ⋆ a_{α,e′}) ; (λ_{α,e} ⋆ T_v(β))  =  (β ⋆ λ_{α,e′}) ; θ_{v,β},     (19)
     ```
     both sides running from `β;τ_{u,e′};a_{α,e′}` to `τ_{v,e};T_v(β)`.
   - **Without (19) the λ's are not cartesian.** Take u, v : 0 → 1, α : u ⇒ v, fibres `x →h y` and `z →k w`, T_u = T_v, and a_α = id. The two pastings `θ_u;(λ_x⋆k)` and `(h⋆λ_y);θ_v` have λ-counts (1,0) and (0,1). Counting λ's is a 2-functor to ℤ² that inverting θ preserves. So they are distinct, and the second does not factor through the first over an identity.
4. **Strict references.** Hörmann Def. 2.14; Gurski–Johnson–Osorno, *2-categorical opfibrations, Quillen's Theorem B, and S⁻¹S*, Def. 2.14 (mixed-variance 2-opfibrations); Warren, *The strict ω-groupoid interpretation of type theory*, §3 and App. B (strict ω-categorical Grothendieck construction). These give constructions and axioms, not finite recognition theorems for polygraph presentations.

## 3. The candidate FT₃

Let Γ be a finite 2-computad. Let B be the free **strict** 2-category on Γ, viewed as an (∞,ω)-category, and give it the marking B^♯. Let T : B → Cat be a strict 2-functor whose values are free categories on finite graphs `G_b`. T is determined by finite data: the paths T_u(β) for base edges u, and the paths a_{α,e} satisfying (16) for base 2-generators α.

**The presentation Ψ_T** has:
- the generators of §2 item 2 (vertical, horizontal `u_e`, comparisons `θ_{u,β}`), for the base *edges*;
- for each base 2-generator α and each fibre vertex e over its source, a 2-generator `λ_{α,e}` as in (17);
- for each base 2-generator α and each vertical generator β over its source, a 3-generator `Ξ_{α,β}` between the two sides of (19).

π sends vertical generators, θ's and Ξ's to identities, `u_e` to u, and `λ_{α,e}` to α.

**Marking:** μ = horizontals ∪ θ's ∪ λ's ∪ Ξ's. Vertical generators are unmarked.

**Localisation:** S = θ's ∪ Ξ's, the marked cells over identities.

**Conjecture FT₃.** `Free(Ψ_T)^μ[S⁻¹]` is equivalent over B^♯, as a marked (∞,ω)-category, to the marked Grothendieck construction of T. In particular it is a left cartesian fibration over B^♯. By (Loc), weighted limits with weight T can then be computed over the finite, unlocalised marked computad Ψ_T.

## 4. Questions

1. **Is the base right?** Let Γ be a finite 2-computad. Is `Free(Γ)`, the free (∞,ω)-category, equivalent to the free strict 2-category F₂(Γ)? If not in general, under what condition on Γ? A natural candidate condition is that no 2-generator has an identity 1-cell in its boundary, which rules out Eckmann–Hilton braidings. If the answer is no, take B := F₂(Γ) as the base and present π as a map `Free(Ψ) → B`, as in §3.
2. **Smallest case.** Let Γ = (u, v : 0 → 1, α : u ⇒ v), with fibres free on finite graphs. Prove or refute FT₃.
   - The specific worry: Free(Ψ_T) is a free *weak* structure. Its interchange and associativity cells between λ's and θ's are invertible but not identities, so they could leave non-trivial 3-cells after inverting S. ∫T is a (2,2)-category.
   - Is inverting the Ξ's enough to make the hom maps of `Free(Ψ_T)^μ[S⁻¹]` equivalent to those of ∫T?
3. **General 2-computad bases.** Prove FT₃ for every finite 2-computad Γ satisfying question 1's condition. This includes composite boundary paths u, v and base 2-cells whose boundaries share edges.
4. **Completeness.** Is every strict 2-functor T : F₂(Γ) → Cat with values free on finite graphs presented by some FT₃ datum? The data (16) are finitely many path equalities, so this should reduce to question 3.
5. **Higher.** Is there a finite criterion FT_n for bases that are n-computads and weights valued in free n-categories, alternating the variance in each dimension? If not, give an obstruction.

## 5. Literature search (2026-11-18)

- Loubaton (arXiv 2406.05425): exact infinite criterion (★); localisation via marked trivialisations (Def. 3.2.1.6, Prop. 3.2.1.7); cones (Lemmas 4.2.3.15, 4.2.3.23).
- Hörmann, Gurski–Johnson–Osorno and Warren (above): strict constructions and axioms.
- Abellán–Haugseng–Martini (arXiv 2602.07604) and Gagna–Harpaz–Lanari (arXiv 2012.04537): (∞,2)-dimensional fibrations and partially lax limits. No generator-level criteria.
- **Nothing found** on finite recognition of cartesian fibrations between polygraph-presented higher categories, nor on when the free weak ω-category on a 2-computad is equivalent to the free strict 2-category (question 1).

## 6. What would count as an answer

Any one of:
- an answer to question 1;
- a proof or counterexample for question 2;
- a corrected FT₃ with a proof;
- an obstruction showing that no finite presentation scheme of this kind can work over 2-dimensional bases.

# Researcher Response

**FT₃ holds under your proposed condition that both boundary paths of every generating \(2\)-cell are nonempty.** The base comparison in Question 1 follows from a 2026 pasting theorem. The walking-\(2\)-cell case admits a direct calculation of its entire hom \(\infty\)-categories, and Loubaton’s results on pullback and colimits then extend that calculation to the general positive base.

Without the boundary condition, there is a stronger obstruction: some finitely generated strict \(2\)-categories admit **no presentation by a finite weak computad followed by coherent localisation**, even if additional generators in arbitrarily high—but finitely many—dimensions are permitted.

Throughout, \(\operatorname{Free}\) means the cellular construction specified in §1.3, and all pushouts and localisations below are homotopical.

## 1. Question 1: the proposed condition is sufficient

Call a \(2\)-computad **positive** when the source and target paths of every generating \(2\)-cell are nonempty.

Chanavat’s *A strengthened \((\infty,n)\)-categorical pasting theorem*, arXiv:2603.22242v2, **Corollary 3.39**, states that every positive \(2\)-polygraph is a homotopy polygraph. Definition 3.10 says precisely that its strict cellular-extension squares are preserved as homotopy pushouts by the inclusion into flagged higher categories. [arxiv.org](https://arxiv.org/pdf/2603.22242?utm_source=chatgpt.com)

Consequently,
\[
\boxed{\operatorname{Free}(\Gamma)\simeq F_2(\Gamma)
\quad\text{for every positive \(2\)-computad }\Gamma.}
\tag{20}
\]

Here is the deduction. Write \(B_k=F_2(\Gamma_{\leq k})\), with identity cells added above the indicated dimension. The strict cellular construction uses the squares
\[
\begin{array}{ccc}
\displaystyle\coprod_{\gamma\in\Gamma_k}\partial D_k
&\longrightarrow&B_{k-1}\\
\downarrow&&\downarrow\\
\displaystyle\coprod_{\gamma\in\Gamma_k}D_k
&\longrightarrow&B_k ,
\end{array}
\qquad k=0,1,2.
\]
Chanavat’s result makes these homotopy pushouts. The weak cellular construction uses the same attaching spans. Induction on \(k\), using invariance of pushouts under equivalence of diagrams, proves (20). The resulting equivalence is the canonical comparison because it agrees with the maps of generating cells.

The ambient \(\omega\)-dimensional point is also covered. In Chanavat’s construction, a positive \(2\)-polygraph corresponds to a directed complex of dimension at most \(2\). Every molecule mapping to it therefore has dimension at most \(2\) and is frame-acyclic. **Theorem 3.17 can then be applied with \(n=\omega\)**. Passing from flagged categories to the completeness localisation used by Loubaton preserves the pushouts. Thus (20) is an equivalence in the required ambient higher category, including its higher coherence data. [arxiv.org](https://arxiv.org/pdf/2603.22242?utm_source=chatgpt.com)

There is no requirement that the generating graph be acyclic, that boundary paths be injective, or that the two boundaries use different edges. Positivity is sufficient; I am not claiming it is necessary.

## 2. Question 2: proof of FT₃ for the walking \(2\)-cell

Write
\[
C=F_1(G_0),\qquad D=F_1(G_1),\qquad
U=T_u,\quad V=T_v,\quad a=a_\alpha:U\Rightarrow V,
\]
and let
\[
P=\operatorname{Free}(\Psi_T)[\theta^{-1},\Xi^{-1}].
\]

We will calculate the entire hom \(\infty\)-category \(P(x,z)\) for \(x\in C\), \(z\in D\).

After inverting the \(\Xi\)’s, all generating cells of dimension at least \(3\) are invertible. Thus the calculation takes place in \((\infty,2)\)-categories, with homs in \(\mathrm{Cat}_\infty\). We first replace the weak free vertical categories by \(C,D\), using the graph case. This replacement preserves the cellular presentation up to equivalence.

### 2.1 Why the hom calculation includes all higher coherences

The relevant structural fact is that a composable string crossing from the \(C\)-fibre to the \(D\)-fibre has exactly one mixed arrow:
\[
\text{\(C\)-arrows}\ ;\ \text{mixed arrow}\ ;\ \text{\(D\)-arrows}.
\]
There are no arrows from \(D\) back to \(C\).

Consequently, after fixing \(C,D\), the remaining composition data form a \(C\)-\(D\) bimodule enriched in \(\mathrm{Cat}_\infty\). This description includes the coherent compatibility of the two actions, as in Haugseng’s many-object bimodule construction, Definition 4.1 and Remark 4.2. [arxiv.org](https://arxiv.org/pdf/1506.07341?utm_source=chatgpt.com)

For completeness, the particular free-module calculation needed here is explicit. Put
\[
\mathcal A=
\prod_{(x,z)\in\operatorname{Ob}C\times\operatorname{Ob}D}
\mathrm{Cat}_\infty
\]
and define
\[
(LM)(x,z)=
\coprod_{\substack{y\in\operatorname{Ob}C,\ w\in\operatorname{Ob}D\\
p\in C(x,y),\ q\in D(w,z)}}M(y,w).
\tag{21}
\]
The unit inserts identity paths. Multiplication concatenates the two \(C\)-paths and the two \(D\)-paths. Coherent \(L\)-algebras are precisely the bimodules just described.

The monad \(L\) preserves all colimits, since each summand in (21) is a copy of a coordinate of \(M\). Therefore:

- colimits of \(L\)-modules are created in \(\mathcal A\);
- the free \(L\)-module on a collection \(A\) has underlying collection \(L(A)\).

These are the module-colimit and free-module results of *Higher Algebra*, Corollaries 4.2.3.5 and 4.2.4.8, applied to the action of colimit-preserving endofunctors of \(\mathcal A\). [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HA.pdf?utm_source=chatgpt.com)

The connection with the original cellular presentation follows from the collage universal property. For fixed functors \(F:C\to W\) and \(G:D\to W\), a functor from the collage of \(M\) to \(W\), restricting to \(F,G\), is exactly a module map
\[
M\longrightarrow H_{F,G},
\qquad
H_{F,G}(x,z)=\operatorname{Hom}_W(Fx,Gz).
\]
Every compositional string involving a mixed arrow is accounted for by the module action. There is no operation with two mixed inputs.

It follows that a generating cell at \((y,w)\), evaluated in the hom from \(x\) to \(z\), contributes one cell for every pair
\[
p:x\to y,\qquad q:w\to z.
\]
Thus we may calculate the mixed hom by the generators and their left and right whiskerings. The colimits involved are colimits in \(\mathrm{Cat}_\infty\), so this calculation retains higher homotopy.

### 2.2 The transport generators give rooted trees

Fix \(x\in C\), \(z\in D\). Every mixed \(1\)-path has the form
\[
p;h_y;q,
\qquad
p:x\to y,\quad h\in\{u,v\},\quad q:T_h(y)\to z.
\]

For \(H\in\{U,V\}\) and \(r:H(x)\to z\), define a category \(\mathcal T_{H,r}\) as follows.

Its vertices are pairs
\[
(p,q),\qquad p:x\to y,\quad q:H(y)\to z,
\qquad H(p);q=r.
\]
Its generating arrows are
\[
(p;\beta,q)\longrightarrow(p,H(\beta);q),
\tag{22}
\]
where \(\beta\) is an edge of \(G_0\). These are exactly the whiskered transport generators \(\theta_{h,\beta}\).

Every vertex with nonempty \(p\) has exactly one parent: remove the last edge of \(p\). Each parent step reduces the length of \(p\), and the resulting sequence ends at
\[
(\operatorname{id}_x,r).
\]
Therefore \(\mathcal T_{H,r}\) is the free category on a rooted tree.

This remains true when \(C\) has directed cycles, when \(H\) identifies distinct paths, and when \(H(\beta)\) is an identity. The decreasing quantity is the length of the source path \(p\).

### 2.3 The \(\lambda\)’s and \(\Xi\)’s give mapping cylinders

For each \(s:V(x)\to z\), define
\[
f_s:\mathcal T_{V,s}\longrightarrow
\mathcal T_{U,a_x;s},
\qquad
(p,q)\longmapsto(p,a_y;q),
\tag{23}
\]
where \(p:x\to y\).

Naturality makes this well-defined:
\[
U(p);a_y;q=a_x;V(p);q=a_x;s.
\]
It also makes (23) a functor on the generating parent arrows. Indeed, for \(\beta:y\to y'\),
\[
U(\beta);a_{y'}=a_y;V(\beta).
\tag{24}
\]

Set
\[
\mathcal U=\coprod_{r:U(x)\to z}\mathcal T_{U,r},
\qquad
\mathcal V=\coprod_{s:V(x)\to z}\mathcal T_{V,s},
\]
and let \(f:\mathcal V\to\mathcal U\) be the union of the \(f_s\).

Before inverting the transport arrows, but after inverting the \(\Xi\)’s, the mixed hom is
\[
K=
\mathcal U
\amalg_{\mathcal V\times\{0\}}
\bigl(\mathcal V\times[1]\bigr),
\tag{25}
\]
where the attaching map is \(f\).

To verify (25), observe that:

- the cylinder arrow at \((p,q)\) is the whiskered cell
  \[
  p;\lambda_y;q:
  p;u_y;a_y;q\Longrightarrow p;v_y;q;
  \]
- the cylinder square for a parent arrow (22) is exactly the whiskered \(\Xi_\beta\), with its two boundaries identified using (24).

There are no additional generating coherences in this cylinder presentation. A free tree category is the categorical colimit of its vertex and edge cells, and product with \([1]\) preserves those colimits. For each tree edge, its product with \([1]\) contributes a square with a specified invertible comparison between the two composites. The coherences for longer tree paths follow from this colimit construction.

Thus (25) identifies the homotopy-cellular presentation itself.

### 2.4 Localisation contracts the trees

Invert every transport arrow. Each \(\mathcal T_{H,r}\) has a terminal root, so its groupoid completion is contractible.

Moreover, for a tree category \(\mathcal T\), with generating edges \(E\),
\[
\bigl(\mathcal T\times[1]\bigr)
\bigl[(E\times\{0,1\})^{-1}\bigr]
\simeq
\mathcal T[E^{-1}]\times[1].
\tag{26}
\]
This follows directly from the universal property: a functor
\(\mathcal T\to\operatorname{Fun}([1],X)\) inverts an edge precisely when both endpoint evaluations invert it.

Applying localisation to (25) therefore gives
\[
K[\theta^{-1}]
\simeq
R_U\amalg_{R_V\times\{0\}}
\bigl(R_V\times[1]\bigr),
\tag{27}
\]
where
\[
R_U=D(Ux,z),\qquad R_V=D(Vx,z)
\]
are discrete categories, and the attaching function is
\[
s\longmapsto a_x;s.
\]

The category in (27) has vertices
\[
u_r\quad(r:Ux\to z),\qquad
v_s\quad(s:Vx\to z),
\]
and exactly the nonidentity arrows
\[
u_{a_x;s}\longrightarrow v_s.
\tag{28}
\]
This is precisely
\[
\operatorname{Hom}_{\int T}(x,z).
\]

Because \(D\) is free, composition on the left by \(a_x\) is injective on paths. Hence this hom category is a disjoint union of intervals and isolated \(u\)-vertices. In particular, its mapping spaces are empty or contractible.

**This resolves the higher-cell worry in Question 2:** the localisation has the correct entire hom \(\infty\)-categories. There are no surviving nontrivial higher automorphism spaces hidden by a \(2\)-truncation.

### 2.5 Markings and the relative statement

The comparison sends
\[
\theta\longmapsto\operatorname{id},\qquad
\lambda\longmapsto\text{the corresponding cartesian lift of }\alpha,\qquad
\Xi\longmapsto\operatorname{id}.
\]

Under the normalisation above, a marked mixed \(1\)-cell has identity residual path. Conversely, any mixed \(1\)-cell with identity residual path is equivalent, by transport, to the chosen horizontal lift and is therefore marked. All \(2\)-cells in the strict target are marked: they are the cells (28), obtained by whiskering the \(\lambda\)’s, and identities. Loubaton’s markings are invariant in the relevant cell spaces and stable under composition and whiskering. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The comparison is the identity on the vertical categories, an equivalence on every mixed hom, and compatible with the projection to \(B\). It is therefore a marked equivalence over \(B^\sharp\).

The proof is also **relative to the whole graph-boundary presentation**: its restriction to the \(\theta\)-only construction is exactly the graph-case normalisation. This relative property is what permits the next step.

## 3. Question 3: extension to every positive \(2\)-computad

Let \(\Gamma\) be positive, put
\[
B_1=F_1(\Gamma_{\leq1}),\qquad B=F_2(\Gamma),
\]
and let \(\Gamma_2\) denote its set of generating \(2\)-cells.

Section 1 gives the homotopy pushout
\[
B\simeq
B_1
\amalg_{\coprod_{\alpha\in\Gamma_2}\partial D_2}
\coprod_{\alpha\in\Gamma_2}D_2.
\tag{29}
\]

### 3.1 The strict Grothendieck projection has the required fibration structure

This verification does not use FT₃.

For vertices \((b,x)\), \((c,y)\), the hom category of the strict construction has arrows
\[
(f,r),\qquad f:b\to c,\quad r:T_f(x)\to y,
\]
and a morphism over \(\gamma:f\Rightarrow g\) precisely when
\[
r=T(\gamma)_x;s.
\tag{30}
\]

Thus its hom projection is the category-of-elements projection for the presheaf
\[
B(b,c)^{\mathrm{op}}\longrightarrow\mathrm{Set},
\qquad
f\longmapsto T(c)(T_f(x),y),
\]
whose action on \(\gamma:f\Rightarrow g\) is
\[
s\longmapsto T(\gamma)_x;s.
\]
In particular, it is a discrete cartesian fibration: the unique lift of \(\gamma\) with target \((g,s)\) is
\[
(f,T(\gamma)_x;s)\Longrightarrow(g,s).
\tag{31}
\]

The chosen marked \(1\)-lift of \(f\) at \(x\) is \((f,\operatorname{id})\). Composition with this lift identifies the hom from \((c,T_fx)\) with the required pullback hom, since the residual path is unchanged. These facts verify the three conditions in your §1.1.

Hence
\[
p:E=\int T\longrightarrow B^\sharp
\]
is a left cartesian fibration. Since its base is already maximally marked, it is classified.

### 3.2 Pull back the cellular decomposition

Two results of Loubaton now apply:

- **Proposition 3.1.2.34:** maximal marking \((-)^\sharp\) preserves colimits.
- **Theorem 3.2.3.15**, or its **Corollary 3.2.3.16:** pullback along a classified left cartesian fibration preserves colimits. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Therefore (29), maximally marked and pulled back along \(p\), gives
\[
E\simeq
E_{B_1}
\amalg_{\coprod_\alpha E_{\partial D_2,\alpha}}
\coprod_\alpha E_{D_2,\alpha}.
\tag{32}
\]

Each term has a presentation already established:

- \(E_{B_1}\) has the graph-case FT₂ presentation.
- \(E_{\partial D_2,\alpha}\) has the graph-case presentation for two auxiliary parallel edges.
- \(E_{D_2,\alpha}\) has the walking-\(2\)-cell FT₃ presentation proved in Section 2.

For \(\alpha:u\Rightarrow v\), the boundary attaching map sends the auxiliary horizontal generators to
\[
u_e^{\mathrm{aux}}\longmapsto\tau_{u,e},
\qquad
v_e^{\mathrm{aux}}\longmapsto\tau_{v,e},
\]
and sends their transport generators to the pasted transports
\[
\theta_{u,\beta},\qquad\theta_{v,\beta}.
\]

The walking presentation is relative to these boundary data. Its remaining attachments are exactly:

\[
\lambda_{\alpha,e}:
\tau_{u,e};a_{\alpha,e}\Longrightarrow\tau_{v,e},
\]
and the invertible \(\Xi_{\alpha,\beta}\) with the boundary in (19).

Consequently, the pushout presentation on the right of (32) is exactly
\[
\operatorname{Free}(\Psi_T)^\mu
[(\theta\cup\Xi)^{-1}].
\]
This proves
\[
\boxed{
\operatorname{Free}(\Psi_T)^\mu
[(\theta\cup\Xi)^{-1}]
\ \simeq_{\,B^\sharp}\
\int T
}
\tag{33}
\]
for every positive \(\Gamma\).

Repeated edges, equal boundary paths, and edges used by both boundaries require no additional generators: they enter through the attaching maps in (29). The homotopy pushout (32) supplies the compatibility between different base \(2\)-generators.

By your localisation lemma, the corresponding weighted limits can therefore be computed over the finite, unlocalised marked computad \(\Psi_T\).

## 4. Question 4: completeness and the finite check

For positive \(\Gamma\), the presentation scheme is complete for the specified strict functors \(T\).

Choose finite fibre graphs \(G_b\). The required data are:

1. for each base edge, its action on fibre vertices and fibre generating edges;
2. for each base \(2\)-generator \(\alpha\), one component path \(a_{\alpha,e}\) per source-fibre vertex;
3. the naturality equality (16) for each pair \((\alpha,\beta)\) with \(\beta\) a source-fibre generating edge.

Naturality for arbitrary fibre paths follows by induction on their length. For example, naturality for \(\beta\) and \(\delta\) gives
\[
T_u(\beta;\delta);a
=
T_u(\beta);a;T_v(\delta)
=
a;T_v(\beta;\delta).
\]
Since the base is free as a strict \(2\)-category, the generator assignments then extend to the strict \(2\)-functor without additional relations to check.

For an explicit finiteness count, write
\[
n_b=|G_b{}_0|,\qquad m_b=|G_b{}_1|.
\]
The numbers of generators of \(\Psi_T\) are:

| Dimension | Number |
|---|---:|
| \(0\) | \(\displaystyle\sum_b n_b\) |
| \(1\) | \(\displaystyle\sum_b m_b+\sum_{u\in\Gamma_1}n_{s(u)}\) |
| \(2\) | \(\displaystyle\sum_{u\in\Gamma_1}m_{s(u)}+\sum_{\alpha\in\Gamma_2}n_{s_0(\alpha)}\) |
| \(3\) | \(\displaystyle\sum_{\alpha\in\Gamma_2}m_{s_0(\alpha)}\) |

All naturality checks are equality checks between finite edge words in free categories. Equation (33) establishes the coherences for composite base \(2\)-cells.

This gives a finite sufficient recognition test for presentations in the FT₃ format. Semantic completeness for arbitrary, possibly nonpositive \(\Gamma\) fails for the reason below.

## 5. Failure without positivity, and an obstruction to unrestricted FT\(_n\)

Consider
\[
\Gamma=\{x;\ \sigma:1_x\Rightarrow1_x\}.
\]

### 5.1 The weak and strict free constructions differ

Its free strict \(2\)-category is
\[
B^2\mathbb N:
\]
one vertex, only the identity \(1\)-cell, and \(2\)-cells forming the commutative monoid \((\mathbb N,+)\).

Let \(L\) denote groupoidification. The weak cellular construction gives
\[
L\operatorname{Free}(\Gamma)
\simeq
*\amalg^{h}_{S^1}*
\simeq S^2.
\tag{34}
\]

By contrast,
\[
L(B^2\mathbb N)\simeq K(\mathbb Z,2).
\tag{35}
\]
Ara proves the corresponding nerve calculation in *A Quillen Theorem B for strict \(\infty\)-categories*, Theorem 4.9 and Example 4.10. Ara–Maltsiniotis’s comparison of Street and cellular nerves identifies the same homotopy type for the cellular nerve. [normalesup.org](https://www.normalesup.org/~ara/files/thmB.pdf?utm_source=chatgpt.com)

The spaces in (34) and (35) are not equivalent: \(S^2\) has no homology above degree \(2\), whereas \(K(\mathbb Z,2)\) has nonzero homology in arbitrarily large even degrees. This is also the counterexample discussed in Guetta’s thesis, §4.5.2. [arxiv.org](https://arxiv.org/pdf/2104.12662?utm_source=chatgpt.com)

This answers the unrestricted part of Question 1 negatively.

It also refutes unrestricted FT₃ directly. Take the constant terminal weight on \(B^2\mathbb N\). There are no vertical edges, no transport generators, and no \(\Xi\)’s. The proposed presentation is precisely the weak cellular construction in (34), while the required total category is \(B^2\mathbb N\).

### 5.2 Adding finitely many higher generators cannot repair this example

There is a general obstruction.

**Lemma.** If \(\Psi\) is a finite weak computad and \(S\) is any collection of cells to be coherently inverted, then
\[
L\bigl(\operatorname{Free}(\Psi)[S^{-1}]\bigr)
\]
has the homotopy type of a finite CW complex.

**Proof.** Groupoidification is a left adjoint, so it preserves the cellular pushouts. Moreover,
\[
L(D_k)\simeq *,
\qquad
L(\partial D_k)\simeq S^{k-1}.
\]
The second formula follows inductively from the expression of a globular boundary as two lower-dimensional globes glued along their common boundary. Thus each generating \(k\)-cell becomes an ordinary homotopy attachment of a \(k\)-cell. A finite computad gives a finite CW complex.

Finally,
\[
L\bigl(J[S^{-1}]\bigr)\simeq L(J),
\]
because every functor from \(J\) to a space already sends every cell in \(S\) to an equivalence. This is exactly the universal property of localisation. ∎

Since \(K(\mathbb Z,2)\) has homology in unbounded degrees, the lemma implies
\[
\boxed{
B^2\mathbb N
\not\simeq
\operatorname{Free}(\Psi)[S^{-1}]
\quad\text{for every finite }\Psi.
}
\tag{36}
\]

Therefore no complete presentation scheme of the proposed form can cover **all** finite strict \(2\)-computad bases, even for the constant terminal weight. The same obstruction applies to an unrestricted FT\(_n\) scheme for \(n\ge2\), since these bases are also \(n\)-computads with no generators in higher dimensions.

A higher-dimensional criterion restricted to positive bases and suitably restricted fibres is not decided by this obstruction. For the positive \(2\)-dimensional bases and free categorical fibres in your question, (33) supplies the requested finite presentation theorem.

---

## Verification of the researcher response (2026-11-18)

**Verdict: correct.** FT₃ holds for positive 2-computad bases (both boundary paths of every 2-generator nonempty), and no finite presentation scheme of this form exists for all finite 2-computad bases. Checked step by step, with the sources read at statement level:

- **V1. Q1, base comparison (20).** Chanavat, arXiv 2603.22242v2, Corollary 3.39 reads "Let C be a positive 2-polygraph. Then C is a homotopy polygraph", and Definition 3.10 is the preservation of cellular-extension squares as homotopy pushouts. So Free(Γ) ≃ F₂(Γ) for positive Γ. **Confirmed.** (The same paper, Cor. 3.38, gives all *regular 3-polygraphs* as homotopy polygraphs; used in the follow-up prompt.)
- **V2. Q2, the walking 2-cell.** The tree argument holds: every vertex other than the root has out-degree 1 (the last edge of its path), and the root is terminal, so the transport graph contracts. The cylinder (25) has the stated boundaries. Localising gives (27), which is Hom in the 2-categorical Grothendieck construction (Hörmann, Def. 2.14: a 2-cell (u,r) ⇒ (v,s) exists iff r = a_α ; s). Left cancellation in the free D makes each hom an interval or a point. The hom-wise localisation step is justified by the collage/bimodule argument given. **Confirmed.**
- **V3. Q3, general positive base.** Pullback of the cellular pushout along a left cartesian fibration: Loubaton, arXiv 2406.05425, Thm 3.2.3.15 (pullback along a cartesian fibration preserves colimits) is as cited. Prop. 3.1.2.34 concerns a colimit-preserving functor; its use here (♯ preserves colimits) is correct. **Confirmed.**
- **V4. Q4, counts.** The generator counts in the table were recomputed for the walking 2-cell and the two-2-cell examples. **Confirmed.**
- **V5. §5, non-positive bases.** For Γ = {x; σ : 1_x ⇒ 1_x}, the strict free object is B²ℕ and L(B²ℕ) ≃ K(ℤ,2) (Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9 and Ex. 4.10, read), while the weak cellular construction groupoidifies to * ⊔_{S¹} * = S². The finite-CW lemma is correct: L preserves the cellular pushouts, L(∂D_k) ≃ S^{k−1}, and localisation does not change L. Hence (36): B²ℕ is not Free(Ψ)[S⁻¹] for any finite Ψ. **Confirmed.**

**Consequences.**
- **B14 closed for positive 2-computad bases** with free finitely generated categorical fibres; FT₃ with the positivity hypothesis is the rule. Bases with a 2-generator with an empty boundary path admit no finite presentation of this form at all, so the rule must keep the hypothesis (not a gap that more generators could fill).
- **Evidence for C1/D2 (NGC):** loopy contexts such as (x, σ : 1_x ⇒ 1_x) have weak free object with groupoidification S², not K(ℤ,2); π₃(S²) = ℤ, so the weak free object on such a context has nontrivial higher structure that the strict one lacks. This strongly suggests that relative coherence RC(3) fails for contexts with identity-boundary generators, consistent with the Eckmann–Hilton obstruction.
- Open: FT_n for n ≥ 3 over positive/regular bases. Follow-up prompt: `answered/finite-fibration-test-higher-base-2026-11-18.md`, unsent.
