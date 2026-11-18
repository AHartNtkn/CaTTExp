# Problem: a finite test for when a map of computads presents a cartesian fibration

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product and computads (polygraphs), and nothing else. The questions are in §4, smallest first.*

## 1. Setting

### 1.1 Marked (∞,ω)-categories and left cartesian fibrations

Work in Loubaton's model (F. Loubaton, *Categorical theory of (∞,ω)-categories*, [arXiv 2406.05425](https://arxiv.org/abs/2406.05425)).

- A **marked** (∞,ω)-category is one with a chosen class of positive-dimensional cells. The class contains the equivalences and is closed under composition.
  - A^♯ marks every cell, and A^♭ marks only the equivalences.
  - D_n is the n-globe, and D_n^t is the n-globe with its top cell marked.
  - ⊗ is the marked Gray tensor product.
- **Left cartesian fibrations** (Loubaton Def. 3.2.2.1). A map p : E → B is a left cartesian fibration if it has the *unique* right lifting property against

  ```
  K ⊗ {0} → K ⊗ [1]^♯,        K ∈ { D_n^♭ : n ≥ 0 } ∪ { D_n^t : n ≥ 1 }.        (★)
  ```

  Equivalently (Thm 3.2.2.24(5)), three conditions hold:
  1. Every 1-cell of B has a marked lift with prescribed source, unique up to a contractible space.
  2. For every marked u : x → x′ and every z, `E(x′, z) ≃ E(x, z) ×_{B(px, pz)} B(px′, pz)`.
  3. Every hom map `E(x, y) → B(px, py)` is a *right* cartesian fibration (the dual notion, lifting from endpoint 1).

  Condition 3 makes the variance **alternate with dimension**: cocartesian 1-cells, cartesian 2-cells, cocartesian 3-cells, and so on.
- **Straightening** (Loubaton Thm 4.1.4.2). Left cartesian fibrations over B^♯ correspond to functors B → ω, where ω is the (∞,ω)-category of (∞,ω)-categories.

### 1.2 Computads with markings

- A **finite computad** Ψ is a finite list of generating cells. Each generator has a boundary built from earlier generators. `Free(Ψ)` is the free weak ω-category on Ψ.
- A **map** `π : Ψ → Γ` sends each generator of Ψ to a cell of `Free(Γ)`. That cell may be an identity.
- A **marking** μ is a subset of the positive-dimensional generators of Ψ. It generates a marking of `Free(Ψ)` by closure under identities, composites and equivalences. No condition on μ is needed for this closure to make sense.

### 1.3 Why such maps matter

Let W : I → ω be a weight and F : I → 𝒞 a diagram. The W-weighted limit of F is the **marked lax limit** of F∘p over the total space ∫W, where p : ∫W → I is the left cartesian fibration classifying W, with its fibration marking. This holds in Loubaton's model, in all dimensions (via Cor. 4.2.2.6, Cor. 4.2.3.18 and Thm 4.1.4.2). In a marked lax limit, marking a k-cell of the index makes the corresponding (k+1)-dimensional cone cell invertible (Remark 4.2.3.7).

So if a weight is presented by a finite computad map `(π : Ψ → Γ, μ)`, the weighted limit becomes a marked lax limit over Ψ. A proof checker can then accept weighted limits, provided it can check that π presents a left cartesian fibration. (★) is exact, but it is an infinite schema.

## 2. What is known

1. **(★) is exact but infinite.** It quantifies over all globes and all lifting problems in `Free(Ψ)`.
2. **Existence of marked lifts of generators is not enough.** Let I = (0 → 1), and let E be the free category on arrows u : x → y and v : x → z, both sent to the generator. A lift exists at x, but u is not cocartesian, since factoring v through u needs an arrow y → z.
3. **Solved: set-valued weights over graphs.** Let Γ and Ψ be graphs, π send vertices to vertices and edges to edges, and every edge of Ψ be marked. Then (★) holds **iff π is a discrete opfibration of graphs**: for every vertex e of Ψ and every edge u of Γ out of π(e), there is exactly one edge of Ψ over u out of e.
   - *Proof.* Unique edge lifting gives unique path lifting. The free weak ω-category on a graph is equivalent to the free 1-category on it, because the comparison map is a trivial fibration (via Leinster, Dean–Finster–Markakis–Reutter–Vicary, and Benjamin–Markakis). So homs are discrete and condition 3 is trivial. Condition 2 is unique factorisation. For the converse, a lift of a length-1 path must be a single edge.
   - *Completeness.* Every functor Free(Γ) → FinSet has a presentation of this form, since its category of elements is free on the covering graph.
4. **Where it gets hard.** Let `W : Free(Γ) → Cat`, with Γ a graph.
   - The total space ∫W is a 1-category in which squares `β ; u_{e′} = u_e ; W(u)(β)` commute. Here β : e → e′ is a vertical arrow in a fibre, and u_e is the marked lift of u at e.
   - So ∫W is **not free**. A computad presentation needs 2-generators `θ_{u,β}` filling these squares, and they must be marked: they are the "cartesian 2-cells" of the alternating pattern.
   - Since `π(θ_{u,β})` is an identity, marking θ makes its cone cell invertible. The marked lax limit should therefore not see the difference between θ and an invertible cell. That is not proved.

## 3. The candidate

**FT₂.** Let Γ be a graph and Ψ a computad of dimension ≤ 2, with a map π : Ψ → Γ and a marking μ. Say (π, μ) satisfies FT₂ if:
1. π sends each 1-generator to an edge or an identity (call these *horizontal* and *vertical*), and each 2-generator to an identity.
2. For each vertex e of Ψ and each edge u of Γ out of π(e), there is exactly one marked horizontal generator `u_e` over u out of e.
3. For each vertical generator β : e → e′ and each such u, there is exactly one marked 2-generator `θ_{u,β} : β ; u_{e′} ⇒ u_e ; t_{u,β}`, where t_{u,β} is a vertical path (the *transport*).
4. There are no other generators.

**Localisation lemma (Loc).** Let J be a marked (∞,ω)-category and θ a marked k-cell, k ≥ 2, sent to an equivalence by every diagram under consideration. Then marked lax limits over J and over J[θ⁻¹] agree. In J[θ⁻¹], the inverse of θ and its witnesses are marked.

*Sketch.* A marked cone over J has an invertible cone cell over θ. It extends to J[θ⁻¹] by inverting that cell, and the space of extensions should be contractible.

## 4. Questions

1. **(Loc)** Prove or refute the localisation lemma. Start with k = 2 and J a 2-category.
2. **FT₂.** Show that FT₂ implies that `Free(Ψ)^μ[θ⁻¹] → Free(Γ)^♯` is a left cartesian fibration, where θ ranges over the marked 2-generators. With (Loc), this means FT₂ correctly presents Cat-valued weights. Is every weight `Free(Γ) → Cat` with values free on finite graphs presented by some FT₂ datum?
3. **Higher bases.** Extend the criterion to a base Γ with 2-generators. A 2-generator α : u ⇒ u′ of Γ needs lifted 2-cells between the lifts u_e and u′_e, with the variance of condition 3 in §1.1 (cartesian on hom maps).
4. **All dimensions.** Is there a finite criterion FT_n for weights valued in free n-categories, alternating the variance in each dimension? If not, give an obstruction. For example, transports might fail to be finitely presentable.
5. **Strict analogue.** For strict ω-categories and polygraphs, with Grothendieck fibrations of strict ω-categories, is there a known finite criterion? A reference would answer questions 2–4 in the strict setting.

## 5. Literature search (2026-11-18)

- **Loubaton** (arXiv 2406.05425): the exact criterion (Def. 3.2.1.1, Def. 3.2.2.1, Thm 3.2.2.24), stated for arbitrary marked (∞,ω)-categories. It gives no computad-level test.
- **Abellán–Haugseng–Martini** (arXiv 2602.07604) and **Gagna–Harpaz–Lanari** (arXiv 2012.04537): (∞,2)-dimensional fibrations and partially lax limits. Generator-level criteria are not discussed.
- That discrete opfibrations over a free category are free on a covering graph is folklore for 1-categories.
- **Nothing found** on finite criteria for cocartesian fibrations between free higher categories presented by polygraphs.

## 6. What would count as an answer

Any one of:
- a proof of (Loc);
- a proof of FT₂ ⟹ (★), possibly after localisation;
- a different finite criterion, with a proof that it implies (★);
- a proof that no finite criterion is complete for Cat-valued weights.

# Researcher Response

**(Loc) is true in every positive dimension. FT₂ also gives the desired finite test after making one marking restriction explicit: vertical generators must be unmarked.** With that restriction, the localised presentation is equivalent, over the base and with its marking, to the Grothendieck construction of the transport functors.

The proof uses colimits in Loubaton’s model and therefore establishes the full \((\infty,\omega)\)-categorical statement. It does not stop at a calculation in a strict \((2,1)\)-category.

Throughout, localisation means **coherent localisation**, and \(\operatorname{Free}(\Psi)\) has its cellular universal property: its generators are freely adjoined with the specified boundaries.

## 1. Proof of (Loc)

Here is a slightly stronger statement.

### Theorem

Let \(J\) be a small marked \((\infty,\omega)\)-category, let \(S\) be a set of marked positive-dimensional cells, and give
\[
q:J\longrightarrow Q:=J[S^{-1}]
\]
the induced marking.

For every diagram \(\bar F:Q\to\mathcal C^\sharp\), restriction induces an equivalence
\[
\operatorname{Cone}^{m}_{Q}(c,\bar F)
\;\simeq\;
\operatorname{Cone}^{m}_{J}(c,\bar Fq)
\tag{1}
\]
of entire \((\infty,\omega)\)-categories, naturally in the apex \(c\).

Consequently, the two marked lax limits exist under exactly the same conditions and agree. A diagram \(F:J\to\mathcal C^\sharp\) extends along \(q\) precisely when it sends \(S\) to equivalences.

### 1.1 Localisation is a marked trivialisation

First take \(S=\{\theta\}\), where \(\theta\) has dimension \(k\geq1\). Form the pushout
\[
\begin{array}{ccc}
D_k^{t}&\xrightarrow{\theta}&J\\
\downarrow I_{k-1}&&\downarrow q\\
D_{k-1}^{\flat}&\longrightarrow&Q ,
\end{array}
\tag{2}
\]
in marked \((\infty,\omega)\)-categories. Here \(I_{k-1}\) sends the top \(k\)-cell to an identity.

To identify this pushout, let \(X\) be any marked \((\infty,\omega)\)-category. Write \(X_r=\operatorname{Map}(D_r,X)\), and let \(tX_k\subseteq X_k\) be its space of marked \(k\)-cells. Then
\[
\operatorname{Map}_m(Q,X)
\simeq
\operatorname{Map}_m(J,X)
\times_{tX_k}X_{k-1}.
\tag{3}
\]
The map \(X_{k-1}\to tX_k\) inserts identities. Completeness identifies it with the inclusion of the space of equivalence \(k\)-cells. Thus (3) identifies with
\[
\bigl\{G:J\to X\text{ marked}\mid G(\theta)\text{ is an equivalence}\bigr\}.
\tag{4}
\]
This proves that \(Q\) is the required coherent marked localisation. In particular, its inverse cells and equivalence witnesses are marked.

Loubaton defines **marked trivialisations** as the colimit-closed class generated by
\[
I_n:D_{n+1}^{t}\longrightarrow D_n^\flat,
\]
and proves that every marked trivialisation is both initial and final. Therefore \(q\) is both initial and final. These are Definition 3.2.1.6 and Proposition 3.2.1.7. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For a set \(S\), apply the same construction using a coproduct of the maps \(I_{k-1}\).

The pushout in (2) is a homotopy pushout. An ordinary strict quotient setting \(\theta\) equal to an identity is not a substitute for its universal property.

### 1.2 Initiality identifies the full categories of cones

Use Loubaton’s cone category
\[
\operatorname{Cone}^{m}_{J}(c,F)
:=
\operatorname{hom}_{\operatorname{Hom}_{\ominus}(J,\mathcal C)}
(\operatorname{cst}c,F).
\]
For fixed \(c\), define
\[
H_c:Q\longrightarrow\omega,
\qquad
z\longmapsto\operatorname{hom}_{\mathcal C}(c,\bar Fz).
\]

Lemma 4.2.3.15 identifies cones with a category-valued marked lax limit. Lemma 4.2.3.23 gives invariance of that limit under an initial map. Applying them gives
\[
\begin{aligned}
\operatorname{Cone}^{m}_{Q}(c,\bar F)
&\simeq \operatorname{laxlim}_{Q}H_c\\
&\simeq \operatorname{laxlim}_{J}(H_cq)\\
&\simeq \operatorname{Cone}^{m}_{J}(c,\bar Fq).
\end{aligned}
\tag{5}
\]
These are equivalences of \((\infty,\omega)\)-categories, natural in \(c\). Thus they account for all higher cone morphisms. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The cone functors are therefore equivalent, so their representability—and hence existence of the marked lax limits—is equivalent. This proves (Loc), including the requested \(k=2\) case.

## 2. The marking correction to FT₂

As written, FT₂ does not explicitly prohibit marking a vertical generator. That permits a counterexample.

Take \(\Gamma\) to have one vertex and no edges. Take \(\Psi\) to have
\[
a\xrightarrow{\beta}b,
\]
with \(\beta\) vertical and marked. There are no horizontal generators or \(2\)-generators, so the transport requirements are vacuous. The proposed map is
\[
[1]^\sharp\longrightarrow *.
\]

It fails your condition 2: for the marked arrow \(\beta:a\to b\), take \(z=a\). The required equivalence would be
\[
\operatorname{Hom}(b,a)
\;\simeq\;
\operatorname{Hom}(a,a),
\]
that is, \(\varnothing\simeq *\).

Accordingly, use the following explicit marking clause:
\[
\boxed{\mu=H\cup\Theta,}
\tag{6}
\]
where \(H\) is the set of specified horizontal generators and \(\Theta\) is the set of specified comparison \(2\)-generators. This specifies marked **generators**; the resulting marking still has the closure required in your setting.

If that was already your intended reading, the following theorem proves your intended FT₂.

## 3. Corrected FT₂ implies the full lifting criterion

### Theorem

Suppose the generators are exactly those specified by FT₂, and their marking is (6). Then
\[
\operatorname{Free}(\Psi)^\mu[\Theta^{-1}]
\longrightarrow
\operatorname{Free}(\Gamma)^\sharp
\tag{7}
\]
is a left cartesian fibration.

More precisely, the FT₂ data determine a functor
\[
T:\operatorname{Free}(\Gamma)\longrightarrow\mathbf{Cat},
\]
with free-category fibres, and (7) is equivalent to its marked Grothendieck construction.

### 3.1 Extract the transport functors

For each base vertex \(b\), let \(G_b\) be the graph whose vertices are the vertices of \(\Psi\) over \(b\), and whose edges are the vertical generators over \(1_b\). Put
\[
C_b=\operatorname{Free}(G_b).
\]

For a base edge \(u:b\to c\), write
\[
u_e:e\longrightarrow T_u(e)
\]
for the specified horizontal generator. Define
\[
T_u(\beta)=t_{u,\beta}
\]
on each vertical generator \(\beta:e\to e'\).

The typing of
\[
\theta_{u,\beta}:
\beta;u_{e'}\Longrightarrow u_e;t_{u,\beta}
\]
ensures that \(t_{u,\beta}\) runs from \(T_u(e)\) to \(T_u(e')\). Freeness extends these assignments uniquely to a functor
\[
T_u:C_b\longrightarrow C_c.
\]
Freeness of the base then extends the edge functors uniquely to \(T\).

No equations among the transport paths are needed: both the fibre categories and the base category are free on graphs.

### 3.2 The intended total category

The ordinary Grothendieck construction \(E_T\) has vertices \((b,e)\) and arrows
\[
(w,a):(b,e)\longrightarrow(c,f),
\qquad
w:b\to c,\quad a:T_w(e)\to f.
\]
Composition is
\[
(w,a);(v,b)
=
\bigl(w;v,\ T_v(a);b\bigr).
\tag{8}
\]
Mark the arrows \((w,1)\).

Its projection is a left cartesian fibration. This can be checked directly against the three conditions in your statement:

- The marked lift of \(w\) at \((b,e)\) is \((w,1)\).
- Factoring an arrow over \(w;v\) through \((w,1)\) amounts to the identity
  \[
  T_{w;v}(e)=T_v(T_w(e)).
  \]
  This gives the required bijection on hom-sets.
- Its hom-categories and those of the base are discrete, so the recursive hom-fibration condition is automatic.

The remaining task is to prove that the localised computad presents this \(E_T\), including all higher coherence.

### 3.3 Decompose the total category over the generating base edges

Let
\[
B=\operatorname{Free}(\Gamma).
\]
The marked category \(B^\sharp\) is the colimit of its vertex–edge incidence diagram: a point for each vertex and a marked interval \([1]^\sharp\) for each generating edge, attached at the specified endpoints.

This follows directly from freeness. A map from that colimit specifies vertex images and marked generating-arrow images; composition extends these data, and every base path is marked.

Pullback along the actual left cartesian fibration
\[
p_T:E_T\longrightarrow B^\sharp
\]
preserves colimits, by Loubaton’s Theorem 3.2.3.15. Consequently \(E_T\) is the colimit of its vertex fibres and generating-edge pullbacks. This is also the content of Corollary 3.2.3.16. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For \(u:b\to c\), that edge pullback is the mapping cylinder
\[
M_u
\simeq
\bigl(C_b^\flat\times[1]^\sharp\bigr)
\amalg_{C_b^\flat\times\{1\}}
C_c^\flat,
\tag{9}
\]
where the gluing map at endpoint \(1\) is \(T_u\). The equivalence respects both endpoint fibres and the projection to \([1]^\sharp\). This is Example 4.1.2.6, or Corollary 4.1.2.19 with \(C=*\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 3.4 Compute the cellular presentation of each mapping cylinder

Because \(C_b\) is free on \(G_b\), its minimally marked version is the colimit of the minimally marked vertices and edges of \(G_b\). Marked cartesian product preserves colimits separately, so
\[
C_b^\flat\times[1]^\sharp
\]
is obtained from:

- one marked horizontal interval \(e\times[1]\) for each fibre vertex \(e\);
- one square
  \[
  D_1^\flat\times[1]^\sharp
  \]
  for each vertical generator.

The product-preservation result is Proposition 3.1.1.19. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The relevant square has an exact presentation. Let
\[
P_0=D_1^\flat\vee[1]^\sharp,
\qquad
P_1=[1]^\sharp\vee D_1^\flat
\]
be its two length-two boundary paths. Then
\[
D_1^\flat\times[1]^\sharp
\simeq
P_0\amalg_{D_1^\flat}P_1,
\tag{10}
\]
where each map from the common \(D_1^\flat\) selects the composite path. This is Proposition 3.1.1.38 at \(n=1,\ a=b=*\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Equation (10) is precisely the presentation by a freely adjoined **invertible \(2\)-cell** between the two boundary paths. To see this using §1, first attach a marked \(D_2\) between the paths, then localise its top cell by replacing \(D_2^t\) with \(D_1^\flat\). Pushout-pasting gives (10).

Now perform the gluing in (9). It substitutes
\[
e\longmapsto T_u(e),
\qquad
\beta\longmapsto T_u(\beta)=t_{u,\beta}
\]
at endpoint \(1\). Thus the square indexed by \(\beta:e\to e'\) becomes exactly
\[
\beta;u_{e'}
\;\simeq\;
u_e;t_{u,\beta}.
\tag{11}
\]

Finally, glue the mapping cylinders along the vertex fibres, as in §3.3. The resulting cellular colimit has exactly:

1. the fibre vertices;
2. the vertical generators;
3. the horizontal generators \(u_e\);
4. the invertible comparison cells \(\theta_{u,\beta}\).

Its marking is generated by the specified horizontals and comparisons. Hence
\[
\boxed{
\operatorname{Free}(\Psi)^{H\cup\Theta}[\Theta^{-1}]
\simeq
E_T
\quad\text{over }B^\sharp .
}
\tag{12}
\]

All the colimits used here are colimits of marked \((\infty,\omega)\)-categories over the base. Therefore (12) identifies the projection and its marking in the required model. The higher coherence is supplied by these universal properties. This proves (7), hence \((\star)\).

## 4. Completeness for free-category-valued weights over a finite graph

**Yes: every weight in the stated class has such a finite presentation.**

Let
\[
W:B\longrightarrow\mathbf{Cat},
\qquad B=\operatorname{Free}(\Gamma),
\]
with each \(W(b)\) free on a finite graph \(G_b\). Choose those graphs and use the following generators:
\[
\begin{array}{c|l}
\text{Dimension}&\text{Generators}\\ \hline
0 & e\in(G_b)_0,\ \text{for each }b\\
1 & \beta\in(G_b)_1,\ \text{as vertical generators}\\
1 & u_e:e\to W(u)(e),\ \text{for each base edge }u:b\to c\\
2 & \theta_{u,\beta}:
       \beta;u_{e'}\Rightarrow u_e;W(u)(\beta).
\end{array}
\tag{13}
\]
Here \(W(u)(\beta)\) is its finite path expression in \(G_c\), possibly the empty path. Mark exactly the horizontal and comparison generators.

The generator counts are
\[
\begin{aligned}
|\Psi_0|
&=\sum_b |(G_b)_0|,\\
|\Psi_1|
&=\sum_b |(G_b)_1|
  +\sum_{u\in\Gamma_1}|(G_{s(u)})_0|,\\
|\Psi_2|
&=\sum_{u\in\Gamma_1}|(G_{s(u)})_1|.
\end{aligned}
\tag{14}
\]
They are finite, and §3 identifies the localised presentation with \(\int W\).

This is completeness in your presentation sense: every such weight has an accepted finite presentation. It does not assert that the same syntactic test recognises every alternative computad presentation of that weight.

### Consequence for the proof checker

Write \(J=\operatorname{Free}(\Psi)^\mu\), and let \(F:B\to\mathcal C\). Every \(\theta\in\Theta\) projects to an identity, so \(F\pi\) sends it to an equivalence. Combining (Loc), (12), and your weighted-limit comparison gives
\[
\boxed{
\operatorname{laxlim}^{m}_{J}(F\pi)
\simeq
\operatorname{laxlim}^{m}_{\int W}(Fp_W)
\simeq
\operatorname{lim}^{W}_{B}F .
}
\tag{15}
\]
Thus the checker may use the finite unlocalised marked computad as its indexing syntax.

## 5. What a base \(2\)-generator requires

For a strict \(2\)-dimensional base and ordinary-category fibres, the additional finite data can be stated explicitly.

Suppose
\[
\alpha:u\Rightarrow v,
\qquad u,v:b\to c.
\]
Its action is a natural transformation
\[
a_\alpha:T_u\Rightarrow T_v.
\]
For each fibre vertex \(e\), specify a vertical path
\[
a_{\alpha,e}:T_u(e)\longrightarrow T_v(e).
\]
For each generating vertical arrow \(\beta:e\to e'\), require the path equality
\[
\boxed{
T_u(\beta);a_{\alpha,e'}
=
a_{\alpha,e};T_v(\beta).
}
\tag{16}
\]
These are finitely many equalities of finite paths. They imply naturality on every fibre path by induction on path length.

### 5.1 The correctly typed cartesian lift

Let \(\tau_{u,e}\) denote the composite chosen horizontal lift of the base path \(u\). The required lift is
\[
\boxed{
\lambda_{\alpha,e}:
\tau_{u,e};a_{\alpha,e}
\Longrightarrow
\tau_{v,e}.
}
\tag{17}
\]
It has prescribed **target**, as required by cartesianness on hom maps. A cell directly from \(\tau_{u,e}\) to \(\tau_{v,e}\) is not generally well typed: their target vertices can differ.

The strict Grothendieck formula makes this explicit. A \(2\)-cell over \(\alpha\),
\[
(u,r)\Longrightarrow(v,s),
\]
exists exactly when
\[
r=a_{\alpha,e};s.
\tag{18}
\]
Hörmann’s Definition 2.14 gives this construction as a \(1\)-opfibration and \(2\)-fibration; Proposition 2.16 gives the converse correspondence. [home.mathematik.uni-freiburg.de](https://home.mathematik.uni-freiburg.de/hoermann/2der.pdf?utm_source=chatgpt.com)

The \(\lambda_{\alpha,e}\) are marked cartesian \(2\)-cells. Their images are \(\alpha\), so they remain potentially noninvertible.

### 5.2 The new relation is \(3\)-dimensional

Write
\[
\theta_{u,\beta}:
\beta;\tau_{u,e'}
\Longrightarrow
\tau_{u,e};T_u(\beta)
\]
for the comparison obtained along the path \(u\). Then naturality of the lifted \(2\)-cell requires
\[
\boxed{
(\theta_{u,\beta}\star a_{\alpha,e'});
(\lambda_{\alpha,e}\star T_v(\beta))
=
(\beta\star\lambda_{\alpha,e'});
\theta_{v,\beta}.
}
\tag{19}
\]
Here \(\star\) denotes the indicated whiskering, and (16) identifies the intermediate paths on the left. Both sides run from
\[
\beta;\tau_{u,e'};a_{\alpha,e'}
\quad\text{to}\quad
\tau_{v,e};T_v(\beta).
\]

Thus a presentation must address equality or equivalence between these \(2\)-cell pastings. Adding only the \(\lambda\)’s is insufficient.

For a concrete failure, take
\[
u,v:0\to1,\qquad \alpha:u\Rightarrow v,
\]
with fibres
\[
x\xrightarrow{h}y,
\qquad
z\xrightarrow{k}w.
\]
Let \(T_u=T_v\), with both sending \(h\) to \(k\), and let \(a_\alpha\) be the identity transformation. Adjoin and invert
\[
\theta_u:h;U_y\Rightarrow U_x;k,
\qquad
\theta_v:h;V_y\Rightarrow V_x;k,
\]
and adjoin
\[
\lambda_x:U_x\Rightarrow V_x,
\qquad
\lambda_y:U_y\Rightarrow V_y.
\]

Without (19), the two pastings
\[
\theta_u;(\lambda_x\star k),
\qquad
(h\star\lambda_y);\theta_v
\tag{20}
\]
remain distinct. The first uses \(\lambda_x\) once and \(\lambda_y\) zero times; the second has the reverse counts. Inverting the \(\theta\)’s and applying interchange preserves these counts.

Both pastings project to \(\alpha\). A vertical factorisation relating them cannot change the counts, because a \(2\)-cell over an identity uses neither \(\lambda_x\) nor \(\lambda_y\). Hence the proposed lift fails cartesianness on the hom category.

Equations (16) give a finite certificate for the strict diagram \(B\to\mathbf{Cat}\). Its Grothendieck construction is then available from (18). Establishing a corresponding weak computad theorem by adjoining \(3\)-generators for (19) requires a further presentation comparison; that extension is not proved here.

## 6. All dimensions and the strict literature

I do not obtain a general \(\mathrm{FT}_n\), or an obstruction proving that none can exist. The graph-base theorem establishes a complete finite presentation scheme for the specified free-category-valued class.

For strict functors between finitely generated free higher categories, the generator images themselves are finite terms. The unresolved issue is a finite presentation and verification of the total category’s lifting coherence, rather than the finite description of an individual strict transport functor.

The following references address the strict constructions and the variance:

| Reference | Relevant result |
|---|---|
| Fritz Hörmann, *Six Functor Formalisms and Fibered Multiderivators*, Definition 2.14 and Proposition 2.16 | The \(\mathbf{Cat}\)-valued Grothendieck construction with cocartesian \(1\)-cells and cartesian \(2\)-cells, including formula (18). |
| Nick Gurski, Niles Johnson, Angélica M. Osorno, *2-categorical opfibrations, Quillen’s Theorem B, and \(S^{-1}S\)*, Definition 2.14 | The mixed-variance fibration axioms: opcartesian \(1\)-lifts, local cartesian \(2\)-lifts, and stability under horizontal composition. |
| Michael A. Warren, *The Strict \(\omega\)-Groupoid Interpretation of Type Theory*, §3 and Appendix B | A strict \(\omega\)-categorical Grothendieck construction, its explicit higher-dimensional formulas, and its universal property. |

The second and third references are available in the [Gurski–Johnson–Osorno paper](https://nyjm.albany.edu/j/2021/27-40v.pdf) and [Warren’s paper](https://mawarren.net/papers/crmp1295.pdf). [nyjm.albany.edu](https://nyjm.albany.edu/j/2021/27-40v.pdf?utm_source=chatgpt.com)

These supply constructions and structural criteria. I did not find in them a finite recognition theorem for arbitrary polygraph presentations of strict \(\omega\)-categorical fibrations.

## Verification of the researcher response (2026-11-18)

I checked every step against Loubaton, *Categorical theory of (∞,ω)-categories* (arXiv 2406.05425v2), and Hörmann, *Six functor formalisms and fibered multiderivators* (Def. 2.14, Prop. 2.16). I also found Gurski–Johnson–Osorno Def. 2.14 (2-opfibrations). Warren's paper was not checked.

**Verdict: correct.** (Loc) is proved in every positive dimension. FT₂ is proved after one marking correction, and it is complete for weights valued in finitely generated free categories over a graph. Questions 3–5 are only partly answered, but a well-typed form of question 3 and its first obstruction are given.

### V1. (Loc) (§1): correct

- *The pushout (2) is the localisation.* `Map(D_k^t, X)` is the space `tX_k` of marked k-cells, and `Map(D_{k−1}^♭, X) = X_{k−1}`. Inserting identities `X_{k−1} → tX_k` is, by completeness, the inclusion of the equivalence k-cells, and those are components of `X_k` contained in `tX_k` because markings contain equivalences. So `Map(Q, X)` is the space of marked G with G(θ) an equivalence, as in (3)–(4). It holds for every k ≥ 1, not only k ≥ 2.
- *q is initial and final.* Loubaton Def. 3.2.1.6: marked trivialisations form the smallest cocomplete class containing `I_n : D_{n+1}^t → D_n^♭`. Prop. 3.2.1.7: they are initial and final. q is a pushout of `I_{k−1}`, or for a set S, of a coproduct of them. Confirmed.
- *Cones.* Lemma 4.2.3.15: `hom_{Hom_⊖(I,A)}(cst a, F) ≃ laxlim_I hom_A(a, F(−))`, natural in F and a. Lemma 4.2.3.23: for initial i, `laxlim f → laxlim f∘i` is an equivalence. Composing them gives (1) as an equivalence of whole (∞,ω)-categories of cones, natural in the apex. So the two marked lax limits exist together and agree, and F extends along q iff it inverts S. Confirmed.

### V2. The marking correction (§2): correct

With Γ a point and Ψ = (a →β b), where β is vertical and marked, all FT₂ clauses hold vacuously. But condition 2 of §1.1 fails for u = β and z = a: `E(b, a) = ∅` while `E(a, a) ×_B B = ∗`. Lifts of the marked base identity at a are also not unique, since 1_a and β are both marked. So FT₂ needs **μ = horizontals ∪ comparison 2-generators**, with vertical generators unmarked. This was the intended reading, but the prompt did not say it.

### V3. Corrected FT₂ ⇒ left cartesian fibration (§3): correct

- *Transport.* The type of `θ_{u,β} : β;u_{e′} ⇒ u_e;t_{u,β}` forces `t_{u,β} : T_u(e) → T_u(e′)`. Freeness of `C_b = Free(G_b)` and of the base gives `T : Free(Γ) → Cat`. No equations are needed. (In the (∞,ω) sense this uses that the free (∞,ω)-category on a graph is the free category, item 3 of §2.)
- *E_T.* The composition formula (8) is the split Grothendieck construction, marked on `(w, 1)`. The three conditions of §1.1 are as stated; homs are discrete.
- *Decomposition.* B^♯ is the colimit of points and `[1]^♯`, since every path is marked. Thm 3.2.3.15 (pullback along a *classified* left cartesian fibration preserves colimits) and Cor. 3.2.3.16 (`colim i*p → p` is an equivalence over a colimit base) give `E_T` as the colimit of fibres and edge pullbacks. The response's appeal to 3.2.3.15 needs E_T to be classified, and it is: it is the straightening of T.
- *Mapping cylinders.* Example 4.1.2.6 presents a left cartesian fibration over [1] as the colimit `X(0)^♭ × [1]^♯ ⊔ X(1)^♭`, glued by the transport. Cor. 4.1.2.19 (`LCart([C,1]^♯)` ≃ arrows `X₀ × C → X₁`) gives the same with C = ∗. Confirmed.
- *Cells.* Prop. 3.1.1.19: the marked cartesian product preserves colimits in each variable, so `C_b^♭ × [1]^♯` is built from `e × [1]^♯` and the squares `D₁^♭ × [1]^♯`. Prop. 3.1.1.38 is the general (equaliser/coequaliser) presentation of `[a × b^♯, 1]`. Its case n = 1, a = b = ∗ gives (10): two length-2 paths glued along their composite, i.e. a free *invertible* 2-cell. The cartesian square is not the Gray square, and that is why θ must be inverted. Under gluing by T_u the squares become (11).
- *Marking.* In `D₁^♭ × [1]^♯` the 2-cell projects to identities in both factors, so it is marked. With the horizontals, this gives the marking H ∪ Θ.
- *Assumption, flagged by the response:* `Free(Ψ)` is the (∞,ω) cellular colimit. Identifying it with the free CaTT (Grothendieck–Maltsiniotis) weak ω-category is the standing semantic gap (`semantics-gaps.md`), not a defect of this proof.

### V4. Completeness (§4) and the checker consequence (15): correct

- Functors between free categories send generators to paths, possibly empty, so (13) is an FT₂ datum with T = W. The counts (14) are right: one horizontal per (base edge, source-fibre vertex), and one θ per (base edge, source-fibre edge).
- (15) follows from (Loc) with S = Θ (Fπ sends each θ to an identity), (12), and §1.3. **So a checker may use the finite, unlocalised marked computad (Ψ, H ∪ Θ) as the index of the weighted limit.**
- Scope, as the response notes: this is completeness of a presentation scheme, not recognition of arbitrary presentations of the same weight.

### V5. Base 2-generators (§5): correct, and it corrects question 3

- *Typing.* Hörmann Def. 2.14 has 2-cells `ν : (α, f) ⇒ (β, g)` exactly when `β ∘ Ξ(ν) = α`, with 1-opfibred and 2-fibred projection. In diagrammatic order that is (18): `r = a_{α,e}; s`. The cartesian lift with target `τ_{v,e}` is `λ_{α,e} : τ_{u,e}; a_{α,e} ⇒ τ_{v,e}`. Question 3's "2-cells between the lifts u_e and u′_e" is not well typed in general: their targets `T_u(e)` and `T_v(e)` differ.
- *(16)* is the naturality of a_α on generators, and it extends to paths by pasting.
- *(19).* I typed both sides: each runs `β;τ_{u,e′};a_{α,e′} ⇒ τ_{v,e};T_v(β)`, and (16) identifies the middle on the left.
- *The obstruction (20).* Counting λ_x and λ_y gives a 2-functor to ℤ² (θ's count 0, so inverting them is harmless). The two pastings have counts (1,0) and (0,1). A cell over an identity has count (0,0), since the λ-count is the α-count of the projection. So `(h⋆λ_y);θ_v` does not factor through `λ_x ⋆ k`, and that lift is not cartesian. **A 2-dimensional base needs 3-generators (or 3-dimensional relations) for (19).** The weak presentation theorem with these 3-generators is left open.

### V6. Questions 4–5 (§6)

No FT_n and no obstruction. The strict references are constructions, not recognition theorems. Nothing to check beyond the Hörmann and GJO citations (confirmed).

### V7. Consequences for the project

1. **B14 is closed for Cat-valued weights with free finitely generated values over a graph.** The test is FT₂ with vertical generators unmarked, it is complete for that class, and the checker may use the unlocalised computad (15).
2. **(Loc) holds in all positive dimensions** (Loubaton 3.2.1.7, 4.2.3.15, 4.2.3.23). It applies wherever a marked index cell is sent to an equivalence. That includes `limits-metatheory.md`'s horn rules, and the "cartesian 2-cells" of the alternating pattern (§2 item 4).
3. **Next case (FT₃ for 2-dimensional bases):** the data are (16) per base 2-generator, the lifts λ (17), and a 3-generator for each instance of (19). That this localised 3-computad presents the Grothendieck construction is the open step. It is the natural next prompt, owned by the owner of B14.
4. Questions 4 (FT_n) and 5 (strict literature) remain open.
