# Problem: finite presentations of cartesian fibrations over higher-dimensional bases (FT_n)

*Standalone problem statement. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, computads (polygraphs) and Grothendieck constructions, and nothing else. The questions are in §4, smallest first.*

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

## 2. What is known (all proved)

1. **Localisation lemma (Loc).** If S is a set of marked positive-dimensional cells of a marked (∞,ω)-category J and q : J → J[S⁻¹], then restriction is an equivalence of (∞,ω)-categories of marked cones, natural in the apex. So a marked index cell that every diagram inverts may be inverted without changing marked lax limits.
2. **Base a graph (FT₂).** For a finite graph Γ and a functor T : Free(Γ) → Cat with values free on finite graphs, a finite computad Ψ_T (unmarked vertical generators, marked horizontal lifts u_e : e → T_u(e), marked 2-generators θ_{u,β} : β ; u_{e′} ⇒ u_e ; T_u(β)) presents the Grothendieck construction after inverting the θ's. This is complete for that class.
3. **Positive 2-dimensional bases (FT₃).** Call a 2-computad *positive* when both boundary paths of every 2-generator are nonempty. Then Free(Γ) ≃ F₂(Γ), the free strict 2-category (Chanavat, arXiv 2603.22242, Cor. 3.39: positive 2-polygraphs are homotopy polygraphs). For T : F₂(Γ) → Cat with values free on finite graphs, add to the FT₂ data, for each base 2-generator α : u ⇒ v and fibre vertex e, a marked 2-generator λ_{α,e} : τ_{u,e} ; a_{α,e} ⇒ τ_{v,e} (prescribed target, as in the strict Grothendieck construction), and for each vertical β a marked 3-generator Ξ_{α,β} filling the naturality square of λ against θ. Inverting the θ's and Ξ's presents ∫T as a left cartesian fibration over F₂(Γ)^♯. The proof computes the homs of the walking 2-cell case directly (they are intervals or points) and extends by Loubaton's pullback-preserves-colimits theorem (arXiv 2406.05425, Thm 3.2.3.15).
4. **Non-positive bases admit no finite presentation.** For Γ = {x; σ : 1_x ⇒ 1_x}, F₂(Γ) = B²ℕ with groupoidification K(ℤ,2) (Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9, Ex. 4.10), while every Free(Ψ)[S⁻¹] with Ψ finite groupoidifies to a finite CW complex. So even the terminal weight on B²ℕ has no presentation of this form, with any finite number of higher generators.
5. **Regular 3-polygraphs.** Chanavat (same paper, Cor. 3.38) also proves that all regular 3-polygraphs (Henry's sense) are homotopy polygraphs, and Thm 3.17 gives a general criterion.

## 3. The shape of FT_n

For a base n-computad Γ and a weight T valued in free m-categories, the natural candidate adds, for each base k-generator and each fibre generator, a marked lift with prescribed target (in odd fibre dimensions) or source (in even ones), following the alternating variance of §1.1, plus one marked (k+1)-generator for each naturality square, and inverts the generators lying over identities.

## 4. Questions

1. **Smallest new case: a 3-dimensional base, Cat-valued weight.** Let Γ be the walking 3-cell (u, v : 0 → 1, α, β : u ⇒ v, Ω : α ⇛ β), which is regular and positive. A strict functor T : F₃(Γ) → Cat with free values must send Ω to an identity, so a_α = a_β. Which generators over Ω present ∫T (one marked 3-generator λ_{α,e} ⇛ λ_{β,e} per fibre vertex?), and does inverting the cells over identities give the right homs?
2. **2-dimensional base, 2-category-valued weight.** Let Γ = (u, v : 0 → 1, α : u ⇒ v) and T valued in free 2-categories on finite 2-computads (positive ones). Give the FT data (lifts of fibre 2-cells with the alternating variance) and prove or refute that it presents ∫T.
3. **General FT_n over regular bases.** For a finite regular (or positive, in a suitable sense) n-computad Γ, so that Free(Γ) is the free strict n-category, give a finite criterion FT_n and prove it, or give an obstruction.
4. **Necessity of the hypothesis.** Is regularity (or positivity) also necessary for a finite presentation in dimension ≥ 3? The finite-CW argument of §2 item 4 shows necessity whenever the strict free object has infinite homological dimension after groupoidification. Is there a non-regular 3-computad whose strict free object nevertheless has a finite presentation?

## 5. What would count as an answer

A proof or counterexample for any question; a reference to a published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs.

# Researcher Response

**Question 1 has a finite 4-dimensional presentation:** add one marked 3-generator over \(\Omega\) for each vertex of \(T(0)\), and one invertible 4-generator for each generating arrow of \(T(0)\). The 3-generators alone do not suffice.

**Regularity is not necessary:** there is a positive, non-regular 3-computad whose strict free category is already its homotopy-cellular realization. This answers the final question in Question 4.

I prove both statements below. For Question 2, I give a corresponding obstruction to stopping in dimension three; I do not establish its full presentation theorem or general \(FT_n\).

## 1. Question 1: the corrected finite presentation

Write
\[
A=T(0),\qquad C=T(1),\qquad U=T(u),\qquad V=T(v).
\]
Since \(T(\Omega)\) is an identity, write
\[
a=T(\alpha)=T(\beta):U\Rightarrow V.
\]
For a generating arrow \(f:e\to e'\) of \(A\), naturality says
\[
U(f);a_{e'}=a_e;V(f).
\tag{1}
\]

Composition is diagrammatic. Below, \(;\) denotes vertical composition in the dimension dictated by its arguments; \(\triangleleft\) and \(\triangleright\) denote left and right whiskering.

### 1.1 Generators and their boundaries

Include the generating graphs of \(A\) and \(C\), with disjoint vertex sets. Their nonidentity arrows are unmarked.

For each vertex \(e\) of \(A\), add
\[
u_e:e\to Ue,\qquad v_e:e\to Ve,
\]
and
\[
\lambda_{\gamma,e}:u_e;a_e\Rightarrow v_e,
\qquad \gamma\in\{\alpha,\beta\}.
\]

For each generating arrow \(f:e\to e'\), add
\[
\theta_{u,f}:f;u_{e'}\Rightarrow u_e;U(f),
\qquad
\theta_{v,f}:f;v_{e'}\Rightarrow v_e;V(f).
\]

Define parallel 2-cells
\[
\begin{aligned}
L_{\gamma,f}
&=(f\triangleleft\lambda_{\gamma,e'});\theta_{v,f},\\
R_{\gamma,f}
&=(\theta_{u,f}\triangleright a_{e'});
  (\lambda_{\gamma,e}\triangleright V(f)).
\end{aligned}
\tag{2}
\]
Both have source \(f;u_{e'};a_{e'}\) and target \(v_e;V(f)\); equation (1) identifies the intermediate paths in the second expression.

Choose the orientation
\[
\Xi_{\gamma,f}:R_{\gamma,f}\Rrightarrow L_{\gamma,f}.
\tag{3}
\]
These are the naturality 3-generators already required for the two base 2-cells.

The new generators over \(\Omega\) are
\[
\boxed{
\omega_e:\lambda_{\alpha,e}\Rrightarrow\lambda_{\beta,e}.
}
\tag{4}
\]

They induce 3-cells
\[
L_{\omega,f}:L_{\alpha,f}\Rrightarrow L_{\beta,f},
\qquad
R_{\omega,f}:R_{\alpha,f}\Rrightarrow R_{\beta,f},
\tag{5}
\]
obtained from (2) by whiskering \(\omega_{e'}\) and \(\omega_e\), respectively, with the indicated fixed cells.

For every generating arrow \(f\), add the 4-generator
\[
\boxed{
K_{\Omega,f}:
\bigl(\Xi_{\alpha,f};L_{\omega,f}\bigr)
\Longrightarrow
\bigl(R_{\omega,f};\Xi_{\beta,f}\bigr).
}
\tag{6}
\]
Both boundaries in (6) are 3-cells
\[
R_{\alpha,f}\Rrightarrow L_{\beta,f}.
\]

Thus the complete additional data are:

| Dimension | Generators |
|---|---|
| \(1\) | \(u_e,v_e\), for each source-fibre vertex \(e\) |
| \(2\) | \(\theta_{u,f},\theta_{v,f}\), for each source-fibre generating arrow \(f\); \(\lambda_{\alpha,e},\lambda_{\beta,e}\) |
| \(3\) | \(\Xi_{\alpha,f},\Xi_{\beta,f}\); \(\omega_e\) |
| \(4\) | \(K_{\Omega,f}\) |

Mark these generators and localize at
\[
S=
\{\theta_{u,f},\theta_{v,f},
  \Xi_{\alpha,f},\Xi_{\beta,f},K_{\Omega,f}\}.
\tag{7}
\]

Their projections are identity cells:
\[
p(\theta_{u,f})=1_u,\qquad
p(\Xi_{\gamma,f})=1_\gamma,\qquad
p(K_{\Omega,f})=1_\Omega.
\]
The generators \(\lambda_{\gamma,e}\) and \(\omega_e\) remain marked without being inverted:
\[
p(\lambda_{\gamma,e})=\gamma,\qquad p(\omega_e)=\Omega.
\]

**Claim.** If \(\Psi_T\) is this finite computad, then
\[
\boxed{
\operatorname{Free}(\Psi_T)[S^{-1}]
\simeq \int_B T
}
\tag{8}
\]
over \(B^\sharp\), with the cartesian marking. No independent generator above dimension four is required.

### 1.2 The resulting homs

Here is the strict total category that (8) presents.

Its vertices are
\[
(0,e)\quad(e\in A_0),
\qquad
(1,c)\quad(c\in C_0).
\]
The same-fibre homs are discrete higher categories on the corresponding hom-sets:
\[
\begin{aligned}
E((0,e),(0,e'))&=A(e,e')_{\mathrm{disc}},\\
E((1,c),(1,c'))&=C(c,c')_{\mathrm{disc}},
\end{aligned}
\]
and
\[
E((1,c),(0,e))=\varnothing.
\]

For the remaining hom, set
\[
M_{e,c}=E((0,e),(1,c)).
\]
This is a strict 2-category. Its vertices are
\[
(u,h),\quad h:Ue\to c,
\qquad
(v,k),\quad k:Ve\to c.
\]
Its hom categories are exactly
\[
M_{e,c}((r,h),(s,k))=
\begin{cases}
\mathbf 1,&(r,h)=(s,k),\\[2mm]
[1],&r=u,\ s=v,\ h=a_e;k,\\[2mm]
\varnothing,&\text{otherwise}.
\end{cases}
\tag{9}
\]
In the middle case, the two vertices of \([1]\) are
\[
\alpha_k,\beta_k:(u,a_e;k)\longrightarrow(v,k),
\]
and its nonidentity arrow is
\[
\Omega_k:\alpha_k\longrightarrow\beta_k.
\]
These are respectively 2-cells and a 3-cell of \(E\).

Precomposition by \(f:e'\to e\) sends
\[
(r,h)\longmapsto(r,T(r)(f);h)
\]
and sends the three cells indexed by \(k\) to those indexed by \(V(f);k\). Postcomposition by \(g:c\to c'\) replaces \(h,k\) by \(h;g,k;g\). Equation (1) makes these operations well typed.

The marked cross-fibre 1-cells are
\[
(u,1_{Ue}),\qquad(v,1_{Ve});
\]
all cross-fibre 2- and 3-cells are marked.

These formulas verify the alternating variance directly:

- The marked lifts of \(u,v\) have prescribed source.
- The lifts of \(\alpha,\beta\) with prescribed target \((v,k)\) have source \((u,a_e;k)\).
- The further hom map governing \(\Omega_k\) is \([1]\to[1]\), so the lift of \(\Omega\) has prescribed source.

For example, composition with \(u_e\) identifies
\[
C(Ue,c)_{\mathrm{disc}}
\]
with the fibre of \(M_{e,c}\to B(0,1)\) over \(u\), giving the required cancellation square. The other cases follow from (9) in the same way. Loubaton’s recursive criterion, Theorem 3.2.2.24(5), therefore identifies this projection as the left cartesian fibration classified by \(T\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 1.3 Proof of the coherent presentation

The proof uses a relative Gray tensor, so it identifies the homotopical localization rather than merely a strict quotient.

Let \(I=[1]\). Define \(K\) by the finite generators
\[
\begin{gathered}
x,y_0,y_1,\\
u:x\to y_0,\qquad a:y_0\to y_1,\qquad v:x\to y_1,\\
\lambda_\alpha,\lambda_\beta:u;a\Rightarrow v,\\
\omega:\lambda_\alpha\Rrightarrow\lambda_\beta .
\end{gathered}
\tag{10}
\]
The arrow \(a\) identifies \(I\) with the full subcategory on \(y_0,y_1\).

The projection \(K\to B\) is the special case of (9) with fibres \(\mathbf1,I\). It classifies the weight sending the source vertex to \(\mathbf1\), the target vertex to \(I\), and both \(\alpha,\beta\) to the arrow of \(I\).

The data \(U,V,a\) determine
\[
F:A\times I\longrightarrow C.
\]
There is an equivalence
\[
\boxed{
\int_B T\simeq
(K\times A)\amalg_{I\times A}C,
}
\tag{11}
\]
where the map to \(C\) is \(F\), after exchanging the Cartesian factors.

One can obtain (11) directly from Loubaton’s formula over a suspension: \(B=\Sigma D_2\), and its action
\[
A\times D_2\longrightarrow C
\]
factors through \(A\times I\). In the cone formula of Corollary 4.1.2.19, push out \(1^{\mathrm{co}}\!\star D_2\) along the map \(D_2\to I\) identifying its two arrows and sending its 2-cell to an identity. This gives precisely (10). The cone-pushout strictness is covered by Theorem 2.3.3.22. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Now use the **unlocalized** Gray tensor and set
\[
Q=K\otimes A,\qquad R=I\otimes A.
\]

Both have finite homotopy-cellular presentations. Here is the relevant check for the 4-dimensional tensor. The generating 3-cell of \(K\) has an acyclic oriented incidence graph: one topological order is
\[
x<u<y_0<a<\lambda_\alpha<\omega<\lambda_\beta<v<y_1.
\]
Its lower-dimensional faces inherit acyclicity. Each generating edge of the graph presenting \(A\) also has an acyclic abstract shape. Chanavat’s Corollary 3.27 and monoidality theorem, Theorem 3.29, therefore apply to these directed complexes and their Gray tensor. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

Localize \(Q\) at the mixed generators
\[
k\otimes f,
\qquad
k\in\{u,a,v,\lambda_\alpha,\lambda_\beta,\omega\},
\quad f\in A_1^{\mathrm{gen}}.
\tag{12}
\]
The result is \(K\times A\). Likewise, localizing \(R\) at \(a\otimes f\) gives \(I\times A\). This is the underlying-category content of Loubaton’s marked tensor construction and Proposition 3.1.3.1. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

It suffices to use the generators in (12): the comparison for \(u;a\) is the pasting of those for \(u\) and \(a\), and the comparison against a path in \(A\) is the pasting of those against its generating edges.

The map
\[
R\longrightarrow I\times A\longrightarrow C
\]
already sends \(a\otimes f\) to an identity, by (1). Therefore the universal properties of localization and pushout give
\[
(K\times A)\amalg_{I\times A}C
\simeq
\bigl(Q\amalg_R C\bigr)
\bigl[(\theta,\Xi,K)^{-1}\bigr].
\tag{13}
\]
Explicitly, maps from the right-hand side into a target \(Z\) are compatible maps \(Q\to Z\) and \(C\to Z\) that invert the remaining mixed generators. They are exactly compatible maps \(K\times A\to Z\) and \(C\to Z\) agreeing on \(I\times A\).

The relative generators of \(R\to Q\), after the pushout to \(C\), are:

| Relative tensor generator | Generator in \(\Psi_T\) |
|---|---|
| \(x\otimes e,\ x\otimes f\) | Source-fibre vertices and arrows |
| \(u\otimes e,\ v\otimes e\) | \(u_e,v_e\) |
| \(u\otimes f,\ v\otimes f\) | \(\theta_{u,f},\theta_{v,f}\) |
| \(\lambda_\gamma\otimes e\) | \(\lambda_{\gamma,e}\) |
| \(\lambda_\gamma\otimes f\) | \(\Xi_{\gamma,f}\) |
| \(\omega\otimes e\) | \(\omega_e\) |
| \(\omega\otimes f\) | \(K_{\Omega,f}\) |

The tensor boundary of the final row is (6). Equations (11)–(13) prove (8).

The auxiliary sharp markings used in the Gray–Cartesian comparison serve to establish the underlying equivalence. The marking on the presented fibration is the one specified in §1.1 and verified by (9); in particular, nonidentity fibre arrows remain unmarked.

This argument permits identity values and arbitrary finite path lengths for \(U(f),V(f),a_e\): those choices enter the attaching map \(R\to C\), and (13) is a homotopy-pushout argument.

### 1.4 Why the 3-generators alone fail

Take the constant weight
\[
A=C=I,\qquad U=V=\mathrm{id}_I,\qquad a=\mathrm{id}.
\]
Its total is
\[
B\times I.
\]

The proposed presentation consisting of the existing data and the two generators \(\omega_e\), **without** \(K_{\Omega,f}\), has generator counts
\[
(c_0,c_1,c_2,c_3)=(4,6,6,4).
\]
Indeed, it has:

- four vertices;
- two vertical and four horizontal arrows;
- two \(\theta\)'s and four \(\lambda\)'s;
- two \(\Xi\)'s and two \(\omega\)'s.

Its groupoidification consequently has Euler characteristic
\[
4-6+6-4=0.
\tag{14}
\]
Localizing any of its cells leaves its groupoidification unchanged, since groupoidification already inverts every cell.

But \((B\times I)^{\mathrm{gpd}}\) is contractible: projection to \(B\) is a homotopy equivalence after groupoidification, and the groupoidification of the globe \(B=D_3\) is contractible. Its Euler characteristic is \(1\), contradicting (14).

Thus **the specified presentation with only the vertex-indexed \(\omega_e\)'s is incorrect**. This argument does not exclude every conceivable alternative presentation of dimension at most three.

## 2. Question 4: a non-regular 3-computad with a finite presentation

Consider the finite 3-computad \(\Delta\):
\[
\begin{array}{c|l}
\text{Dimension}&\text{Generators}\\ \hline
0&x,y,z\\
1&p,q:x\to y,\qquad r:y\to z\\
2&\alpha,\beta:p\Rightarrow q\\
3&\zeta:(\alpha\triangleright r)
       \Rrightarrow(\beta\triangleright r).
\end{array}
\tag{15}
\]
It has nine generators. Every generating cell has nonidentity source and target in the dimensions relevant to positivity.

I claim
\[
\boxed{
\operatorname{Free}(\Delta)\simeq F_3(\Delta),
}
\tag{16}
\]
although \(\Delta\) is not regular. Thus the requested presentation is simply
\[
\Psi=\Delta,\qquad S=\varnothing.
\]

### 2.1 Failure of regularity

The generic 2-polyplex for the source of \(\zeta\) is a 2-globe post-whiskered by an edge:
\[
W=D_2\mathbin{\#_0}D_1.
\]
Its 1-source and 1-target are
\[
p;r,\qquad q;r,
\]
and its 0-source and 0-target are \(x,z\).

The spherical-boundary condition for a regular 3-plex requires the canonical map
\[
(p;r)\amalg_{\{x,z\}}(q;r)\longrightarrow W
\tag{17}
\]
to be a monomorphism. This is the relevant instance of the definition of spherical boundaries recalled in Chanavat §1.51. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

Map (17) is not monic. Its domain has two distinct generating arrows \(r^-,r^+\), while both map to the same arrow \(r\) of \(W\). Its two intermediate vertices likewise both map to \(y\).

This failure concerns the generic arity of the whiskered 2-cell. It is not merely an identification of labels in a map from a regular shape. Therefore the top 3-plex is non-regular.

### 2.2 The top-cell attachment is nevertheless homotopical

Set
\[
M=F_3(\Delta),\qquad
M_2=F_2(\Delta_{\leq2}).
\]
The nonidentity hom categories of \(M_2\) are
\[
\begin{aligned}
M_2(x,y)&=(p\overset{\alpha,\beta}{\rightrightarrows}q),\\
M_2(y,z)&=\mathbf1,\\
M_2(x,z)&=
\bigl(p;r\overset{\alpha\triangleright r,\,
                         \beta\triangleright r}
                    {\rightrightarrows}q;r\bigr).
\end{aligned}
\tag{18}
\]
The only change on passing to \(M\) is the addition of \(\zeta\) to the last hom.

Consequently, the full strict subcategory \(G\subseteq M\) on \(x,z\) is a 3-globe:
\[
G\cong D_3,\qquad M_2\cap G\cong\partial D_3.
\]
Its two 1-generators map to the composite arrows \(p;r,q;r\) of \(M\).

The defining strict pushout is therefore
\[
M=M_2\amalg_{\partial D_3}D_3.
\tag{19}
\]

To prove that (19) is a homotopy pushout, use the ordinary \(\Theta_\omega\)-nerve
\[
\nu M(\tau)=
\operatorname{Hom}_{\mathrm{sCat}_\omega}(\tau,M).
\]
A theta has the form
\[
\tau=[m](\tau_1,\ldots,\tau_m).
\]
A strict functor \(\tau\to M\) is specified by a vertex sequence
\[
(c_0,\ldots,c_m)
\]
and functors
\[
\tau_i\longrightarrow M(c_{i-1},c_i).
\]
This is the suspension decomposition of theta shapes recalled in Chanavat Example 2.24. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

Every such vertex sequence is weakly increasing for
\[
x<y<z,
\]
because the reverse hom categories are empty.

There are two cases.

1. **The sequence uses \(y\).** It cannot have an adjacent pair \((x,z)\). Every adjacent hom used by the functor is unchanged from \(M_2\) to \(M\), so the functor factors through \(M_2\).

2. **The sequence does not use \(y\).** It factors through the full subcategory \(G\cong D_3\).

The intersection of these two subpresheaves is \(\nu\partial D_3\). Hence
\[
\boxed{
\nu M
=
\nu M_2\amalg_{\nu\partial D_3}\nu D_3
}
\tag{20}
\]
as an equality of set-valued presheaves.

Both maps from \(\nu\partial D_3\) are monomorphisms. Thus (20) is also a homotopy pushout of space-valued presheaves, and remains a pushout after localization to higher categories. Campion’s Lemma 2.16 gives precisely this preservation statement for unions of subpresheaves; Remark 2.12 covers passage from finite dimension to dimension \(\omega\). [arxiv.org](https://arxiv.org/pdf/2311.00200?utm_source=chatgpt.com)

Finally, \(\Delta_{\leq2}\) is a positive 2-polygraph, so its strict cellular construction is homotopical by Chanavat Corollary 3.39. Combining this with the verified top-cell attachment (20) proves (16). [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

Therefore **regularity is not necessary for finite coherent presentation, even with an actual 3-generator and with no localization at all**. This example is positive, so it does not settle whether some positivity hypothesis is necessary.

## 3. What these results establish for Questions 2 and 3

For Question 2, the constant weight with fibre \(D_2\) gives a diagnostic parallel to §1.4. The full generator-pair construction for
\[
D_2\times D_2
\]
has counts
\[
(4,8,8,4,1).
\]
Omitting the generator indexed by the pair of top 2-cells leaves Euler characteristic
\[
4-8+8-4=0,
\]
whereas the actual product groupoidifies to a contractible space. Thus the construction truncated after dimension three fails: a 4-dimensional compatibility indexed by the fibre 2-generator is required.

That necessity does not itself prove sufficiency for arbitrary positive 2-category fibres. I have not completed that sufficiency proof here.

For Question 3, the proved extension is the walking-3-cell, Cat-valued case above. Its finite test is explicit: verify the finitely many path equalities (1), construct the boundaries (2)–(6), and localize the specified set (7). A general \(FT_n\) recognition theorem is not established by these arguments.

# Verification of the researcher response (2026-11-18)

**Verdict: correct, with two steps resting on cited results that I did not re-derive.**
- **Q1 is answered.** Over the walking 3-cell the presentation needs one 3-generator ω_e per fibre vertex and one 4-generator K_{Ω,f} per fibre arrow. The ω_e alone are provably not enough.
- **The second part of Q4 is answered.** Regularity is not necessary: an explicit non-regular, positive 3-computad is already homotopical.
- **Q2 is partly answered.** A 4-dimensional generator indexed by the fibre 2-cell is necessary; sufficiency is not proved.
- **Still open:** Q3 (general FT_n) and whether positivity is necessary.

Step by step.

1. **The generators (§1.1).** These extend the FT₃ data of known item 3 consistently.
   - u_e, v_e are marked lifts with prescribed source, and λ_{γ,e} : u_e ; a_e ⇒ v_e has prescribed target.
   - θ and Ξ are as before.
   - The new generators are ω_e : λ_{α,e} ⇛ λ_{β,e} and K_{Ω,f}. K_{Ω,f} goes between the two 3-cells R_{α,f} ⇛ L_{β,f}, namely Ξ_α ; L_ω and R_ω ; Ξ_β, so it is well typed. ✓

2. **The homs (§1.2), checked directly.**
   - A 2-cell from (u, h) to (v, k) over α or β exists exactly when h = a_e ; k, and then it is unique. The two such cells are joined by Ω_k, so the hom is [1].
   - The only other non-empty homs are identities.
   - The variance is correct: lifts of α, β with prescribed target, and a hom map [1] → [1] over Ω.
   - So (9) is the strict Grothendieck construction, and it satisfies Loubaton's recursive criterion. ✓

3. **The coherent presentation (§1.3).**
   - The formal part is correct. The localisation-and-pushout identity (13) is formal. The relative generators of I ⊗ A → K ⊗ A are (K ∖ I) × A with dimensions added, and they match the table row for row, the last row being ω ⊗ f ↦ K_{Ω,f}.
   - **Rests on citations, not re-derived:**
     - (11), ∫T ≃ (K × A) ∐_{I×A} C, via Loubaton's cone formula over a suspension (Cor. 4.1.2.19, Thm 2.3.3.22);
     - "Gray tensor localised at the mixed generators ≃ cartesian product" (Loubaton Prop. 3.1.3.1). For (∞,2) this is the classical biequivalence between the pseudo Gray tensor and the product.
     - Chanavat Cor. 3.27 / Thm 3.29 for the homotopy-cellularity of K ⊗ A and I ⊗ A.
   - **Independent consistency check (mine).** By the table, the relative generators contribute (1 − 2 + 2 − 1)·χ(A) = 0 to the Euler characteristic, so χ(Ψ_T) = χ(C). The groupoidification of the right side of (11) is C^gpd, because K^gpd and I^gpd are contractible. The two agree for every A and C.

4. **ω_e alone fail (§1.4).** Correct.
   - For A = C = I with identity functors, the generator counts without K are (4, 6, 6, 4), so χ = 0.
   - The groupoidification of a free (∞,ω)-category on a finite computad, localised or not, is a CW complex with one cell per generator.
   - B × I groupoidifies to a point, which has χ = 1.
   - Adding the one K_{Ω,f} gives χ = 1.

5. **Non-regular but homotopical (§2).** Correct.
   - **Δ is not regular.** Its 3-generator ζ : α ▷ r ⇛ β ▷ r has a whiskered 2-cell as boundary, whose 1-source p ; r and 1-target q ; r share r.
   - **Strict homs.** The strict homs of M₂ = F₂(Δ≤2) are as stated. ζ changes only M(x, z). The full subcategory on x, z is D₃, and it meets M₂ in ∂D₃.
   - **The nerve splits.** A Θ-shape map is a weakly increasing vertex sequence (x < y < z) together with maps into the adjacent homs. If the sequence contains y, it has no adjacent pair (x, z) and so lands in M₂; otherwise it lands in D₃. So νM = νM₂ ∪ νD₃ with intersection ν∂D₃, a pushout of presheaves of sets along monomorphisms.
   - **The homotopy pushout.** That pushout is a homotopy pushout. Localisation preserves it, and strict ω-categories without non-trivial invertible cells are local. So M ≃ M₂ ∐^h_{∂D₃} D₃.
   - **Conclusion.** Since Free(Δ≤2) ≃ M₂ (Chanavat Cor. 3.39, positive 2-polygraph), Free(Δ) ≃ F₃(Δ).
   - Δ is positive, so whether positivity is necessary stays open.

6. **Q2 diagnostic (§3).** Correct.
   - D₂ ⊗ D₂ has generator counts (4, 8, 8, 4, 1).
   - Dropping the 4-cell gives χ = 0, but the product is contractible after groupoidification.
   - So any finite presentation of the constant D₂-valued weight over the walking 2-cell built from the FT₃ shape needs a 4-generator indexed by (base 2-cell, fibre 2-cell).

**Consequences for B14.**
- **The FT_n shape of §3 is corrected.** The generators are exactly the relative Gray-tensor generators k ⊗ a, for k in the universal total K ∖ I and a a fibre generator. Their dimension is dim k + dim a, so the top generators can exceed the base dimension by the fibre dimension (4-generators over a 3-dimensional base with a Cat-valued weight).
- **The proof method of §1.3 looks general.** It writes ∫T as a pushout of a universal total times the fibre, then localises a relative Gray tensor. Whenever the weight factors through a product with a universal total in this way, it should give FT_n.
- **Regularity is not a necessary hypothesis.**

Follow-up prompt: `finite-fibration-test-higher-base-r2-2026-11-18.md` (round 2, answered).
