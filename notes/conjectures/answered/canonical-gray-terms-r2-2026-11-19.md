# Canonical CaTT terms for the cells of Gray tensors of pasting diagrams: beyond suspensions

*A self-contained problem. It assumes familiarity with the type theory CaTT, strict ω-categories and Steiner's directed complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** The most general theorem: a construction for **all** pairs and all finite families of globular pasting diagrams, or a proof that none exists for some pair together with the equations such a counterexample forces. The question is purely syntactic: whether chosen terms can match their boundaries on the nose in a theory with no definitional equalities.

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
7. **Where wedges fail.** Closure under P, Q ↦ P ∨ Q is not established. A cell of I ⊗ (P ∨ Q) uses generators from both pieces. When three independent n-generators are reordered, the selected (n+1)-cells compare adjacent orders, and a generic (n+2)-coherence in a common arity has as faces **derived** pair-comparison terms, which are not syntactically the selected ones and cannot be substituted for them. In the cylinder-extension formulation, changing a seed gives a transported filler ℓ_u⁻¹ ; F⁰(u) ; r_u with exactly the boundary of the prescribed F¹(u), and what is missing is a term κ_u from it to F¹(u), with higher compatibilities when several changes are composed. D¹ ⊗ D¹ ⊗ D¹ = I ⊗ (I ⊗ I) is the smallest case not covered, since I ⊗ I is not a suspension.

## 4. Questions

**Q1 (main).** Decide CT for **all** pairs Θ, Δ and for all iterated tensors Θ₁ ⊗ ⋯ ⊗ Θ_k, compatibly with associativity (the assignments for (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) agree up to renaming). Item 6 suggests an induction on the globular structure; the missing operations are wedge (item 7) and tensoring with a non-suspension. A positive answer may use any terms (non-layered composites, single coherence heads over chosen pasting diagrams, globally chosen bracketings, simultaneous inductive choices).

**Q2 (wedge closure).** As a step, prove CT(I ⊗ P) ∧ CT(I ⊗ Q) ⇒ CT(I ⊗ (P ∨ Q)), which with item 6 gives CT(I ⊗ P) for every globular P, and then CT(I ⊗ (I ⊗ I)) by a variant for the non-globular second factor. Equivalently, construct the terms κ_u of item 7 with their higher compatibilities, or show they cannot exist.

**Q3 (if CT fails).** If CT fails for some pair (D¹ ⊗ D¹ ⊗ D¹ is the natural candidate), prove that no assignment satisfies (a)–(c) and identify the minimal extra rule that makes the family contexts well formed, for example a typing rule for generators whose boundaries are molecules, or a definitional equation between bracketings. A precise description of the forced equations is the useful answer.

## 5. What counts as a solution

An explicit construction of T for all pairs and iterated tensors; wedge closure with proof; an impossibility proof with the forced equations; or a published reference.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Steiner, HHA 2004; Hadzihasanovic, arXiv 2404.07273 (molecules, layerings, Prop. 8.3.17 on supports).
- Campion, arXiv 2311.00205; Chanavat, arXiv 2603.22242.
- Finster–Mimram, arXiv 1706.02866; Benjamin–Markakis, arXiv 2406.12127 (invertibility of coherences).
- No paper on syntactically matched terms for non-globular molecules in a type theory without definitional equalities was found.

# Researcher Response 1

**Wedge closure holds.** More precisely:

> **Theorem.** Let \(P,Q\) be finite globular pasting diagrams, and let \(I=D^1\). Then
> \[
> \mathrm{CT}(I\otimes P)\ \land\ \mathrm{CT}(I\otimes Q)
> \quad\Longrightarrow\quad
> \mathrm{CT}\bigl(I\otimes(P\vee Q)\bigr).
> \]
> The construction uses the existing generator variables, ordinary CaTT composition terms, and one 2-dimensional coherence for each of certain 1-paths. It introduces no definitional equations.

Together with your suspension theorem, this proves
\[
\boxed{\mathrm{CT}(I\otimes P)\quad\text{and}\quad \mathrm{CT}(P\otimes I)
\quad\text{for every finite globular pasting diagram }P.}
\]

This resolves **Q2**. The proof below does not resolve arbitrary pairs or the associativity-compatible construction for arbitrary iterated tensors.

The decisive fact is that the terms for cells crossing the wedge point can be chosen simultaneously using a factorization determined by their **1-dimensional source and target**. Its intermediate 1-path remains fixed on every higher boundary. Consequently, the necessary correction is a fixed 2-term; higher seed-comparison terms \(\kappa_u\) are not required for this construction.

## 1. Notation and the relevant strict hom

Write \(z\) for the terminal vertex of \(P\), identified with the initial vertex of \(Q\). Set
\[
A=I\otimes P,\qquad B=I\otimes Q,\qquad C=I\otimes(P\vee Q),
\]
using this notation for their associated strict \(\omega\)-categories. Their common interval has vertices \(z_0,z_1\) and generator
\[
u:z_0\longrightarrow z_1.
\]

Fix vertices
\[
a\in P_0\setminus\{z\},\qquad b\in Q_0\setminus\{z\}.
\]
The only difficult new hom is
\[
H=C(a_0,b_1).
\]
Define
\[
\begin{aligned}
U&=P(a,z),&
V&=Q(z,b),\\
L&=A(a_0,z_1),&
R&=B(z_0,b_1).
\end{aligned}
\]
There are strict functors
\[
i:U\longrightarrow L,\qquad i(p)=p_0\#_0u,
\]
and
\[
j:V\longrightarrow R,\qquad j(q)=u\#_0q_1.
\]
Here \(p_0\) denotes the copy of a cell of \(P\) at interval endpoint \(0\), and \(q_1\) denotes the copy at endpoint \(1\).

An \(n\)-cell of any of these homs is an \((n+1)\)-cell of the original strict \(\omega\)-category. In particular, vertices of \(H\) are ordinary 1-paths in \(C\).

We will prove:

1. \(i\) is a full sieve and \(j\) is a full cosieve.
2. \(H\) is the full sub-\(\omega\)-category of \(L\times R\) on the vertices
   \[
   (l,r)\quad\text{such that}\quad l\in i(U_0)\ \text{or}\ r\in j(V_0).
   \tag{1}
   \]
3. These facts give a factorization of every remaining cell whose intermediate vertex depends only on its zero-source and zero-target in \(H\).

The strict calculation uses Steiner’s positive-tableau definition of \(\nu\): its rows satisfy
\[
d x_k^\pm=x_{k-1}^+-x_{k-1}^-,
\]
with nonnegative coefficients and augmentation \(1\) in degree zero. Composition is the affine operation \(x\#_k y=x-d_k^+x+y\). These are Definitions 2.6 and 2.8 in Steiner. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

## 2. Full sieve and full cosieve

### A positivity lemma

Let \(K\) have a strongly loop-free unital basis. If \(w\) is a nonzero positive chain of positive degree, then \(dw\) has both a negative coefficient and a positive coefficient.

To see this, extend the strong order to a total order on the finite set of basis elements under consideration. Choose the least basis element \(g\) with nonzero coefficient in \(w\). Unitality supplies a basis element \(f\) in \(d^-g\). A positive contribution to the coefficient of \(f\) from another supported basis element \(h\) would require
\[
h<f<g,
\]
contradicting minimality of \(g\). Thus the coefficient of \(f\) in \(dw\) is negative. Using the greatest supported basis element gives a positive coefficient.

Consequently,
\[
w\geq0,\quad dw\geq0\quad\Longrightarrow\quad w=0,
\tag{2}
\]
and likewise with \(dw\leq0\).

### The inclusion \(i\) is a full sieve

Write a positive \(k\)-chain in \(\lambda I\otimes\lambda P\), for \(k\geq1\), as
\[
0\otimes p_k+1\otimes q_k+e\otimes r_{k-1}.
\]
Its differential has coefficients in the two endpoint copies of \(\lambda P\)
\[
dp_k-r_{k-1},
\qquad
dq_k+r_{k-1}.
\tag{3}
\]

Suppose an ordinary 2-cell has target path \(i(p)=p_0\#_0u\). Its target 1-chain has no horizontal edge at interval endpoint \(1\), so \(q_1^+=0\). Equation (3) gives
\[
dq_2+r_1=-q_1^-.
\]
All three chains \(q_2,r_1,q_1^-\) are nonnegative. Applying (2) to \(q_2\) gives
\[
q_2=r_1=q_1^-=0.
\]
The source path also has no horizontal edge at interval endpoint \(1\). Since it ends at \(z_1\), its vertical edge is \(u\), so it is also in \(i(U_0)\). This proves the sieve condition.

For fullness, take any higher cell of \(L\) whose zero-source and zero-target are in \(i(U_0)\). Thus \(q_1^\pm=0\). Inductively, its tableau satisfies
\[
dq_k^\pm+r_{k-1}^\pm
=q_{k-1}^+-q_{k-1}^-=0.
\]
Again (2) implies
\[
q_k^\pm=r_{k-1}^\pm=0
\qquad(k\geq2).
\]
The remaining rows are exactly those of a unique cell of \(P(a,z)\), followed by \(u\). Therefore \(i\) is full in every dimension.

### The inclusion \(j\) is a full cosieve

The dual argument uses the endpoint-\(0\) equation in (3).

If an ordinary 2-cell starts at \(j(q)=u\#_0q_1\), then \(p_1^-=0\), and
\[
dp_2-r_1=p_1^+.
\]
Thus \(dp_2\geq0\), forcing
\[
p_2=r_1=p_1^+=0.
\]
The target also belongs to \(j(V_0)\). Induction in the higher tableau rows proves fullness.

Hence \(i\) is a full sieve and \(j\) a full cosieve, including all identity cells.

## 3. An explicit description of every crossing cell

Collapsing \(Q\) to \(z\), or \(P\) to \(z\), gives strict projections
\[
H\longrightarrow L,\qquad H\longrightarrow R.
\tag{4}
\]

Their product identifies \(H\) with the full subcategory \(G\subseteq L\times R\) specified in (1). Here is the inverse, directly on tableaux.

Let \(E_u\) be the tableau of \(u\), regarded in the required dimension by identities. Its degree-zero entries are \(z_0,z_1\), its degree-one entries are \(u,u\), and its higher entries are zero.

For a pair of tableaux \((l,r)\), define
\[
c=l+r-E_u.
\tag{5}
\]
Explicitly,
\[
\begin{aligned}
c_k^\pm&=l_k^\pm+r_k^\pm &&(k\geq2),\\
c_1^\pm&=l_1^\pm+r_1^\pm-u,\\
c_0^-&=a_0,\qquad c_0^+=b_1.
\end{aligned}
\tag{6}
\]

We check all requirements.

**Positivity.** Every 1-path from interval endpoint \(0\) to endpoint \(1\) has exactly one vertical edge: projection to \(I\) sends its positive 1-chain to \(e\), with coefficient one.

A path in \(L\) uses \(u\) precisely when it is \(i(p)\) for some \(p\in U_0\). A path in \(R\) uses \(u\) precisely when it is \(j(q)\) for some \(q\in V_0\). Therefore
\[
l_1+r_1-u\geq0
\]
precisely when \(l\in i(U_0)\) or \(r\in j(V_0)\).

For higher cells this condition is imposed on their zero-source and zero-target in \(L\times R\). It ensures positivity of both degree-one rows in (6). Every row of degree at least two is a sum of positive chains.

**Boundary equations.** In degree one,
\[
(z_1-a_0)+(b_1-z_0)-(z_1-z_0)=b_1-a_0.
\]
In degree two, the subtracted \(u\) cancels between the positive and negative degree-one rows. Every higher boundary equation is additive. The degree-zero entries have augmentation one.

**Inverse property.** Collapsing \(Q\) sends each degree-one row of \(r\) to \(u\), and every higher row of \(r\) to zero. It therefore recovers \(l\) from (6). The other collapse recovers \(r\). Conversely, (6) recovers every crossing cell from its projections.

Thus (4) is a bijection on all cells with a globular inverse. Since the projections are strict functors, it is a strict isomorphism
\[
H\cong G.
\tag{7}
\]

### The factorization determined by the endpoints

Identify the following full subcategories of \(G\):
\[
X=L\times V,\qquad
Y=U\times R,\qquad
D=X\cap Y=U\times V,
\]
using the embeddings
\[
(l,q)\longmapsto(l,jq),\qquad
(p,r)\longmapsto(ip,r).
\]

Write
\[
X^\circ_0=X_0\setminus D_0,\qquad
Y^\circ_0=Y_0\setminus D_0.
\]

Because \(i\) is a sieve and \(j\) a cosieve, every positive-dimensional cell of \(G\) has exactly one of the following forms:

| Zero-source and zero-target in \(G\) | Where the cell is determined |
|---|---|
| Both in \(X_0\) | \(X\) |
| Both in \(Y^\circ_0\) | \(Y\) |
| Source in \(Y^\circ_0\), target in \(D_0\) | \(Y\) |
| Source in \(Y^\circ_0\), target in \(X^\circ_0\) | The product description \(G\subseteq L\times R\) |

The other directions are empty.

Consider the fourth case. Write the endpoints as
\[
y=(ip,r),\qquad x=(l,jq).
\]
An \(n\)-cell \(h:y\to x\), \(n\geq1\), is uniquely a pair
\[
h=(\alpha,\beta),
\]
where \(\alpha\) is an \(n\)-cell of \(L\) from \(ip\) to \(l\), and \(\beta\) is an \(n\)-cell of \(R\) from \(r\) to \(jq\).

Set
\[
d=(p,q)\in D_0.
\]
There is a strict factorization
\[
h=
(\mathbf1_p,\beta)\ \#_0\ (\alpha,\mathbf1_q),
\tag{8}
\]
through \(d\). Here \(\mathbf1_p,\mathbf1_q\) denote the identity towers in the dimension of \(h\).

**The point needed for syntax is that \(p,q,d\) depend only on \(y,x\).** For \(n>1\), the immediate source and target of \(h\) have the same zero-endpoints, and hence the same intermediate vertex \(d\). Their factorizations are obtained from (8) by taking the immediate boundaries of \(\alpha,\beta\).

## 4. The CaTT operations used in the construction

We need three families of terms:

- \(A_m(a,b)\): composition of two \(m\)-terms along dimension \(0\), for \(m\geq1\);
- \(V_m(a,b)\): composition of two \(m\)-terms along dimension \(1\), for \(m\geq2\);
- \(W_m(a,\gamma)\): composition along dimension \(1\) of an \(m\)-term \(a\) with a 2-term \(\gamma\), for \(m\geq2\).

Choose these recursively over the globular pasting contexts
\[
D^m\vee_0D^m,\qquad
D^m\vee_1D^m,\qquad
D^m\vee_1D^2.
\]
These two-globe arities are globular pasting diagrams; see Benjamin–Markakis, Example 5. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

At the lowest relevant dimension, use the ordinary composition coherence. Above that dimension, prescribe its source and target recursively. Thus, literally,
\[
\begin{aligned}
\partial^\epsilon A_m(a,b)
  &=A_{m-1}(\partial^\epsilon a,\partial^\epsilon b)
  &&(m>1),\\
\partial^\epsilon V_m(a,b)
  &=V_{m-1}(\partial^\epsilon a,\partial^\epsilon b)
  &&(m>2),\\
\partial^\epsilon W_m(a,\gamma)
  &=W_{m-1}(\partial^\epsilon a,\gamma)
  &&(m>2),
\end{aligned}
\tag{9}
\]
for \(\epsilon\in\{-,+\}\).

For example,
\[
W_2(a,\gamma):\partial^-a\longrightarrow\partial^+\gamma.
\]

These prescriptions are valid applications of CaTT’s composition rule: by induction, each prescribed boundary term uses exactly the variables of the corresponding boundary of its two-globe arity. Their strict interpretations are the indicated strict composites.

Equation (9) is therefore an equality of syntax, arising from the chosen types of the coherence heads. No associativity equation is being imposed.

## 5. Merge the contexts and choose the joining-path coherences

Let \((\Gamma_A,T_A)\) and \((\Gamma_B,T_B)\) witness the two hypotheses.

Identify the declarations of \(z_0,z_1,u\), and take the union of the remaining declarations. This produces a well-formed context \(\Gamma\): every declaration retains its original type and its original dependencies.

There is a small issue concerning the chosen terms for identity towers in the common interval. Use \(T_A\) on the entire common interval and \(T_B\) elsewhere in \(B\).

This preserves the boundary condition. Indeed, the full subcategory of either tensor on \(z_0,z_1\) is the interval \(I\): a 1-path cannot leave the wedge endpoint and return, and the positivity argument of Section 2 excludes additional higher cells. Thus no cell outside \(I\) has a positive-dimensional boundary in \(I\). At dimension zero, the two choices already agree because they are the same vertex variables.

We now work in \(\Gamma\).

### Preliminary terms on \(X\) and \(Y\)

For an \(n\)-cell \((l,q)\in X_n\), set
\[
S_X(l,q)
=
A_{n+1}\bigl(T_A(l),T_B(q_1)\bigr).
\tag{10}
\]
For an \(n\)-cell \((p,r)\in Y_n\), set
\[
S_Y(p,r)
=
A_{n+1}\bigl(T_A(p_0),T_B(r)\bigr).
\tag{11}
\]

Here \(l,r,p_0,q_1\) are regarded as original \((n+1)\)-cells when applying the given sections.

By (9) and the hypotheses on \(T_A,T_B\), both preliminary assignments commute literally with every positive-dimensional boundary in their respective homs.

### A single 2-term at each vertex of \(D\)

For \(d=(p,q)\in D_0\), the two preliminary 1-terms are
\[
\begin{aligned}
S_Y(d)
  &=A_1\bigl(T_A(p_0),T_B(u\#_0q_1)\bigr),\\
S_X(d)
  &=A_1\bigl(T_A(p_0\#_0u),T_B(q_1)\bigr).
\end{aligned}
\]
Both strictly interpret as the path
\[
p_0\#_0u\#_0q_1.
\tag{12}
\]

Choose a term
\[
\gamma_d:S_Y(d)\longrightarrow S_X(d)
\tag{13}
\]
by a single application of CaTT’s coherence rule over the generic 1-dimensional context of the path (12).

Here is why this application is available even for arbitrary given choices \(T_A,T_B\). A CaTT 1-term strictly interpreting as a fixed directed path uses exactly that path’s edge variables and vertices. In dimension one this also follows directly from the rules: a coherence producing a 1-term has a point or a path as its arity, and strict interpretation concatenates the substituted paths. Therefore both terms in (13) strengthen, by renaming, to terms over that generic path context, and both have full support there. The coherence rule applies with precisely those terms as its endpoints. [arxiv.org](https://arxiv.org/pdf/1706.02866?utm_source=chatgpt.com)

The strict interpretation of \(\gamma_d\) is the identity 2-cell on (12), since the strict category of a 1-dimensional path has no nonidentity 2-cells.

Only these 2-dimensional comparisons are used. We do not choose comparisons between \(S_X\) and \(S_Y\) on higher cells of \(D\).

## 6. Define the terms for all cells of the crossing hom

First define the term for every vertex \(h\in H_0\), that is, every original crossing 1-cell:
\[
T(h)=
\begin{cases}
S_X(h),&h\in X_0,\\
S_Y(h),&h\in Y^\circ_0.
\end{cases}
\tag{14}
\]
Thus \(S_X\) is the chosen value on \(D_0\).

Now let \(h\in H_n\), where \(n\geq1\), and put \(m=n+1\), its original dimension.

Use the four cases from Section 3.

### Case 1: both zero-endpoints lie in \(X_0\)

Set
\[
T(h)=S_X(h).
\tag{15}
\]

### Case 2: both zero-endpoints lie in \(Y^\circ_0\)

Set
\[
T(h)=S_Y(h).
\tag{16}
\]

### Case 3: source in \(Y^\circ_0\), target \(d\in D_0\)

Set
\[
T(h)=W_m\bigl(S_Y(h),\gamma_d\bigr).
\tag{17}
\]

For \(m=2\), this has source equal to the selected term at the source of \(h\), and target
\[
\partial^+\gamma_d=S_X(d),
\]
which is the selected term at its target.

For \(m>2\), the immediate boundaries retain the same zero-endpoints and the same \(d\). Hence (9) gives
\[
\begin{aligned}
\partial^\epsilon T(h)
&=W_{m-1}\bigl(\partial^\epsilon S_Y(h),\gamma_d\bigr)\\
&=W_{m-1}\bigl(S_Y(\partial^\epsilon h),\gamma_d\bigr)\\
&=T(\partial^\epsilon h)
\end{aligned}
\tag{18}
\]
literally.

### Case 4: source in \(Y^\circ_0\), target in \(X^\circ_0\)

Use the unique pair and factorization from (8):
\[
h=(\alpha,\beta),\qquad
h_Y=(\mathbf1_p,\beta),\qquad
h_X=(\alpha,\mathbf1_q),\qquad d=(p,q).
\]
Define
\[
T(h)=
V_m\!\left(
  W_m\bigl(S_Y(h_Y),\gamma_d\bigr),
  S_X(h_X)
\right).
\tag{19}
\]

This is well typed. The first argument has 1-target \(S_X(d)\), and the second has 1-source \(S_X(d)\), literally.

For \(m=2\), its source and target are exactly the selected 1-terms at the endpoints of \(h\).

For \(m>2\), the immediate boundaries retain the same case and the same \(d\). Moreover, taking an immediate boundary of the strict factorization replaces \(\alpha,\beta\) by their corresponding boundaries. Thus
\[
\begin{aligned}
\partial^\epsilon T(h)
=
V_{m-1}\!\left(
 W_{m-1}\bigl(S_Y(\partial^\epsilon h_Y),\gamma_d\bigr),
 S_X(\partial^\epsilon h_X)
\right)
=
T(\partial^\epsilon h)
\end{aligned}
\tag{20}
\]
as raw syntax.

This is the required higher compatibility. It follows from the recursive types of the ordinary composition operations and the fixed intermediate vertex \(d\).

### Strict interpretation

Equations (15)–(16) have the required interpretation by construction.

In (17), \(\gamma_d\) interprets as an identity, so the interpretation remains \(h\).

In (19), deleting that strict identity leaves the strict composite
\[
h_Y\#_0h_X
\]
in \(H\), equivalently composition along dimension \(1\) in \(C\). By (8), this is \(h\).

Identity towers require no additional choices or equations. They are covered by the same cases, and their faces satisfy the same recursive formulas.

## 7. Complete the assignment on \(C\)

It remains to account for the other original zero-endpoints.

If both endpoints lie in \(A\), use \(T_A\). If both lie in \(B\), use \(T_B\), with the common-interval convention already specified.

There are no additional cells with these endpoints using generators from the other piece. For example, collapsing \(P\) sends a cell whose endpoints lie in \(A\) to a cell of \(B\) with endpoints among \(z_0,z_1\), hence to a cell of the common interval. Positivity then forces every non-seam \(B\)-generator coefficient in the original tableau to vanish. The other case is symmetric.

For crossing endpoints on the same interval level,
\[
C(a_\epsilon,b_\epsilon)
\cong P(a,z)\times Q(z,b).
\]
Use the ordinary \(A_m\)-composition of the two supplied terms. Equation (9) gives literal agreement of boundaries.

There is no crossing cell from interval level \(1\) to level \(0\). Cases with \(a=z\) or \(b=z\) already lie in one original piece.

Every cell of \(C\) has now been assigned a term. Finally, check the three CT conditions.

**(a) Generators.** Every basis generator of
\[
\lambda I\otimes\lambda(P\vee Q)
\]
belongs to one of the two original tensor complexes. None has zero-source in \(P\setminus\{z\}\) and zero-target in \(Q\setminus\{z\}\). Therefore all generators retain their original variable terms.

**(b) Interpretation.** All new terms are built using the ordinary CaTT composition operations and the coherences \(\gamma_d\). Their strict interpretations were checked above.

**(c) Literal boundaries.** This holds in the original pieces by hypothesis, in the same-level crossing homs by (9), and in the mixed crossing hom by (18) and (20). Iterating these literal boundary equalities also identifies the complete lower type syntactically.

The variable declarations remain the original declarations from the two well-formed contexts. Their boundary cells lie in their respective pieces, so they have exactly the terms required by the completed assignment.

This proves wedge closure.

## 8. Consequence and remaining scope

Every finite globular pasting diagram has a recursive decomposition
\[
P=\bigvee_{j=1}^{r}\Sigma P_j,
\]
with the point as the base case. This is the Batanin-tree description of globular pasting diagrams; Benjamin–Markakis give it explicitly as
\[
\operatorname{Pos}(\operatorname{br}[B_1,\ldots,B_r])
=
\bigvee_j\Sigma\operatorname{Pos}(B_j).
\] :chatgpt-content-reference{index="3"}

Starting from \(\mathrm{CT}(I\otimes D^0)\), apply your known suspension closure to each \(P_j\), and then apply the wedge theorem repeatedly. This gives
\[
\mathrm{CT}(I\otimes P)
\]
for every finite globular \(P\). Applying the odd-opposite tensor flip to \(I\otimes P^{\mathrm{op}}\) gives \(\mathrm{CT}(P\otimes I)\).

The restriction to an interval factor is substantive. In the tableau reconstruction
\[
c=l+r-E_u,
\]
the subtracted tableau has zero entries in every degree above one. Consequently, positivity is determined entirely by the vertices of the crossing hom, and the intermediate path \(d\) stays fixed under higher boundaries.

For a general first factor \(\Theta\), reconstructing across the wedge would require subtracting a varying cell of the common copy of \(\Theta\). Positivity conditions then occur in higher degrees as well. The endpoint-based factorization proved here does not supply that extension.

Thus the established result is **uniform wedge closure and CT for every globular cylinder \(I\otimes P\), in all dimensions, with literal CaTT typing**. Arbitrary pairs, non-globular second factors such as \(I\otimes I\), and compatibility for arbitrary iterated tensors remain unresolved by this argument.

# Researcher Response 2

**Q2 holds, including the three-interval cube.** For finite globular pasting diagrams
$P,Q$, sections on $I⊗P$ and $I⊗Q$ give a section on $I⊗(P∨Q)$.
Consequently every globular cylinder admits a section. The cube
$I⊗(I⊗I)$ also admits one. In both constructions a generator is its
declared variable, every term has the required strict image, and its two
immediate boundaries are literally the chosen terms. Both tensor parenthesizations give the same cube terms under renaming.

### Why the wedge construction works in all dimensions

Write $z$ for the wedge point, $u:z_0→z_1$ for its interval, and
$A=I⊗P, B=I⊗Q$. Consider the hom from $a_0$ to $b_1$, where
$a$ is strictly on the $P$ side and $b$ strictly on the $Q$ side.
Set $L=A(a_0,z_1)$, $R=B(z_0,b_1)$. Embed $U=P(a,z)$ in $L$ by
$p↦p_0;u$, and $V=Q(z,b)$ in $R$ by $q↦u;q_1$, with strict
whiskering understood in higher dimensions.

The two projections obtained by collapsing one side at a time to $z$ identify the crossing hom with the full
sub-ω-category of $L×R$ on vertices $(l,r)$ for which $l∈U$
or $r∈V$. Indeed, the inverse on Steiner tableaux is $l+r-E_u$, with
$E_u$ the tableau of $u$. The degree-zero entries are $a_0,b_1$.
In degree one one subtracts a single $u$ from each row. A path in either
factor crosses the interval exactly once, and uses $u$ precisely when
it is in the indicated embedded hom. This gives exactly the stated
positivity test on both path endpoints. In higher degrees the rows add.
The boundary equations follow by linearity, and either projection of the
formula recovers its input. Conversely each non-seam basis coefficient
is retained by its own projection, and the single interval crossing
determines the seam coefficient. [Steiner, Definitions 2.6 and 2.8](https://arxiv.org/pdf/math/0403237)

Here $U$ is a full sieve and $V$ is a full cosieve. For details of the
sign test, a nonzero positive chain of positive degree in a unital strongly
loop-free basis has a differential of both signs. A negative face of its
least supported basis element cannot cancel, and a positive face of its
greatest cannot cancel. Write a degree-$k$ row as
$0⊗p_k+1⊗q_k+e⊗r_{k-1}$. For a 2-cell ending in $U$ the equation in
the endpoint-1 copy is $dq_2+r_1=-q_1^-$. The sign test gives
$q_2=r_1=q_1^-=0$, so the source also ends by crossing at $u$.
If both endpoint paths are in $U$, the same equation in each higher row
gives $q_k^±=r_{k-1}^±=0$ for $k≥2$. What remains is exactly a cell of
$U$ whiskered by $u$. At endpoint 0 the differential is $dp_k-r_{k-1}$.
Starting in $V$ gives $dp_2-r_1=p_1^+$, and the identical sign test
gives the cosieve and fullness on that side.

Put $X=L×V, Y=U×R, D=U×V$, identifying these with their embedded
images. Define preliminary terms $S_X,S_Y$ on $X,Y$ by
horizontally composing the two given terms, using the endpoint-1 copy of
the right factor on $X$ and the endpoint-0 copy of the left factor on $Y$.
Choose $S_X$ at vertices in $X$, and $S_Y$ at all remaining vertices.
At each $d∈D$ the two terms represent the same directed edge path. They
use exactly its edges and vertices, since a one-dimensional CaTT composite
concatenates the paths of its arguments. The path is acyclic, so the terms
rename to full-support terms on its generic path context. That context
supplies a coherence $g_d:S_Y(d)→S_X(d)$ with strict image the identity.

For a positive-dimensional cell in the crossing hom, choose the following
term according to its endpoints there. Here $*_1$ is composition at
dimension one in the cylinder, allowing a 2-term to whisker a higher term.

| Endpoints in the crossing hom | Chosen term |
|---|---|
| Both in $X$ | $S_X(h)$ |
| Both in $Y∖D$ | $S_Y(h)$ |
| From $Y∖D$ to $d∈D$ | $S_Y(h)*_1g_d$ |
| From $(ip,r)∈Y∖D$ to $(l,jq)∈X∖D$ | $(S_Y(1_p,β)*_1g_d)*_1S_X(α,1_q)$, where $h=(α,β), d=(p,q)$ |

Here $i,j$ are the embeddings above, and the identities are in the
dimension of $h$. The sieve and cosieve exclude all other directions.
In the last row the strict product factors through $d$, first by
$(1_p,β)$ then by $(α,1_q)$. This proves the claimed strict image.
In ambient dimension two the displayed endpoints agree literally by the
type of $g_d$. Above dimension two both faces of $h$ have the same
path endpoints, hence the same $d$. For the horizontal composites and both uses of $*_1$, choose operations
over two globes glued along the composition dimension, specifying their
source and target recursively by the same operations on the faces.
Keep the 2-term fixed when taking a higher face of its whiskering. Each
prescribed face uses the entire corresponding boundary of the glued
arity, so CaTT's composition rule applies. Taking a face of a table entry
now gives precisely the table entry for that face. This proves literal
boundary agreement in every dimension.

The two original contexts glue along the variables of $u$ and its
endpoints. Use one section for all common identity towers. Both sections already agree on the seam generators. An exterior
cell cannot have a positive-dimensional face in the common interval, since
such a cell would have both object endpoints in that interval, where
the only paths are seam paths and the sign test excludes additional
higher rows. Cells with endpoints in one piece stay there, since
projection to the other piece retains all its non-seam coefficients and
must land in the interval. Same-level crossing homs are $U×V$, by
splitting at $z$, so ordinary horizontal composition applies. Reverse
crossings are empty and wedging with a point is the unit case. All
generators lie in the pieces. This completes the wedge proof in
Researcher Response 1. The point, suspension closure (§3 item 6), and
the wedge decomposition of a Batanin tree give the claim for every
globular cylinder. [Benjamin–Markakis, §2](https://arxiv.org/pdf/2402.01611)

### A section on every cell of the three-interval cube

Label a vertex by the subset of coordinates already set to one. A path
from that vertex is a word of distinct available coordinates, in the
order in which they change. Choose the right-associated composite $T(w)$
of its edges, the variable for a singleton and the identity for the
empty word. The six square generators act by $ji→ij$ for $j>i$, at
the initial vertex of the square. Declare each square variable with the
two corresponding path terms as its type boundaries. These orientations
follow from $d(e⊗e)=(1-0)⊗e-e⊗(1-0)$.

Every nonidentity strict 2-cell is a nonempty sequence of adjacent swaps.
Indeed the atoms freely present the strict category with their globular
boundaries. Horizontal composition of two swap sequences can be serialized
by interchange. The only possible change of order is an exchange of
disjoint swaps, which would require four distinct moves in one word.
Equivalently, on a two-coordinate interval there is just one directed
swap, and on the full interval the six permutations form the following
two directed chains with common endpoints.

$$321→231→213→123,\qquad 321→312→132→123.$$

Their full routes use different square generators, so even those two
parallel composites are distinct. This accounts for six bare squares
and twelve nonempty subroutes on three-letter words.
[Steiner, Theorem 6.1](https://arxiv.org/pdf/math/0403237)

For a swap $w→w'$, take the square variable, whiskered by the untouched
prefix or suffix if present, and call the result $s$. Precompose it
vertically with the path coherence $T(w)→∂^-s$ and postcompose with the
path coherence $∂^+s→T(w')$, omitting a correction when its endpoints
already agree syntactically. Both coherences have strict identity image
by the generic path argument above. A bare square therefore retains its
variable. For a longer route take the left-associated vertical composite
of the corrected steps. Each junction now uses the same $T(w)$ on
both sides. This applies the path correction of
§4 of the project’s invertibility notes to the whole strict 2-skeleton. [Path corrections](../../invertibility-markings.md)

Write $H^-,H^+$ for the terms for the two full routes in the order
displayed. The tensor differential gives source squares $0ee,e1e,ee0$
in route order and target squares $ee1,e0e,1ee$. Thus $H^-,H^+$
represent the correct strict faces, and both have the literal type
$T(321)→T(123)$. Declare the top variable at $H^-→H^+$ and select it.

To see that this exhausts the nonidentity 3-cells, consider any strict
composite involving the top atom. Composition at dimension zero adds only
units at the initial or terminal cube vertex. At dimension one a factor
would have to end at $321$ or begin at $123$. Every swap strictly
decreases inversion number, so the only such 2-cells are identities.
At dimension two an identity on the matching hemisphere is a unit, and
two top atoms cannot compose because their hemispheres differ. Induction
on a strict composition expression therefore gives just the top atom.
All strict cells above dimension three are identities. At any dimension
select the CaTT identity on the already chosen lower term for an identity
cell. Its two boundaries are that term literally and its strict image
is the required identity. This proves (a)–(c) for all cells. Flattening
either tensor parenthesization to the same three ordered coordinates
also makes these cube choices agree under renaming.

The generator constructs the 27-variable context, enumerates the cells and
checks the square coefficients of each route. Agda 2.8.0 verified the inferred
types against the selected boundaries for all 30 nonidentity paths, all 18
nonidentity 2-cells and the top cell. As a negative control, Agda rejected
the uncorrected first whisker on $321→231$ at the selected type, although
its two strict path boundaries agree with those of the corrected term.
[Generator](../../../tools/canonical_gray_cube.py) · [Agda certificate](../../../src/CaTTExp/Generated/CanonicalGrayCube.agda)

Q1 for arbitrary pairs and iterated tensors remains open.

## Verification of the researcher responses (2026-11-19)

*Checked by the thread "Process seven round-3 researcher responses". Verdict: **correct**. Q2 (wedge closure) is proved, so CT(I ⊗ P) and CT(P ⊗ I) hold for every finite globular P. The three-interval cube holds for both parenthesizations. Q1 for general pairs and iterated tensors stays open.*

- **Sieve and cosieve.** The sign test is correct: for a nonzero positive chain w in a strongly loop-free unital basis, the least supported generator's negative face cannot cancel, and the greatest one's positive face cannot either. Equations (3) for the two endpoint copies are the Leibniz formula. They give the sieve and cosieve conditions and fullness row by row.
- **H ≅ G.** On tableaux the inverse is l + r − E_u. Degree-one rows are positive exactly when l ∈ iU₀ or r ∈ jV₀, since every crossing path uses the seam edge exactly once, and higher rows add. I sanity-checked P = Q = D¹ (the 1 × 2 grid): G has 3 vertices and 2 generating 2-cells plus their composite, which matches the grid hom.
- **The case table.** It is exhaustive, which I checked from the sieve and cosieve properties. Cells from X to Y° are impossible: the first component would force l ∈ iU, and the second would force the target into D. Cells from D to Y° land in D. X and Y are full subcategories because i and j are full.
- **Literal boundaries.**
  - γ_d is a coherence over the generic path context of p₀ u q₁. By the support lemma, a 1-term denoting a path uses exactly its edges and vertices, and the path is acyclic, so the coherence rule applies.
  - W_m, A_m and V_m are composition heads over D^m ∨_k D^{m′} with recursively prescribed types. Each prescribed face uses exactly the corresponding boundary of the arity, so the composition-case condition holds.
  - Faces of a crossing cell keep its 0-endpoints, hence its case and its d, so (18) and (20) hold as raw syntax.
- **Gluing.** Exterior cells have no positive-dimensional face in the common interval. Same-level crossing homs are U × V, and reverse crossings are empty.
- **The cube (Response 2).** I installed Agda 2.6.3 in the checking container. `src/CaTTExp/Generated/CanonicalGrayCube.agda` (generated by `tools/canonical_gray_cube.py`) type-checks under `--safe`. Its checks are `infer c58 t ≡ just (A, …)` by `refl`, and `infer` (`CheckWith.agda`) also certifies the 27-variable context. That covers all 30 nonidentity paths, 18 nonidentity 2-cells and the top cell. The exhaustion argument (inversion number strictly decreases, and the two top routes use distinct squares) is correct.
- **MARK's note.** The layered-term failure on D¹ ⊗ D¹ ⊗ D¹ (`canonical-gray-terms.md` §8) concerns only layered choices. It is not a candidate counterexample now that path corrections give the cube.

**Open after this response.** CT for general pairs Θ ⊗ Δ with both factors positive-dimensional and non-interval. This includes I ⊗ K for non-globular K beyond the cube, and associativity-compatible iterated tensors. The response pins the obstacle: across a wedge of the second factor, the subtracted tableau is a varying cell of the common Θ copy, so positivity constraints appear in higher degrees and the intermediate vertex is no longer fixed under higher faces. The follow-up prompt is `outbox/canonical-gray-terms-r3.md` (answered 2026-11-19: `answered/canonical-gray-terms-r3-2026-11-19.md`).
