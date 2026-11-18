# A formalisation-friendly proof that strict ω-categories model CaTT

*This problem is self-contained. It assumes no knowledge of the project that posed it. We are looking for a proof structure suited to a proof assistant, not a new theorem: the result is known.*

## Background

**Strict ω-categories, single-set definition** (Street 1987; Steiner, arXiv math/0403237, Def. 2.1). A strict ω-category is a set C with maps s_n, t_n : C → C for n ∈ ℕ and partial operations x #_n y, defined exactly when t_n x = s_n y. The axioms are:

- **Boundary maps.**
  - s_m s_n x = s_m t_n x = s_m x for m ≤ n.
  - s_m s_n x = s_n x = t_m s_n x for m > n, and likewise for t.
  - Every x has some n with s_n x = x.
- **Units.** s_n x #_n x = x = x #_n t_n x.
- **Boundaries of composites.**
  - s_n(x #_n y) = s_n x and t_n(x #_n y) = t_n y.
  - For m > n: s_m(x #_n y) = s_m x #_n s_m y, and likewise for t_m.
  - For m < n: s_m(x #_n y) = s_m x, and likewise for t_m.
- **Associativity** of each #_n.
- **Interchange.** For m < n: (x #_n y) #_m (z #_n w) = (x #_m z) #_n (y #_m w), whenever both sides are defined.

**CaTT** (Finster–Mimram, LICS 2017). This is a dependent type theory.
- Types are ⋆ and `s →_A u`.
- Terms are variables and `coh Θ (s →_A u) σ`. Here Θ is a *pasting context*, a context presenting a globular pasting diagram, given by the rules
  - ps-start: `x : ⋆ ⊢ps x : ⋆`.
  - ps-extend: from `Γ ⊢ps x : A`, derive `Γ, y : A, f : x →_A y ⊢ps f : x →_A y`.
  - ps-drop: from `Γ ⊢ps f : x →_A y`, derive `Γ ⊢ps y : A`.
  - finish: from `Γ ⊢ps x : ⋆`, conclude that Γ is a pasting context.
- The side condition on s and u is one of two cases.
  - Either both s and u (with A) use all variables of Θ;
  - or s uses exactly the variables of the source boundary ∂⁻Θ, u those of the target boundary ∂⁺Θ, and dim Θ = dim A + 1.
- σ is a substitution into Θ.
- Substitution is strict and syntactic.

**What we have.** We have a full, checked proof of soundness in the strict ω-categories ν(K) of Steiner, for every chain complex K with a basis. It includes the following.
- Every derivable term over a pasting context Θ, evaluated at the generic environment of ν(λΘ), is a cell of ν(λΘ).
- The top chain of a term t : B, at that environment, is the set of variables of t of dimension dim B.
- The coh over Θ in an environment ρ is the image of the coh at the generic environment under the chain map induced by ρ.

## Question

Give a proof, organised for formalisation, of the following theorem.

**Theorem.** Let C be a strict ω-category in the single-set sense.
- Let `Γ ⊢ t : A` be derivable in CaTT.
- Let ρ assign to each variable of Γ a cell of C, compatibly with the boundaries prescribed by Γ.

Then the evident interpretation ⟦t⟧ρ exists. Coherences are interpreted as pasting composites of their substitutions, or as the identity on such composites. When A = s →_B u, the interpretation satisfies s_{dim B} ⟦t⟧ρ = ⟦s⟧ρ and t_{dim B} ⟦t⟧ρ = ⟦u⟧ρ.

Our current plan, with five steps:
1. Labelled Batanin trees with a fold-defined composite.
2. A boundary lemma.
3. A binary pasting lemma: comp(S₁ ⊔_k S₂) = comp S₁ #_k comp S₂.
4. A functor F_λ : ν(λΘ) → C, sending a cell to the composite of its support.
5. Interpretation equals F_λ applied to the ν-interpretation.

Step 4 needs a dictionary between cells of ν(λΘ) and sub-pasting diagrams of Θ. Building that dictionary is a lot of combinatorics.

1. Is there a shorter route that avoids step 4? For instance:
   - a direct induction on CaTT derivations, with a stronger invariant;
   - a definition of the composite of a pasting context directly by recursion on ps-derivations, for which "composite of composites is composite" has a short inductive proof;
   - using only the binary pasting lemma.
2. If step 4 is needed, what is the most economical description of cells of the free strict ω-category on a globular pasting diagram, for the purpose of defining F_λ and proving it preserves #_k?
3. Which interchange instances are actually used? A list of the axioms each step uses would help us size the formalisation.

## What would count as an answer

A sequence of lemmas, each with a proof sketch. Each proof should be by structural induction on trees, ps-derivations or CaTT derivations, with the axioms used named at each step. A reference to a source whose proof has this shape would also do.

## Literature status (searched 2026-11-18)

- Ara's thesis, Ch. 5, §5.1, proves that Θ is a pseudo-coherator for ∞-categories: unique lifts of admissible pairs.
- Ara (arXiv 1212.3085) proves the groupoid case.
- Steiner (arXiv math/0403237) proves Thms 5.6, 5.7 and 6.1: ν(K) is presented by its atoms for loop-free unital bases.
- Leinster (arXiv math/0305049) gives, in App. F and §8.1, the free strict ω-category monad via pasting diagrams.
- Power gives the n-categorical pasting theorem (1991).
- Benjamin–Finster–Mimram (arXiv 2106.04475) show that CaTT models are Grothendieck–Maltsiniotis weak ω-categories.
- None of these is organised as the induction asked for here.

# Researcher Response

**Yes. Step 4 can be avoided.** Define a strict ω-category \(N(T)\) directly from a finite planar tree \(T\), using intervals and recursively defined tuples. Its generator-support function is injective, with a short proof by tree induction. The stronger invariant needed for CaTT is then

\[
\operatorname{supp}\bigl(\llbracket t\rrbracket_{\eta_\Theta}\bigr)
=
\operatorname{FV}(t)\cup\operatorname{FV}(A),
\qquad \Theta\vdash t:A,
\]

where \(\eta_\Theta\) is the generic labeling in \(N(T_\Theta)\).

Crucially, this support invariant is needed **only for terms over pasting contexts at their generic labelings**. Typing, substitution, and naturality are proved for arbitrary strict targets and environments.

Below is a complete proof structure. Section 5 gives a second route that reuses your checked \(\nu\)-soundness proof: the same interval description can be extracted directly from the tableau equations, without a dictionary between supports and sub-pasting diagrams.

## 1. Two conventions to make explicit

First, the standard single-set globularity equation is

\[
d_m^\beta d_n^\alpha x=
\begin{cases}
d_m^\beta x,&m<n,\\
d_n^\alpha x,&m\ge n,
\end{cases}
\qquad
d_n^-=s_n,\quad d_n^+=t_n.
\]

Thus the split in the question should be \(m<n\) versus \(m\ge n\). With the stated equal-index equations and units, one instead forces \(s_nx=t_nx\). Steiner’s Definition 2.1 has the standard split above. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

Second, a type-compatible environment includes a dimension bound. Put

\[
C_n=\{x\in C:s_nx=x\}.
\]

Globularity implies that \(t_nx=x\) as well. Interpret types by

\[
\llbracket\star\rrbracket_\rho=C_0,
\]

\[
\llbracket s\to_Au\rrbracket_\rho
=
\left\{
x\in C_{\dim A+1}:
s_{\dim A}x=\llbracket s\rrbracket_\rho,\
t_{\dim A}x=\llbracket u\rrbracket_\rho
\right\}.
\]

Without the dimension bound, even assigning a nonidentity arrow to \(x:\star\) would prevent interpreting the identity term at \(x\).

In the single-set convention, viewing \(x\in C_n\) as an identity in a higher dimension does not introduce a new element.

## 2. Trees and explicit strict cells

### Lemma 1 — Parse a ps-derivation into a tree

Use finite ordered trees

\[
T=[T_1,\ldots,T_r],
\]

including the leaf \([]\).

Define a finite globular set \(G(T)\) recursively:

\[
G(T)_0=\{v_0,\ldots,v_r\},
\qquad
G(T)_{n+1}
=
\bigsqcup_{i=1}^{r}\operatorname{tag}_i G(T_i)_n.
\]

For \(g\in G(T_i)_0\), the generator \(\operatorname{tag}_i g\) has source \(v_{i-1}\) and target \(v_i\). For positive-dimensional \(g\), its source and target are obtained by tagging those of \(g\).

There is a direct parser for the supplied ps-rules.

Maintain a tree and an active vertex at depth \(d\) on its rightmost branch. A vertex at depth \(d\) denotes a \(d\)-dimensional generator of \(G(T)\).

- **ps-start:** use the leaf, with its sole vertex active.
- **ps-extend at dimension \(d\):** append a leaf to the node whose last vertex is active. This adds precisely a new \(d\)-generator \(y\) and a new \((d+1)\)-generator \(f:x\to y\). Move the active position to \(f\).
- **ps-drop:** move from the active vertex to its immediate target, one level upward.
- **finish:** discard the active position.

Formally, define the tree modification by

\[
\operatorname{grow}_0[T_1,\ldots,T_r]
=
[T_1,\ldots,T_r,[]],
\]

and let \(\operatorname{grow}_{d+1}\) apply \(\operatorname{grow}_d\) to the last subtree. Its domain condition is exactly the existence of the active position at depth \(d+1\).

**Proof.** Induct on the ps-derivation, maintaining:

1. a dimension-preserving bijection from context variables to \(G(T)\);
2. preservation of their declared sources and targets;
3. identification of the active variable with the active tree vertex.

The extension case adds exactly the two generators specified above. The drop case changes only the active position.

If `coh` stores the context rather than a ps-proof, also prove proof independence. Induct on context length: drops and finish do not change the tree, while the final pair of declarations \(y:A,f:x\to_Ay\) determines the last growth operation and its depth.

**Axioms of \(C\) used:** none.

This supplies the tree conversion directly from the rules. Finster–Mimram’s Proposition 37 gives the corresponding ps-context/pasting-scheme identification. [arxiv.org](https://arxiv.org/pdf/1706.02866?utm_source=chatgpt.com)

### Lemma 2 — Define \(N(T)\) by intervals and tuples

For \(T=[T_1,\ldots,T_r]\), define the **single set** \(N(T)\) by the following constructors:

\[
v_a\qquad(0\le a\le r),
\]

and

\[
(a,b;x_{a+1},\ldots,x_b),
\qquad
0\le a<b\le r,\quad x_i\in N(T_i).
\]

Only nonempty intervals are a second constructor. An empty interval is the vertex \(v_a\), not an additional element.

Define boundaries by

\[
d_n^\varepsilon(v_a)=v_a,
\]

\[
s_0(a,b;\mathbf x)=v_a,
\qquad
t_0(a,b;\mathbf x)=v_b,
\]

and

\[
d_{n+1}^\varepsilon(a,b;\mathbf x)
=
\bigl(a,b;(d_n^\varepsilon x_i)_{a<i\le b}\bigr).
\]

Define \(0\)-composition by concatenation:

\[
(a,b;\mathbf x)\#_0(b,c;\mathbf y)
=
(a,c;\mathbf x,\mathbf y),
\]

with vertices acting as the corresponding empty intervals.

For \(k>0\), two nonvertex cells are \(k\)-composable precisely when their outer endpoints agree and their coordinates are \((k-1)\)-composable. Set

\[
(a,b;\mathbf x)\#_k(a,b;\mathbf y)
=
\bigl(a,b;(x_i\#_{k-1}y_i)_{a<i\le b}\bigr).
\]

The remaining positive-level composites are \(v_a\#_kv_a=v_a\).

Then \(N(T)\) is a strict ω-category.

**Proof.** Induct on \(T\).

- Globularity and composite-boundary equations reduce to the corresponding coordinate equations, except at level \(0\), where they are endpoint calculations.
- Units and associativity of \(\#_0\) are the empty-list and concatenation laws.
- Units and associativity at positive levels hold coordinatewise.
- For interchange with lower index \(0\), the equation says that coordinatewise composition commutes with concatenation.
- For interchange with both indices positive, apply the subtree induction hypothesis coordinatewise, decreasing both indices by one.

Every cell has finite dimension, with

\[
\dim(v_a)=0,\qquad
\dim(a,b;\mathbf x)=1+\max_{a<i\le b}\dim(x_i).
\]

**Axioms of \(C\) used:** none. These are verifications of the explicitly defined operations.

This is the specialization to a linear sequence of adjacent homs of the path-product construction in Leinster’s Appendix F.1.1. Appendix F.2 then gives the dimension induction for free strict categories. [sas.rochester.edu](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/leinster-book.pdf?utm_source=chatgpt.com)

### Lemma 3 — Evaluate tuples in any strict target

Define the generic generator labeling

\[
\eta_T:G(T)\longrightarrow N(T)
\]

by

\[
\eta_T(v_a)=v_a,
\qquad
\eta_T(\operatorname{tag}_ig)
=
(i-1,i;\eta_{T_i}(g)).
\]

Let \(\rho:G(T)\to C\) preserve dimensions and generator boundaries. There is a fold-defined strict functor

\[
E_{T,\rho}:N(T)\longrightarrow C
\]

extending \(\rho\).

**Definition.** Write \(a_i=\rho(v_i)\). The labeling of the \(i\)-th subtree takes values in

\[
C(a_{i-1},a_i)
=
\{x\in C:s_0x=a_{i-1},\ t_0x=a_i\},
\]

with boundary and composition indices shifted down by one.

By tree induction, obtain

\[
E_i:N(T_i)\longrightarrow C(a_{i-1},a_i).
\]

Set

\[
E_{T,\rho}(v_i)=a_i
\]

and

\[
E_{T,\rho}(a,b;\mathbf x)
=
E_{a+1}(x_{a+1})\#_0\cdots\#_0E_b(x_b).
\tag{1}
\]

**Proof of strictness.**

The \(0\)-boundaries follow from the endpoints of the factors. Higher boundaries follow by distributing the boundary map over the \(\#_0\)-fold and applying the subtree induction hypotheses.

Preservation of \(\#_0\) is associativity and units.

For \(k>0\), the required calculation is

\[
\left(\mathop{\#_0}_{i=a+1}^{b}u_i\right)
\#_k
\left(\mathop{\#_0}_{i=a+1}^{b}w_i\right)
=
\mathop{\#_0}_{i=a+1}^{b}(u_i\#_kw_i).
\tag{2}
\]

Prove (2) by induction on the interval length. Length one is immediate. Each extension uses one interchange equation between \(\#_0\) and \(\#_k\). The vertex case is a unit equation. The boundary equations establish composability before interchange is invoked.

The generator-extension equation follows immediately from singleton intervals and the subtree induction hypothesis.

Two further consequences will be useful:

\[
H\circ E_{T,\rho}=E_{T,H\rho}
\tag{3}
\]

for every strict functor \(H:C\to D\), by induction on the fold; and \(E_{T,\rho}\) is the unique strict functor extending \(\rho\). For uniqueness, restrict to each adjacent hom \(N(T_i)\), apply the subtree induction hypothesis, and then use the decomposition of every interval into singleton intervals.

**Axioms used:** globularity, dimension bounds, composite-boundary equations, units, associativity, and precisely the rectangular interchange instances in (2).

## 3. The stronger invariant: recursive generator support

### Lemma 4 — Support is injective in \(N(T)\)

Define \(S_T:N(T)\to\mathcal P(G(T))\) by

\[
S_T(v_a)=\{v_a\},
\]

\[
S_T(a,b;\mathbf x)
=
\{v_a,\ldots,v_b\}
\;\cup\!
\bigcup_{i=a+1}^{b}\operatorname{tag}_iS_{T_i}(x_i).
\tag{4}
\]

Thus support records **all intermediate vertices at every recursive level**.

The following hold:

\[
S_T(d_n^\varepsilon x)\subseteq S_T(x),
\tag{5}
\]

\[
S_T(x\#_ny)=S_T(x)\cup S_T(y),
\tag{6}
\]

\[
\dim(x)=\max\{\deg(g):g\in S_T(x)\},
\tag{7}
\]

and

\[
S_T(x)=S_T(y)\Longrightarrow x=y.
\tag{8}
\]

**Proof.** Induct on \(T\).

Equations (5) and (7) follow from the boundary and dimension recursions. For (6), level-zero composition concatenates intervals; positive-level composition reduces to the coordinate induction hypotheses.

For injectivity, intersect support with \(G(T)_0\). This identifies whether the cell is a vertex or a nonempty interval, and in the latter case recovers \(a,b\). Intersecting with each disjoint tagged generator set then recovers every \(S_{T_i}(x_i)\). Apply the induction hypothesis to recover each \(x_i\).

No characterization of which subsets are supports is required.

**Axioms of \(C\) used:** none.

Support injectivity is used only in \(N(T)\).

### Lemma 5 — The full composite and its boundaries

Define

\[
c_{[]} = v_0,
\]

\[
c_{[T_1,\ldots,T_r]}
=
(0,r;c_{T_1},\ldots,c_{T_r})
\qquad(r>0).
\tag{9}
\]

Then

\[
S_T(c_T)=G(T),
\]

so \(c_T\) is the unique cell of full support.

For boundary supports, define

\[
B_0^-(T)=\{v_0\},
\qquad
B_0^+(T)=\{v_r\},
\]

\[
B_{n+1}^\varepsilon(T)
=
\{v_0,\ldots,v_r\}
\cup
\bigcup_{i=1}^{r}\operatorname{tag}_iB_n^\varepsilon(T_i).
\tag{10}
\]

Then

\[
S_T(s_nc_T)=B_n^-(T),
\qquad
S_T(t_nc_T)=B_n^+(T).
\tag{11}
\]

Under Lemma 1’s variable identification, if \(h=\dim T>0\), these give

\[
B_{h-1}^-(T)=\operatorname{Var}(\partial^-\Theta),
\qquad
B_{h-1}^+(T)=\operatorname{Var}(\partial^+\Theta).
\tag{12}
\]

**Proof.** Full support and (11) follow immediately by tree induction.

For (12), verify compatibility with the ps-parser. At a fixed boundary level \(n\), an extension at active dimension \(d\):

- retains both new declarations when \(d<n\);
- leaves the source boundary unchanged and replaces its active target \(n\)-generator by the new one when \(d=n\);
- leaves both \(n\)-boundaries unchanged when \(d>n\).

These are exactly the effects of (10). Drops and finish change neither the tree nor its boundary sets.

**Axioms of \(C\) used:** none.

Consequently, the labeled composite can simply be defined by

\[
\operatorname{comp}_T(\rho)=E_{T,\rho}(c_T).
\tag{13}
\]

### Lemma 6 — Support under evaluation

For any compatible labeling \(\rho:G(T)\to N(U)\) and any \(x\in N(T)\),

\[
S_U(E_{T,\rho}(x))
=
\bigcup_{g\in S_T(x)}S_U(\rho(g)).
\tag{14}
\]

This is the replacement for a general theorem about substitution of pasting shapes.

**Proof.** Construct a specific expression for \(x\) in the generating cells:

- a vertex gives its generator;
- an interval gives the \(\#_0\)-fold of its lifted child expressions;
- lifting tags each generator and increases each composition index by one.

Inductively, the union of the globular closures of the generators used in that expression is exactly \(S_T(x)\).

Evaluate the expression in \(N(U)\). Equation (6) makes its support the union of the supports of its generator values. Enlarging the set of those generators to its globular closure does not change that union: \(\rho\) preserves generator boundaries, and (5) says that the support of a boundary is a subset of the support of the cell.

This proves (14), including when \(\rho\) identifies generators or sends positive-dimensional generators to identities.

**Axioms used:** the already-proved strictness of \(E\), together with (5)–(6).

Your binary pasting lemma can now be derived rather than used as a prerequisite. For a supplied gluing \(T=T_1\sqcup_kT_2\), evaluate the two principal cells in \(N(T)\) along the generator inclusions. Their \(k\)-composite has support

\[
G(T_1)\cup G(T_2)=G(T).
\]

By injectivity it equals \(c_T\). Applying \(E_{T,\rho}\) gives the desired binary pasting equation.

## 4. The CaTT induction

Write

\[
V_P(t:A)=\operatorname{FV}(t)\cup\operatorname{FV}(A)
\]

for the typed free-variable set appearing in the side conditions.

The required induction package is:

1. interpretation exists and satisfies its type, for every strict target;
2. interpretation commutes with syntactic substitution;
3. strict functors commute with term interpretation;
4. for every pasting context \(P\), at its generic labeling,
   \[
   S_P\bigl(\llbracket t\rrbracket_{\eta_P}\bigr)=V_P(t:A).
   \tag{15}
   \]

There is no need to assert (15) for arbitrary environments or arbitrary contexts.

### Organizing the recursion without circularity

One formalisation arrangement is to stage coherence symbols by their generic annotations.

For a symbol

\[
q=(\Theta,\ s\to_Au),
\]

give \(q\) rank one greater than the maximum rank of symbols in \(s,u,A\). Symbols in the application substitution are not part of \(q\)’s rank.

A stage consists of all finite terms using symbols up to a given rank. Each stage is closed under substitution, because substitution changes the arguments of a coherence application and leaves its generic symbol unchanged.

At each stage:

1. use the preceding stage to interpret the generic annotations of new symbols;
2. define all new symbol operations;
3. prove the four assertions above by structural induction on terms, types, and substitutions using those operations.

Every finite CaTT derivation belongs to a finite stage.

### Lemma 7 — The generic endpoints have the required strict values

Let

\[
q=(\Theta,\ s\to_Au),\qquad d=\dim A,
\]

and let \(T=T_\Theta\).

The generic interpretations of \(s,u\) are already available when \(q\) is installed.

#### Full-support case

By (15),

\[
S_T(\llbracket s\rrbracket_{\eta_T})
=
S_T(\llbracket u\rrbracket_{\eta_T})
=
G(T).
\]

Therefore Lemmas 4–5 give

\[
\llbracket s\rrbracket_{\eta_T}
=
c_T
=
\llbracket u\rrbracket_{\eta_T}.
\tag{16}
\]

The endpoints have dimension at most \(d\), so (7) gives \(\dim T\le d\). Hence

\[
s_dc_T=c_T=t_dc_T.
\tag{17}
\]

Thus the required \((d+1)\)-cell is the identity on \(c_T\), which is the same single-set element \(c_T\).

#### Composition case

Here \(\dim T=d+1\). By (15), the side conditions, and (11)–(12),

\[
S_T(\llbracket s\rrbracket_{\eta_T})
=
B_d^-(T)
=
S_T(s_dc_T),
\]

and similarly on the target side. Injectivity gives

\[
\llbracket s\rrbracket_{\eta_T}=s_dc_T,
\qquad
\llbracket u\rrbracket_{\eta_T}=t_dc_T.
\tag{18}
\]

Thus \(c_T\) again has exactly the required boundaries.

**Axioms used:** the previously established generic interpretation, support injectivity, and stabilization of boundaries above a cell’s dimension.

### Lemma 8 — Define the coherence in an arbitrary target

For a compatible labeling \(\lambda:\Theta\to C\), define

\[
q_C(\lambda)=E_{T,\lambda}(c_T).
\tag{19}
\]

For an application with substitution \(\sigma:\Gamma\to\Theta\), set

\[
\boxed{
\llbracket\operatorname{coh}_{\Theta,s\to_Au}[\sigma]\rrbracket_\rho
=
E_{T,\llbracket\sigma\rrbracket_\rho}(c_T).
}
\tag{20}
\]

This is the same fold in both cases. Lemma 7 determines whether it is being used as a composition or as an identity in the required dimension.

**Proof of typing.** Write \(\lambda=\llbracket\sigma\rrbracket_\rho\). Strictness of \(E\), Lemma 7, and naturality of the previously interpreted endpoint terms give

\[
\begin{aligned}
s_dE_{T,\lambda}(c_T)
&=E_{T,\lambda}(s_dc_T)\\
&=E_{T,\lambda}(\llbracket s\rrbracket_{\eta_T})\\
&=\llbracket s\rrbracket_\lambda.
\end{aligned}
\tag{21}
\]

The last expression equals \(\llbracket s[\sigma]\rrbracket_\rho\) by the substitution lemma. The target calculation is identical. The dimension bound follows from strictness of \(E\) and the bound on \(c_T\).

### Lemma 9 — Close the induction package

The new operation satisfies naturality:

\[
H(q_C(\lambda))
=
H(E_{T,\lambda}(c_T))
=
E_{T,H\lambda}(c_T)
=
q_D(H\lambda)
\]

by (3).

Syntactic substitution is proved by structural induction. Its coherence step is precisely

\[
\begin{aligned}
\llbracket q[\sigma][\delta]\rrbracket_\rho
&=E_{T,\llbracket\sigma\circ\delta\rrbracket_\rho}(c_T)\\
&=E_{T,\llbracket\sigma\rrbracket_{\llbracket\delta\rrbracket_\rho}}(c_T)\\
&=\llbracket q[\sigma]\rrbracket_{\llbracket\delta\rrbracket_\rho}.
\end{aligned}
\tag{22}
\]

The middle equality is the induction hypothesis on the substitution entries. No substitution-of-trees theorem is involved.

It remains to establish the generic support invariant (15).

For a variable \(x:A_x\) in a pasting context \(P\),

\[
S_P(\eta_P(x))
=
\{x\}\cup\operatorname{FV}(A_x).
\]

This is the globular closure of \(x\), by the generator definition.

For a coherence application \(q[\sigma]\) over \(P\), equations (14) and \(S_T(c_T)=G(T)\) give

\[
S_P(\llbracket q[\sigma]\rrbracket_{\eta_P})
=
\bigcup_{x\in\Theta}
S_P(\llbracket\sigma(x)\rrbracket_{\eta_P}).
\]

Apply the structural induction hypothesis to each substitution term:

\[
=
\bigcup_{x:A_x\in\Theta}
V_P(\sigma(x):A_x[\sigma]).
\tag{23}
\]

This union is exactly \(\operatorname{FV}(\sigma)\). Every substituted declaration type uses variables supplied by the substitution, and every substitution term contributes its own free variables. Also,

\[
\operatorname{FV}((s\to_Au)[\sigma])
\subseteq\operatorname{FV}(\sigma).
\]

Since the free variables of the coherence application are those of its substitution, (23) is exactly

\[
V_P(q[\sigma]:(s\to_Au)[\sigma]).
\]

This closes (15), and hence the induction.

**Conclusion.** Formula (20) interprets every coherence by the labeled tree composite, or by its identity at the required dimension. Equation (21), followed by (22), proves the requested boundary equations for arbitrary contexts and compatible environments.

## 5. Reusing the checked \(\nu\)-proof

If preserving your existing proof is the priority, the economical replacement for the proposed support dictionary is a **direct interval decomposition of \(\nu(\lambda\Theta)\)**.

Here are the additional lemmas needed.

### Lemma 10 — Write the tree complex recursively

For \(T=[T_1,\ldots,T_r]\), write \(K(T)=\lambda\Theta\) as

\[
K(T)_0=\mathbb Z\{v_0,\ldots,v_r\},
\qquad
K(T)_{q+1}
=
\bigoplus_{i=1}^{r}\sigma_iK(T_i)_q.
\]

Its differential is

\[
\partial(\sigma_i z)=
\begin{cases}
\epsilon(z)(v_i-v_{i-1}),&z\in K(T_i)_0,\\
\sigma_i(\partial z),&\deg z>0.
\end{cases}
\tag{24}
\]

The tags \(\sigma_i\) increase degree by one; there is no sign in the second clause.

This is Steiner’s construction \(V(r,K)\) in *Simple omega-categories and chain complexes*, §5. [arxiv.org](https://arxiv.org/pdf/math/0608680?utm_source=chatgpt.com)

### Lemma 11 — Positive cycles vanish

For these complexes,

\[
z\ge0,\quad \epsilon z=0,\quad \deg z=0
\quad\Longrightarrow\quad z=0,
\]

and

\[
z\ge0,\quad \partial z=0,\quad \deg z>0
\quad\Longrightarrow\quad z=0.
\tag{25}
\]

**Proof.** The degree-zero statement follows because every basis vector has augmentation one.

Induct on the tree for positive degrees. In degree one, write \(z=\sum_i\sigma_i z_i\). The equation

\[
0=\sum_i\epsilon(z_i)(v_i-v_{i-1})
\]

forces every \(\epsilon(z_i)=0\), since the path-edge vectors are linearly independent. Then each \(z_i=0\).

In higher degrees, the direct-sum projections give \(\partial z_i=0\), and the subtree induction hypothesis applies.

### Lemma 12 — Decode a \(\nu\)-tableau into an interval tuple

Let \(x\in\nu K(T)\). Its degree-zero rows are uniquely

\[
x_0^-=v_a,\qquad x_0^+=v_b.
\]

Write

\[
x_{q+1}^{\varepsilon}
=
\sum_i\sigma_i y_{i,q}^{\varepsilon}.
\]

The degree-one tableau equation is

\[
\sum_i\epsilon(y_{i,0}^{\varepsilon})(v_i-v_{i-1})
=
v_b-v_a.
\]

Its unique solution is

\[
\epsilon(y_{i,0}^{\varepsilon})
=
\mathbf1_{a<i}-\mathbf1_{b<i}.
\tag{26}
\]

Nonnegativity implies \(a\le b\), and the coefficient is one exactly when \(a<i\le b\).

Outside that interval, the degree-zero positivity lemma gives \(y_{i,0}^\varepsilon=0\). The remaining tableau equations and (25), successively, make every higher row zero there.

For \(a<i\le b\), the rows \(y_i\) form a cell of \(\nu K(T_i)\). Conversely, any such tuple gives a tableau by the displayed summation formula.

Thus

\[
\nu K(T)(v_a,v_b)\cong
\begin{cases}
\varnothing,&a>b,\\
\mathbf1,&a=b,\\
\displaystyle\prod_{i=a+1}^{b}\nu K(T_i),&a<b.
\end{cases}
\tag{27}
\]

The tableau formula

\[
x\#_ky=x+y-t_kx
\]

then gives concatenation at level zero and coordinatewise composition at positive levels. Boundaries are likewise coordinatewise.

This identifies \(\nu K(T)\) with the explicit \(N(T)\) above, by tree induction. It proves the necessary generation and uniqueness statements directly from tableaux.

### Transfer the checked semantics

Use Lemma 3’s fold to obtain

\[
F_\rho:\nu K(T)\longrightarrow C.
\]

Interpret a coherence by applying \(F_\rho\) to its already-checked generic \(\nu\)-value.

For a substitution inducing a chain map \(h:K(S)\to K(T)\), the key equation is

\[
F_\rho\circ\nu(h)=F_\lambda,
\tag{28}
\]

where \(\lambda\) assigns each generator of \(S\) its image under the left-hand side. Both sides are strict functors agreeing on generators, so evaluation uniqueness proves (28). Your checked chain-map naturality then gives the term comparison by induction on terms and substitutions.

This route retains your steps 4–5 as maps, but replaces the combinatorial support dictionary with the linear equation (26) and a positive-cycle induction.

One distinction matters: **top-chain equality alone is insufficient for cell equality**. A 2-cell \(\alpha\) and its whiskering \(\alpha\#_0h\) have the same top 2-chain when \(h\) is a 1-cell. The direct proof in §§2–4 establishes canonical composites using recursive support; the tableau route transfers the precise generic cells already constructed in your checked model.

## 6. Interchange and the formalisation dependency list

For the direct route, the dependencies are:

| Step | Induction | Strict-target axioms used |
|---|---|---|
| ps-context to tree | ps-derivation | None |
| Definition and laws of \(N(T)\) | Tree and finite lists | None externally; the laws are verified |
| Evaluation: domains and boundaries | Tree and fold length | Globularity, dimension bounds, composite-boundary equations |
| Evaluation preserves \(\#_0\) | Fold length | Associativity and units |
| Evaluation preserves \(\#_k\), \(k>0\) | Tree and fold length | Subtree hypotheses and interchange between \(\#_0,\#_k\) |
| Support, injectivity, principal boundaries | Tree | None externally |
| Support under evaluation | Canonical generator expression | Strict evaluation; support-union and boundary-inclusion lemmas |
| CaTT coherence typing | Generic annotations, then syntax | Strict evaluation and boundary stabilization |
| Substitution and naturality | Terms and substitutions | Evaluation formula and preservation by strict functors |

At recursion depth \(m\), the local interchange between \(\#_0\) and \(\#_k\) becomes interchange between

\[
\#_m\quad\text{and}\quad\#_{m+k}
\]

in the original category. Therefore **this proof uses the family for every pair \(m<n\)**. It does not establish that adjacent-index interchange alone is sufficient.

Every use has the ordinary \(2\times2\) rectangular form. For an interval of length \(\ell>0\), the fold-distribution proof uses \(\ell-1\) such equations at that tree level. No separate theorem about rearranging arbitrary pasting expressions is required.

The essential replacement for your proposed dictionary is therefore:

\[
\boxed{
\text{recursive interval tuples}
\;+\;
\text{injective recursive support}
}
\]

for the direct CaTT proof, or

\[
\boxed{
\text{recursive interval tuples}
\;+\;
\text{the path-flow equation (26)}
}
\]

when reusing the checked \(\nu\)-proof.
