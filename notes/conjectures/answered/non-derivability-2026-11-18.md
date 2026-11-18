# Three non-derivability questions for a coherence-style theory of ω-categories with limits

*A self-contained problem. No knowledge of the project that posed it is assumed. The three questions are independent. The smallest one is Question 3 (effectiveness of quotients), which is a question about 1-categories of sets inside a higher setting.*

## Background

**The base theory.** Fix a dependent type theory 𝕋 for weak ω-categories in the style of CaTT (Finster–Mimram, LICS 2017): contexts of typed variables (objects, and cells between cells), and one term former `coh` producing cells between parallel composites over pasting contexts. Add to it, as rules stated by universal properties witnessed by cells (never by definitional equalities, and with no universe):
- **finite limits** in the ambient (∞,ω)-category of ω-categories: a terminal object ⊤, pullbacks, and *cotensors* `[⟦D⟧, C]` by finite shapes D;
- **finite colimits**: pushouts, coequalisers, coproducts, and lax colimits of finite diagrams;
- **R-A (free objects on finite computads):** for each finite context Γ, an object ⟦Γ⟧ such that maps `⟦Γ⟧ → C` correspond to substitutions Γ → C (up to cells at every level). In particular, for the loop `L = (x : ⋆, s : x → x)`, maps `⟦L⟧ → C` correspond to an object of C with an endo-1-cell.

Write `Hom_C(a, b)` for the pullback of `[⟦D¹⟧, C] → C × C` along `(a, b)`. Put `N := Hom_{⟦L⟧}(x, x)`, with `zero := 1_x` and `succ := – ; s`. Semantically (in the (∞,ω)-category of (∞,ω)-categories), ⟦L⟧ is the free category on one loop and N is the discrete set ℕ (the free weak ω-category on a graph is the free category on it).

**Truncation levels.** An object C is *n-truncated* (C trunc n) when parallel cells into C of level ≥ n + 1 are connected and cells of level n + 1 are invertible. Sets are the 0-truncated objects. A *truncation rule* `Trunc_n` gives for each X a reflection `|–| : X → ‖X‖_n` onto n-truncated objects (existence of extensions, and of cells between extensions agreeing on X).

**Derivability.** A rule is *derivable* if every instance of its conclusion is a term of 𝕋 (with the stated additional rules). Non-derivability can be shown by a model of the rules in which the conclusion fails, or by a normal-form argument on the syntax.

## Statement

**Question 1 (recursion on a hom object).** In 𝕋 (finite limits, finite colimits, R-A), is the recursion principle for N derivable? That is: for every object A, point `a : ⊤ → A` and map `f : A → A`, is there a map `r : N → A` with invertible cells `r ∘ zero ≅ a` and `r ∘ succ ≅ f ∘ r`?

**Question 2 (discreteness of N).** In 𝕋 together with any rules that make Bool := ⊤ ⊔ ⊤ a set (coproducts of sets are sets and disjoint), is `N trunc 0` derivable? More generally: is "⟦Γ⟧ is 1-truncated for every finite graph Γ" derivable?

**Question 3 (effective quotients).** In 𝕋 + Trunc₀, for a set X and an equivalence relation `R ↪ X × X` (R a set, with reflexivity, symmetry and transitivity maps), let `X/R := ‖coeq(R ⇉ X)‖₀` (pseudo coequaliser, then set-truncation). Is the canonical map `R → X ×_{X/R} X` an equivalence (derivably)?

The expected answer to all three is **no**. A "no" should come with a model (or a syntactic argument) showing it; a "yes" with a derivation.

## What is known

- **Semantically all three conclusions hold** in the intended model (ω-categories, or (∞,ω)-categories): N is ℕ, free categories on graphs are 1-categories (Dwyer–Kan-type rigidity; the free weak ω-category on a graph is the free category on it), and sets are ordinary sets, whose quotients are effective.
- **Where the obvious derivations stop.**
  - *Q1.* R-A produces maps *out of* ⟦L⟧ from endo-1-cells of an object C; functoriality then gives `N → Hom_C(c, c)`. To land in an arbitrary A with action f, one needs a C whose endo-hom at some c is A with composition-by-s acting as f. The lax colimit T of the diagram (A, f) over L is the natural candidate, but colimit rules describe maps *out of* T, not the homs of T. With a rule identifying lax colimits with Grothendieck constructions plus a "directed J" rule (comma objects `a ↓ C` are free cocartesian fibrations), recursion and induction *are* derivable (the posing project has a proof). The question is whether those rules can be avoided.
  - *Q2.* A Hedberg-style derivation (as in homotopy type theory's proof that ℕ is a set) goes through with the directed J rule up to one step: from `eq(m, n) = true` produce an invertible arrow m → n. The standard proof inducts on m for all n at once, which needs a function object Π over N (exponentials), or an induction principle whose parameter changes along the step. Without exponentials the derivation stalls there.
  - *Q3.* In homotopy type theory effectiveness is proved by encode–decode against a family `X/R → Prop`, which uses a universe of propositions (univalence). The theory here has no universe. Effectiveness is a statement about maps *into* a pullback over X/R, and no colimit or truncation rule describes those.
- **1-categorical analogues.** Finite sets have finite limits and colimits but no natural numbers object, so a primitive NNO is independent of finite limits and colimits; but here N is already given by R-A, so this does not settle Q1. Regular categories with coequalisers of equivalence relations need not be exact (e.g. torsion-free abelian groups, or topological spaces), which is the 1-categorical shadow of Q3; the question is whether such a failure can occur for the 0-truncated objects of a model of 𝕋 + Trunc₀.

## What has been tried

- For Q1, candidate countermodels where *cell-iteration* (needed by R-A for every object C) is available but *map-iteration* (recursion into an arbitrary A) is not: internal ω-categories in a base with restricted function classes (e.g. elementary or primitive recursive maps). The difficulty is that R-A for internal categories already seems to require a parametrised natural numbers object in the base, which gives recursion. Not resolved.
- For Q2, the term model: with a variable `c`, two variables `u, u' : c → ⟦L⟧` and parallel `α, β : u → u'`, no rule of 𝕋 obviously produces a cell α → β, since `coh` needs α and β in one pasting context and no rule introduces cells between variables whose target is a constant. Turning this into a proof needs a normal-form theorem for 𝕋, which is not available.
- For Q3, nothing beyond the observation above.

## Why it matters

A type theory for weak ω-categories that adds only universal properties (limits, colimits, free objects) is very economical. These questions decide whether it already contains basic arithmetic (recursion on ℕ), whether ℕ is provably a set, and whether quotient sets behave correctly, or whether each needs its own rule. A "no" justifies adding the rule; a "yes" removes a rule from the design.

## What would count as a solution

For each question: a model of the stated rules in which the conclusion fails (or a syntactic argument), or a derivation, or references.

## Literature status (2026-11-18)

Searched: "natural numbers object not derivable from free category on a graph finite limits colimits recursion"; "effective quotients exact category not implied by regular category with coequalizers counterexample". Found: Rijke, *An elementary approach to truncations* (arXiv 1812.10527), constructing truncations in homotopy type theory from non-recursive higher inductive types (it works in a univalent setting, so does not bear on Q3 without a universe); the nLab pages on natural numbers objects and on exact categories (standard 1-categorical facts quoted above). No result on derivability of recursion, discreteness or effectiveness in a CaTT-style theory with limits was found.

# Researcher Response

**For the listed universal properties, with “cotensor” understood in its enriched sense, all three answers are no.** Explicit countermodels are given below.

There is one material qualification for **Question 2**: its countermodel satisfies enriched shape cotensors, but not the stronger requirement that these cotensors be cartesian exponentials by the realized objects \(\llbracket D\rrbracket\). If that stronger requirement is intended, the constructions below settle Questions 1 and 3, while Question 2 needs a different argument.

| Question | Countermodel | Failure |
|---|---|---|
| 1. Recursion | Categories equipped with an auxiliary equivalence relation on their object sets | \(N\) is the discrete category on the usual \(\mathbb N\), but every permitted map \(N\to\mathrm{Bool}\) is constant |
| 2. Discreteness | A comma \(\infty\)-category constructed from spaces and \(D(\mathbb Z)\) | A map into \(N\) has a nontrivial group of automorphisms |
| 3. Effectiveness | \(\mathbf{Pos}\), with discrete hom higher categories | \(R\to X\times_{X/R}X\) is bijective, but its inverse is not monotone |

I give Question 3 first because its counterexample is finite.

## 1. Question 3: a finite counterexample

### 1.1 The higher model

Take the ordinary category \(\mathbf{Pos}\) of posets and monotone maps, and give it **discrete hom higher categories**:
\[
\mathcal K(A,B)
=
\operatorname{Disc}\bigl(\mathbf{Pos}(A,B)\bigr).
\]

Thus the ambient \(1\)-cells are monotone maps, and every ambient cell of dimension at least \(2\) is an identity.

**The order relation of a poset is not interpreted as a cell relation.** It restricts which functions are admitted as maps. Equivalently, use internal discrete categories in \(\mathbf{Pos}\), and then add identity cells in all higher dimensions.

Every member of this model is a set: each \(\mathcal K(T,C)\) is discrete. Consequently,
\[
\operatorname{Trunc}_0(C)=C,\qquad \eta_C=\operatorname{id}_C
\]
satisfies the required reflection property.

The category \(\mathbf{Pos}\) has limits, colimits, and cartesian exponentials. Its limits have coordinatewise order; colimits are obtained by generating a preorder and then quotienting by mutual comparability. These facts are stated, with these constructions, in Balan–Kurz–Velebil, §3.I. [dep2.mathem.upb.ro](https://dep2.mathem.upb.ro/balan/papers/calco2013.pdf?utm_source=chatgpt.com)

In our discrete enrichment, a lax or pseudo comparison cell exists precisely when its boundary maps are equal. Hence ordinary finite colimits supply the required finite lax and pseudo colimits, with their universal properties at every dimension.

### 1.2 Verification of R-A and cotensors

For a finite computad \(\Gamma\), let \(k(\Gamma)\) be the finite set obtained from its \(0\)-generators by identifying the endpoints of every \(1\)-generator. Interpret
\[
\llbracket\Gamma\rrbracket=\Delta k(\Gamma),
\]
where \(\Delta S\) denotes the discrete poset on \(S\).

A substitution of \(\Gamma\) into the internal discrete category associated to \(C\) assigns an element of \(C\) to each \(0\)-generator. A \(1\)-generator can be interpreted exactly when its endpoint values coincide. All higher assignments are then forced identities. Therefore
\[
\mathbf{Pos}(\Delta k(\Gamma),C)
\cong
\operatorname{Sub}(\Gamma,C).
\]

This verifies the whole higher correspondence, since both sides have only identity higher cells.

It also works with arbitrary parameters. For any poset \(T\), a \(T\)-parameterized substitution assigns monotone maps \(T\to C\), equal along the endpoints of every \(1\)-generator. Thus
\[
\operatorname{Sub}_T(\Gamma,C)
\cong
\mathbf{Pos}\bigl(T,C^{k(\Gamma)}\bigr)
\cong
\mathbf{Pos}\bigl(T\times\Delta k(\Gamma),C\bigr).
\]

The required cotensor is consequently
\[
[\llbracket D\rrbracket,C]=C^{k(D)}.
\]

So this is a model of the higher rules, including R-A.

### 1.3 The equivalence relation

Let
\[
X=\{0<1\}.
\]

The underlying set of \(R\) is \(\{0,1\}^2\), but equip it with the order
\[
r\le_R r'
\quad\Longleftrightarrow\quad
r=r'
\ \text{or}\
\bigl(r=(0,0)\ \text{and}\ r'=(1,1)\bigr).
\]

Its only strict comparison is therefore
\[
(0,0)<_R(1,1).
\]

The map
\[
m:R\longrightarrow X\times X
\]
is the identity on underlying sets. It is monotone and injective, hence monic.

The equivalence-relation operations are
\[
e(x)=(x,x),
\qquad
i(x,y)=(y,x),
\qquad
c\bigl((x,y),(y,z)\bigr)=(x,z).
\]

These are monotone:

- \(e\) takes \(0<1\) to \((0,0)<_R(1,1)\).
- \(i\) preserves that comparison.
- The only strict comparison in \(R\times_XR\) is
  \[
  \bigl((0,0),(0,0)\bigr)
  <
  \bigl((1,1),(1,1)\bigr),
  \]
  and \(c\) takes it to \((0,0)<_R(1,1)\).

The reflexivity, inverse, and associativity equations follow directly from the displayed functions. Thus \(R\rightrightarrows X\) is an internal equivalence relation between sets in this model.

### 1.4 Its prescribed quotient is not effective

A monotone map \(g:X\to Y\) equalizes the two projections from \(R\) exactly when
\[
g(0)=g(1).
\]
It therefore factors uniquely through the one-point poset. Hence
\[
Q=\operatorname{coeq}(R\rightrightarrows X)=1.
\]

Pseudo-coequalization gives the same result, and \(\operatorname{Trunc}_0\) is the identity. Thus this is exactly your prescribed quotient.

Its kernel pair is
\[
X\times_QX=X\times X
\]
with the product order. In particular,
\[
(0,0)<(0,1)
\]
in the kernel pair, while those two elements are incomparable in \(R\).

The canonical map
\[
R\longrightarrow X\times_QX
\]
is therefore a bijective monotone map whose inverse is not monotone. In a locally discrete higher category, an equivalence must be an isomorphism. The comparison is not an equivalence.

One can detect the failure using the generalized element
\[
(\operatorname{const}_0,\operatorname{id}_X):
X\longrightarrow X\times X.
\]
Its only possible lift to \(R\) sends \(0<1\) to \((0,0),(0,1)\), so that lift is not monotone.

**This proves the non-derivability in Question 3.**

---

## 2. Question 1: failure with the actual discrete category \(\mathbb N\)

Here is a countermodel that does not collapse the free loop or its powers.

### 2.1 The ambient \(2\)-category

Define \(\mathcal K\) as follows.

An object is a pair
\[
(C,E_C),
\]
where \(C\) is an ordinary category and \(E_C\) is an auxiliary equivalence relation on its set \(C_0\) of objects.

A \(1\)-cell
\[
F:(C,E_C)\longrightarrow(D,E_D)
\]
is a functor satisfying
\[
c\,E_C\,c'
\quad\Longrightarrow\quad
F(c)\,E_D\,F(c').
\]

The \(2\)-cells are **all natural transformations** between the permitted functors. There are only identity cells above dimension \(2\).

The relation \(E_C\) is distinct from equality and from the existence of an arrow in \(C\).

### 2.2 The structural rules hold

For conical limits, take the ordinary categorical limit and impose
\[
x\,E_{\lim C_i}\,y
\quad\Longleftrightarrow\quad
p_i(x)\,E_{C_i}\,p_i(y)
\text{ for every }i.
\]

A functor into this limit preserves the relation exactly when all its composites with the projections do.

For conical colimits, take the ordinary categorical colimit and let its auxiliary relation be generated by
\[
j_i(x)\,E_{\operatorname{colim}C_i}\,j_i(y)
\qquad\text{whenever }x\,E_{C_i}\,y.
\]

A functor out preserves this generated relation exactly when its composites with all the injections do. Since natural transformations are unrestricted, these constructions give universal properties of **hom categories**, not just of sets of functors.

For any ordinary indexing category \(J\), define the cotensor \(C^J\) to have underlying category \(\operatorname{Fun}(J,C)\), with
\[
F\,E_{C^J}\,G
\quad\Longleftrightarrow\quad
F(j)\,E_C\,G(j)
\text{ for every }j\in J_0.
\]

Currying restricts to an isomorphism
\[
\mathcal K(A,C^J)
\cong
\operatorname{Fun}\bigl(J,\mathcal K(A,C)\bigr).
\]

Tensors also exist: \(J\otimes A\) has underlying category \(J\times A\), with
\[
(j,a)\,E_{J\otimes A}\,(j',a')
\quad\Longleftrightarrow\quad
j=j'\ \text{and}\ a\,E_A\,a'.
\]

Conical limits and cotensors, and dually conical colimits and tensors, give all enriched weighted limits and colimits by Kelly’s Theorem 3.73 and its dual. Thus the required finite pseudo and lax constructions are available. [sas.rochester.edu](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/kelly-book.pdf?utm_source=chatgpt.com)

Concretely, pseudolimits use categories of pseudocones with relations imposed through their projections. Lax colimits use the categorical presentation of a lax cocone, with the relation generated by the diagram relations. Pseudocolimits additionally invert the specified comparison arrows. These constructions preserve the actual component functors of each cone or cocone, so the condition of preserving \(E\) agrees on both sides of the universal property.

### 2.3 R-A holds

For a finite computad \(\Gamma\), let \(P_\Gamma\) be the ordinary category presented by:

- its \(0\)-generators as objects;
- its \(1\)-generators as arrows;
- equality of the source and target of every \(2\)-generator.

All higher generators are interpreted by identities. Set
\[
\llbracket\Gamma\rrbracket=(P_\Gamma,=).
\]

Every functor from a category whose auxiliary relation is equality preserves that relation. Therefore
\[
\mathcal K(\llbracket\Gamma\rrbracket,(C,E_C))
=
\operatorname{Fun}(P_\Gamma,C).
\]

The right side is precisely the category of \(\Gamma\)-substitutions into the ordinary category \(C\), together with their transformations. Thus R-A holds at every level.

For these realizations, the cotensors also satisfy the stronger cartesian exponential law:
\[
\mathcal K(A\times\llbracket\Gamma\rrbracket,C)
\cong
\mathcal K(A,C^{P_\Gamma}).
\]
Indeed, the relation on \(A\times\llbracket\Gamma\rrbracket\) compares \((a,\gamma)\) and \((a',\gamma')\) exactly when \(aE_Aa'\) and \(\gamma=\gamma'\).

### 2.4 Computing the specified \(N\)

Let \(B\mathbb N\) be the one-object category whose endomorphism monoid is \((\mathbb N,+,0)\). Then
\[
\llbracket L\rrbracket=(B\mathbb N,=).
\]

Let \(I\) be the walking arrow. The objects of
\[
[I,B\mathbb N]
\]
are the natural numbers, one for each arrow of \(B\mathbb N\).

Its auxiliary relation is **total**: every functor \(I\to B\mathbb N\) has the same value on both objects of \(I\), so the pointwise condition defining the cotensor relation holds for every pair of functors.

An arrow \(n\to m\) in this arrow category is a commutative square. In the fiber over \((x,x)\), both vertical arrows must be identities, so such a square exists exactly when \(n=m\), and it is then the identity.

Consequently, the hom object specified in the question is
\[
\boxed{
N=
\bigl(\operatorname{Disc}\mathbb N,\,
      \mathbb N\times\mathbb N\bigr).
}
\]

The pseudofiber gives the same result, because \(B\mathbb N\) has no nonidentity isomorphisms. The maps
\[
\operatorname{zero}(*)=0,
\qquad
\operatorname{succ}(n)=n+1
\]
are permitted maps.

In particular, \(N\) is a set in this model: for every \(T\), the category \(\mathcal K(T,N)\) has only identity natural transformations.

### 2.5 Recursion fails

Take
\[
A=(\operatorname{Disc}\{0,1\},=),
\qquad
a(*)=0,
\qquad
f(0)=1,\quad f(1)=0.
\]

This \(A\) is itself the realization of the context with two unrelated \(0\)-generators.

Every permitted map \(r:N\to A\) must satisfy
\[
r(m)=r(n)
\qquad\text{for every }m,n\in\mathbb N,
\]
because it must preserve the total auxiliary relation on \(N\). Thus \(r\) is constant.

Natural isomorphisms between functors into the discrete category \(A\) are equalities. The requested equations would therefore imply
\[
r(0)=0,
\qquad
r(1)=f(r(0))=1,
\]
contradicting constancy.

**This proves Question 1 has a negative answer, even when the specified \(N\) is a set and its underlying category is exactly \(\operatorname{Disc}\mathbb N\).**

The distinction is between having the usual natural-number cells and admitting every set-theoretic function on those cells. R-A guarantees the required maps out of the specified free realizations; it does not guarantee all functors between arbitrary ambient objects.

---

## 3. Question 2: a countermodel with enriched cotensors

For this construction, use representable truncation: in an \((\infty,1)\)-category, \(C\) is \(n\)-truncated when every \(\operatorname{Map}(T,C)\) is an \(n\)-type. This is the standard formulation of truncation for an abstract \(\infty\)-category. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HTT.pdf?utm_source=chatgpt.com)

### 3.1 The comma \(\infty\)-category

Let \(\mathcal S\) denote spaces, and let \(D(\mathbb Z)\) be the unbounded derived \(\infty\)-category of abelian groups. Use homological grading, so \(\mathbb Z[k]\) has its nonzero group in degree \(k\).

Define
\[
F:\mathcal S\longrightarrow D(\mathbb Z),
\qquad
F(X)=H_1(X;\mathbb Z)[1].
\]

The values needed below are
\[
F(\varnothing)=F(*)=F(S)=0
\quad\text{for discrete }S,
\qquad
F(S^1)=\mathbb Z[1].
\]

Consider
\[
\mathcal K=(F\downarrow\operatorname{id}_{D(\mathbb Z)}).
\]

Its members are triples
\[
C=(X,A,\alpha:F(X)\to A).
\]

The mapping spaces are
\[
\operatorname{Map}_{\mathcal K}
 \bigl((X,A,\alpha),(Y,B,\beta)\bigr)
\simeq
\operatorname{Map}_{\mathcal S}(X,Y)
\times^h_{\operatorname{Map}_{D(\mathbb Z)}(F(X),B)}
\operatorname{Map}_{D(\mathbb Z)}(A,B),
\tag{1}
\]
where the two maps to the denominator send
\[
f\longmapsto\beta F(f),
\qquad
g\longmapsto g\alpha.
\]

Regard \(\mathcal K\) as a higher category in which all cells above dimension \(1\) are invertible.

### 3.2 Limits, colimits, and cotensors

Both \(\mathcal S\) and \(D(\mathbb Z)\) have all small limits and colimits; the derived category is presentable and stable. For the latter, see Lurie, *Higher Algebra*, §1.3.5, especially Proposition 1.3.5.21. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HA.pdf?utm_source=chatgpt.com)

For a diagram \((X_i,A_i,\alpha_i)\), its limit in \(\mathcal K\) is
\[
\left(
\lim_iX_i,\,
\lim_iA_i,\,
F(\lim_iX_i)\longrightarrow\lim_iF(X_i)
                    \longrightarrow\lim_iA_i
\right).
\tag{2}
\]

For its colimit, put \(X=\operatorname{colim}_iX_i\). The result is
\[
\left(
X,\,
F(X)\amalg_{\operatorname{colim}_iF(X_i)}
              \operatorname{colim}_iA_i,\,
\text{canonical map}
\right).
\tag{3}
\]

These formulas follow directly by substituting into (1): mapping into (2) gives the limit of the mapping spaces, and mapping out of (3) gives compatible maps out of the original diagram. **No limit or colimit preservation assumption on \(F\) is used.**

In particular,
\[
\mathbf1=(*,0),\qquad \mathbf0=(\varnothing,0).
\]

All enriched shape cotensors exist. If \(D\) is a higher shape and \(|D|\) is its groupoidal realization, take
\[
C^D=\lim_{|D|}C.
\]
Then
\[
\operatorname{Map}_{\mathcal K}(T,C^D)
\simeq
\operatorname{Map}_{\mathcal S}
\bigl(|D|,\operatorname{Map}_{\mathcal K}(T,C)\bigr).
\tag{4}
\]

This is the enriched cotensor universal property. Cotensors as limits of constant diagrams, with this mapping-space characterization, are described by Riehl–Verity, Definition 4.3.6. [emilyriehl.github.io](https://emilyriehl.github.io/files/elements.pdf?utm_source=chatgpt.com)

Since comparison cells in this model are invertible, lax colimit universal properties reduce to the corresponding homotopy-coherent colimit universal properties. Those colimits exist by (3).

### 3.3 R-A holds naturally at every level

Define
\[
P(X,A,\alpha)=X,
\qquad
T(G)=(G,F(G),\operatorname{id}_{F(G)}).
\]

Equation (1) gives
\[
\operatorname{Map}_{\mathcal K}(T(G),C)
\simeq
\operatorname{Map}_{\mathcal S}(G,P(C)).
\tag{5}
\]
Thus \(T\dashv P\).

Also,
\[
P(C)\simeq\operatorname{Map}_{\mathcal K}(\mathbf1,C).
\tag{6}
\]

For a finite computad \(\Gamma\), let \(|\Gamma|\) be its groupoidal realization and interpret
\[
\llbracket\Gamma\rrbracket=T(|\Gamma|).
\]

The groupoidal realization can be constructed by attaching a point for each \(0\)-generator and an \(n\)-disk for each \(n\)-generator, along the boundary specified by its source and target. Mapping from this realization to a space gives precisely the corresponding assignments of points, paths, and higher cells.

Equations (5)–(6) therefore give
\[
\operatorname{Map}_{\mathcal K}
  (\llbracket\Gamma\rrbracket,C)
\simeq
\operatorname{Sub}(\Gamma,C).
\]

This is an equivalence of entire spaces, natural in \(C\). It verifies the higher correspondence, rather than merely a correspondence on equivalence classes of substitutions.

### 3.4 The loop realization and its hom object

For the one-loop graph,
\[
|L|=S^1.
\]
Hence
\[
\llbracket L\rrbracket
=
(S^1,\mathbb Z[1],\operatorname{id}).
\tag{7}
\]

In this locally groupoidal model, the endomorphism object at a point is its based loop object. Indeed, applying a representable mapping-space functor to the arrow-cotensor construction gives the based path space. Consequently,
\[
N\simeq\mathbf1\times_{\llbracket L\rrbracket}\mathbf1.
\]

Using (2),
\[
\begin{aligned}
N
&\simeq
\left(
\Omega S^1,\,
0\times_{\mathbb Z[1]}0,\,
0
\right)\\
&\simeq
(\mathbb Z,\mathbb Z[0],0).
\end{aligned}
\tag{8}
\]

Now take
\[
E=(\varnothing,\mathbb Z[-1],0).
\]

Because \(F(\varnothing)=0\), equation (1) simplifies to
\[
\begin{aligned}
\operatorname{Map}_{\mathcal K}(E,N)
&\simeq
\operatorname{Map}_{D(\mathbb Z)}
  (\mathbb Z[-1],\mathbb Z[0])\\
&\simeq K(\mathbb Z,1).
\end{aligned}
\tag{9}
\]

Thus \(N\) is not \(0\)-truncated.

Similarly,
\[
\begin{aligned}
\operatorname{Map}_{\mathcal K}
  (E,\llbracket L\rrbracket)
&\simeq
\operatorname{Map}_{D(\mathbb Z)}
  (\mathbb Z[-1],\mathbb Z[1])\\
&\simeq K(\mathbb Z,2),
\end{aligned}
\tag{10}
\]
so \(\llbracket L\rrbracket\) is not \(1\)-truncated.

The derived mapping-space calculation follows from
\[
\pi_k\operatorname{Map}_{D(\mathbb Z)}
  (\mathbb Z[-n],A)
\cong H_{k-n}(A).
\]
An explicit reference is Cnossen, Definition 6.2.1 and Proposition 6.2.3. [Stable Homotopy Theory and Higher Algebra](https://bastiaancnossen.com/notes/stable-homotopy-higher-algebra/section/homological-algebra/ordinary-homology-and-cohomology-via-d-z/index.html?utm_source=chatgpt.com)

Therefore the same finite graph \(L\) refutes both assertions in Question 2.

### 3.5 Bool is a set, and coproducts of sets are disjoint

The sets in this model are exactly
\[
(S,0,0)
\qquad\text{with }S\text{ discrete}.
\tag{11}
\]

To prove necessity, suppose \(C=(X,A,\alpha)\) is \(0\)-truncated.

First, testing with \(\mathbf1\) shows that \(X\) is discrete. Next, for any \(W\in D(\mathbb Z)\), put
\[
E(W)=(\varnothing,W,0).
\]
Then
\[
\operatorname{Map}_{\mathcal K}(E(W),C)
\simeq
\operatorname{Map}_{D(\mathbb Z)}(W,A).
\]

Taking \(W=A[-1]\), discreteness requires
\[
0
=
\pi_1\operatorname{Map}_{D(\mathbb Z)}(A[-1],A)
\cong
\operatorname{End}_{hD(\mathbb Z)}(A).
\]
In particular, \(\operatorname{id}_A=0\), so \(A\simeq0\).

Conversely,
\[
\operatorname{Map}_{\mathcal K}
 \bigl((Y,B,\beta),(S,0,0)\bigr)
\simeq
\operatorname{Map}_{\mathcal S}(Y,S),
\]
which is discrete when \(S\) is discrete.

Formula (3) now gives
\[
(S,0)\amalg(S',0)=(S\amalg S',0).
\]
Thus
\[
\mathrm{Bool}=(\{0,1\},0)
\]
is a set. The summand injections are monomorphisms, and their mutual pullback is
\[
(\varnothing,0)=\mathbf0.
\]
Coproducts of sets are therefore sets and disjoint.

This model even admits the stated set reflection:
\[
\operatorname{Trunc}_0(X,A,\alpha)=(\pi_0X,0,0),
\]
as follows from the same mapping-space formula.

### 3.6 Why R-A does not detect this failure

Every realized computad tests the walking loop through
\[
\operatorname{Map}_{\mathcal K}
  (T(|\Gamma|),\llbracket L\rrbracket)
\simeq
\operatorname{Map}_{\mathcal S}(|\Gamma|,S^1),
\]
which is a \(1\)-type.

But the additional domain \(E\) gives \(K(\mathbb Z,2)\).

Thus the full higher naturality of R-A does not imply that maps from the realized computads detect truncation. The displayed universal property does not supply that detection principle.

---

## 4. The precise qualification concerning Question 2

The distinction is between the enriched cotensor law
\[
\mathcal K(A,C^D)
\simeq
\operatorname{Fun}\bigl(D,\mathcal K(A,C)\bigr)
\tag{C}
\]
and the additional cartesian exponential law
\[
\mathcal K(A,C^D)
\simeq
\mathcal K(A\times\llbracket D\rrbracket,C).
\tag{E}
\]

The Question 2 model satisfies **(C)**. It does not satisfy **(E)**, nor the corresponding product-parameterized strengthening of R-A.

This failure is explicit. Take the context with two unrelated object generators, whose realization is
\[
T(2)=(2,0).
\]
Let
\[
E_2=(\varnothing,\mathbb Z/2[0],0).
\]
Then
\[
E_2\times T(2)\simeq E_2.
\]
Consequently,
\[
\operatorname{Map}_{\mathcal K}(E_2\times T(2),E_2)
\]
is discrete with two elements, whereas
\[
\operatorname{Map}_{\mathcal K}(E_2,E_2)^2
\]
is discrete with four elements. Hence
\[
\mathcal K(A\times\llbracket\Gamma\rrbracket,C)
\simeq
\operatorname{Sub}\bigl(\Gamma,\mathcal K(A,C)\bigr)
\]
does not hold for arbitrary \(A\) in that model.

Likewise, its disjoint coproducts of sets are not required to remain coproduct diagrams after arbitrary base change.

Therefore:

- **Questions 1 and 3 have the countermodels above even with cartesian exponentials by the finite realized shapes and the corresponding product-parameterized R-A.**
- **Question 2 has the countermodel above for enriched cotensors and the R-A correspondence as stated.**
- **If the intended rules additionally impose (E), product-parameterized R-A, or universal coproducts under arbitrary base change, I have not established Question 2 for that strengthened theory.**

---

## Verification of the researcher response (2026-11-18)

I checked each step against the definitions in the prompt and against the project's rules: R-A as stated in `limits-representables.md` §5.2 and `ordinary-math.md` Theorem 4.1 (restriction `Hom(⟦Γ⟧, C) → Fam_Γ(C)` essentially surjective at every level), and `C trunc n` read through T-fill/T-inv, which test cells into C from an arbitrary object, i.e. representable truncation.

**Verdict: correct.** All three questions have a negative answer. For Q1 and Q3 the countermodels also satisfy the stronger, product-parameterised form of R-A. For Q2 the countermodel satisfies R-A in the hom-wise (enriched) form, which is the form the project uses; the product-parameterised strengthening is left open, as the response says.

### V1. Q3 (effectiveness), the poset model: correct

- **The model.** Pos with discrete hom ω-categories. Every comparison cell is an identity, so finite lax and pseudo colimits are ordinary colimits, and the universal properties hold at every level trivially. Every object is a set, and Trunc₀ = id satisfies Tr-J1/Tr-J2.
- **R-A.** `⟦Γ⟧` is the discrete poset on the 0-generators modulo "joined by a 1-generator". A substitution into C must send both ends of a 1-cell to the same element, since the only 1-cells of a hom are identities. So `Pos(Δk(Γ), C) ≅ Sub(Γ, C)` ✓, also with a parameter poset T ✓.
- **The relation.** R = {0,1}² with the single strict comparison (0,0) < (1,1). `R → X × X` is monotone and injective, which makes it a mono here because homs are discrete. e, i and c are monotone; I checked the only non-trivial comparison in `R ×_X R` ✓.
- **The quotient.** A monotone g with g∘r₀ = g∘r₁ has g(0) = g(1), witnessed by (0,1) ∈ R. So Q = 1 and the kernel pair is X × X with the product order. The comparison `R → X × X` is a bijection, but (0,0) < (0,1) holds in the product and not in R, so its inverse is not monotone. In a locally discrete model an equivalence is an isomorphism, so the comparison is not an equivalence ✓.
- **Caveat.** In this model ⟦L⟧ collapses to a point, so N = ⊤. That is harmless, since EX is a statement about all sets. It does mean the model says nothing about arithmetic.

### V2. Q1 (recursion), categories with an auxiliary equivalence relation: correct

- **The model.** Objects are (C, E_C); 1-cells are functors preserving E; 2-cells are all natural transformations. Limits take the limit relation through the projections, and colimits take the generated relation. Cotensors use the pointwise relation and tensors the relation "same j and related a". Weighted limits and colimits follow from conical ones plus (co)tensors (Kelly 3.73). Because 2-cells are unrestricted, the universal properties hold for hom categories, which is what R-A and the colimit rules require ✓.
- **R-A.** `⟦Γ⟧ = (P_Γ, =)`. Every functor out of an object whose relation is equality preserves it, so `K(⟦Γ⟧, C) = Fun(P_Γ, C)` ✓. The product-parameterised law holds too, since the relation on `A × ⟦Γ⟧` is "related in A and equal in ⟦Γ⟧" ✓.
- **N.** `[I, BN]` has the natural numbers as objects, and its relation is total: every functor I → BN takes both objects to the single object, so the pointwise condition holds. Pulling back along (x, x) keeps the relation total, so `N = (Disc ℕ, total)`. zero and succ preserve the total relation ✓.
- **Failure.** Take `A = (Disc{0,1}, =)`, which is Bool = ⊤ ⊔ ⊤ by the colimit formula. Any permitted r : N → A is constant, so `r(0) = a = 0` and `r(1) = f(r 0) = 1` cannot both hold, and invertible cells into a discrete category are equalities ✓.
- **Consequence.** In this model N is a set, but recursion into Bool fails, even for "is zero". The model must violate G or DJ (§4.6), since together they derive recursion. That is consistent: both are new principles, not consequences of limits, colimits and R-A.

### V3. Q2 (discreteness), the comma (F ↓ id) with F = H₁(–)[1]: correct for hom-wise R-A

- **Mapping spaces.** (1) is the standard formula for maps in the comma `F ↓ id_{D(ℤ)}` ✓. The projection to `S × D(ℤ)` creates limits because the codomain functor is the identity, giving formula (2). Colimits are computed by the pushout (3); I checked this against the universal property through (1), and it uses no preservation by F ✓. Cotensors by shapes are limits over the groupoidal realisation, which is right for an (∞,1)-category regarded as an (∞,ω)-category with all higher cells invertible ✓.
- **R-A.** `T(G) = (G, F G, id)` is left adjoint to `P(X, A, α) = X`, and `P(C) ≃ Map(1, C)`. So `Map(T|Γ|, C) ≃ Map_S(|Γ|, P C) ≃ Sub(Γ, C)` as spaces, naturally in C. This is R-A at every level in the hom-wise form ✓.
- **N.** The arrow cotensor is C itself, since |D¹| ≃ ∗, so `Hom_C(x, x) = 1 ×_C 1`. For `⟦L⟧ = (S¹, ℤ[1], id)` this gives `(ℤ, ℤ[0], 0)` by (2) ✓. With `E = (∅, ℤ[−1], 0)`, `Map(E, N) ≃ Map_{D(ℤ)}(ℤ[−1], ℤ) ≃ K(ℤ, 1)`. I checked π₁ = H₀(ℤ) = ℤ with the formula `π_k Map(ℤ[−n], A) = H_{k−n}(A)` ✓. So N is not 0-truncated, and likewise ⟦L⟧ is not 1-truncated (K(ℤ, 2)).
- **Bool and coproducts.** The sets are exactly (S, 0, 0) with S discrete, and the necessity argument via `E(A[−1])` is right ✓. Bool = ({0,1}, 0) is a set, and coproducts of sets are sets and disjoint ✓. Trunc₀ exists ✓.
- **Scope (§4 of the response).** The model fails the cartesian law `K(A × ⟦D⟧, C) ≃ K(A, C^D)`. The `E₂` computation gives 2 against 4 maps ✓. The project's R-A is the hom-wise one, so Q2 is answered for the theory as stated. If R-A were ever strengthened to the product-parameterised form (or coproducts required to be universal), Q2 would be open again.

### V4. Consequences for the project

1. **F1c, closed.** Route II's recursion is not derivable from finite limits, colimits and R-A, even with the product-parameterised R-A and with N provably a set. Route II must add `rec` as a rule, as `ordinary-math.md` §4.5 assumed.
2. **F3b, closed for the theory as stated.** T-graph (and its instance `N trunc 0`) is not derivable from R-A, limits, colimits, Trunc₀ and a Bool that is a set with disjoint coproducts. This makes Prop. 2.5 a theorem for hom-wise R-A. Open, and optional: the same question for product-parameterised R-A.
3. **F4b, closed.** EX is not derivable from limits, colimits, R-A, Trunc₀ and the T-rules, even with cartesian exponentials by shapes. So EX is a genuine rule.
4. **The three are independent new principles.** rec (or G + DJ), T-graph and EX each have to be added. None follows from the universal-property core.
