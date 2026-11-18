# Relative coherence for cartesian closed higher categories, round 2: generators of dimension 3

*A self-contained problem. No knowledge of the project that posed it is assumed. Round 1 and its verified answer are archived in `answered/dir-relative-coherence-2026-11-18.md`. The smallest open case is Question 1.*

## Background

**Pasting types.** Mimram (*An unbiased simply typed combinatory logic*, CSL 2026) defines a decidable class of simple types (with →, ×, 1), the **pasting types**. Each has exactly one inhabitant up to βη (his Theorem 15). A type theory with a constant for every pasting type, and an equality rule identifying all terms of a pasting type, presents the free cartesian closed category.

**Higher contexts.** A context may contain:
- objects (type variables);
- 1-cells f : A → B between types;
- higher cells α : s → t between parallel terms one dimension down.

A goal of dimension n is a pair of parallel (n−1)-terms. A filler is an n-cell between them.

**Semantics.** Let 𝒞(Γ) be the free cartesian closed (∞,ω)-category on such a context Γ. Products and exponentials are pseudo: Map(A × B, C) ≃ Map(A, C^B) as mapping (∞,ω)-categories.

**What is known.**
- **Graph contexts** (no hypotheses of dimension ≥ 2). 𝒞(Γ) is the free cartesian closed 1-category: simply typed λ-terms with constants modulo βη, with all higher cells identities up to contractible choice. Sketch of the proof: the free cartesian closed (∞,1)-category on a graph has discrete mapping spaces, by a retract argument onto a set of normal forms. The 1-core functor, which keeps all cells of dimension ≤ 1 and the invertible higher cells, is right adjoint to the inclusion of (∞,1)-categories (Ozornova–Rovelli–Walde, arXiv 2603.11005, Thm 2.20). It preserves cartesian closed structure, so freeness on a graph transfers. In particular, any two parallel 2-cells between βη-equal 1-terms are joined by a contractible space of invertible 3-cells. This includes coherence for cartesian closed tricategories over a graph.
- **Dimension 2 over a graph:** Fiore–Saville, *Coherence for bicategorical cartesian closed structure* (MSCS 2021).
- **Invertible higher hypotheses** that have a free endpoint can be contracted. This is Mimram's reversible criterion; it is sound by the result above.
- **2-dimensional generators (round 1, proved).** Let 𝓕 be the free pseudo cartesian closed (∞,2)-category on atomic types, primitive 1-generators, and 2-generators forming disjoint directed chains f₀ ⇒ f₁ ⇒ ⋯ ⇒ f_r of primitive parallel 1-generators. Then for all u, v : U → V the space of 2-cells u ⇒ v is empty or contractible, and the free (∞,ω) object is 𝓕 with only identities above dimension 2 up to contractible choice. Proof: β-normal η-long forms give a bijection 𝓕₁(U,V) ≅ ∐_ν ∏_{p∈P_ν} X_{σ(p)} natural in relabelling constants (no quotient by permutations); apply it degreewise to X = Δ^r to get a simplicially enriched ccc 𝒦 whose homs are nerves of posets ∐_ν ∏ [r_p]; rectify 𝓕 to a strictly enriched ccc D (Haugseng; enriched injective presheaves); interpret 𝒦 → D degreewise; the retract 𝓕 → 𝒦 → D ≃ 𝓕 makes 2-cell spaces of 𝓕 retracts of poset mapping spaces. In particular duplication creates [1]^m, not ambiguity. So **Dir is sound for every context whose non-invertible generators have dimension ≤ 2**.

## The criterion

**(Dir)**, from Mimram's tool cccatt (`src/pasting.ml`). For a goal of dimension n:
1. The n-dimensional hypotheses must be cells x → y between variables, with:
   - no loops;
   - pairwise distinct sources and pairwise distinct targets;
   - an acyclic relation "x → y".
2. Let the **source context** be the context without the targets of these cells, and the **target context** the context without their sources. Both must, recursively, accept the goal's (n−1)-dimensional type.
3. The goal's source term must avoid targets, and its target term must avoid sources.

There is no fullness condition. With no n-dimensional hypotheses, every parallel pair of terms of a pasting (n−1)-type is accepted, in both directions.

*(Note: the unordered implementation at commit 69bb11af does not enforce distinctness in step 1, because it compares position-carrying terms (filed as smimram/cccatt#15). The question is about the abstract criterion above, not the implementation.)*

## Questions

1. **(Smallest open case.)** Take f, g : A → B, 2-generators α, α′ : f ⇒ g (parallel), and one 3-generator Ξ : α ⇛ α′. (This is Dir-pasting.) In the free cartesian closed (∞,ω)-category 𝒞(Γ), is the space of 3-cells between any two parallel 2-cells empty or contractible? Concretely: with a term using f twice through the diagonal, the 3-cells ⟨Ξ, 1⟩ ∗ ⟨1, Ξ⟩-type composites in the two orders, and the interchange of Ξ with α′ along the two coordinates: are all parallel 3-cells connected by an essentially unique 4-cell?
   - The round-1 method needs a strict model whose hom (∞,1)-categories are nerves of posets. Here the candidate replaces the constant family Δ¹ by the free (∞,2)-category (or a Θ₂-set) on the 2-globe with Ξ: is there a simplicially (or Θ₂-) enriched ccc model built degreewise from long normal forms, with homs that are "free on a poset of addresses", and does the rectification/retract argument go through one dimension up?
2. **(General Dir.)** For every Dir-pasting context (generators in any dimension, Dir's recursive conditions), is every Dir-accepted goal fillable with a contractible filler space?
3. **(Counterexample search.)** If 1 fails, give two parallel 3-cells in 𝒞(Γ) with no 4-cell between them, or with a non-contractible space of 4-cells, ideally detected in a strict cartesian closed 3-category model.

## What counts as a solution

A proof of Question 1 or 2, a counterexample with an explicit model, or a reference proving relative coherence for free cartesian closed higher categories with generators of dimension ≥ 3.

## Literature (searched 2026-11-18)

- Mimram (CSL 2026), and the tool cccatt.
- Fiore–Saville (MSCS 2021), dimension 2 over a graph.
- Hirschowitz, arXiv 1307.6318: free strict cartesian closed 2-category on a 2-signature (Thm 7.11).
- Ozornova–Rovelli–Walde (arXiv 2603.11005): the core adjunctions.
- Haugseng (arXiv 1312.3881): rectification of enriched ∞-categories.
- No relative coherence theorem for cartesian closed structure with generators of dimension ≥ 3 was found.

# Researcher Response

**Yes. Question 1 is affirmative, and the same method proves Question 2 for finite contexts, uniformly in their dimension.**

The additional ingredients are:

1. Rezk’s \(\Theta_d\)-space model supports the enriched presheaf argument used in round 1.
2. Dir’s recursive chain conditions force the shifted generator diagrams to be disjoint unions of globular pasting diagrams.
3. The free strict categories on those diagrams have at most one cell with a fixed parallel boundary in their highest dimension.

The existence part requires a separate argument: the directed chains induce a cell from each source expression to its root-to-sink renaming. I give that construction below.

Throughout, variable equality means equality of the declared variables, and parallel cells have the same specified boundaries.

## 1. The model for Question 1

Let \(G\) be the strict \(2\)-category
\[
\operatorname{Ob}(G)=\{f,g\},
\qquad
G(f,g)=\{\alpha\xrightarrow{\Xi}\alpha'\}=[1],
\]
with
\[
G(f,f)=G(g,g)=1,
\qquad
G(g,f)=\varnothing.
\]
Thus \(G\) is the walking \(2\)-cell, viewed one dimension below the generators of \(\Gamma\).

Use the model category
\[
\mathcal V_2=\Theta_2\mathrm{Sp}_{\infty}
\]
of Rezk \(\Theta_2\)-spaces. The discrete nerve of \(G\) is the representable
\[
X=N_{\Theta_2}G
  =\Theta_2[-,[1]([1])].
\tag{1}
\]
It is already fibrant: Rezk’s Proposition 11.24 says that the discrete nerve of a strict \(d\)-category is fibrant precisely when all its invertible positive-dimensional cells are identities. This holds for \(G\), its finite products, and their disjoint unions. Rezk’s §11.8 identifies (1) as the free-standing \(2\)-cell. [rezk.web.illinois.edu](https://rezk.web.illinois.edu/cs-objects-revised-arxiv.pdf?utm_source=chatgpt.com)

Let \(F_1\) denote the ordinary free cartesian closed category construction. Apply it pointwise to \(X\), using a separate singleton constant family for every other primitive \(1\)-generator:
\[
\mathcal K(U,V)(\theta)_k
=
F_1\bigl(X(\theta)_k\bigr)(U,V).
\tag{2}
\]
Here both \(\theta\in\Theta_2\) and the simplicial degree \(k\) are evaluated.

The round-1 normal-form lemma gives
\[
\mathcal K(U,V)
\cong
\coprod_{\nu}X^{m_\nu}
\cong
N_{\Theta_2}\!\left(\coprod_\nu G^{m_\nu}\right).
\tag{3}
\]
The index \(\nu\) retains the typed η-long normal-form tree and the names of the other constants; \(m_\nu\) counts its addresses belonging to the \(f,g\) family.

The nerve preserves the products in (3). It also preserves these coproducts: every \(\Theta_2\)-shape is nonempty and connected, so a functor from it to a disjoint union factors through exactly one summand.

Every hom-category of \(G\) is a poset. Consequently, every hom-category of
\[
Q_{U,V}:=\coprod_\nu G^{m_\nu}
\]
is a poset. Thus, in \(\mathcal K\), there is **at most one \(3\)-cell between any fixed parallel \(2\)-cells**, and the corresponding space is literally empty or a point.

Composition, products, and exponentials in (2) are defined pointwise. Naturality of ordinary free-CCC interpretation gives actual enriched isomorphisms
\[
\begin{aligned}
\mathcal K(T,1)&\cong 1,\\
\mathcal K(T,U\times V)
&\cong\mathcal K(T,U)\times\mathcal K(T,V),\\
\mathcal K(T,V^U)
&\cong\mathcal K(T\times U,V).
\end{aligned}
\tag{4}
\]
Therefore \(\mathcal K\) is a strictly \(\mathcal V_2\)-enriched cartesian closed category with fibrant homs.

The remaining issue is transferring this calculation to the free **pseudo** cartesian closed higher category.

## 2. The enriched presheaf argument works in every finite dimension

The needed semantic statement is the following.

> **Semantic lemma.** For every finite \(d\), a small pseudo cartesian closed \((\infty,d+1)\)-category is equivalent, as a cartesian closed higher category, to a small category strictly enriched in Rezk \(\Theta_d\)-spaces, with fibrant homs, whose product and exponential universal properties are actual isomorphisms of enriched homs.

This is a generalization of the lemma used in round 1. Its model-category hypotheses hold for Rezk spaces.

Write
\[
\mathcal V_d=\Theta_d\mathrm{Sp}_{\infty}.
\]
This is a cartesian model category, with monomorphisms as cofibrations; in particular, every presheaf is cofibrant. It is excellent in Lurie’s sense. The latter fact is stated explicitly in Moser–Rasekh–Rovelli, §1.1. [arxiv.org](https://arxiv.org/pdf/1206.4354?utm_source=chatgpt.com)

Haugseng’s Theorem 5.8 supplies strict \(\mathcal V_d\)-enriched presentations. Its hypotheses hold here: the model structure is left proper and tractable, its tensor is cartesian, and the monoid axiom follows because multiplying a trivial cofibration by any presheaf preserves trivial cofibrations. [arxiv.org](https://arxiv.org/pdf/1312.3881?utm_source=chatgpt.com)

Here are the remaining details of the semantic lemma.

### Fibrant enriched presheaves

Choose a small locally fibrant \(\mathcal V_d\)-category \(C\) presenting the given higher category, and put
\[
M=[C^{\mathrm{op}},\mathcal V_d]_{\mathrm{inj}}.
\]
The enriched injective model structure exists by HTT Proposition A.3.3.2 and remains a \(\mathcal V_d\)-enriched model structure by Remark A.3.3.4. Every presheaf is cofibrant. [www.math.ias.edu](https://www.math.ias.edu/~lurie/papers/HTT.pdf?utm_source=chatgpt.com)

The enriched presheaf category has actual cartesian closed structure:
\[
(G^F)(c)=\underline M(yc\times F,G).
\tag{5}
\]
Enriched co-Yoneda gives
\[
\underline M(P,G^F)\cong\underline M(P\times F,G).
\]
Its injective model structure is cartesian, since the pushout-product calculation is pointwise. Consequently, fibrant presheaves are closed under the actual terminal presheaf, products, and exponentials.

Replace the **whole enriched Yoneda diagram**
\[
y:C\longrightarrow M
\]
by an injectively fibrant diagram
\[
i:y\hookrightarrow j
\]
in \([C,M]_{\mathrm{inj}}\). Thus \(j\) remains an enriched functor, each \(jc\) is fibrant, and each \(yc\to jc\) is a trivial cofibration. This uses the enriched diagram theorem a second time; injective fibrancy implies pointwise fibrancy by HTT Remark A.3.3.5. [www.math.ias.edu](https://www.math.ias.edu/~lurie/papers/HTT.pdf?utm_source=chatgpt.com)

For \(a,b\in C\), restriction gives a weak equivalence
\[
\underline M(ja,jb)
\longrightarrow
\underline M(ya,jb)
\cong jb(a).
\]
Its composite with
\[
C(a,b)\longrightarrow\underline M(ja,jb)
\]
is \(i_b(a)\). Two-out-of-three proves that \(j\) is fully faithful.

The product comparison
\[
j(A\times B)\longrightarrow jA\times jB
\]
is a pointwise weak equivalence, by the product universal property in \(C\). The terminal comparison is analogous.

For exponentials, evaluation and an inverse, up to homotopy, of the product comparison give an actual map
\[
j(B^A)\longrightarrow(jB)^{jA}.
\tag{6}
\]
Testing (6) by enriched homs out of \(jX\) gives, up to equivalence,
\[
C(X,B^A)\simeq C(X\times A,B).
\]
These tests detect weak equivalences between fibrant presheaves, because
\[
\underline M(jX,Q)
\simeq
\underline M(yX,Q)
\cong Q(X).
\]
Thus (6) is a weak equivalence.

Finally, take the small full enriched subcategory \(D\) generated by the \(jX\) under the actual terminal object, products, and exponentials. Every added presheaf is equivalent to some \(jX\). Hence
\[
C\simeq D
\]
is a cartesian closed equivalence, and \(D\) has the required enriched universal-property isomorphisms. This proves the semantic lemma.

## 3. Interpretation and the retract

First consider Question 1.

Let \(\mathcal F\) be the free pseudo cartesian closed \((\infty,3)\)-category on \(\Gamma\), and choose, by the semantic lemma,
\[
e:\mathcal F\simeq D.
\]

An interpretation of the specified globe
\[
f,g,\alpha,\alpha',\Xi
\]
in \(D(A,B)\) gives an actual presheaf map
\[
X=N_{\Theta_2}G\longrightarrow D(A,B).
\tag{7}
\]
Rezk’s §§11.8–11.12 describe cells and parallel boundaries by maps out of globe representables and their boundaries. Since the boundary inclusion is a cofibration and \(D(A,B)\) is fibrant, representatives can be chosen with the prescribed boundary. [rezk.web.illinois.edu](https://rezk.web.illinois.edu/cs-objects-revised-arxiv.pdf?utm_source=chatgpt.com)

Evaluate \(D\) at each \((\theta,k)\). Its enriched universal-property isomorphisms make the resulting hom-sets into an ordinary cartesian closed category. The maps (7), together with the other constant interpretations, therefore induce ordinary free-CCC interpretation functors in every degree.

Uniqueness of ordinary interpretation makes them commute with all presheaf restriction maps. They assemble into
\[
s:\mathcal K\longrightarrow D.
\tag{8}
\]

Freeness supplies
\[
q:\mathcal F\longrightarrow\mathcal K.
\]
The functors \(sq\) and \(e\) induce the same interpretation of the **entire** generating signature, including \(\Xi\). Therefore
\[
sq\simeq e.
\]
Setting \(r=e^{-1}s\), we obtain
\[
rq\simeq\operatorname{id}_{\mathcal F}.
\tag{9}
\]

For any fixed parallel \(2\)-cells \(p,q\), endpoint transport along (9) makes
\[
\operatorname{Fill}^{\mathcal F}_3(p,q)
\]
a homotopy retract of the corresponding \(3\)-cell space in \(\mathcal K\). By (3), the latter is empty or contractible. Hence
\[
\boxed{\operatorname{Fill}^{\mathcal F}_3(p,q)
\text{ is empty or contractible}.}
\tag{10}
\]

The same retract transfers existence whenever the model has a filler.

Finally, the core argument from your background applies with \(3\) in place of \(1\): a signature with no generators above dimension \(3\) has its free higher cartesian closed category in \((\infty,3)\)-categories. Products and exponentials pass to the core, and freeness gives the comparison. The relevant core adjunctions are Ozornova–Rovelli–Walde, Theorem 2.20. [arxiv.org](https://arxiv.org/pdf/2603.11005?utm_source=chatgpt.com)

Thus (10) is the requested statement in \(\mathcal C(\Gamma)\). If \(P,Q:p\Rrightarrow q\) are existing parallel \(3\)-cells, they are two points of a nonempty contractible space, so
\[
\operatorname{Fill}_4(P,Q)
\simeq
\operatorname{Path}_{\operatorname{Fill}_3(p,q)}(P,Q)
\simeq *.
\tag{11}
\]

### The two orders of applying \(\Xi\)

For two relevant addresses,
\[
G^2\bigl((f,f),(g,g)\bigr)=[1]^2.
\]
Its four vertices are
\[
(\alpha,\alpha),\quad
(\alpha',\alpha),\quad
(\alpha,\alpha'),\quad
(\alpha',\alpha').
\]
The two orders of applying \(\Xi\) are two factorizations of the unique arrow
\[
(\alpha,\alpha)\longrightarrow(\alpha',\alpha').
\]
All parallel \(3\)-cell expressions involving these updates and their interchangers have the same image in this poset. Equations (9)–(11) give a contractible space of \(4\)-comparisons in the free pseudo structure.

This settles Question 1, without requiring the particular \(3\)-goal to be Dir-accepted.

## 4. What Dir forces on a general finite context

Now fix an \(n\)-dimensional Dir judgment with no generators above dimension \(n\), and put
\[
d=n-1.
\]

Shift generator dimensions down by one:

- primitive \(1\)-generators become \(0\)-generators;
- primitive \(2\)-generators become \(1\)-generators;
- and so on.

The recursive checks first ensure that these data have **variable boundaries in every positive shifted dimension**. To see why deletion cannot hide a composite boundary, consider a deleted intermediate vertex of a top-dimensional chain. It is parallel to the chain’s root. That root survives the source reduction and is checked recursively. Therefore every vertex of that chain has the same variable boundaries certified for the root. Isolated vertices survive and are checked directly.

The resulting finite globular set \(G_\Gamma\) is a disjoint union of globular cardinals.

Here is a direct proof.

At shifted dimension \(0\), the assertion says that a set is a disjoint union of singleton diagrams. Suppose it holds for the source reduction. The top generators form disjoint chains
\[
c_0\xrightarrow{e_1}c_1
\xrightarrow{e_2}\cdots
\xrightarrow{e_r}c_r.
\tag{12}
\]
Only \(c_0\) survives in the source reduction.

A globular cardinal has the linear order generated by
\[
s(a)<a<t(a).
\]
Replace the entry \(c_0\) in its source diagram’s order by
\[
c_0<e_1<c_1<e_2<\cdots<e_r<c_r.
\tag{13}
\]
The dimensions in the inserted block are
\[
d-1,d,d-1,\ldots,d,d-1.
\]
Globularity says that all the \(c_i\) have the same lower boundaries. Consequently, (13) gives exactly the original source and target maps; consecutive dimensions still differ by \(1\), and the endpoint dimensions remain \(0\).

This is the characterization of globular cardinals by finite graded linear orders in Steiner’s Theorem 2.4. [arxiv.org](https://arxiv.org/pdf/math/0608680?utm_source=chatgpt.com)

The construction also proves that the source and target reductions are isomorphic:
\[
\rho:G_\Gamma^-\xrightarrow{\cong}G_\Gamma^+,
\tag{14}
\]
where \(\rho\) sends each root of (12) to its sink and fixes all lower-dimensional generators.

In particular, unused generators produce additional globular-cardinal summands. They do not introduce additional shapes.

## 5. The general normal-form model and its interpretation

Each globular-cardinal summand has one fixed primitive-arrow type \(A_\lambda\to B_\lambda\). Its free strict \(d\)-category \(C_\lambda\) is a \(\Theta_d\)-shape. This identification follows from the description of \(\Theta_d\) as free strict \(d\)-categories on globular pasting diagrams; see Berger, Theorem 3.7, or Ara, §5.6. [arxiv.org](https://arxiv.org/pdf/math/0512575?utm_source=chatgpt.com)

Use the label presheaves
\[
X_\lambda=N_{\Theta_d}C_\lambda.
\]
The same pointwise free-CCC construction gives
\[
\mathcal K_\Gamma(U,V)
\cong
N_{\Theta_d}\!\left(
\coprod_{\nu}
\prod_{p\in P_\nu}C_{\sigma(p)}
\right).
\tag{15}
\]

### Highest-dimensional uniqueness

For a \(\Theta_d\)-shape
\[
C=[m](C_1,\ldots,C_m),
\]
its strict hom categories are
\[
C(i,j)=
\begin{cases}
\displaystyle\prod_{k=i+1}^{j}C_k,&i<j,\\[4pt]
1,&i=j,\\
\varnothing,&i>j.
\end{cases}
\tag{16}
\]
This is the defining enriched description of the \(\Theta\)-construction. [rezk.web.illinois.edu](https://rezk.web.illinois.edu/cs-objects-revised-arxiv.pdf?utm_source=chatgpt.com)

Starting with finite ordinals in dimension \(1\), induction using (16) proves that a \(\Theta_d\)-shape has at most one \(d\)-cell between any fixed parallel \((d-1)\)-cells. Finite products and disjoint unions preserve this property.

The same induction proves that every invertible positive-dimensional cell is an identity. Thus the nerves in (15) are fibrant, and their highest-dimensional cell spaces are empty or points.

### Interpreting a whole pasting diagram

For the general signature, a label is a pasting diagram rather than a single globe. We must extend the given assignment of its generators to its \(\Theta_d\)-nerve.

Let \(I_\theta\) be the globular core of a shape \(\theta\): the presheaf obtained by gluing its generating globe representables along their specified faces. The inclusion
\[
I_\theta\hookrightarrow y\theta
\tag{17}
\]
is a trivial cofibration in the Rezk \(\Theta_d\)-space model. Ara defines these monomorphisms in §5.13, collects them in §5.17, and explicitly includes them among the generating weak equivalences of the Rezk model in §8.1. [arxiv.org](https://arxiv.org/pdf/1206.4354?utm_source=chatgpt.com)

An assignment of the generators gives a map
\[
I_\theta\longrightarrow D(A_\lambda,B_\lambda).
\]
Since the target is fibrant, (17) extends this to
\[
y\theta=N_{\Theta_d}C_\lambda
\longrightarrow D(A_\lambda,B_\lambda).
\tag{18}
\]
The space of extensions is contractible: restriction along (17) is a trivial Kan fibration on simplicial mapping spaces.

Equations (18) provide exactly the label maps needed for pointwise free-CCC interpretation. Applying the semantic lemma and freeness therefore gives, as before,
\[
\mathcal F_n(\Gamma)
\xrightarrow{q}
\mathcal K_\Gamma
\xrightarrow{r}
\mathcal F_n(\Gamma),
\qquad
rq\simeq\operatorname{id}.
\tag{19}
\]

It follows that, for \(n\ge2\),

> **Every \(n\)-cell space between fixed parallel \((n-1)\)-cells is empty or contractible whenever the context satisfies the recursive Dir shape conditions.**

This is the uniqueness assertion. It remains to establish nonemptiness for accepted goals.

## 6. Constructing the filler for an accepted goal

Write the accepted goal as
\[
u\longrightarrow v,
\]
where \(u,v\) are parallel \((n-1)\)-terms.

The avoidance conditions imply that their interpretations come from the respective source and target models:
\[
u^-\in\mathcal K_{\Gamma^-},
\qquad
v^+\in\mathcal K_{\Gamma^+}.
\]

The inclusions into \(\mathcal K_\Gamma\) are injective on cells. One way to verify this is to collapse each top chain to its root, sending its top generators to identities. This defines a retraction of the source inclusion of strict label categories. Collapsing to sinks gives the analogous target retraction. Polynomiality transfers these injections to the normal-form models.

Under the renaming \(\rho\) of (14), the two inclusions agree below shifted dimension \(d-1\).

### Identifying the required target

Suppose first that \(n\ge3\), so \(d-1\ge1\). The source label categories are \(\Theta_{d-1}\)-shapes. Hence the source model has at most one cell of shifted dimension \(d-1\) with any fixed parallel boundary.

Since \(u\) and \(v\) are parallel, injectivity and agreement of the lower boundaries show that
\[
u^-,
\qquad
\rho^{-1}(v^+)
\]
are parallel cells of shifted dimension \(d-1\) in the source model. Therefore
\[
u^-=\rho^{-1}(v^+).
\tag{20}
\]

For \(n=2\), this argument reaches dimension \(0\), where uniqueness is not automatic. Here the recursive base condition supplies precisely what is needed: Mimram’s Theorem 15 says that the accepted \(1\)-type has one βη-class of inhabitants in the source context. After root-to-sink renaming, the target context is the same context. Thus (20) holds in this case as well.

It now suffices to construct a directed \(n\)-cell
\[
i^-(u^-)\longrightarrow i^+(\rho u^-).
\tag{21}
\]

### A strict construction of the root-to-sink action

The construction can be made directly in the label categories.

For a strict \(d\)-category \(C\), define a strict \((d-1)\)-category \(E_d(C)\) by
\[
(E_dC)_k=C_k\quad(k<d-1),
\qquad
(E_dC)_{d-1}=C_d.
\tag{22}
\]
For the highest-dimensional cells, use twice-iterated boundaries, the compositions of \(C\) in directions \(0,\ldots,d-2\), and twice-iterated identities. These satisfy the strict axioms because the corresponding operations in \(C\) do.

There are strict functors
\[
S,T:E_d(C)\rightrightarrows\tau_{\le d-1}C
\tag{23}
\]
which are identities below dimension \(d-1\) and take a \(d\)-cell to its source or target. When \(d=1\), (22) simply means the set of arrows of \(C\), with its source and target maps.

Take \(C\) to be one of the full label categories. For every root \(c_0\), compose its chain (12), obtaining
\[
\zeta_{c_0}:c_0\longrightarrow c_r.
\]
For an isolated root, use its identity \(d\)-cell.

Send each highest-dimensional generator of the source label category to this chain composite, and each lower generator to its unchanged image. Freeness of the source strict category extends this assignment to
\[
\ell:C^-\longrightarrow E_d(C).
\tag{24}
\]
Its two boundary functors satisfy the exact equalities
\[
S\ell=i^-,
\qquad
T\ell=i^+\rho.
\tag{25}
\]

Now express the semantic value of \(u^-\) using (15):
\[
u^-=(\nu,(a_p)_{p\in P_\nu}).
\]
Apply (24) at each address:
\[
\chi_{u^-}
=
(\nu,(\ell(a_p))_{p\in P_\nu}).
\tag{26}
\]
By (25), this is the required cell (21). By (20), its target is exactly \(v\).

This construction handles terms involving currying, evaluation, pairing, and higher composition because the term has already been interpreted in the normal-form model before (26) is formed. It requires no additional coherence assertion about how a higher transformation acts on arbitrary syntax.

Finally, apply the retraction (19) and transport endpoints along \(rq\simeq\operatorname{id}\). This produces a filler in the free pseudo cartesian closed category. Its space is contractible by the uniqueness result.

Thus
\[
\boxed{\text{Every Dir-accepted goal has a contractible space of fillers.}}
\tag{27}
\]

When there are no hypotheses in the goal’s dimension, the core argument one dimension lower also shows that these fillers are invertible.

## 7. Dimensional scope and absence of fullness

The proof above treats an \(n\)-goal in a context of dimension at most \(n\). This covers the usual dimensional typing convention.

It also covers lower-dimensional checks against a context already known to be Dir-pasting. For \(2\le n<\dim\Gamma\), there are distinct parallel \(n\)-generators, obtained as the boundaries of an \((n+1)\)-generator. Those two generators repeat their source and target, so the \(n\)-dimensional distinctness test fails.

If a \(1\)-dimensional pasting goal is allowed in a higher Dir context, its ordinary normal-form hom-set has exactly one element. In (15), that forces exactly one normal-form summand and one \(0\)-cell in every label factor used by it. A \(\Theta\)-shape with one \(0\)-cell is terminal. Hence that entire hom in \(\mathcal K_\Gamma\) is terminal, and the retraction again gives contractible fillers.

No fullness condition enters the proof. An unused generator contributes no address to the relevant product in (15). Repeated uses contribute distinct addresses, and (26) applies the directed chain independently at each one.

For the specific signature \(f,g,\alpha,\alpha',\Xi\), this gives both requested conclusions: \(3\)-cell spaces are empty or contractible, and every pair of existing parallel \(3\)-cells has a contractible space of invertible \(4\)-comparisons.
