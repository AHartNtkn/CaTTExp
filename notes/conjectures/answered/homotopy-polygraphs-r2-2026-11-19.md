# Which polygraphs are homotopy polygraphs? From dimension 2 to every dimension

*A self-contained problem. It assumes familiarity with polygraphs (computads), strict ω-categories and (∞,ω)-categories, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** The most general recognition theorem you can prove, valid in every dimension: ideally an exact characterisation of the finite homotopy polygraphs, and failing that the sharpest sufficient condition with a matching counterexample. Isolated low-dimensional examples are of little use to us.

## 1. Setting

- A **polygraph** Γ (computad) is a set of generators of each dimension, each n-generator having a source and a target which are parallel (n−1)-cells of the free strict ω-category on the lower generators. All polygraphs here are finite.
- `F(Γ)` is the free strict ω-category on Γ.
- `Free(Γ)` is the free (∞,ω)-category on Γ: generators are attached one at a time along their boundaries by pushouts of `∂Dⁿ → Dⁿ` in (∞,ω)-categories (Loubaton's Cat_ω, arXiv 2406.05425, or Campion's framework, arXiv 2311.00200). Strict ω-categories are (∞,ω)-categories, so there is a canonical comparison `c_Γ : Free(Γ) → F(Γ)`.
- Γ is a **homotopy polygraph** (or *homotopical*) when c_Γ is an equivalence, i.e. when every strict pushout attaching a generator is also a homotopy pushout.
- A 2-cell `1_x ⇒ 1_x` of F(Γ) other than the identity is a **bubble**.
- Γ is **positive in every dimension** when every generator of dimension n ≥ 2 has a source and a target that are not identity cells. (For n = 2: both boundary paths are nonempty.)
- More generally, a non-identity n-cell `e : 1^{n−1−k}_c ⇒ 1^{n−1−k}_c` (n ≥ 2, source and target both the (n−1)-dimensional iterated identity of a k-cell c, k ≤ n−2) is an **iterated-identity endo-cell**. Γ is **bubble-free in every dimension** when F(Γ) has none. For n = 2, k = 0 these are the bubbles.
- A strict ω-functor p : C → D is a **discrete Conduché functor** when every factorisation of p(x) in D lifts uniquely to a factorisation of x in C.

## 2. Why it matters

Homotopy polygraphs are exactly the computads whose free (∞,ω)-category can be computed strictly. Finite presentations of Grothendieck constructions over a free base, the comparison of weak and strict free objects in type theories for weak ω-categories, and pasting theorems for non-globular shapes all need this hypothesis, and at present each use checks it by hand. Dimension 2 is now settled exactly (item 5 below); everything above dimension 2 is open beyond closure rules.

## 3. What is known

1. **Pasting theorems.** For a strongly loop-free Steiner complex K, ν(K) is the free (∞,ω)-category on its atoms (Campion, *Pasting diagrams in higher categories are free*, arXiv 2311.00200). Chanavat (*A strengthened (∞,n)-categorical pasting theorem*, arXiv 2603.22242) extends this to regular directed complexes with frame-acyclic molecules (Thm 3.17), and deduces that positive 2-polygraphs (Cor. 3.39) and regular 3-polygraphs in Henry's sense (Cor. 3.38) are homotopical. Comment 3.40 there describes the extension to arbitrary regular and positive polygraphs as expected, without proof.
2. **Bubbles obstruct.** If F(Γ) has a bubble q, sending every 2-generator to 1 gives r : F(Γ) → B²ℕ with r(q) = k > 0, and q defines i : B²ℕ → F(Γ) by Eckmann–Hilton; ri = [k] acts by kʲ on H_{2j}(K(ℤ,2); ℚ), so the groupoidification of F(Γ) has nonzero rational homology in every even degree, while that of Free(Γ) is a finite CW complex. Example: (x; σ : 1_x ⇒ 1_x), F(Γ) = B²ℕ ≃ K(ℤ,2) after groupoidification, Free(Γ) ≃ S².
3. **Bubble-freeness is undecidable**, already for one-vertex 2-polygraphs with no generating bubble (reduction from reachability in positive semi-Thue systems via an insertion rule 1 ⇒ L w Z and a deletion rule L v Z ⇒ 1).
4. **Dimension 2, combinatorial core.** For a progressive one-colour string diagram G every component of which meets the boundary, the cell complex K_G whose vertices are the *tier encodings* of G (decompositions into layers of simultaneous generators) and whose faces are products of permutohedra (splitting a layer) has contractible components. Proof: right-exchange runs (which terminate for boundary-connected diagrams, Delpeuch–Vicary arXiv 1804.07832, Cor. 2.16) give a unique maximal cell F(v) with source v; deleting vertices in topological order removes a closed star along its antistar, a ball. Two floating scalars give a circle, so the boundary condition is needed.
5. **Dimension 2, exact answer.** A finite 2-polygraph is homotopical **iff it is bubble-free**. The "if" direction uses item 4 and Heidemann's mesh model of (∞,2)-categories (arXiv 2411.04870): a presheaf X_Γ on meshes with L₂ j*X_Γ ≃ Free(Γ), and an objectwise equivalence j*X_Γ → N₂F(Γ) computed as X_Γ(Q) ≃ B(Q↓t) ≃ ⊔_G BP_G over the diagrams G of shape Q, with each BP_G contractible by item 4 (a bubble-free polygraph has no boundary-disjoint diagram component and no diagram automorphisms). Consequences: homotopicality of finite 2-polygraphs is undecidable (item 3); the finite case of Guetta's conjecture (homologically coherent ⟺ bubble-free, *Homology of strict ω-categories*, arXiv 2104.12662, Conj. 6.6.5) holds; every 2-polygraph whose 2-generators all have non-empty target (or all non-empty source) is homotopical, with any number of vertices.
6. **Suspensions.** Σ^k Γ is homotopical iff Γ is (Hom_{ΣC}(0,1) ≃ C, and suspension preserves and detects the comparison). So for 2-polygraphs, Σ^k Γ is homotopical iff Γ is bubble-free.
7. **Graph assembly, every dimension.** For a finite directed graph Q (loops and parallel edges allowed) and finite polygraphs P_e on its edges, the polygraph B_Q(P_•) with vertices Q₀ and (r+1)-generators ⊔_e (P_e)_r (the free category on Q enriched in the F(P_e)) is homotopical iff every P_e is. In particular **adjoining a 1-generator preserves homotopicality in every dimension**.
8. **Discrete Conduché descent (Theorem A).** If p : Γ → Δ is a polygraph map with F(p) discrete Conduché and Δ homotopical, then Γ is homotopical. Surjectivity on generators alone is not enough ([1] → F(loop)).
9. **Typing into positive templates (Theorem B).** A polygraph map Γ → Δ into a homotopical Δ that is source-positive or target-positive in every dimension makes Γ homotopical (Henry's cartesianness for such polygraphs makes F(p) discrete Conduché).
10. **Mapping cylinders (Theorem C).** Strict double mapping cylinders of finite homotopical presentations along arbitrary strict functors have finite homotopical presentations, with generators Δ_n ⊔ ℰ_n ⊔ Γ_{n−1}; Gray cylinders, cones and suspensions are instances (Loubaton arXiv 2406.05425 Thm 2.3.3.22, Campion's pasting theorem for Dⁿ ⊗ [1]). Items 7–10 give a sound finite-certificate system, but typing into templates from a good class cannot leave that class, so it does not reach all positive polygraphs.
11. **Positivity is not necessary.** (∗; t; η : 1 ⇒ t) is homotopical (Blans–Linskens, arXiv 2605.03150), and so is its suspension, a non-positive 3-polygraph. Regularity is not necessary either: the positive non-regular 3-polygraph x, y, z; p, q : x → y, r : y → z; α, β : p ⇒ q; ζ : α ▷ r ⇛ β ▷ r is homotopical.
12. **Positivity in the top dimension alone is not enough.** One vertex, b : 1 ⇒ 1, Ω : b ⇛ b: Ω has non-identity boundaries, but b is a bubble.
13. **Strict versus "stricter".** Chanavat (*Homotopy theory of stricter n-categories*, arXiv 2509.26563, Comment 2.67) gives a 4-dimensional regular directed complex whose molecules do not form a polygraph under strict composition. This is **not** a counterexample to the positive case: the extra equations appear in the passage from the free strict category to molecules, not in the free strict category itself.

14. **Higher bubbles obstruct in every dimension.** If a nonidentity n-cell is an endomorphism of an iterated identity on any k-cell, k ≤ n − 2, then the strict n-skeleton has nonzero mod-p cohomology in arbitrarily high degrees for some prime p. The free cellular n-skeleton has cohomological dimension at most n, and homotopicality passes to skeleta. This covers composite bubbles and positive-dimensional bases. [Proof of the higher-bubble obstruction](../answered/higher-bubble-obstruction-2026-11-19.md)

## 4. Questions

**Question 1 (main: the all-dimensional characterisation).** Is a finite polygraph Γ homotopical **iff F(Γ) is bubble-free in every dimension** (no iterated-identity endo-cell, §1)? This is the all-dimensional form of item 5. "Only if" for endo-cells of 1_x^{n−1} at a vertex x should follow by the argument of item 2 (an endo-cell q of 1^{n−1}_x gives Bⁿℕ → F(Γ) → Bⁿℕ with nonzero degree); please prove or refute it for endo-cells of 1^{n−1−k}_c with c of positive dimension k. For "if", the expected route is item 5's method one dimension up: a mesh or Θ-presheaf model of the free (∞,n)-category in which the fibres over each shape are classifying spaces of combinatorial complexes of "encodings" of a pasting diagram, contractible under the bubble-free hypothesis.

**Status, 2026-11-19.** Item 14 settles the “only if” conjecture over every base cell. The open direction is whether bubble-freeness suffices.

**Question 2 (positivity in every dimension).** If Question 1 is out of reach, prove that every finite polygraph that is positive in every dimension (§1) is homotopical — the "positive" half of Chanavat's Comment 3.40, which is a sub-case of Question 1 because positive polygraphs are bubble-free in every dimension. If it fails, give the smallest counterexample with a proof of non-homotopicality.

**Question 3 (dimension 3).** As a fallback, settle Question 1 for finite 3-polygraphs: is a finite 3-polygraph homotopical iff F(Γ) has no bubble and no non-identity 3-cell 1_{1_x} ⇛ 1_{1_x} or 1_f ⇛ 1_f? Item 4's combinatorics suggest the 3-dimensional analogue: contractibility of the complex of "layerings" of a boundary-connected 3-dimensional diagram in which no component is a closed 2-sphere.

## 5. What counts as a solution

A proof of Question 1, 2 or 3; a counterexample with a proof of non-homotopicality (for example by a homology computation as in item 2); or a published reference.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (Thm 3.17, Cors. 3.38–3.39, Comment 3.40) and arXiv 2509.26563.
- Heidemann, arXiv 2411.04870 (mesh model of (∞,n)-categories).
- Delpeuch–Vicary, arXiv 1804.07832.
- Henry, *Regular polygraphs and the Simpson conjecture*, arXiv 1807.02627.
- Guetta, arXiv 2104.12662 (Conj. 6.6.5, Thm 6.11); Guetta, *Polygraphs and discrete Conduché ω-functors*, Higher Structures 4(2) (2020).
- Loubaton, arXiv 2406.05425.
- Blans–Linskens, arXiv 2605.03150.
- No published recognition theorem for homotopy polygraphs in dimension ≥ 3 beyond the classes in item 1 was found.

# Researcher Response 1

**The full “only if” direction of Question 1 can be proved in every dimension, including endo-cells based at positive-dimensional cells.** The proof uses suspended Eilenberg–Mac Lane spaces and Steenrod operations.

There is also an explicit sufficient condition in every dimension: **positive-to-one polygraphs are homotopical**, with a dimensionwise dual variant. Below I prove both statements and give an all-dimensional family showing why groupoidification alone ceases to recognize homotopicality above dimension two.

These results do **not** establish the converse in Question 1, the unrestricted positive case, or the sufficiency direction in Question 3.

## 1. The necessary condition holds in every dimension

### Theorem 1

Assume the discrete Conduché descent theorem in your item 8. If a finite polygraph \(\Gamma\) is homotopical, then \(F(\Gamma)\) has no nonidentity cell
\[
q:1_c^{\,n-1-k}\Longrightarrow 1_c^{\,n-1-k},
\qquad 0\le k\le n-2.
\]

More precisely, suppose such a \(q\) exists. Let \(\Gamma_{\le n}\) be the \(n\)-skeleton, and let \(w>0\) be the total number of generating \(n\)-cells in any expression for \(q\). For every odd prime \(p\nmid w\),
\[
\boxed{
H^{\,n+2(p^j-1)}
\!\left(BF(\Gamma_{\le n});\mathbb F_p\right)\ne0
\quad\text{for every }j\ge1.
}
\tag{1}
\]
Here \(B\) denotes groupoidification, or equivalently the classifying space of the Street nerve.

The proof has four steps.

### 1.1. Skeleton inclusions are discrete Conduché

For each dimension \(r\), let \(\ell_r(a)\) count the generating \(r\)-cells in an expression for an \(r\)-cell \(a\). Associativity, units and exchange preserve this count, so it is well-defined and satisfies
\[
\ell_r(a*_i b)=\ell_r(a)+\ell_r(b).
\]
Furthermore,
\[
\ell_r(a)=0
\quad\Longleftrightarrow\quad
a\text{ is an identity }r\text{-cell}.
\tag{2}
\]
Indeed, an expression with count zero is composed entirely of identity \(r\)-cells, and the strict identity laws reduce it to an identity.

Consider
\[
j_n:F(\Gamma_{\le n})\hookrightarrow F(\Gamma).
\]
We prove that every factorization of a cell in its image lifts uniquely.

In dimensions \(r\le n\), the two categories have the same \(r\)-cells. Suppose \(r>n\), and consider a factorization
\[
1_a=y*_i z
\]
of an \(r\)-cell in the image. Additivity and (2) imply
\[
y=1_b,\qquad z=1_d.
\]

If \(i=r-1\), composability forces \(b=d\), and equality of identities gives \(a=b=d\). If \(i<r-1\), the equation becomes
\[
a=b*_i d,
\]
and induction on \(r\) shows that \(b,d\), hence \(y,z\), belong to the skeleton. Uniqueness follows from injectivity of \(j_n\).

Thus \(j_n\) is discrete Conduché. Your descent theorem gives
\[
\Gamma\text{ homotopical}
\quad\Longrightarrow\quad
\Gamma_{\le n}\text{ homotopical}.
\tag{3}
\]

This reduction is essential: counting \(n\)-generators need not define a functor on the whole of \(F(\Gamma)\), because an \((n+1)\)-generator can have boundaries with different counts.

### 1.2. An endo-cell based at a \(k\)-cell gives a suspended scalar

Write
\[
E_r=B^r\mathbb N,
\]
the strict category with one cell below dimension \(r\), and with \(\mathbb N\) as its set of \(r\)-cells, all \(r\)-dimensional compositions being addition.

Put
\[
C=F(\Gamma_{\le n}),\qquad m=n-k\ge2.
\]
Eckmann–Hilton supplies a strict functor
\[
i:\Sigma^kE_m\longrightarrow C
\tag{4}
\]
sending the principal \(k\)-cell to \(c\) and the generating \(n\)-cell to \(q\).

Since \(C\) has no generators above dimension \(n\), there is also a strict functor
\[
\lambda:C\longrightarrow E_n
\tag{5}
\]
sending every \(n\)-generator to \(1\), and every lower-dimensional cell to the appropriate identity. Set
\[
w=\lambda(q)=\ell_n(q)>0.
\]

Let
\[
\kappa_{k,m}:\Sigma^kE_m\longrightarrow E_{m+k}
\]
send its top generator to \(1\) and all lower cells to identities. Then
\[
\lambda i=[w]\kappa_{k,m},
\tag{6}
\]
where \([w]\) multiplies the top-dimensional monoid by \(w\).

Ara’s Theorem 4.9 and Example 4.10 give
\[
BE_r\simeq K(\mathbb Z,r),
\tag{7}
\]
with the generating \(r\)-cell corresponding to \(1\in\pi_rK(\mathbb Z,r)\). [arxiv.org](https://arxiv.org/pdf/1808.02650?utm_source=chatgpt.com)

We also have a natural equivalence
\[
B(\Sigma A)\simeq\Sigma BA.
\tag{8}
\]
For completeness, this follows by using the iterated nerve: after realizing the inner directions, \(\Sigma A\) has two vertices, \(BA\) as its only nonidentity hom-space, and no composable pair of nonidentity outer arrows. Its realization is therefore the unreduced suspension of \(BA\). Ara–Maltsiniotis, Corollary 3.7 and Theorem 3.16, identify this realization naturally with the Street classifying space. [arxiv.org](https://arxiv.org/pdf/2010.00266?utm_source=chatgpt.com)

Consequently, (4) gives
\[
Bi:\Sigma^kK(\mathbb Z,m)\longrightarrow BC.
\]

Let \(u_r\in H^r(K(\mathbb Z,r);\mathbb Z)\) be the integral fundamental class. With compatible orientations,
\[
(B\kappa_{k,m})^*u_n=\sigma^ku_m,
\tag{9}
\]
where \(\sigma\) is the reduced cohomological suspension.

One can check the coefficient in (9) directly. The generating \(n\)-cell of \(\Sigma^kE_m\) defines the suspension of the fundamental sphere
\[
S^m\longrightarrow BE_m.
\]
It generates \(H_n(\Sigma^kK(\mathbb Z,m);\mathbb Z)\), and \(\kappa_{k,m}\) sends that generating cell to \(1\), so its degree on this bottom homology group is \(1\).

Define
\[
v=(B\lambda)^*u_n\in H^n(BC;\mathbb Z).
\]
Equations (6) and (9) imply
\[
\boxed{(Bi)^*v=w\,\sigma^ku_m.}
\tag{10}
\]

This is the replacement for the unsuspended retraction argument.

### 1.3. Stable cohomology operations detect the suspended class

Fix an odd prime \(p\nmid w\), and write bars for reduction modulo \(p\).

We use the Steenrod reduced powers
\[
P^a:H^d(-;\mathbb F_p)\longrightarrow
H^{d+2a(p-1)}(-;\mathbb F_p).
\]
The needed properties are naturality, additivity, the Cartan formula, commutation with suspension, and
\[
P^a(z)=z^p\quad\text{when }|z|=2a.
\]
These are stated in Steenrod–Epstein, *Cohomology Operations*, Chapter VI §1, printed pages 76–77. [sas.rochester.edu](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/steenrod-epstein.pdf?utm_source=chatgpt.com)

Define
\[
\theta_j=P^{p^{j-1}}\cdots P^pP^1.
\]
Its degree is
\[
|\theta_j|
=2(p-1)(1+p+\cdots+p^{j-1})
=2(p^j-1).
\tag{11}
\]

We claim that, for every \(m\ge2\),
\[
\theta_j\bar u_m\ne0.
\tag{12}
\]

Here is an elementary proof, avoiding the full computation of the cohomology of Eilenberg–Mac Lane spaces.

For \(m=2\), use
\[
K(\mathbb Z,2)\simeq\mathbb CP^\infty,
\qquad
H^*(\mathbb CP^\infty;\mathbb F_p)=\mathbb F_p[x],
\quad |x|=2.
\]
Successive applications of the top-power formula give
\[
\theta_jx=x^{p^j}\ne0.
\]

For \(m>2\), let \(s\) be the integral fundamental class of \(S^{m-2}\), and let
\[
g:\mathbb CP^\infty\times S^{m-2}\longrightarrow K(\mathbb Z,m)
\]
classify the integral class \(xs\). The polynomial cohomology calculation and the representability of integral cohomology by \(K(\mathbb Z,m)\) are Hatcher’s Theorems 3.19 and 4.57. [pi.math.cornell.edu](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf?utm_source=chatgpt.com)

Every positive reduced power of \(\bar s\) vanishes for dimensional reasons. The Cartan formula therefore gives, inductively,
\[
g^*(\theta_j\bar u_m)
=\theta_j(\bar x\,\bar s)
=\bar x^{p^j}\bar s
\ne0.
\]
This proves (12).

Apply \(\theta_j\) to (10). Naturality, additivity and stability give
\[
\begin{aligned}
(Bi)^*(\theta_j\bar v)
&=\theta_j\bigl(w\,\sigma^k\bar u_m\bigr)\\
&=w\,\sigma^k(\theta_j\bar u_m)\\
&\ne0.
\end{aligned}
\]
Thus \(\theta_j\bar v\ne0\). Together with (11), this proves (1).

The argument applies equally to odd and even \(n\). In particular, it does not rely on unbounded rational cohomology.

### 1.4. Contradiction with homotopicality

Groupoidifying the globular attachments defining
\(\mathrm{Free}(\Gamma_{\le n})\) gives an \(n\)-dimensional CW model: a globe has contractible groupoidification, its boundary has the homotopy type of a sphere, and groupoidification preserves the attaching pushouts.

If \(\Gamma_{\le n}\) were homotopical, \(BC\) would have that homotopy type. Its cohomology would vanish above dimension \(n\), contradicting (1). Equation (3) then rules out homotopicality of \(\Gamma\). This proves Theorem 1.

### Consequence for Question 3

For a nonidentity
\[
q:1_f\Rrightarrow1_f
\]
in a free strict \(3\)-category, take \(k=1,m=2,n=3\). The proof gives
\[
H^{\,2p^j+1}\!\left(BF(\Gamma_{\le3});\mathbb F_p\right)\ne0
\qquad(j\ge1,\ p\nmid\ell_3(q)).
\]

Together with the \(k=0,n=3\) case and the reduction to the \(2\)-skeleton, this establishes **all of the necessary conditions listed in Question 3**.

## 2. Groupoidification alone fails as a recognition test from dimension three onward

The skeleton reduction cannot be replaced by a claim that every lower-dimensional bubble forces unbounded cohomology of the entire strict category.

Consider
\[
\Pi=
\left(
x;\quad
a:1_x\Rightarrow1_x;\quad
\varepsilon:a\Rrightarrow1_{1_x}
\right).
\tag{13}
\]

Then
\[
B\mathrm{Free}(\Pi)\simeq *,
\qquad
BF(\Pi)\simeq *,
\]
but \(\Pi\) is not homotopical.

Here are the computations.

For the weak free category, the generator \(a\) gives \(S^2\) after groupoidification. The generator \(\varepsilon\) attaches a \(3\)-cell by a map of degree \(1\), so
\[
B\mathrm{Free}(\Pi)\simeq S^2\cup_{\mathrm{id}}D^3\simeq *.
\]

For the strict free category, its \(2\)-cells are the natural numbers. There is exactly one \(3\)-cell \(m\to n\) when \(m\ge n\), and none otherwise. Indeed, Eckmann–Hilton makes the two lower compositions a strictly commutative tensor product, and every \(3\)-cell reduces to
\[
\varepsilon^{\otimes(m-n)}\otimes1_{a^{\otimes n}}.
\]
Thus the innermost hom-category is the poset
\[
(\mathbb N,\ge),
\]
which has terminal element \(0\). Its nerve is contractible, and the iterated nerve description makes \(BF(\Pi)\) contractible as well.

Nevertheless, the \(2\)-skeleton has the bubble \(a\). Skeleton descent, or Theorem 1, proves that \(\Pi\) is not homotopical.

This also gives a homologically coherent, nonhomotopical finite \(3\)-polygraph: its polygraphic chain complex has
\[
C_3=C_2=C_0=\mathbb Z,\qquad C_1=0,\qquad d_3=-1,
\]
so its homology agrees with the homology of its contractible Street nerve.

By suspension, for every \(d\ge3\),
\[
\Sigma^{d-3}\Pi
\]
is a finite \(d\)-polygraph whose comparison becomes an equivalence after groupoidification but is not an equivalence of \((\infty,\omega)\)-categories.

The dimension threshold is sharp under your dimension-two theorem: for finite \(2\)-polygraphs, equivalence after groupoidification excludes bubbles, and bubble-freeness implies homotopicality.

These examples have iterated-identity endo-cells. They delimit recognition by global homotopy type or homology; they do not refute your proposed bubble-free characterization.

## 3. An explicit sufficient condition in every dimension

### Theorem 2: positive-to-one recognition

Let \(\Gamma\) be a finite polygraph satisfying, for every generator \(a\in\Gamma_d\), \(d\ge2\),
\[
t_{d-1}(a)\in\Gamma_{d-1},
\qquad
s_{d-1}(a)\text{ is not an identity}.
\tag{14}
\]
Then \(\Gamma\) is homotopical.

Thus the target must be an actual generating cell, not a whiskered generator or an arbitrary composite.

This follows by combining Zawadowski’s description of positive-to-one polygraphs with Chanavat’s theorem for directed complexes with acyclic atoms. The compatibility of the specified generating bases matters, so I include that step.

### 3.1. The opetopic presheaf

Let \(\mathcal O^+\) be a skeleton of the category of positive opetopes. Zawadowski’s Corollary 13.5 identifies positive-to-one polygraphs with presheaves on \(\mathcal O^+\), using
\[
K_\Gamma(O)=\operatorname{Hom}_{\mathrm{pPoly}}(O^*,\Gamma).
\]
His Proposition 12.2 gives a unique labelled opetope presentation for each generator. Consequently,
\[
\Gamma_d\cong
\coprod_{\substack{O\in\mathcal O^+\\\dim O=d}}K_\Gamma(O),
\tag{15}
\]
with the boundary restrictions recording the attaching maps. [arxiv.org](https://arxiv.org/pdf/0708.2658?utm_source=chatgpt.com)

Leclerc identifies these positive opetopes with dendritic face complexes; their morphisms identify the source with the principal face ideal determined by the image of its greatest face. Hadzihasanovic identifies the resulting shapes as acyclic atoms and proves closure under taking faces. Hence positive opetopes form a full sieve in the category of atoms. [higher-structures.math.cas.cz](https://higher-structures.math.cas.cz/api/files/issues/Vol9Iss2/Leclerc?utm_source=chatgpt.com)

We may therefore extend \(K_\Gamma\) to a directed complex \(X_\Gamma\) by setting
\[
X_\Gamma(A)=
\begin{cases}
K_\Gamma(A),&A\text{ a positive opetope},\\
\varnothing,&\text{otherwise}.
\end{cases}
\tag{16}
\]
The sieve condition ensures that all restriction maps are defined. Every atomic section of \(X_\Gamma\) has an acyclic domain.

### 3.2. Identification of the strict presentation

For a positive opetope \(O\), there is a natural isomorphism
\[
O^*\cong\operatorname{Mol}/O
\tag{17}
\]
preserving the face generators.

To verify (17), induct on dimension. Both categories are freely generated by the faces. In Zawadowski’s construction, the generator associated with a face \(x\) has source and target
\[
d[x]=[\delta(x)],\qquad c[x]=[\gamma(x)],
\]
and composition of compatible subcardinals is their union. [arxiv.org](https://arxiv.org/pdf/0708.2658?utm_source=chatgpt.com)

On the molecule side, the corresponding source is
\[
M=\partial^-\operatorname{cl}\{x\}
  =\operatorname{cl}\delta(x).
\]
Choose an atomic pasting decomposition of \(M\). Under the already constructed lower-dimensional isomorphism, each factor maps to its face closure in \(O^*\). Composition there takes their union, which is exactly \([\delta(x)]\). The target similarly maps to \([\gamma(x)]\).

Thus the source and target **composites** agree, and the identification extends across the generator \(x\). Induction proves (17); naturality under face embeddings follows because the isomorphism sends each face generator to that same face generator. Freeness on the atomic basis is provided by the directed-complex results used in Chanavat’s pasting theorem. [arxiv.org](https://arxiv.org/html/2404.07273v2?utm_source=chatgpt.com)

Now use (15). The atomic sections of \(X_\Gamma\) correspond exactly to the generators of \(\Gamma\). By (17), their labelled source and target composites are exactly those prescribed by \(\Gamma\). Therefore
\[
\operatorname{Mol}/X_\Gamma\cong F(\Gamma)
\tag{18}
\]
as strict categories with their specified polygraphic bases.

### 3.3. Apply the pasting theorem

Chanavat’s Corollary 3.27 says that a directed complex with acyclic atoms generates a homotopy polygraph. Apply it to \(X_\Gamma\), then use the basis-preserving identification (18). This proves the canonical comparison for \(\Gamma\), establishing Theorem 2. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

### Dimensionwise dual variant and finite test

For each dimension \(d\ge2\), choose either source or target. Suppose every \(d\)-generator has:

- its chosen boundary equal to one generating \((d-1)\)-cell;
- its other boundary nonidentity.

Then \(\Gamma\) is homotopical. Apply the globular opposite reversing precisely the selected dimensions to obtain a positive-to-one polygraph. Opposites preserve globe attachments and carry the strict/weak comparison to the corresponding comparison.

The choice is uniform **within each dimension**, but may differ between dimensions.

This gives a decidable sufficient test on a finite presentation: in each dimension, test the target condition for all generators or the source condition for all generators. Equality with a specified generator is decidable by the computad word problem; identity detection also follows directly from (2). Makkai proves the required word-problem decidability in Theorem 7.(3). [math.mcgill.ca](https://www.math.mcgill.ca/makkai/WordProblem/WordProblemCombined.pdf?utm_source=chatgpt.com)

## 4. Status of the three questions

| Statement | Result established here |
|---|---|
| Homotopical \(\Rightarrow\) bubble-free in every dimension | **Proved**, including endo-cells based at arbitrary positive-dimensional cells |
| Bubble-free in every dimension \(\Rightarrow\) homotopical | Not established |
| Every positive polygraph is homotopical | Proved for the positive-to-one class and its dimensionwise duals; unrestricted case not established |
| Dimension-three necessary conditions in Question 3 | **All proved** |
| Dimension-three sufficiency in Question 3 | Not established |
| Recognition solely by groupoidification or homological coherence | **Fails in every dimension \(\ge3\)**, by the suspended family above |

The unresolved sufficiency step remains contractibility of the appropriate encoding or subdivision spaces over a **fixed strict cell**. Absence of iterated-identity endo-cells supplies the obstruction theorem above, but does not by itself provide that contractibility argument. Chanavat’s Comment 3.40 likewise leaves the unrestricted positive extension contingent on a subdivision-contractibility result. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

# Researcher Response 2

**Higher bubbles obstruct homotopicality over any base cell.** Let Γ be a finite polygraph. Suppose its free strict category contains a nonidentity n-cell $q:1^{n-1-k}_c\to 1^{n-1-k}_c$, where $0\le k\le n-2$. Then Γ is not homotopical. The proof uses the same space $K(\mathbb Z,2)$ for every base dimension.

**Proof.** Put $d=n-2$, $b=1^{d-k}_c$ (with $1^0_c=c$), and $C=F(\Gamma_{\le n})$. In the d-fold hom specified by the faces of b, q is a 2-endomorphism of the identity arrow on b. Its horizontal and vertical powers agree by Eckmann–Hilton. Sending the generator of $B^2\mathbb N$ to q in this hom, then using categorical suspension, gives the first of two strict functors
$$
\Sigma^d B^2\mathbb N \xrightarrow{i} C \xrightarrow{r} B^n\mathbb Z.
$$
The second sends each n-generator to 1 and each lower generator to the unique cell of its degree. Thus $m=r(q)$ counts the n-generators in q with multiplicity. Since a composite of identity n-cells is an identity, $m>0$.

Write $|-|$ for groupoidification. The source of $|i|$ is homotopy equivalent to $\Sigma^d\mathbb{CP}^{\infty}$ and the target of $|r|$ to $K(\mathbb Z,n)$. Let x and u be their respective unsuspended degree-two and degree-n fundamental classes. On the bottom sphere $\Sigma^d\mathbb{CP}^1$, the composite represents m in $\pi_n K(\mathbb Z,n)$ because its top globe maps to m. Restriction to that sphere is an isomorphism in degree n, so $|i|^*|r|^*u=m\,\sigma^d x$, where σ is cohomology suspension.

Choose an odd prime p not dividing m and reduce coefficients modulo p. Starting with $a_0=|r|^*u$, set $a_{j+1}=P^{p^j}a_j$. Naturality, stability under suspension, and the top-power identity for Steenrod reduced powers give
$$
|i|^*a_j=(m\bmod p)\,\sigma^d(x^{p^j})\ne0
\qquad\text{in degree }n-2+2p^j .
$$
Nonvanishing follows from $H^*(\mathbb{CP}^{\infty};\mathbb F_p)=\mathbb F_p[x]$. Already $j=1$ distinguishes $|C|$ from the groupoidification of the free cellular n-skeleton, which has a CW model of dimension n. The skeletal comparison therefore fails. Since homotopicality passes to skeleta, Γ cannot be homotopical. ∎ [Detailed proof and references](../answered/higher-bubble-obstruction-2026-11-19.md)

For a composite example, let f be a path of two arrows, take a 2-generator $\alpha:f\Rightarrow f$, and adjoin 3-generators $1_f\to\alpha$ and $\alpha\to1_f$. Their composite is a bubble of count two. With $p=3$, the first reduced power detects $2\sigma(x^3)$ in degree seven, above the dimension of the free cellular realization.

This proves the necessity direction of Question 1. Researcher Response 1 gives sufficiency for positive-to-one polygraphs and their dimensionwise duals. Whether bubble-freeness suffices for every finite polygraph remains open.

## Verification of the researcher responses (2026-11-19)

*Checked by the thread "Process seven round-3 researcher responses", alongside HPOL's in-house proof (`homotopy-polygraphs.md` §1–2, which already records Response 1's scope). Verdict: **correct**, with the stated reliance on cited results.*

- **Theorem 1 / Response 2 (necessity in every dimension, every base cell).**
  - This agrees with HPOL's Theorem N and with `higher-bubble-obstruction-2026-11-19.md`.
  - The skeleton step: j_n : F(Γ_{≤n}) ↪ F(Γ) is discrete Conduché. Counting r-generators is a functor F(Γ_{≤r}) → B^rℕ, and r-cells of F(Γ) are r-cells of F(Γ_{≤r}). A factorisation of an identity r-cell (r > n) has identity factors by additivity, and induction on r finishes it.
  - The Steenrod computation (θ_j on σ^k ι_m, detected on ℂP^∞ × S^{m−2}) is standard.
- **Section 2 (Π = (x; a : 1 ⇒ 1; ε : a ⇛ 1)).** Recomputed.
  - The strict side: in F(Π), the hom on 1_{1_x} is a commutative monoid in Cat, freely generated by the object a and the arrow ε : a → 0. Interchange plus commutativity reduce every composite to ε^{⊗k} ⊗ 1_{a^n}, so its hom is the poset (ℕ, ≥), whose nerve is contractible (0 is terminal).
  - The weak side is S² ∪_{deg 1} D³ ≃ ∗.
  - Non-homotopicality follows from the bubble a in the 2-skeleton.
  - The chain complex claim (C₃ = C₂ = C₀ = ℤ, C₁ = 0, d₃ = −1) is correct.
- **Theorem 2 (positive-to-one ⇒ homotopical, and the dimensionwise duals).**
  - I checked Chanavat (arXiv 2603.22242) in the paper. Def. 3.22–3.23 defines acyclic atoms (acyclic oriented Hasse diagram) and directed complexes with acyclic atoms. Cor. 3.27 says Mol/X is a polygraph and a homotopy polygraph for such X.
  - The inputs "positive opetopes are acyclic atoms forming a full sieve" (Zawadowski arXiv 0708.2658 Cor. 13.5 / Prop. 12.2, Leclerc, Hadzihasanovic) and the identification (17) O* ≅ Mol/O are taken on citation. The inductive argument for (17) given in the response is sound as written: generators match, and boundary composites are unions of face closures.
  - The decidable sufficient test uses only identity detection and the word problem for computads (Makkai).

**Open after these responses.** Sufficiency (bubble-free ⇒ homotopical) in every dimension, including the positive case (Chanavat Comment 3.40). The follow-up prompt is `outbox/homotopy-polygraphs-r3.md`, written with HPOL's current dimension-3 state (tier-sequence poset Π_G contractible via the braid-cone description, and the open reduction of the infinite fibre with interchange slices to Π_G).
