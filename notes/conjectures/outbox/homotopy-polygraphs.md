# Which polygraphs are homotopy polygraphs? A recognition theorem in every dimension

*A self-contained problem. It assumes familiarity with polygraphs (computads), strict ω-categories and (∞,ω)-categories, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** A recognition theorem valid in every dimension, or counterexamples that delimit one. Isolated new examples in low dimension are of little use to us.

## 1. Setting

- A **polygraph** Γ (computad) is a set of generators of each dimension, each n-generator having a source and a target which are parallel (n−1)-cells of the free strict ω-category on the lower generators. All polygraphs here are finite.
- `F(Γ)` is the free strict ω-category on Γ.
- `Free(Γ)` is the free (∞,ω)-category on Γ: generators are attached one at a time along their boundaries by pushouts of `∂Dⁿ → Dⁿ` in (∞,ω)-categories (Loubaton's Cat_ω, arXiv 2406.05425, or Campion's framework, arXiv 2311.00200). Strict ω-categories are (∞,ω)-categories, so there is a canonical comparison `c_Γ : Free(Γ) → F(Γ)`.
- Γ is a **homotopy polygraph** (or *homotopical*) when c_Γ is an equivalence, i.e. when every strict pushout attaching a generator is also a homotopy pushout.
- A 2-cell `1_x ⇒ 1_x` of F(Γ) other than the identity is a **bubble**.
- Γ is **positive in every dimension** when every generator of dimension n ≥ 2 has a source and a target that are not identity cells. (For n = 2: both boundary paths are nonempty.)

## 2. Why it matters

Homotopy polygraphs are exactly the computads whose free (∞,ω)-category can be computed strictly. Many constructions need this as a hypothesis: finite presentations of Grothendieck constructions over a free base (a weight on F(Γ) has a finite cellular presentation of its total space only when the base is homotopical), the comparison of weak and strict free objects in type theories for weak ω-categories, and pasting theorems for diagrams of non-globular shape. At present each use has to check homotopicality by hand for its particular shape.

## 3. What is known

1. **Pasting theorems.** For a strongly loop-free Steiner complex K, ν(K) is the free (∞,ω)-category on its atoms (Campion, *Pasting diagrams in higher categories are free*, arXiv 2311.00200). Chanavat (*A strengthened (∞,n)-categorical pasting theorem*, arXiv 2603.22242) extends this to regular directed complexes with frame-acyclic molecules (Thm 3.17), and deduces that **positive 2-polygraphs** (Cor. 3.39) and **regular 3-polygraphs** in Henry's sense (Cor. 3.38) are homotopy polygraphs. Comment 3.40 there describes the extension to arbitrary regular and positive polygraphs as expected, without proof.
2. **Bubbles obstruct.** If F(Γ) has a bubble q (Γ of dimension 2), sending every 2-generator to 1 gives r : F(Γ) → B²ℕ with r(q) = k > 0, and q defines i : B²ℕ → F(Γ) by Eckmann–Hilton. Since ri = [k] acts by kʲ on H_{2j}(K(ℤ,2); ℚ), the groupoidification of F(Γ) has nonzero rational homology in every even degree. The groupoidification of Free(Γ) is a finite CW complex, so Γ is not homotopical. Example: (x; σ : 1_x ⇒ 1_x), where F(Γ) = B²ℕ groupoidifies to K(ℤ,2) (Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9, Ex. 4.10) and Free(Γ) to S².
3. **Bubble-freeness is undecidable**, already for one-vertex 2-polygraphs with no generating bubble: reachability `w ⇒* v` in a positive semi-Thue system R reduces to the existence of a bubble in R plus an insertion rule `ins : 1 ⇒ L w Z` and a deletion rule `del : L v Z ⇒ 1` with fresh letters L, Z.
4. **Positivity is not necessary.** (∗; t : ∗ → ∗; η : 1 ⇒ t) is homotopical: F₂ of it is BΔ⁺_inj (order-preserving injections under concatenation), and coherent freeness follows from Env_{E1}(E0) ≃ Δ⁺_inj (Blans–Linskens, arXiv 2605.03150). Its suspension (0, 1; f; α : f ⇒ f; T : 1_f ⇛ α) is a non-positive homotopical 3-polygraph.
5. **An operadic class.** If Γ has one vertex and every 2-generator has a single generating arrow as target (any source, possibly empty), then F₂(Γ) ≅ B Env_{E1}(P) for the free planar coloured operad P, and Γ is homotopical. The same holds with "source" for "target".
6. **Not every non-positive polygraph with one-sided units is homotopical.** For R = (∗; t; η : 1 ⇒ t, ε : t ⇒ 1), η · ε is a bubble, so R is not homotopical.
7. **Adjoining 1-generators preserves homotopicality** in dimension 2 (loops and cycles allowed): in Haugseng's matrix enrichment, adjoining f : s → t is a tensor algebra whose homs agree with the strict extension's homs. Consequently a **partition test** is sufficient and decidable: if the vertices split into parts such that no 2-generator's boundary uses an arrow between parts, and each part is either positive, or a single vertex whose 2-generators all have a single generating arrow as target (or all as source), then Γ is homotopical.
8. **Positivity in the top dimension alone is not enough.** One vertex, b : 1 ⇒ 1, Ω : b ⇛ b: Ω has non-identity boundaries, but b is a bubble.
9. **Regularity is not necessary.** The positive, non-regular 3-polygraph x, y, z; p, q : x → y, r : y → z; α, β : p ⇒ q; ζ : α ▷ r ⇛ β ▷ r is homotopical (the Θ-nerve of F is a union of the nerve of the 2-skeleton and a full sub-3-globe, meeting in ∂D₃).
10. **Some 3-dimensional attachments.** Let D be a strict 3-category with a finite homotopical presentation and vertices s, t such that no nonidentity 1-cell enters s or leaves t and D(s,s) = D(t,t) = 1. Replacing D(s,t) by a homotopical 2-cell attachment of it is a homotopical 3-cell attachment. With incoming and outgoing arrows, the correct attachment is along `I ∨ ∂D₃ → I ∨ D₃`, and wedge-suspension preserves homotopy pushouts.
11. **Strict versus "stricter".** Chanavat (*Homotopy theory of stricter n-categories*, arXiv 2509.26563) shows that strict n-categories and stricter n-categories (governed by regular directed complexes) agree for n ≤ 3 and differ from n = 4 (Comment 2.67: a 4-dimensional regular directed complex whose molecules do not form a polygraph under strict composition).
12. **Homological coherence.** Homotopical implies homologically coherent (polygraphic homology equals the homology of the Street nerve). Guetta conjectures that a free 2-category is homologically coherent exactly when it is bubble-free (*Homology of strict ω-categories*, PhD thesis, arXiv 2104.12662, Conj. 6.6.5); item 2 gives one half.

## 4. Questions

**Question 1 (main: positivity in every dimension).** Is every finite polygraph that is positive in every dimension a homotopy polygraph? This is the "positive" half of Chanavat's Comment 3.40. If it fails, find the smallest counterexample. Item 11 suggests where to look in dimension 4: a positive polygraph whose strict free ω-category satisfies an exchange relation that its free (∞,4)-category does not.

**Question 2 (dimension 2 exactly).** Is every finite bubble-free 2-polygraph homotopical? This would give, for 2-polygraphs, "homotopical ⇔ bubble-free" and the "if" half of Guetta's conjecture. The smallest open cases are one-sided polygraphs outside item 7, for example
- (∗; s, t; η : 1 ⇒ st, μ : ts ⇒ t);
- several vertices in one part, or 2-generators whose source and target are both composite and some boundary empty.

If the answer is no, characterise the homotopical 2-polygraphs (the class is then not decidable by item 3 alone, so the characterisation may be a non-decidable one).

**Question 3 (a criterion for all dimensions that covers the non-positive examples).** Give a sufficient condition for homotopicality, in every dimension, that contains both positive polygraphs (if Question 1 is positive) and the operadic class of items 4–5 and their suspensions, and that is checkable on finite data. One candidate shape: Γ is homotopical when it is bubble-free in a suitable all-dimensional sense (no nonidentity endo-cell of an iterated identity, in any dimension) and each generator's attachment is "locally" one of the known homotopical types.

## 5. What counts as a solution

A proof of Question 1 or 2; a counterexample with a proof of non-homotopicality (for example by a homology computation, as in item 2); a sufficient criterion for Question 3 with proof; or a published reference.

## 6. Literature (searched 2026-11-18)

- Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (Thm 3.17, Cors. 3.38–3.39, Comment 3.40); Chanavat, arXiv 2509.26563.
- Henry, *Regular polygraphs and the Simpson conjecture*, arXiv 1807.02627.
- Guetta, arXiv 2104.12662 (Conj. 6.6.5); Guetta, *Polygraphs and discrete Conduché ω-functors*, Higher Structures 4(2) (2020).
- Ara, *A Quillen Theorem B for strict ∞-categories*.
- Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273.
- Blans–Linskens, arXiv 2605.03150.
- No published recognition theorem for homotopy polygraphs beyond the classes in item 1 was found.

# Researcher Response

**I do not have a proof or counterexample for Question 1 or Question 2.** I can prove an exact reduction theorem for free enriched graph assembly, valid in every dimension, and extend your item 7 to arbitrary dimensions. Together they give a finite sufficient certificate covering the operadic examples, all their suspensions, and further assemblies of them. They do **not** establish the requested coverage of every positive polygraph.

There is also a correction to the proposed dimension-four route: the cited example identifies two cells upon passing from a strict category to a *stricter* category. It does not identify them in the free strict category itself.

## 1. An exact reduction theorem in every dimension

Let \(Q=(V,E,s,t)\) be a finite directed graph, allowing loops and parallel edges. Assign a finite polygraph \(P_e\) to each edge \(e\).

Define a polygraph \(B_Q(P_\bullet)\) by
\[
B_Q(P_\bullet)_0=V,\qquad
B_Q(P_\bullet)_{r+1}
=\coprod_{e\in E}(P_e)_r.
\]

Write a generator in the latter set as \((e,x)\). Its boundary is defined as follows:

- If \(x\) is a \(0\)-generator, then
  \[
  (e,x):s(e)\longrightarrow t(e).
  \]
- Otherwise, suspend the source and target of \(x\): replace every generator \(y\) by \((e,y)\), every identity by the corresponding identity, and every composition \(\#_i\) by \(\#_{i+1}\).

Thus each generator and every generator named in its attaching expressions have the same edge index \(e\).

### Theorem

For the cellular definition of homotopicality in your §1,
\[
\boxed{
B_Q(P_\bullet)\text{ is homotopical}
\quad\Longleftrightarrow\quad
P_e\text{ is homotopical for every }e\in E.
}
\tag{1}
\]

This is an exact recognition theorem for polygraphs supplied with such a decomposition.

### Proof

Choose a finite dimension bound large enough for all the polygraphs. Let \(\iota\) denote the inclusion of strict categories into the chosen higher categorical model.

#### A. The strict free category has an explicit path formula

For \(a,b\in V\),
\[
F(B_Q(P_\bullet))(a,b)
\cong
\coprod_{\substack{p=(e_1,\ldots,e_m)\\p:a\leadsto b}}
\prod_{j=1}^{m}F(P_{e_j}).
\tag{2}
\]

The empty path contributes the terminal category when \(a=b\).

To verify (2), form the strict enriched category given by its right-hand side. Composition concatenates paths and tuples. A strict functor from it to a strict category \(X\), with a prescribed assignment of vertices, is exactly a family
\[
F(P_e)\longrightarrow X(s(e),t(e)).
\]
These are precisely the assignments of the generators of \(B_Q(P_\bullet)\) respecting their suspended boundaries. This proves the required free universal property.

#### B. The weak free enriched category has the same formula

For higher categories \(A_e\), let \(T_Q(A_\bullet)\) be the free enriched category on these edge labels. Its homs are
\[
T_Q(A_\bullet)(a,b)
\simeq
\coprod_{\substack{p=(e_1,\ldots,e_m)\\p:a\leadsto b}}
\prod_{j=1}^{m}A_{e_j}.
\tag{3}
\]

The relevant references are Haugseng’s comparison of Segal \(\Theta_{n+1}\)-spaces with iterated Segal spaces, **Theorem 4.1**, and the free outer-composition calculation in **Proposition 4.4 and its proof**. With a discrete set of vertices, the iterated fibre products in that calculation separate into the path-indexed products in (3). **Remark 4.7** gives compatibility with completeness. [arxiv.org](https://arxiv.org/pdf/1604.08480?utm_source=chatgpt.com)

The strict nerve preserves the products and coproducts appearing here. Products follow from the restricted Yoneda formula. For coproducts, every \(\Theta\)-shape is nonempty and connected, so a strict functor from a \(\Theta\)-shape to a disjoint union factors through exactly one summand. Consequently,
\[
\iota\,T_Q^{\mathrm{strict}}(C_\bullet)
\simeq
T_Q(\iota C_\bullet).
\tag{4}
\]

This argument uses preservation of these particular products and coproducts; it does not require preservation of arbitrary strict pushouts.

#### C. Cellular comparisons are carried to cellular comparisons

Write \(P_e^{[r]}\) for the \(r\)-skeleton, with \(P_e^{[-1]}=\varnothing\). Its \(r\)-dimensional cellular comparison is
\[
\lambda_{e,r}:
\left(
\iota F(P_e^{[r-1]})
\amalg^{h}_{\coprod_{x\in(P_e)_r}\iota\partial D^r}
\coprod_{x\in(P_e)_r}\iota D^r
\right)
\longrightarrow
\iota F(P_e^{[r]}).
\tag{5}
\]

The free enriched construction satisfies
\[
\operatorname{Map}_{V/}\!\left(T_Q(A_\bullet),X\right)
\simeq
\prod_{e\in E}
\operatorname{Map}\!\left(A_e,X(s(e),t(e))\right).
\tag{6}
\]
It is therefore a left adjoint into the category of higher categories equipped with a map from \(V\), and preserves pushouts there.

For a label \(A\) placed only at edge \(e\), with the other labels empty,
\[
T_Q(A\text{ at }e)
\simeq
V\amalg_{\partial D^1}\Sigma A.
\tag{7}
\]
Here the two distinguished vertices of \(\Sigma A\) map to \(s(e)\) and \(t(e)\), including when these are equal.

Suspension takes
\[
\partial D^r\longrightarrow D^r
\quad\text{to}\quad
\partial D^{r+1}\longrightarrow D^{r+1}.
\]
Strict and weak suspension agree, and suspension preserves the relevant pushouts: this is Campion’s **Corollary 2.26 and Observation 2.27**. The pointed formulation matters; no preservation of unpointed coproducts is being assumed. [arxiv.org](https://arxiv.org/html/2311.00200v1?utm_source=chatgpt.com)

Apply \(T_Q\) to the cellular pushouts in (5). Using (7) and pushout pasting identifies the resulting pushout with the attachment of all the corresponding \((r+1)\)-generators of \(B_Q(P_\bullet)\). Under (4), its comparison is
\[
\lambda_{B,r+1}
\simeq
T_Q\bigl((\lambda_{e,r})_{e\in E}\bigr).
\tag{8}
\]

If every \(\lambda_{e,r}\) is an equivalence, so is every \(\lambda_{B,r+1}\). The \(0\)-dimensional attachment of \(V\) is already homotopical. This proves the forward construction.

#### D. The construction also reflects the comparisons

Formula (3) has a canonical grading by paths in the ordinary free category \(Q^*\). For an edge \(e:a\to b\), the fibre over the **length-one path \(e\)** is exactly \(A_e\).

Thus an equivalence
\[
T_Q(A_\bullet)\longrightarrow T_Q(A'_\bullet)
\]
induced by maps \(A_e\to A'_e\) restricts, on that fibre, to an equivalence
\[
A_e\longrightarrow A'_e.
\]

Apply this to (8). If all cellular comparisons for \(B_Q(P_\bullet)\) are equivalences, then all \(\lambda_{e,r}\) are equivalences.

Loops cause no problem: the paths \(e\), \(ee\), and the empty path are distinct indices. Repeated uses of an edge retain their ordered positions; there is no permutation quotient. This proves (1). \(\square\)

## 2. Adjoining \(1\)-generators works in every dimension

Your item 7 extends without a dimension restriction.

### Proposition

Let \(C\) be a strict category of any finite dimension, and let \(s,t\) be two of its \(0\)-cells. Then
\[
C\longrightarrow C\langle f:s\to t\rangle
\]
is the homotopy pushout of the attachment \(\partial D^1\to D^1\).

Consequently, adjoining finitely many \(1\)-generators to a homotopical polygraph preserves homotopicality in every dimension.

### Proof

The strict extension has homs
\[
\begin{aligned}
C\langle f\rangle(a,b)\cong {}&
C(a,b)\\
&\amalg
\coprod_{m\geq1}
C(a,s)\times C(t,s)^{m-1}\times C(t,b).
\end{aligned}
\tag{9}
\]

The summand indexed by \(m\) describes
\[
u_0\,f\,u_1\,f\,\cdots\,f\,u_m.
\]
Identity choices for the \(u_i\) are retained. The number and positions of the new letters \(f\) determine the factorization.

For completeness, the weak calculation follows from a relative tensor algebra. In the monoidal category of matrices of higher categories on the vertex set of \(C\), regard \(C\) as an associative algebra \(A\). Let \(G\) be the matrix with a single terminal entry at \((s,t)\) and empty entries elsewhere. The free algebra under \(A\) adjoining \(G\) is
\[
T_A(A\otimes G\otimes A).
\]
Its terms satisfy
\[
(A\otimes G\otimes A)^{\otimes_A m}
\simeq
A\otimes G\otimes A\otimes\cdots\otimes G\otimes A.
\tag{10}
\]
The underlying results are the identification of algebras under \(A\) with algebras in \(A\)-bimodules, the free associative algebra formula, and unitality of relative tensor products; see *Higher Algebra*, **Corollary 3.4.1.7**, **Proposition 4.1.1.18**, and **Propositions 4.4.3.12 and 4.4.3.16**. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HA.pdf?utm_source=chatgpt.com)

Expanding the matrix products in (10) gives exactly (9), now with homotopy coproducts and products. Its universal property is a functor out of \(C\), together with the choice of the image of \(f\). This is the universal property of the required homotopy pushout.

The strict nerve preserves every product and coproduct displayed in (9), so the strict and weak extensions agree.

Finally, if \(C=F(P)\), none of the original attaching maps for \(P\) uses the newly adjoined generator. Pushout pasting therefore permits the new \(1\)-attachment to be performed before the original higher attachments. Those higher squares remain homotopy pushouts. \(\square\)

## 3. A finite sufficient certificate

The preceding results give a concrete certificate format, without quantifying over all composites.

Choose the following permitted leaves:

| Leaf | Finite data to check |
|---|---|
| A positive \(2\)-polygraph | Both boundary words of each \(2\)-generator are nonempty. |
| An operadic \(2\)-polygraph from your item 5 | One vertex; either every target is one generating arrow, or every source is one generating arrow. |
| A strongly loop-free unital Steiner presentation | Its finite based chain complex, unitality checks, a compatible ordering of the basis, and identification of its generators and boundaries with the given polygraph. |

The homotopicality of these leaves is part of your established results.

Allow three construction rules:

1. Form \(B_Q(P_\bullet)\) from already certified labels.
2. Take a finite disjoint union.
3. Adjoin finitely many \(1\)-generators.

A certificate is a finite expression using these leaves and rules, together with an identification of its resulting generators with those of \(\Gamma\).

At a graph-assembly step, verify:

- the bijections
  \[
  \Gamma_{r+1}\cong\coprod_{e\in E}(P_e)_r;
  \]
- the specified endpoints of the \(1\)-generators;
- the suspended attaching expressions of every higher generator.

For boundary comparisons, require either literal equality after translation or a supplied finite derivation using strict associativity, units, and exchange. **Verification therefore does not assume a decision procedure for equality of arbitrary higher composites.**

Soundness follows by induction on the certificate: use theorem (1), the proposition above, and preservation of disjoint unions.

This criterion includes the entire operadic class and every iterated suspension of it. Suspension is the graph construction with two vertices and one edge. It also permits directed cycles and assemblies whose homs involve products of several different certified labels, as shown explicitly by (2).

If Question 1 is proved, **all positive polygraphs can be added as leaves without changing either closure proof**. Unconditionally, the positive leaves must remain within classes already known to be homotopical. Thus this is a finite certificate for a dimension-independent subclass, not the full positive recognition theorem requested in Question 1.

## 4. Why the cited dimension-four example does not refute positivity

Let \(U\) be the directed complex used in Chanavat’s Comment 2.67, and put
\[
C_U=
\operatorname*{colim}_{x\in U}^{\mathrm{strict}}
\operatorname{Mol}/U_x.
\]
The comparison in that example is
\[
q:C_U\longrightarrow \operatorname{Mol}/U.
\tag{11}
\]
The domain is a polygraph; the codomain satisfies additional equations and is not that free strict polygraph. [arxiv.org](https://arxiv.org/html/2509.26563v1?utm_source=chatgpt.com)

More specifically, Hadzihasanovic’s **Example 8.2.20** exhibits two formal strict \(4\)-composites that are **distinct in \(C_U\)** and become equal in \(\operatorname{Mol}/U\). His argument shows that the interchange needed to equate them in \(C_U\) is unavailable. [arxiv.org](https://arxiv.org/html/2404.07273v2?utm_source=chatgpt.com)

Accordingly, the relevant factorization is
\[
\operatorname{Free}(\Gamma_U)
\xrightarrow{\,c_{\Gamma_U}\,}
C_U
\xrightarrow{\,q\,}
\operatorname{Mol}/U.
\]
Failure of \(q\), or of the composite, to be an equivalence does not establish failure of \(c_{\Gamma_U}\). It is consistent with \(c_{\Gamma_U}\) being an equivalence.

Chanavat’s **Comment 3.40** still presents the extension to all positive polygraphs as expected, with a missing contractibility argument. The dimension-four example explains why retaining only the underlying oriented poset loses information; it does not supply the proposed positive counterexample. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

For Question 2, I found no verified proof or counterexample. The two closure theorems above do not settle arbitrary bubble-free \(2\)-polygraphs, including your example with \(\eta:1\Rightarrow st\) and \(\mu:ts\Rightarrow t\). Nor do they prove equivalence with Guetta’s conjecture: the implication from homotopicality to homological coherence gives only the direction already identified in your statement.

# Followup 1

I have **not established a full resolution**. The continuation produced a substantial candidate proof of Question 2, but its identification of the diagram model with your globularly attached free object requires a further argument that I cannot certify from the cited results. My preceding progress update asserting that this comparison was complete was too strong.

The part that can be separated from that issue is an all-homotopy-groups statement about planar diagrams. I give its argument below, then state the remaining comparison precisely. This avoids presenting a proposed solution of Guetta’s conjecture as a theorem before its essential categorical step has been justified.

## 1. The geometric statement

Let \(G\) be a finite directed graph equipped with:

- ordered incoming and outgoing edge lists at each internal vertex;
- individually identified, ordered endpoints on the source and target boundaries;
- auxiliary identifiers for its internal vertices and edges.

A **progressive drawing** of \(G\) in \(\mathbb R\times[0,1]\) places each internal vertex at a height strictly between \(0\) and \(1\), and expresses every edge \(e:s\to t\) as a continuous graph
\[
y\longmapsto (x_e(y),y),
\qquad y_s\le y\le y_t,
\]
with \(y_s<y_t\). Distinct edges intersect only at their prescribed common endpoints.

Give the drawing space \(\mathcal E(G)\) the topology determined by vertex coordinates and the uniform topology on the normalized edge functions
\[
u\longmapsto x_e\bigl(y_s+u(y_t-y_s)\bigr),
\qquad 0\le u\le1.
\]

The following geometric claim has a concrete proof:

> **Geometric claim.** If every undirected connected component of \(G\) meets the external boundary, every path component of \(\mathcal E(G)\) is weakly contractible. Empty incoming or outgoing edge lists are allowed.

The proof uses Delpeuch–Vicary’s termination theorem, together with a finite complex that records simultaneous exchanges. Their definition of boundary-connectedness includes exactly the hypothesis used here, and their Corollary 2.16 proves termination of right exchanges under that hypothesis. [arxiv.org](https://arxiv.org/pdf/1804.07832?utm_source=chatgpt.com)

### 1.1 A finite poset of level encodings

For a drawing, partition its internal vertices into nonempty sets
\[
B_1,\ldots,B_k
\]
of equal height, ordered from source to target.

At each such height, record the left-to-right list of:

- the vertices at that height;
- the identified edges crossing that height without ending there.

Replacing each vertex in this list by its incoming edge list gives the wire order immediately before that level. Replacing it by its outgoing edge list gives the order immediately afterward.

**A vertex with an empty edge list remains an explicit entry.** In particular, the two horizontal orders of two scalar vertices at the same height give different encodings.

An encoding is refined by splitting one or more equal-height sets into ordered subsets. The resulting wire orders are determined: before a vertex’s new height use its incoming edges, at its height use the vertex, and afterward use its outgoing edges.

Let \(P(G)\) be the finite poset of realizable encodings, ordered by
\[
\sigma\le\tau
\quad\Longleftrightarrow\quad
\tau\text{ refines }\sigma.
\]
Equip it with the upper Alexandrov topology. There is a continuous map
\[
p:\mathcal E(G)\longrightarrow P(G).
\]

For continuity, a sufficiently small perturbation preserves the strict height inequalities between existing levels. It also preserves the horizontal order of the finitely many vertices and through-edges at each level. Thus it can only split an existing level.

### 1.2 Principal-open preimages are contractible

Fix \(\sigma\), with levels \(B_1,\ldots,B_k\). The permitted vertex-height vectors form the convex set
\[
H_\sigma=
\left\{
Y\in(0,1)^{V(G)}:
Y_v<Y_w
\text{ if }v\in B_i,\ w\in B_j,\ i<j
\right\}.
\]
There is no height inequality between vertices belonging to the same original level.

Every \(Y\in H_\sigma\) determines one refinement of \(\sigma\), by splitting its levels according to the equalities and inequalities in \(Y\).

Construct a canonical drawing at height vector \(Y\) as follows. Between consecutive original levels choose the interface
\[
c_i(Y)=
\frac{\max_{v\in B_i}Y_v+\min_{w\in B_{i+1}}Y_w}{2}.
\]
Within the corresponding slab, assign disjoint horizontal intervals, in the recorded order, to its vertices and through-edges. Draw each vertex at a fixed horizontal coordinate in its interval. Draw ordered incoming and outgoing fans, and connect them to fixed ordered wire positions at the slab interfaces.

These choices vary continuously with \(Y\). Denote the resulting drawing by \(B_\sigma(Y)\).

For a fixed \(Y\), an arbitrary drawing in \(p^{-1}(\uparrow\sigma)\) and \(B_\sigma(Y)\) impose the same horizontal order on every pair of edges meeting a common horizontal slice. They also impose the same order on each vertex and every nonincident edge at its height.

Consequently, interpolation
\[
x_e^{\,t}(y)
=
(1-t)x_e(y)+t\,x_e^{B_\sigma(Y)}(y)
\]
preserves all required strict inequalities. Endpoint incidences are preserved because they are linear equalities. This contracts each fixed-height drawing space onto its canonical drawing, continuously in \(Y\). Contracting \(H_\sigma\) then contracts \(p^{-1}(\uparrow\sigma)\).

McCord’s Theorem 6 applies to the principal upper opens, and his Theorem 2 identifies the finite Alexandrov space with its order complex up to weak equivalence. Hence
\[
\mathcal E(G)\simeq_{\mathrm w}|P(G)|.
\tag{1}
\]
These theorems require local weak equivalences over the indicated open cover; they do not require \(p\) to be a fibration. [webhomes.maths.ed.ac.uk](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/mccord1.pdf?utm_source=chatgpt.com)

### 1.3 The exchange complex

Associate to an encoding \(\sigma=(B_1,\ldots,B_k)\) the polytope
\[
Q_\sigma=\prod_{i=1}^{k}\operatorname{Perm}(B_i).
\]
Here the coordinates of each permutohedron are indexed by the identified vertices of \(B_i\).

An ordered partition of \(B_i\) specifies both a face of its permutohedron and a refinement of that level. Glue these polytopes along the resulting face maps. Call the finite CW complex \(K(G)\).

The vertex identifiers prevent self-identifications of a closed cell: different ordered partitions of one level give different refined encodings. The face maps preserve the intrinsic coordinates of the corresponding refined polytope. Thus each closed cell embeds, and \(K(G)\) is regular. Different closed cells may intersect in a union of faces.

Its face poset is \(P(G)^{\mathrm{op}}\), so
\[
|P(G)|\cong |\operatorname{sd}K(G)|.
\tag{2}
\]

The possibility of several edges with the same endpoints is necessary. For two isolated scalar vertices, the two horizontal orders at equal height give two exchange edges between the same sequential encodings. Their union is a circle. The construction therefore retains the elementary braid obstruction.

### 1.4 A maximal outgoing cell at every sequential encoding

A vertex \(v\) of \(K(G)\) is a sequential diagram
\[
g_1,\ldots,g_N.
\]
Let \(a_i\) be the number of wires strictly to the left of the input of \(g_i\), measured immediately before applying \(g_i\), and let \(p_i\) be its input arity.

The right exchanges available at \(v\) are exactly
\[
R(v)=
\{\,i:a_i\ge a_{i+1}+p_{i+1}\,\}.
\tag{3}
\]
This is Delpeuch–Vicary’s right-exchange condition. [arxiv.org](https://arxiv.org/pdf/1804.07832?utm_source=chatgpt.com)

Consider a maximal consecutive run
\[
k,k+1,\ldots,l-1
\]
in \(R(v)\). Then
\[
a_j+p_j\le a_{j-1},
\qquad k<j\le l.
\]
Every preceding substitution in this run takes place to the right of the inputs used by \(g_j\). Thus those inputs are the interval
\[
[a_j,a_j+p_j)
\]
in the wire word preceding \(g_k\).

These intervals are disjoint, in the horizontal order
\[
g_l,\ldots,g_k.
\]
When an interval is empty, that displayed order still specifies the corresponding vertex’s position. This constructs one simultaneous level whose reverse-horizontal sequentialization is
\[
g_k,\ldots,g_l.
\]

Merge each maximal run in this way. The resulting product of permutohedra, denoted \(F(v)\), has exactly the outgoing right-exchange edges at \(v\).

Moreover:

1. Every vertex of \(F(v)\) is reachable from \(v\) by right exchanges.
2. Every cell having \(v\) as its source is a face of \(F(v)\).

For the second assertion, a source vertex of a permutohedron lists its vertices in reverse horizontal order. Every adjacent pair within such a list is therefore a right exchange at \(v\), and the list must lie in one of the maximal runs defining \(F(v)\).

This also provides local confluence: two outgoing right exchanges belong to \(F(v)\), and their targets both reach its sink.

### 1.5 Contracting each connected component

By termination and the local confluence just established, each connected component of the exchange graph has one sink.

Choose a topological ordering of the directed exchange graph. Remove its vertices in that order, retaining the sink. At any stage, retain precisely the cells none of whose vertices has yet been removed.

Let \(v\) be the next vertex.

Every remaining cell incident to \(v\) has all its incident edges at \(v\) directed outward. Therefore it has \(v\) as its source, and is a face of \(F(v)\). Conversely, \(F(v)\) is still present because all its other vertices are reachable from \(v\) and occur later in the ordering.

The remaining closed star of \(v\) is consequently \(F(v)\). Its intersection with the complex after removal is
\[
A(v)=
\bigcup\{
\text{faces of }F(v)\text{ not incident to }v
\}.
\]
Radial projection from \(v\) identifies \(A(v)\) with a small convex vertex figure. Thus \(A(v)\) is a ball.

The inclusion \(A(v)\hookrightarrow F(v)\) is a cofibration and a homotopy equivalence between contractible spaces. It admits a deformation retraction, which extends by the identity on the rest of the complex. This is the standard CW-pair consequence of the homotopy extension property. [pi.math.cornell.edu](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf?utm_source=chatgpt.com)

Iterating contracts the component to its sink. Equations (1)–(2) prove the geometric claim.

## 2. Why bubble-freeness supplies its hypothesis

In a progressive \(\Gamma\)-labelled string diagram, suppose an undirected graph component avoids both external boundaries.

Take a small regular neighborhood of that graph component, disjoint from the other graph components. The label on its outer boundary is a single \(0\)-generator \(x\). After removing the other graph components and extending the adjacent region labels, the selected component gives a diagram
\[
1_x\Longrightarrow1_x.
\]
It has at least one generating \(2\)-vertex. Counting generating \(2\)-vertices shows that its strict composite is not an identity.

Thus, if \(F(\Gamma)\) is bubble-free, every graph component of every \(\Gamma\)-labelled diagram meets the external boundary.

There is also no residual finite automorphism quotient in this case. An automorphism preserving the ordered external endpoints fixes a boundary edge. That fixes its incident vertex; the ordered incoming and outgoing lists then fix every incident edge. Propagation along the undirected graph fixes the entire component.

Therefore the geometric claim applies directly to the spaces of unmarked, boundary-fixed diagrams relevant to a bubble-free polygraph.

This establishes the following precise intermediate conclusion:

\[
\boxed{
\begin{gathered}
\Gamma\text{ bubble-free}\\
\Longrightarrow\\
\text{each component of its progressive planar drawing spaces}\\
\text{is weakly contractible.}
\end{gathered}}
\tag{4}
\]

## 3. The categorical statement still needed

To turn (4) into the requested recognition theorem, one needs the following model comparison.

> **Required comparison.** For every ordinary \(2\)-polygraph \(\Gamma\), the \((\infty,2)\)-category of \(\Gamma\)-labelled progressive diagrams, retaining their full spaces of isotopies, is the homotopy pushout
> \[
> F(\Gamma_{\le1})
> \amalg^{h}_{\coprod_{g\in\Gamma_2}\partial D^2}
> \coprod_{g\in\Gamma_2}D^2,
> \tag{5}
> \]
> compatibly with the functor taking a diagram to its strict composite.

If this comparison holds with the stated diagram spaces, (4) proves Question 2 immediately: the comparison to the strict free \(2\)-category is the identity on generating objects and words, and its map on each \(2\)-morphism space is the map to a discrete set of components, all of which are contractible. Necessity is already your item 2.

Heidemann provides a potentially suitable framework. His §4.4 constructs labelled manifold diagrams from a **diagrammatic computad**, and Lemma 4.4.3.2 identifies the construction with a presheaf left Kan extension. The subsequent adjunction is between diagrammatic computads and \((\infty,n)\)-categories. It does not, by itself, identify that left adjoint with (5) for an ordinary globular computad. [arxiv.org](https://arxiv.org/html/2411.04870v1?utm_source=chatgpt.com)

### The attempted verification

There is an explicit candidate diagrammatic computad \(\Sigma_\Gamma\):

- label genuine regions by \(\Gamma_0\);
- label genuine wires by \(\Gamma_1\), respecting their adjacent regions;
- label genuine vertices by \(\Gamma_2\), matching their ordered input and output words.

For a target \(C\), the desired universal property is
\[
\operatorname{Map}(\mathbb F\Sigma_\Gamma,C)
\simeq
\operatorname{Map}(F(\Gamma_{\le1}),C)
\times^{h}_{\prod_g\operatorname{Map}(\partial D^2,C)}
\prod_g\operatorname{Map}(D^2,C).
\tag{6}
\]

The left Kan extension formula reduces the left side to a space of natural evaluations on labelled meshes. Segal descent suggests reducing these evaluations to mesh atoms. Normalization should assign identity cells to artificial mesh strata. Regularity then identifies the relative evaluation at a genuine corolla with the choice of a single \(2\)-cell having its specified boundary. The relevant source ingredients are Heidemann’s normal-form construction, submersive maps, and the regularity square for atoms. [arxiv.org](https://arxiv.org/html/2411.04870v1?utm_source=chatgpt.com)

The issue is **coherent naturality over the full category of labelled meshes**. Pointwise contractibility of evaluation choices does not prove (6). One must first construct the compatible diagram of those choices and prove that restriction and extension give inverse equivalences on their homotopy limits.

The attempted argument uses an active/inert factorization
\[
A\longrightarrow S\hookrightarrow N
\]
of a mesh morphism restricted to a source atom \(A\), followed by normalization
\[
S\longrightarrow \operatorname{nf}(S).
\]
Submersivity supplies an atomic normal form in this local situation. This is promising, but it must be turned into an actual equivalence of coherent section spaces. Normal form is not functorial on arbitrary labelled bordisms, so this step cannot be replaced by an appeal to a global normalization functor.

The scalar corolla is a necessary test. Its punctured boundary has a circle of incidence data. Showing that all its region labels equal \(x\) does not alone justify replacing that boundary diagram by a point; its coherent attaching map must be retained. Otherwise one risks imposing precisely the extra relation that the bubble example detects.

A second, separate verification is required to identify the topology used in (4) with Heidemann’s simplicial spaces of essentially tame parameterized diagrams. Finite truss realizations and a subdivision argument provide a route, but that identification also belongs in a complete proof of (5).

## 4. What this establishes—and what it does not

The geometric contraction is stronger than a normalization result for individual diagrams: it addresses all homotopy groups through the finite permutohedral complex. It also handles empty inputs and outputs, rather than only positive diagrams.

However, I cannot presently promote it to
\[
\Gamma\text{ bubble-free}
\Longrightarrow
c_\Gamma\text{ an equivalence}
\]
without treating the required comparison (5) as an additional theorem. I have not found a published statement of that comparison in the precise form needed, and the attempted derivation above is not yet a sufficiently certified substitute.

Consequently:

- **Question 1:** no proof or counterexample obtained.
- **Question 2:** reduced to the explicit diagram-model comparison (5), with the geometric contractibility argument supplied above.
- **Question 3:** no sufficient criterion meeting the requested all-dimensional coverage obtained.

I therefore do not claim a recognition theorem or a resolution of Guetta’s conjecture.

# Followup 2

**Question 2 has an affirmative answer.** The remaining comparison can be proved using a category of finite \(2\)-dimensional meshes and an explicit normalization on its active maps.

## Theorem

Let \(\Gamma\) be a finite \(2\)-polygraph. Then
\[
\boxed{\quad
c_\Gamma:\operatorname{Free}(\Gamma)\longrightarrow F(\Gamma)
\text{ is an equivalence}
\quad\Longleftrightarrow\quad
F(\Gamma)\text{ is bubble-free}.
\quad}
\]

The reverse implication is your known bubble obstruction. The proof below establishes the forward implication, including generators with empty boundaries and arbitrarily many vertices.

This resolves Question 2. It does **not** establish positivity in dimensions \(3\) and above. At the end, I give the resulting recognition theorem for iterated suspensions and a finite sufficient test in every dimension.

Throughout, \(B\mathcal C=|N\mathcal C|\) denotes the classifying space of an ordinary category. Colimits and limits of spaces or higher categories mean their \(\infty\)-categorical versions.

---

# 1. The combinatorial spaces that must be contracted

Start with a finite progressive diagram whose vertices and edges have distinct marks. Retain its directed incidences, ordered input and output ports, ordered boundary ports, region incidences, and \(\Gamma\)-labels. Call these data \(G\).

A **tier encoding** of \(G\) consists of:

1. An ordered partition
   \[
   T_1|\cdots|T_r
   \]
   of its vertices into nonempty equal-height tiers.
2. At each tier, the complete left-to-right list of its vertices and its through-edges.
3. The ordered wire word between consecutive tiers.

Replacing a vertex in its tier list by its input ports gives the wire word immediately below; replacing it by its output ports gives the word immediately above. These requirements include vertices with no inputs or no outputs.

An encoding \(\sigma'\) **refines** \(\sigma\) when it splits some tiers. The new horizontal lists are prescribed: before a vertex’s new tier, replace that vertex by its input list; at its tier retain the vertex; afterwards replace it by its output list.

Let \(P_G\) be the resulting finite poset, ordered from coarser tiers to finer tiers. Recording the complete horizontal lists is essential. For two marked scalar vertices, for example, there are two different equal-height encodings, distinguished by which vertex lies on the left.

We will prove two facts:

\[
\begin{aligned}
&\text{If every undirected connected component of }G
  \text{ meets the boundary,}\\
&\hspace{35mm}\text{every connected component of }BP_G
  \text{ is contractible}; \tag{1}
\end{aligned}
\]

and

\[
\operatorname{Free}(\Gamma)
\text{ has a presheaf model whose grid values are computed by these }BP_G.
\tag{2}
\]

The second statement is the model comparison that remained unresolved previously.

---

# 2. Contractibility of the tier spaces

## 2.1. A finite complex of products of permutohedra

Associate to an encoding
\[
\sigma=T_1|\cdots|T_r
\]
the polytope
\[
Q_\sigma=\prod_{i=1}^{r}\operatorname{Perm}(T_i).
\]

The faces of a permutohedron are indexed by ordered partitions. Consequently, the faces of \(Q_\sigma\) are exactly the tier refinements of \(\sigma\), with their prescribed horizontal lists.

Gluing these polytopes along those faces produces a finite regular CW complex \(K_G\) with face poset \(P_G^{op}\). Marks prevent distinct faces of one closed cell from being identified. Therefore
\[
|K_G|\cong |N(P_G^{op})|\simeq BP_G.
\]

The vertices of \(K_G\) are generic encodings: every tier has one vertex. Its edges are exchanges of adjacent independent vertices.

## 2.2. The maximal outgoing cell

Write a generic encoding as
\[
v=(g_1,\ldots,g_N).
\]
Immediately before applying \(g_i\), let \(a_i\) be the number of wires to its left, and let \(p_i\) be its input arity.

Orient an adjacent exchange to the right when
\[
a_i\geq a_{i+1}+p_{i+1}.
\tag{3}
\]
Thus the later operation acts to the left of the earlier one.

Consider a maximal consecutive run
\[
k,k+1,\ldots,l-1
\]
of indices satisfying (3). For \(k\leq i<j\leq l\),
\[
a_i\geq a_j+p_j.
\]
Every later input interval consequently lies to the left of every earlier operation in the run. All these input intervals are subwords of the wire word immediately before \(g_k\); none uses an output of an earlier operation in the run.

Hence the operations can be performed simultaneously, in left-to-right order
\[
g_l,\ldots,g_k.
\]
This remains true when some \(p_i=0\): an empty input list retains its vertex’s specified position in the factor list.

Merge each maximal run into one tier. The resulting cell, denoted \(F(v)\), is a product of permutohedra satisfying:

- its edges at \(v\) are exactly the outgoing exchanges;
- \(v\) is its unique source;
- every vertex of \(F(v)\) is reachable from \(v\);
- every cell whose source is \(v\) is a face of \(F(v)\).

For the last assertion, each tier in a source-\(v\) cell is read in reverse horizontal order in \(v\). Its consecutive positions therefore form a run satisfying (3), and that run lies in one of the maximal runs defining \(F(v)\).

## 2.3. Termination and deletion of sources

Delpeuch–Vicary’s Corollary 2.16 states that right exchanges terminate on boundary-connected diagrams. Their definition includes diagrams in which every undirected connected component meets a boundary. Thus the orientation above is acyclic under the hypothesis of (1). [arxiv.org](https://arxiv.org/pdf/1804.07832?utm_source=chatgpt.com)

Every pair of outgoing edges at \(v\) can be continued to the sink of \(F(v)\). The orientation is therefore locally confluent. Finite termination gives a unique sink in each connected component.

Delete all other vertices in a topological order, retaining at each stage precisely the cells having no deleted vertex.

When \(v\) is deleted, its remaining closed star is exactly \(F(v)\):

- every other vertex of \(F(v)\) follows \(v\), so \(F(v)\) is still present;
- if a remaining cell containing \(v\) had a different source \(w\), a directed path in that cell would run from \(w\) to \(v\), so \(w\) would already have been deleted.

The intersection of \(F(v)\) with the rest of the remaining complex is
\[
A(v)=\bigcup_{\substack{H\text{ a face of }F(v)\\v\notin H}}H.
\]

This is the antistar of a vertex in a convex polytope, and \(F(v)\) strongly deformation retracts onto \(A(v)\). Here is an explicit retraction, so no collapse assertion is needed.

Choose a linear functional uniquely minimized at \(v\), and a sufficiently small vertex figure \(V\). Radial projection from \(v\) gives a homeomorphism
\[
\alpha:A(v)\longrightarrow V.
\]
Fix \(c\in V\). Write \(x\neq v\) uniquely as
\[
x=v+s(q-v),\qquad q\in A(v),\quad 0<s\leq1.
\]
Set
\[
r(x)=\alpha^{-1}\bigl((1-s)c+s\alpha(q)\bigr),
\qquad
r(v)=\alpha^{-1}(c).
\]
This is continuous and fixes \(A(v)\). Convexity makes
\[
H_t(x)=(1-t)x+t\,r(x)
\]
a strong deformation retraction. Extend it by the identity over the rest of the complex.

Successive deletions retract each connected component of \(K_G\) onto its sink. This proves (1), in all homotopy degrees.

---

# 3. Bubble-freeness supplies the boundary condition

Suppose a finite \(\Gamma\)-labelled progressive diagram has an undirected connected component \(H\) disjoint from its boundary.

Choose a small regular neighborhood of \(H\), disjoint from the other graph components. Since \(H\) is connected and planar, each complementary face has a connected boundary collar. That collar lies in one original labelled region, so its object label is constant.

Erase the other graph components and label each resulting face by its collar label. This preserves every side label of an edge and every generator’s ordered ports. The outer face has some label \(x\), and a rectangle surrounding \(H\) now gives a \(\Gamma\)-diagram
\[
1_x\Longrightarrow1_x.
\]

It has at least one generator vertex: a finite progressive wire cannot be a closed circle. Counting generator vertices shows that the resulting \(2\)-cell is nonidentity.

Therefore, if \(\Gamma\) is bubble-free, every connected component of every finite \(\Gamma\)-diagram meets the boundary.

There is also no graph automorphism to quotient out in this case. An automorphism preserving the ordered boundary ports fixes each boundary edge. At a fixed incident vertex, preservation of the ordered port lists fixes every incident edge. Propagation through each undirected connected component fixes every vertex and edge.

Thus, under bubble-freeness, passing from marked diagrams to unmarked diagrams introduces no automorphism groups.

---

# 4. A mesh model with the globular attachment universal property

We now construct the model needed for (2).

Working in \(\mathrm{Cat}_{(\infty,2)}\) computes the required free object: its inclusion into \(\mathrm{Cat}_\omega\) is fully faithful and preserves colimits. In Loubaton’s formulation, these are Construction 2.2.1.40, Proposition 2.2.1.43, and Construction 2.2.1.44. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

## 4.1. Mesh notation and the external input

Let \(\mathsf T\) be the ordinary category of finite open \(2\)-trusses.

An open \(1\)-truss \([r]\) has regular positions \(R_0,\ldots,R_r\) and singular positions \(S_0,\ldots,S_{r-1}\), with
\[
S_i\longrightarrow R_i,\ R_{i+1}.
\]
A monotone map \(\alpha:[r]\to[s]\) has the singular-predecessor relation
\[
S_i\longrightarrow S_j
\quad\Longleftrightarrow\quad
\alpha(i)\leq j<\alpha(i+1).
\tag{4}
\]
A regular source position never precedes a singular target position.

An open \(2\)-truss is a zigzag of open \(1\)-trusses
\[
L_0\longleftarrow S_0\longrightarrow L_1
\longleftarrow\cdots\longrightarrow L_r.
\]
The outer truss records heights; the inner trusses record horizontal positions. Morphisms are compatible monotone maps at these two levels.

We use the following mesh results:

- active/inert factorization, with inert maps identifying constructible open submeshes;
- terminal labelled degeneracies \(M\to\operatorname{nf}(M)\);
- atomic Segal descent and the regularity pushout below.

These are the results of Heidemann’s §§3.3–3.5 and §4.1, specifically Definition 3.3.2.1, Proposition 3.4.4.2, Corollary 3.5.3.9, and the atomic results in §4.1. [arxiv.org](https://arxiv.org/html/2411.04870v1?utm_source=chatgpt.com)

Here is the precise categorical form of the last input. Let
\[
j:\Delta^2\hookrightarrow\mathsf T,
\qquad
A(M)=L_2j^*y(M),
\]
where \(L_2\) is localization to complete globular \(2\)-fold Segal spaces.

For an atom \(B\), let \(\partial_{\mathrm{at}}B\) be the presheaf assembled from its proper inert submeshes, and let \(\square B\) be its singular cube. Then
\[
A(B)\simeq
A(\partial_{\mathrm{at}}B)
\coprod_{A(\partial_{\mathrm{at}}\square B)}
A(\square B).
\tag{5}
\]
Moreover, for every \((\infty,2)\)-category \(C\),
\[
\widehat C(M):=\operatorname{Map}(A(M),C)
\]
satisfies atomic Segal descent. Equation (5) is the localized form of Heidemann’s arXiv Lemma 4.1.0.12. [arxiv.org](https://arxiv.org/html/2411.04870v1?utm_source=chatgpt.com)

## 4.2. The directly defined category \(I_\Gamma\)

Give a truss dimension labels in \(0<1<2\). We require every atomic neighborhood, after normalization, to be one of these three explicitly specified forms:

- a region;
- a progressive wire;
- a corolla with \(p\) input wires and \(q\) output wires.

Label regions by \(\Gamma_0\), wires by \(\Gamma_1\), and vertices by \(\Gamma_2\). A wire’s two region labels must be its source and target. A vertex’s ordered input and output labels must be the boundary words of its generator.

Artificial subdivisions retain the dimension and generator label of the stratum they subdivide. Equivalently, equal-dimension incidence arrows are inverted when determining which mesh strata receive one genuine label.

Define \(I_\Gamma\) using these labelled trusses. Its morphisms preserve labels and satisfy the following condition.

> For every inert \(S\hookrightarrow M\) whose normal form is atomic, factor \(S\to N\) into its active image \(T\hookrightarrow N\). Require \(\operatorname{nf}(T)\) to be atomic and require an actual commuting square
> \[
> \begin{array}{ccc}
> S&\longrightarrow&T\\
> \downarrow&&\downarrow\\
> \operatorname{nf}(S)&\xrightarrow{\cong}&\operatorname{nf}(T)
> \end{array}
> \]
> preserving the genuine generator label and ordered ports.

The quantifier is over **all** inert submeshes with atomic normal form.

This condition is closed under composition: apply it first to \(S\), then to its active image, and compose the two normalization squares. Inert restrictions preserve the condition, as do the normalization degeneracies. Active/inert factorization therefore restricts to \(I_\Gamma\).

Let \(t:I_\Gamma\to\mathsf T\) forget labels, and define
\[
X_\Gamma=\operatorname*{colim}_{M\in I_\Gamma}y(tM).
\tag{6}
\]

We prove
\[
L_2j^*X_\Gamma\simeq\operatorname{Free}(\Gamma).
\tag{7}
\]

## 4.3. Reduction to meshes with atomic normal form

Let \(D\subset I_\Gamma\) be the full subcategory on \(S\) with \(\operatorname{nf}(S)\) atomic.

Let \(E\) have as its objects inert inclusions
\[
S\hookrightarrow M,\qquad S\in D,
\]
and as its morphisms commuting squares. There are projections
\[
p:E\to I_\Gamma,\qquad q:E\to D
\]
to the codomain and domain.

Active-image factorization makes \(p\) a cocartesian fibration. The condition imposed on \(I_\Gamma\)-morphisms is exactly what ensures that its pushforward domain remains in \(D\).

For fixed \(M\), atomic Segal descent gives
\[
\widehat C(M)\simeq
\lim_{(E_M)^{op}}\widehat C(S).
\tag{8}
\]
To justify the enlarged indexing category in (8), include the actual atomic cover of \(M\) into \(E_M\). For each \(S\in E_M\), the atoms of \(M\) lying in \(S\) are exactly the atomic cover of \(S\). Applying Segal descent to every such \(S\), followed by transitivity of right Kan extension, proves (8).

The fiberwise Kan-extension criterion now gives
\[
\widehat C|_{I_\Gamma^{op}}
\simeq
\operatorname{Ran}_{p^{op}}
\bigl(\widehat C|_{D^{op}}\circ q^{op}\bigr).
\]
This is the opposite of the cocartesian fiberwise criterion in Kerodon §7.3.4. [kerodon.net](https://kerodon.net/tag/02ZL?utm_source=chatgpt.com)

The functor \(S\mapsto(S\xrightarrow{\mathrm{id}}S)\) is left adjoint to \(q\). Hence \(q^{op}\) is initial, and
\[
\lim_{I_\Gamma^{op}}\widehat C
\simeq
\lim_{E^{op}}\widehat Cq^{op}
\simeq
\lim_{D^{op}}\widehat C.
\tag{9}
\]

This establishes the equivalence of coherent limits.

## 4.4. A finite final category

Let \(K\subset D\) be the full subcategory with the following labelled atoms:

\[
\begin{array}{c|l}
R_x & \text{one region labelled }x,\\
W_f & \text{one progressive wire labelled }f,\\
B_g & \text{the corolla labelled }g,\\
U_x & \text{one artificial horizontal cut, entirely labelled }x.
\end{array}
\]

For a generator with input length \(p\) and output length \(q\), the underlying corolla is
\[
[p]\longleftarrow[1]\longrightarrow[q],
\]
with endpoint-preserving legs. The central singular point has dimension label \(0\); its ports have label \(1\).

The artificial atom is
\[
[0]\longleftarrow[0]\longrightarrow[0].
\]
It has a normalization and two inert sections
\[
\nu:U_x\to R_x,\qquad
\delta_\pm:R_x\to U_x,\qquad
\nu\delta_\pm=\mathrm{id}.
\tag{10}
\]

We need the following finite classification:

> If \(V\hookrightarrow B\), \(B\in K\), is inert and \(\operatorname{nf}(V)\) is atomic, then \(V\) is isomorphic to an atom in \(K\).

Only the corolla case requires explanation.

- If \(V\) includes its central vertex, openness forces \(V=B\).
- If \(V\) avoids the central height, it is a consecutive portion of an input or output word. Atomic normal form permits zero or one genuine wire, giving \(R\) or \(W\).
- If \(V\) meets the central height but omits the vertex, its horizontal fiber selects exactly one artificial ray. It cannot select both rays, because a mesh fiber is an interval. Adding a genuine wire only above or below that height would give a wire whose height projection is a proper subinterval of the height projection of \(V\). Such a mesh cannot normalize to a wire atom, whose wire crosses every height. There is no genuine vertex, so it cannot normalize to a corolla. Thus \(V=U\).

Fix \(S\in D\). In \(S/K\), active-image factorization gives a right adjoint to the inclusion of the full subcategory of active arrows. The classification above ensures that the active image still belongs to \(K\).

That active-arrow subcategory has terminal object
\[
\nu_S:S\to\operatorname{nf}(S).
\]
Existence of the arrow from any active \(S\to B\) to \(\nu_S\) is supplied by its normalization square. Uniqueness follows because ordered trusses have no nonidentity automorphisms; any such factor is active and its normalization square determines it.

Thus \(B(S/K)\) is contractible. Quillen’s Theorem A gives
\[
K\hookrightarrow D\quad\text{final}.
\tag{11}
\]
The relevant comma-category criterion is Kerodon §7.2.3. [kerodon.net](https://kerodon.net/tag/02NX?utm_source=chatgpt.com)

Combining (9) and (11), naturally in \(C\),
\[
\lim_{I_\Gamma^{op}}\widehat C
\simeq
\lim_{K^{op}}\widehat C.
\tag{12}
\]

## 4.5. Computing that finite colimit

Put \(K_{\leq1}=K\setminus\{B_g\}\). Within this subcategory, the inclusion of the regions and wires is a right adjoint: its left adjoint sends \(U_x\) to \(R_x\). Therefore
\[
\operatorname*{colim}_{K_{\leq1}}A(t-)\simeq C_1,
\]
where \(C_1\) is the ordinary free category on \(\Gamma_{\leq1}\).

Each \(B_g\) has no nonidentity outgoing morphism in \(K\). The colimit obtained by adjoining these objects is consequently
\[
\operatorname*{colim}_K A(t-)
\simeq
C_1
\coprod_{\displaystyle\coprod_g
 \operatorname*{colim}_{K_{\leq1}/B_g}A(t-)}
\coprod_g A(B_g).
\tag{13}
\]

Active-image factorization reflects \(K_{\leq1}/B_g\) onto its proper inert atomic incidences. Their colimit is
\[
A(\partial_{\mathrm{at}}B_g).
\]
Here one uses atomic descent: a proper submesh with several parallel wires need not itself lie in \(K_{\leq1}\), but its atomic covering diagram does.

For every genuine corolla, \(\square B_g=[1,1]\). After globular localization,
\[
A(\square B_g)=D^2,\qquad
A(\partial_{\mathrm{at}}\square B_g)=\partial D^2.
\]
Substitute (5) into (13), and use associativity of pushouts:
\[
\operatorname*{colim}_K A(t-)
\simeq
C_1\coprod_{\coprod_{g\in\Gamma_2}\partial D^2}
\coprod_{g\in\Gamma_2}D^2.
\tag{14}
\]

The two boundary arrows are the prescribed source and target words. Empty words are included. In particular, for a scalar corolla, (10) gives a natural transformation of its boundary diagram to the constant region diagram, so both boundary arrows attach to \(1_x\) coherently.

Equations (12)–(14) prove (7).

---

# 5. Computing the values of \(X_\Gamma\)

The remaining calculation is entirely in ordinary finite trusses.

For a grid \(Q=[m,n]\), (6) gives
\[
X_\Gamma(Q)\simeq B(Q\downarrow t).
\tag{15}
\]

## 5.1. Active support

Let \(\mathcal A_Q\) be the full subcategory on active maps \(Q\to tM\). Active/inert factorization, with restriction of labels along the inert factor, gives a right adjoint to
\[
\mathcal A_Q\hookrightarrow(Q\downarrow t).
\]
Hence
\[
B\mathcal A_Q\simeq B(Q\downarrow t).
\tag{16}
\]

Every morphism in \(\mathcal A_Q\) is active, by cancellation in the active class.

For \(Q=[1,1]\), an active map \(Q\to M\) exists precisely when every leg
\[
S_i\to L_i,\qquad S_i\to L_{i+1}
\]
is endpoint-preserving. When it exists, it is unique.

Indeed, the outer map is the unique endpoint map \([1]\to[r]\). At every target height stratum, activity forces the corresponding inner map \([1]\to[k]\) to be its unique endpoint map. Compatibility is exactly endpoint preservation by the legs.

This guarantees that every genuine wire continues to a vertex or to the top or bottom boundary. There is no wire entering or leaving through a side at an intermediate height.

## 5.2. Active maps preserve the graph

Let \(h:M\to N\) be active.

Every genuine target vertex has a source predecessor. Applying (4) at the outer and inner levels shows that this predecessor is unique. Its dimension label must be \(0\), because neither \(1\) nor \(2\) maps to \(0\).

Conversely, apply the normalized-germ condition to a source vertex’s atomic neighborhood. Its active image has the same corolla normal form and therefore exactly one genuine target vertex.

Thus \(h\) gives a bijection of genuine vertices and their ordered ports. The wire-germ condition propagates this bijection along wires. A wire cannot pass through a target vertex, since that would require \(1\leq0\). Ordered boundary ports are preserved, so edges and their incidences are preserved as well.

Region labels and side incidences are preserved because a region stratum cannot precede a genuine wire or vertex.

## 5.3. A functorial normalization on \(\mathcal A_Q\)

Normalization is not needed as a functor on all of \(I_\Gamma\). On \(\mathcal A_Q\), the following explicit construction is functorial.

**First, delete all artificial singular points in every horizontal fiber.**

If a source singular point has label \(2\), its interval in (4) cannot cross a target singular point labelled \(0\) or \(1\). Therefore the target quotient is constant on every interval collapsed by the source quotient. Every horizontal ordinal map descends uniquely.

**Second, delete every singular-height row having no genuine vertex.**

After the first step, such a row has only genuine wire points. Each continues uniquely on both sides, and activity accounts for every adjacent wire. Its two legs are therefore identity maps of the same ordered wire word.

For an active map with outer ordinal map \(\alpha\), a deleted source row cannot map across a retained target vertex tier: that target vertex would have a genuine source vertex predecessor in the deleted row. Thus the outer map descends uniquely too.

The descended inner maps satisfy their compatibility equations because those equations held before taking the surjective quotients.

Consequently there is an actual functor \(N\) and natural transformation
\[
\nu:\mathrm{id}_{\mathcal A_Q}\Longrightarrow iN,
\qquad Ni=\mathrm{id},
\tag{17}
\]
where \(i\) includes the normal meshes. The degeneracies in (17) preserve every genuine normalized germ, so they are morphisms of \(I_\Gamma\).

After fixing marks on the graph, a normal mesh is precisely a tier encoding. Its singular row is the full list of vertices and through-edges. If that list is \(b_1,\ldots,b_k\), its two leg maps are
\[
j\longmapsto\sum_{\ell=1}^{j}d^\pm(b_\ell),
\]
where
\[
d^-(b)=
\begin{cases}
1,&b\text{ is a through-edge},\\
\text{input arity of }b,&b\text{ is a vertex},
\end{cases}
\]
and \(d^+\) uses output arity.

These prefix-sum formulas show both directions:

- a tier refinement defines a unique active map of normal marked meshes;
- an active map of normal marked meshes is exactly such a refinement.

Thus the normal marked category for the square is \(P_G\), and (17) gives
\[
B\mathcal A_{[1,1],G}\simeq BP_G.
\tag{18}
\]

Under bubble-freeness the graph automorphisms are trivial, by Section 3.

---

# 6. Grids, naturality, and the strict comparison

For \(Q=[m,n]\), the same calculation retains the grid’s horizontal and vertical cut data. Vertices lie in grid cells; wires cannot cross a vertical cut. Restriction gives a functor
\[
P_{G,Q}\longrightarrow
\prod_{\text{grid cells }c}P_{G_c,[1,1]}.
\tag{19}
\]

This functor is final. Here is the required comma-category calculation.

Fix cell encodings \((\sigma_c)\). The comma category consists of global tier encodings whose restriction to each cell refines \(\sigma_c\). The only additional choice is how to interleave events in different columns.

Choose heights in their horizontal grid bands. Impose strict inequalities between different original tiers of each \(\sigma_c\), and impose no equalities within an original tier. These are consistent strict linear inequalities, so the permitted height set is nonempty and convex.

The global weak orders of these heights, together with the fixed horizontal factor lists, index exactly the comma category. Its nerve is contractible. One finite verification is to use the braid arrangement: after quotienting common translation, slice the permitted convex cone by a positive linear functional. The allowed faces are upward-closed under refinement. In the barycentric subdivision, deleting the coordinates of disallowed face-vertices and renormalizing retracts the allowed region onto their order complex. The denominator is positive because the maximal support face is allowed.

Quillen’s criterion therefore proves finality of (19), and
\[
BP_{G,Q}\simeq
\prod_c BP_{G_c,[1,1]}.
\tag{20}
\]

The low-dimensional grid values are also explicit:
\[
X_\Gamma([0,n])\simeq\Gamma_0,
\qquad
X_\Gamma([m,0])\simeq N(C_1)_m.
\tag{21}
\]
For the first, activity permits no genuine horizontal singular point. For the second, a normal mesh is a wire word, and an active map \([m]\to[\text{word length}]\) splits it into \(m\) possibly empty subwords.

Now consider the **canonical evaluation map**
\[
j^*X_\Gamma\longrightarrow N_2F(\Gamma)
\tag{22}
\]
induced by the generator assignments in (14).

On a normal mesh, (22) evaluates a tier by horizontal composition and evaluates consecutive tiers by vertical composition. Refining a tier changes the order of independent operations, so strict interchange leaves its value unchanged.

The connected components are exactly the strict \(2\)-cells. To see this without an additional geometric coherence theorem, construct a strict \(2\)-category whose \(2\)-cells are sequential generator applications modulo adjacent independent exchanges. Concatenation gives vertical composition; placing histories side by side gives horizontal composition, and exchanges make the result independent of the chosen interleaving. This strict \(2\)-category has the defining universal property of \(F(\Gamma)\).

If \(\Gamma\) is bubble-free, Sections 2–3 show that every connected component of each \(BP_{G_c,[1,1]}\) is contractible. Equations (18)–(21) consequently show that every fiber of (22) is contractible. Thus (22) is an objectwise equivalence.

The map is natural on grids: outer faces restrict diagrams, inner faces remove cuts and compose, and degeneracies insert identity rows or columns. These operations are the ones used by the canonical atomic cocone defining (22).

Finally, \(N_2F(\Gamma)\) is complete. The number of \(2\)-generator vertices is additive under composition, so an invertible \(2\)-cell must be an identity. An equivalence of \(1\)-cells would therefore be a strict inverse, and positive word length excludes nonidentity strict inverses.

Applying \(L_2\) to (22), and using (7), gives
\[
\operatorname{Free}(\Gamma)
\simeq
L_2j^*X_\Gamma
\simeq
F(\Gamma).
\]
The map sends every generator to itself, so it is \(c_\Gamma\). This proves the sufficiency direction and hence the theorem.

---

# 7. Consequences and higher-dimensional scope

## Exact recognition in dimension two

Combining the theorem with your known results gives:

\[
\boxed{
\text{finite homotopical \(2\)-polygraphs}
=
\text{finite bubble-free \(2\)-polygraphs}.
}
\]

Recognition is therefore undecidable, by your item 3.

It also gives the finite case of the stated homological-coherence conjecture. Bubble-free free \(2\)-categories are homotopical and hence homologically coherent by your item 12. A bubble gives nonzero nerve homology in arbitrarily high degrees, while the polygraphic chain complex of a free \(2\)-category is concentrated in degrees at most \(2\).

## A broader finite sufficient test

A finite \(2\)-polygraph is homotopical if either:

- every \(2\)-generator has a nonempty target; or
- every \(2\)-generator has a nonempty source.

For the first condition, once a derivation starting at an empty word becomes nonempty, it cannot become empty again. For the second, no nonidentity derivation can start at an empty word. Both conditions therefore imply bubble-freeness.

This applies to multiple vertices and arbitrary composite boundaries. In particular, your example
\[
\eta:1\Rightarrow st,\qquad \mu:ts\Rightarrow t
\]
is covered by the first condition.

## An exact theorem for iterated suspensions

For every \(k\geq0\),
\[
\boxed{
\Sigma^k\Gamma\text{ is homotopical}
\quad\Longleftrightarrow\quad
\Gamma\text{ is bubble-free},
}
\]
when \(\Gamma\) is a finite \(2\)-polygraph.

Suspension preserves the relevant colimits, and its distinguished hom is the original category:
\[
\operatorname{Hom}_{\Sigma C}(0,1)\simeq C.
\]
These are Loubaton’s suspension adjunction and Proposition 2.2.1.20. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

Thus
\[
c_{\Sigma\Gamma}=\Sigma c_\Gamma,
\]
and suspension both preserves and detects equivalences of these comparisons.

Consequently, an iterated suspension of a \(2\)-polygraph satisfying either finite syntactic test above is homotopical in every dimension. This includes the operadic classes in your items 4–5 and all their suspensions.

The argument does not settle Question 1 or provide a finite sufficient condition encompassing **all** positive polygraphs in higher dimensions. Its complete recognition result is Question 2, together with the suspension theorem above.

# Followup 3

I obtained two dimension-independent closure theorems. Together they give a **finite-certificate recognition criterion** covering the operadic examples, their suspensions, and mapping cylinders and cones built from them.

**This does not yet resolve Question 1.** In particular, I have not proved that every positive polygraph satisfies the criterion below. The distinction matters: positivity will certify a *map into an already homotopical template*; it will not be used to assume that the template is homotopical.

I use your stagewise formulation of homotopicality throughout.

## 1. Homotopicality is inherited along discrete Conduché functors

Recall that a strict \(\omega\)-functor \(p:C\to D\) is **discrete Conduché** if it uniquely lifts identity decompositions and binary compositions. Concretely, whenever
\[
p(u)=v*_k w,
\]
there is exactly one factorization
\[
u=\widetilde v*_k\widetilde w,
\qquad
p(\widetilde v)=v,\quad p(\widetilde w)=w,
\]
and a cell mapping to an iterated identity is itself the corresponding iterated identity. This is Guetta’s Definition 3.2. [dml.cz](https://www.dml.cz/bitstream/handle/10338.dmlcz/153427/HigherStructures_004-2020-2_4.pdf?utm_source=chatgpt.com)

### Theorem A

Let \(\Gamma,\Delta\) be finite polygraphs and
\[
p:F(\Gamma)\longrightarrow F(\Delta)
\]
a discrete Conduché strict functor. Then
\[
\boxed{\Delta\text{ homotopical}\quad\Longrightarrow\quad
\Gamma\text{ homotopical}.}
\]

This follows from Guetta’s description of the lifted generating basis and Loubaton’s theorem that discrete Conduché pullback preserves colimits in \(\mathrm{Cat}_{\omega}\). The relative cell calculation needed to combine those results is given below. [dml.cz](https://www.dml.cz/bitstream/handle/10338.dmlcz/153427/HigherStructures_004-2020-2_4.pdf?utm_source=chatgpt.com)

### Proof

Write \(C=F(\Gamma)\), \(D=F(\Delta)\), and let \(C^{(n)},D^{(n)}\) denote the strict subcategories generated through dimension \(n\). We regard these strict categories as \((\infty,\omega)\)-categories.

**First, identify the generators and skeleta.** Guetta’s Theorem 6.11 gives
\[
\Gamma_n=p_n^{-1}(\Delta_n).
\tag{1}
\]
Moreover,
\[
C\times_D D^{(n)}\cong C^{(n)}.
\tag{2}
\]
Indeed, the higher-dimensional cells of \(D^{(n)}\) are iterated identities on cells of dimension at most \(n\), and discrete Conduché identity lifting gives precisely the analogous cells in \(C\).

**Second, calculate the pullback of one globe attachment.** For \(g\in\Delta_n\), put
\[
G_g=C\times_D D^n,\qquad
L_g=C\times_D\partial D^n,
\]
using the characteristic map \(g:D^n\to D\).

The projection \(G_g\to D^n\) is discrete Conduché. A globe has no composition of two nonunit factors. Unique lifting therefore gives the same property in \(G_g\). Consequently its nerve is assembled from its individual globes by their face maps.

More formally, Loubaton’s Lemma 2.2.2.6 supplies a final category of globular maps into this pullback; every globular \(\Theta\)-subshape of \(D^n\) is itself a globe. Thus \(L_g\to G_g\) has the following relative presentation, which is a homotopy pushout already in space-valued presheaves:
\[
\begin{array}{ccc}
\displaystyle\coprod_{a\in p_n^{-1}(g)}\partial D^n
&\longrightarrow&
\displaystyle\coprod_{a\in p_n^{-1}(g)}D^n
\\[4pt]
\downarrow&&\downarrow
\\
L_g&\longrightarrow&G_g.
\end{array}
\tag{3}
\]

There is a necessary precision here: **\(G_g\) need not be a coproduct of globes.** Distinct lifted generators can have identical boundary cells. Diagram (3) identifies those boundary cells through \(L_g\).

Also, a formal face of the original globe retains its tag in the pullback. Its image is
\[
\bigl(a|_\sigma,\sigma\bigr)\in L_g.
\]
Thus two formal faces identified by \(g:D^n\to D\) are not prematurely identified in this calculation.

**Third, pull back the skeletal attachment.** The dimension-\(n\) attachment comparison for \(D\) is
\[
\alpha_n^D:
D^{(n-1)}
\amalg_{\coprod_{g\in\Delta_n}\partial D^n}
\coprod_{g\in\Delta_n}D^n
\longrightarrow D^{(n)},
\tag{4}
\]
where the pushout on the left is taken in \(\mathrm{Cat}_{\omega}\).

Loubaton’s Theorem 2.2.2.10 says that
\[
p^*:\mathrm{Cat}_{\omega}/D\longrightarrow
\mathrm{Cat}_{\omega}/C
\]
preserves colimits. Applying it to (4), then using (2), gives a comparison with domain
\[
C^{(n-1)}
\amalg_{\coprod_{g\in\Delta_n}L_g}
\coprod_{g\in\Delta_n}G_g.
\]

Substituting (3) and composing pushouts identifies this domain with
\[
C^{(n-1)}
\amalg_{\coprod_{a\in\Gamma_n}\partial D^n}
\coprod_{a\in\Gamma_n}D^n.
\]
The resulting comparison to \(C^{(n)}\) is its prescribed skeletal attachment comparison. Therefore
\[
\boxed{p^*(\alpha_n^D)\simeq\alpha_n^C.}
\tag{5}
\]

If \(\Delta\) is homotopical, every \(\alpha_n^D\) is an equivalence, hence so is every \(\alpha_n^C\). The same argument applies to successive individual generator attachments. ∎

### A reflection statement

There is also an exact converse under an additional hypothesis:
\[
\boxed{
\begin{gathered}
p\text{ discrete Conduché and surjective on all strict cells}\\
\Longrightarrow\\
\Gamma\text{ homotopical}\iff\Delta\text{ homotopical}.
\end{gathered}}
\tag{6}
\]

To prove this, take any \(\theta\to D\). Lift its composite cell to \(C\). Unique lifting against the active map
\[
D^{\dim\theta}\longrightarrow\theta
\]
extends that lift to \(\theta\to C\). Thus \(Np\) is objectwise surjective. Pullback along such a map detects equivalences of presheaves over the base, so \(p^*\) is conservative. Apply this to (5).

Surjectivity on generators alone does not supply this argument: \([1]\to F(\text{one loop})\) is discrete Conduché and surjective on generators, but the square of the loop has no lift.

## 2. A finite typing test that guarantees the Conduché hypothesis

The lifting hypothesis in Theorem A quantifies over all cells. Henry’s results remove that quantifier for an important class of maps.

Call a polygraph **source-positive** if every generator of dimension at least \(2\) has nonidentity source. Define **target-positive** dually.

### Theorem B

Let \(\Delta\) be a finite homotopical polygraph that is source-positive or target-positive. If there is a polygraphic map
\[
p:\Gamma\longrightarrow\Delta,
\]
then \(\Gamma\) is homotopical.

Here *polygraphic* means that every generator maps to a generator of the same dimension.

### Proof

Henry’s condition (C) says that composition is a **cartesian natural transformation** in the polygraph:
\[
F(X)_n\times_{F(X)_k}F(X)_n
\longrightarrow F(X)_n.
\]
Corollary 2.3.13 proves condition (C) for every good class of polygraphs. Theorem 2.4.8 establishes this for source-positive polygraphs; its dual gives target-positive polygraphs. This is stronger than the assertion that polygraphs in these classes have no polyplex automorphisms. [higher-structures.math.cas.cz](https://higher-structures.math.cas.cz/api/files/issues/Vol3Iss1/Henry?utm_source=chatgpt.com)

Cartesianity says exactly that every composition factorization lifts uniquely along a polygraphic map in either class.

Such maps also reflect identities. For an \(n\)-cell \(u\), let \(w_n(u)\) count its \(n\)-generators. The strict category equations preserve this count, and
\[
w_n(u)=0
\quad\Longleftrightarrow\quad
u\text{ is an identity on an }(n-1)\text{-cell}.
\]
A polygraphic map preserves \(w_n\), so a cell mapping to an identity must be an identity.

Thus \(F(p)\) is discrete Conduché, and Theorem A applies. Domain positivity follows automatically: an identity boundary in \(\Gamma\) could not map to the required nonidentity boundary of a generator of \(\Delta\). ∎

### What is checked on finite data

For a proposed typing, the required data are:

1. Functions \(p_n:\Gamma_n\to\Delta_n\) on the finite generating sets.
2. The boundary equations
   \[
   F(p)(s(a))=s(p(a)),\qquad
   F(p)(t(a))=t(p(a))
   \]
   for every generator \(a\).
3. The source-positive or target-positive condition on \(\Delta\).
4. A homotopicality certificate for \(\Delta\).

The boundary equations are decidable: Makkai’s *The word problem for computads*, Theorem 7.(3), proves decidability of equality between explicitly given cells in a computad. Alternatively, a certificate can supply finite derivations using the strict category axioms. [math.mcgill.ca](https://www.math.mcgill.ca/makkai/WordProblem/WordProblemCombined.pdf?utm_source=chatgpt.com)

In particular, for a **fixed finite catalogue of certified finite templates**, existence of such a typing is decidable: enumerate the finitely many assignments of generators and check their boundary equations.

The role of positivity in this theorem is precise: **it certifies unique lifting along the typing map. Homotopicality of the template is a separate hypothesis.**

## 3. Mapping cylinders preserve homotopical presentations

The next result supplies new templates in arbitrarily high dimensions, including non-positive ones.

### Theorem C

Let
\[
A=F(\Gamma),\qquad B=F(\Delta),\qquad E=F(\mathcal E)
\]
have finite homotopical presentations, and let
\[
f:A\longrightarrow B,\qquad g:A\longrightarrow E
\]
be arbitrary strict functors.

Their strict double mapping cylinder
\[
M_{\mathrm s}(f,g)=
B\amalg_{A\otimes_{\mathrm s}\{0\}}
(A\otimes_{\mathrm s}[1])
\amalg_{A\otimes_{\mathrm s}\{1\}}E
\tag{7}
\]
has a finite homotopical polygraphic presentation.

Its generating sets are
\[
\boxed{
M(f,g)_n=
\Delta_n\sqcup\mathcal E_n
\sqcup\{\widehat a:a\in\Gamma_{n-1}\},
}
\tag{8}
\]
where \(\Gamma_{-1}=\varnothing\).

Thus every \(n\)-generator \(a\) of \(\Gamma\) supplies one \((n+1)\)-generator \(\widehat a\). The endpoint functors may send generators to composites or identities.

The generators supplied by \(B\) and \(E\) in (8) are disjoint copies, including when \(B=E\).

### Proof

There are two separate points to establish: strictness of the weak mapping cylinder, and homotopicality of its stated cellular presentation.

#### 3.1. The weak mapping cylinder is the strict one

Loubaton’s Theorem 2.3.3.22 proves that double mapping cylinders of strict inputs are strict. Proposition 2.3.3.1 identifies their strictifications with the ordinary strict Gray constructions. Hence there is a canonical equivalence
\[
B\amalg_{A\otimes\{0\}}
(A\otimes[1])
\amalg_{A\otimes\{1\}}E
\simeq M_{\mathrm s}(f,g),
\tag{9}
\]
with the left-hand pushouts and tensor computed in \(\mathrm{Cat}_{\omega}\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The applicable strict inputs are gaunt. Finite free strict categories have this property: generator count excludes invertible cells in the top dimension, and descending induction excludes equivalences in lower dimensions.

Equation (9) by itself does not establish that presentation (8) is homotopical. For that, one needs the following relative prism calculation.

#### 3.2. The universal prism attachment

Set
\[
Q_n=D^n\otimes_{\mathrm s}[1]
\]
and
\[
L_n=
(\partial D^n\otimes_{\mathrm s}[1])
\amalg_{\partial D^n\otimes_{\mathrm s}\partial[1]}
(D^n\otimes_{\mathrm s}\partial[1]).
\tag{10}
\]

The polygraph \(L_n\) is precisely the \(n\)-skeleton of \(Q_n\). The only omitted generator is the \((n+1)\)-generator obtained from the top generator of \(D^n\) and the generating arrow of \([1]\).

Let
\[
\beta_n:\partial D^{n+1}\longrightarrow L_n
\]
be its prescribed boundary map. Then
\[
\begin{array}{ccc}
\partial D^{n+1}&\longrightarrow&D^{n+1}\\
\downarrow\beta_n&&\downarrow\\
L_n&\longrightarrow&Q_n
\end{array}
\tag{11}
\]
is both a strict pushout and a homotopy pushout.

Indeed, \(Q_n\) is a strong Steiner polygraph, by stability of strong Steiner complexes under tensor product. Campion’s pasting theorem applies to its top-cell attachment (11). [webusers.imj-prg.fr](https://webusers.imj-prg.fr/~yves.guiraud/articles/polybook.pdf?utm_source=chatgpt.com)

We also need the homotopy version of expression (10) to compute \(L_n\). This follows from (9), applied to the double mapping cylinder
\[
D^n\longleftarrow\partial D^n\longrightarrow D^n.
\]
Thus no preservation of arbitrary strict pushouts is being assumed.

#### 3.3. The strict generating basis and its boundaries

The endpoint inclusion
\[
A\amalg A\longrightarrow A\otimes_{\mathrm s}[1]
\]
is a relative polygraph with one generator \(\widehat a\) for each generator \(a\) of \(A\), shifted up one dimension.

This follows by applying the strict cylinder to the cellular presentation of \(A\): the relevant pushout-product at an \(n\)-generator is exactly \(L_n\to Q_n\), which adjoins one \((n+1)\)-generator.

Push this relative presentation out along
\[
f\amalg g:A\amalg A\longrightarrow B\amalg E.
\]
This gives (8). Substitution of composite or identity endpoint images changes the attaching boundaries and does not equate the newly adjoined generators. The strict polygraph tensor and cylinder constructions are also described in *Polygraphs*, §17.2 and §§17.4.25–17.4.26. [webusers.imj-prg.fr](https://webusers.imj-prg.fr/~yves.guiraud/articles/polybook.pdf?utm_source=chatgpt.com)

The boundary of \(\widehat a\) is specified without a choice of pasting convention as follows. For the characteristic map \(\chi_a:D^n\to A\), define
\[
L_n\longrightarrow M_{\mathrm s}(f,g)^{(n)}
\]
by using:

- the previously adjoined generators \(\widehat b\) on the lateral part \(\partial D^n\otimes[1]\);
- \(f\chi_a\) at endpoint \(0\);
- \(g\chi_a\) at endpoint \(1\).

The attaching map is
\[
\partial D^{n+1}
\xrightarrow{\beta_n}
L_n
\longrightarrow M_{\mathrm s}(f,g)^{(n)}.
\tag{12}
\]

This is a finite boundary specification in every dimension.

#### 3.4. The skeletal attachments are homotopy pushouts

Write \(A_j,B_j,E_j\) for the subcategories generated through dimension \(j\), with \(A_{-1}=\varnothing\). The \(k\)-skeleton of (8) is
\[
R_k=M_{\mathrm s}(A_{k-1};B_k,E_k).
\tag{13}
\]

For \(k\geq1\), insert
\[
T_k=M_{\mathrm s}(A_{k-2};B_k,E_k).
\]

The passage
\[
R_{k-1}\longrightarrow T_k
\]
adjoins the \(k\)-generators of \(B\) and \(E\). Their attachments are homotopical by hypothesis. Pushout associativity and (9) preserve these attachments after forming the mapping cylinder.

The passage
\[
T_k\longrightarrow R_k
\]
adjoins the generators \(\widehat a\) for \(a\in\Gamma_{k-1}\). Applying the colimit-preserving weak cylinder to the homotopical attachment \(A_{k-2}\to A_{k-1}\) gives
\[
R_k\simeq
T_k
\amalg_{\coprod_{a\in\Gamma_{k-1}}L_{k-1}}
\coprod_{a\in\Gamma_{k-1}}Q_{k-1}.
\tag{14}
\]

Substitute (11) into (14):
\[
R_k\simeq
T_k
\amalg_{\coprod_{a\in\Gamma_{k-1}}\partial D^k}
\coprod_{a\in\Gamma_{k-1}}D^k.
\tag{15}
\]

The boundaries of these new \(k\)-generators already factor through \(R_{k-1}\): they use endpoint cells through dimension \(k-1\), and generators \(\widehat b\) with \(\dim b\leq k-2\). Consequently the endpoint attachments and the attachments in (15) combine into exactly the canonical dimension-\(k\) attachment for (8).

Finally, \(R_0=B_0\amalg E_0\) is discrete. Induction proves the theorem. ∎

### Consequences in every dimension

Taking particular endpoint functors in Theorem C gives:

| Construction | Endpoint data | Generators in dimension \(n\) |
|---|---|---|
| Gray cylinder of \(\Gamma\) | \(A\xrightarrow{\mathrm{id}}A\) at both ends | Two copies of \(\Gamma_n\), plus \(\Gamma_{n-1}\) |
| Mapping cone of \(f:A\to B\) | \(f:A\to B\), \(A\to1\) | \(\Delta_n\sqcup\Gamma_{n-1}\) for \(n\geq1\); one new vertex |
| Suspension of \(\Gamma\) | \(A\to1\) at both ends | Two vertices; \(\Gamma_{n-1}\) in dimension \(n\geq1\) |

All preserve homotopicality.

For example, if
\[
P_\Gamma(z)=\sum_n|\Gamma_n|z^n,
\]
then iterating the cylinder \(r\) times gives
\[
P_{\operatorname{Cyl}^r\Gamma}(z)
=(2+z)^rP_\Gamma(z).
\]
Starting with any operadic example in your item 5 therefore gives an explicit family of finite homotopical polygraphs in unbounded dimensions.

## 4. The resulting recognition criterion

Here is a precise finite-certificate version.

### Corollary: finite construction and typing certificates

A finite polygraph is homotopical if it has a finite certificate built from the following rules.

**Initial certificates.** Use any of the established finite classes, with the finite data verifying the applicable hypothesis:

- positive \(2\)-polygraphs;
- the operadic \(2\)-polygraphs and their duals;
- the partition test in your item 7;
- regular \(3\)-polygraphs;
- strong Steiner polygraphs, or directed complexes with acyclic atoms.

For the last item, acyclicity is checked on the supplied finite atom shapes; it does not require quantification over all pasting diagrams. Chanavat’s Corollary 3.27 supplies the corresponding homotopicality theorem. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

**Construction rules.**

1. Form a finite disjoint union.
2. Apply an orientation duality.
3. Form a double mapping cylinder of two specified strict functors between previously certified presentations.
4. Apply Theorem B: provide a polygraphic typing into a previously certified source-positive or target-positive template.

Cones, cylinders, and suspensions are instances of rule 3.

Each certificate is a finite directed acyclic list of constructions. A verifier checks generator dimensions, boundary equations, the applicable positivity condition, and the initial certificates. Theorems A–C prove soundness by induction through this list.

This gives two distinct effective statements:

- **Certificate verification terminates** for the unrestricted construction system.
- **Recognition by typing into a fixed finite catalogue terminates** by finite enumeration of generator assignments and decidability of cell equality.

The operadic classes and all their suspensions are included directly. The mapping-cylinder rule adds constructions involving arbitrary strict functors, including functors with identity or composite generator images.

## 5. What remains unresolved

The criterion above does **not** establish that every positive polygraph has a certificate.

There is an exact limitation to obtaining that conclusion merely by typing into known shape classes. Henry’s definition of a class of polygraphs makes it closed under domains of polygraphic maps:
\[
Y\longrightarrow X,\quad X\in\mathcal J
\quad\Longrightarrow\quad Y\in\mathcal J.
\]
Thus typing into templates from an existing good class cannot by itself reach polygraphs outside that class. New constructions of templates can enlarge the criterion, but the enlargement must be proved.

The proposed dimension-four obstruction also remains inconclusive. Chanavat’s example supplies a factorization
\[
\mathsf{Sp}\,U\longrightarrow C\longrightarrow\mathrm{Mol}/U,
\]
where \(C\) is the free strict category obtained from the atomic attachments, while the second map imposes the additional stricter equations. The published failure concerns the composite into \(\mathrm{Mol}/U\); it does not establish failure of the comparison into \(C\). [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

For the regular subclass, Chanavat’s Comment 3.40 identifies the remaining contraction problem: the subdivision category of a regular polyplex that is not a plex should be contractible. The results above neither prove that assertion nor produce a positive polyplex violating it. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

Accordingly, the new result is a **proved sufficient recognition system in every dimension**, with the requested non-positive operadic examples and their suspensions. **Question 1, and the requirement that a recognition system cover every positive polygraph, remain unresolved here.**
