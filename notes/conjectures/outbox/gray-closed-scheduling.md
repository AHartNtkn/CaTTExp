**Status: unsent** (ready to send).

# Schedules in free Gray-monoidal biclosed 2-categories: does the closed structure add 2-cells?

*A self-contained problem (2026-11-18). No knowledge of the project that posed it is assumed. The smallest open case is Question 1.*

## Background

**Schedules.** Fix a finite poset P on labels {1, …, n}, with numerical order as the left/right order of incomparable labels. Let S(P) be the category with:
- objects: the linear extensions of P;
- generating arrows: swaps ji → ij of adjacent P-incomparable labels with i < j;
- equations: commuting squares for swaps at disjoint positions, and the braid hexagon for three pairwise incomparable labels.

Then S(P)(w, v) is a singleton if Inv_P(v) ⊆ Inv_P(w) and empty otherwise. Here Inv_P(w) is the set of pairs i < j, incomparable, with j before i in w. (Proof: move the first differing label left, then resolve the first swaps by a square or a hexagon and induct.)

**Gray monoids.** In the free strict Gray monoid (a monoid in 2-Cat for Gray's lax tensor) on a set of objects and generating 1-cells, fix the image in the free strict monoidal category, i.e. the string diagram. Then the hom-category between the 1-cells with that diagram is S(P). Here P is the diagram's dependency order, with left/right given by planarity. The 2-cells are whiskered interchangers (f ⊗ B′)∘(A ⊗ g) ⇒ (A′ ⊗ g)∘(f ⊗ B), "right factor first ⇒ left factor first".

**The ω-version.** The hom ω-category of the Steiner complex ν(I^⊗n), from bottom to top, is not thin: two hexagon 2-cells are joined by the 3-cell ***. Gray's 2-tensor is its intelligent 2-truncation (Ara–Maltsiniotis, *Joint et tranches*, A.25 and A.31). For a dependency poset P, the subcomplex K_P ⊆ I^⊗n spanned by the faces (order ideal J, S ⊆ min(P∖J)) has paths equal to the linear extensions of P. Its truncated hom is S(P).

## Setting: the biclosed version

Formulas are built from atoms with ⊗ and the residuals B\A and A/B, with no unit. 𝒢 is the free **Gray-monoidal biclosed strict 2-category** on a set of generating 1-cells fᵢ : Pᵢ → Qᵢ between formulas. Its structure:
- a strict 2-category with a Gray monoidal structure (lax interchangers, as above);
- closed structure: isomorphisms of hom-categories Φ : 𝒢(A ⊗ B, C) ≅ 𝒢(B, A\C), and the mirror one for /.
  - Φ is **strictly natural in the context variable B**.
  - Φ is natural in the **bound variable A only up to the interchanger**.
  - Strict naturality in A would force (f ⊗ B′)(A ⊗ g) = (A′ ⊗ g)(f ⊗ B), collapsing distinct schedules into one 1-cell. That is not wanted.

**Two warnings, both established.**
1. *Nesting is not invariant under naive normalization.* For a generator h : U → U with U = X\Y,

   ```
   h = Λ(ev) ∘ h = Λ(ev ∘ (1 ⊗ h))
   ```

   So h can be "ambient" or "inside a closure". β-reduction ev ∘ (1 ⊗ Λk) = k also changes nesting. Any invariant notion of "event inside a closure" must start from a βη-canonical form.
2. *Unit-free planar coherence.* In the free unit-free biclosed monoidal 1-category, a balanced sequent (each atom twice, opposite polarities) has at most one morphism, and exactly one when it is provable in the Lambek calculus with product. So the purely structural parts of 1-cells are unique.

## Questions

1. **(Smallest open case: one closure, two events.)** Take generators φ : P → C/B and b : X → B, and the 1-cells

   ```
   t₁ = ev ∘ (φ ⊗ B) ∘ (P ⊗ b)      (b first)
   t₂ = ev ∘ (C/B ⊗ b) ∘ (φ ⊗ X)    (φ first)
   ```

   from P ⊗ X to C. Is 𝒢(t₁, t₂) a singleton (the interchanger) and 𝒢(t₂, t₁) empty?
   Do the same with b replaced by a generator acting inside a curried argument. For example, take ψ : Q → B\D and a 1-cell that curries, applies a generator to the bound variable, and evaluates. Is the hom-category again S(P) for an appropriate P, or does currying create new 2-cells or new identifications?
2. **(Comparison theorem.)** Define a βη-canonical nested form for 1-cells of 𝒢: a tree of closures, each with its own internal schedule. Is each hom-category of 𝒢, between 1-cells with the same canonical tree and the same string diagram at each node, the product over nodes of the S(Pₙ)? Here a closure containing events counts as one compound event at its parent node.
3. **(Cross-level cells.)** Is the ordinary interchanger between an outer event and a closure 1-cell, (c ⊗ 1)(1 ⊗ a) ⇒ (1 ⊗ a)(c ⊗ 1), the only 2-cell relating schedules across levels? Equivalently, is the canonical tree an invariant of the connected components of hom-categories?
4. **(ω-version.)** For the free Gray-monoidal biclosed (∞,ω)-category, defined using the lax Gray tensor of Campion (arXiv 2311.00205), with biclosedness on mapping spaces only: are the hom ω-categories between such 1-cells products of the ν(K_P)-homs?

## What counts as a solution

- An answer to Question 1 with proof, for either variant.
- A proof or counterexample for Question 2 or Question 3.
- A reference treating 2-cells of free Gray-monoidal (bi)closed 2-categories.

## Literature (searched 2026-11-18)

- **Gray monoids and categories:** Gordon–Power–Street, *Coherence for tricategories* (1995); Forest–Mimram, *Coherence of Gray categories via rewriting* (FSCD 2018); Bourke–Lobbia (arXiv 2212.12358) on skew-closed structures.
- **Weak order on linear extensions:** Björner–Wachs, JCTA 58 (1991), Thm 6.8; Chatel–Pilaud–Pons (arXiv 1701.07995), Prop. 26.
- **Higher Bruhat orders:** Manin–Schechtman (1989); Kapranov–Voevodsky (1991).
- **Biclosedness on mapping spaces only:** Gagna–Harpaz–Lanari (arXiv 2006.14495), Rem. 2.20.
- **Oriented categories:** Gepner–Heine (arXiv 2510.10504), Cor. 4.1.11.
- No paper on 2-cells of free Gray-closed structure was found.

# Researcher Response

**An ordinary interchanger can change the closure structure after β-reduction.** More precisely, it can connect a 1-cell that necessarily has a generator beneath currying to a 1-cell with a tensor-only representative. This gives a counterexample to the component-invariance formulation of Question 3 for a normal form that fixes already-normal tensor-only terms.

The argument works with two generators between tensor-only formulas. It distinguishes their βη-equivalence classes, so it does not rely on the nesting ambiguity in Warning 1.

I do **not** establish the singleton/empty assertion in Question 1, or the restricted product assertion in Question 2.

## 1. The counterexample

Take four distinct atoms \(X,A,B,C\), and exactly two generating 1-cells
\[
a:X\longrightarrow A,
\qquad
f:A\otimes B\longrightarrow C.
\]
Put
\[
U=A\backslash C,\qquad
c=\Lambda_A(f):B\longrightarrow U,
\qquad
e=\operatorname{ev}_{A,C}:A\otimes U\longrightarrow C.
\]

Define
\[
s
=
e\circ(a\otimes U)\circ(X\otimes c)
\]
and
\[
t
=
e\circ(A\otimes c)\circ(a\otimes B).
\]

Your interchanger orientation gives
\[
\chi_{a,c}:
(a\otimes U)\circ(X\otimes c)
\;\Longrightarrow\;
(A\otimes c)\circ(a\otimes B).
\]
Postcomposition with \(e\) therefore gives
\[
\boxed{\theta=e*\chi_{a,c}:s\Longrightarrow t.}
\tag{1}
\]

On the target, the stated β-equation applies:
\[
e\circ(A\otimes\Lambda_A(f))=f.
\]
Consequently,
\[
\boxed{t=f\circ(a\otimes B).}
\tag{2}
\]

Thus \(t\) has a tensor-only representative. The corresponding β-contraction in \(s\) is interrupted by \(a\otimes U\).

That observation alone would not be enough: perhaps some other sequence of βη-equalities removes the closure from \(s\). The next argument excludes that possibility, including structural detours through additional residual types.

## 2. A distinction invariant under βη-equality

For a 1-cell \(u\), let \(E(u)\) mean:

> There is a term denoting \(u\) such that no generator leaf is a descendant of a currying node in its syntax tree.

Here derived residual actions are expanded using currying and evaluation. Generator-free currying is permitted. Thus \(E\) allows arbitrary purely structural closed terms; it only prohibits placing a generating 1-cell beneath currying.

Because this definition quantifies over all representatives of \(u\), it is a property of its βη-equivalence class.

I will prove
\[
\boxed{E(t)\text{ holds},\qquad E(s)\text{ does not hold}.}
\tag{3}
\]

### 2.1 A generator-word invariant

Under the fixed-object closure axioms stated in the question, there is an invariant \(W\) of **1-cell equality** with values in words in the generating labels:
\[
\begin{aligned}
W(1)&=\epsilon,\\
W(a)&=a,\qquad W(f)=f,\\
W(v\circ u)&=W(u)W(v),\\
W(D\otimes u)&=W(u\otimes D)=W(u),\\
W(\Lambda_\ell u)&=W(\Lambda_r u)=W(u),\\
W(\operatorname{ev}_\ell)&=
W(\operatorname{ev}_r)=\epsilon.
\end{aligned}
\tag{4}
\]
The word is written in composition order: first the word for \(u\), then the word for \(v\).

Here is a model establishing that this respects the specified equations, without assuming a normalization theorem.

Construct a strict 2-category \(\mathcal D\) as follows:

- There is one object, \(*\).
- Its 1-cells are finite words in the generating labels.
- There is exactly one 2-cell \(u\Rightarrow v\) when \(u\) and \(v\) have the same multiplicity of each label, and no such 2-cell otherwise.
- Composition of 1-cells is concatenation.

Give \(\mathcal D\) a lax Gray-monoidal structure by taking tensoring by its sole object to be the identity 2-functor. The interchanger is the unique 2-cell
\[
vu\Longrightarrow uv.
\]
The Gray coherence equations hold because their two sides are parallel 2-cells, and each such 2-cell set has at most one element.

Choose both fixed-object residual 2-functors and both currying isomorphisms to be identities. Evaluations and adjunction units are the empty word. Both fixed-object adjunctions are therefore identity adjunctions. Strict context naturality, and also strict codomain naturality, hold literally.

This model uses the question’s weak bound-variable reading: bound-variable comparisons are 2-cells, rather than additional 1-cell equalities. Requiring a separately strict contravariant action in the bound variable would be an additional axiom.

Sending each generator to its label gives (4). In particular,
\[
W(s)=fa,\qquad W(t)=af.
\tag{5}
\]
Hence
\[
s\ne t
\]
as 1-cells.

The model may send distinct formula atoms to the same object; that is sufficient for separating the two 1-cells in the free theory.

### 2.2 Why every representative of \(s\) requires a generator beneath currying

Suppose \(E(s)\) held, and choose a representative witnessing it.

Every currying subterm in this representative is generator-free. By flattening composition and tensor whiskering, we can therefore factor the representative into a sequence of:

1. generator-free structural 1-cells; and
2. individual generators whiskered on the left and right by formulas.

Equation (5) forces the first generator in this sequence to be \(f\), followed later by \(a\). Immediately before applying that first generator, there must therefore be a generator-free structural 1-cell
\[
p:X\otimes B
\longrightarrow
L\otimes(A\otimes B)\otimes R,
\tag{6}
\]
where the left or right tensor factors may be absent.

But no such structural 1-cell exists. To see this, interpret the generator-free fragment in the Boolean biclosed poset
\[
0<1,
\]
with
\[
p\otimes q=p\wedge q,
\qquad
p\backslash q=q/p=\neg p\vee q.
\]
Its closedness is the elementary equivalence
\[
p\wedge q\le r
\quad\Longleftrightarrow\quad
q\le\neg p\vee r.
\]

Assign
\[
X=B=1,\qquad A=0.
\]
The source of (6) evaluates to \(1\). Its target evaluates to \(0\), regardless of \(L\) and \(R\), because \(A\) is a tensor factor. Thus (6) would require a morphism
\[
1\longrightarrow0,
\]
which this poset does not have.

Only the generator-free prefix \(p\) is being interpreted here. There is no requirement to interpret the generator \(a:X\to A\) in this Boolean model.

This contradiction proves \(\neg E(s)\). Equation (2) proves \(E(t)\), completing (3).

## 3. Consequences for Questions 2 and 3

The normal-form-independent result is:
\[
\boxed{
s\Longrightarrow t,\qquad
\neg E(s),\qquad E(t).
}
\tag{7}
\]

Therefore, **admitting a representative with all generators outside currying is not invariant under connected components of hom-categories.**

Any βη-normal-form procedure that fixes the tensor-only term
\[
f\circ(a\otimes B)
\]
must assign \(t\) a tree with no generator-bearing closure. Every representative of \(s\), including its canonical representative, must have a generator-bearing closure. Their trees consequently differ despite the 2-cell (1).

This also shows that the two formulations of Question 3 are not equivalent:

> “Cross-level comparisons are generated by ordinary interchangers” does not imply “the canonical closure tree is invariant.”

The comparison \(\theta\) is itself an ordinary interchanger between \(a\) and the entire closure \(c\), followed by evaluation. On its target, evaluation and currying β-contract. Thus ordinary interchangers already suffice to change the tree after normalization.

### What this does and does not refute in Question 2

It rules out using closure trees as invariant labels for connected components, with the product of schedule categories then describing each component.

It does **not** by itself refute the narrower assertion that the full subcategory selected by one particular canonical tree and its node diagrams has a product description. That assertion would require a separate argument controlling 2-cell composites whose intermediate 1-cells have different trees.

The example is also a concrete instance of the bound-argument variant in Question 1. For
\[
\psi:Q\to B\backslash D,\qquad b:X\to B,
\]
there is the comparison
\[
\operatorname{ev}\circ
(b\otimes(B\backslash D))\circ(X\otimes\psi)
\Longrightarrow
\operatorname{ev}\circ(B\otimes\psi)\circ(b\otimes Q).
\]
When \(\psi=\Lambda_B(f)\), its target contracts to
\[
f\circ(b\otimes Q).
\]
The counterexample above proves that the resulting change of generator depth can survive passage to βη-equivalence classes.

## 4. What is established for the original Question 1

For your original generators
\[
\varphi:P\to C/B,\qquad b:X\to B,
\]
write \(H=C/B\) and \(e_B:H\otimes B\to C\). The canonical forward comparison is
\[
\boxed{
\alpha=e_B*\chi_{\varphi,b}:t_1\Longrightarrow t_2.
}
\tag{8}
\]

The same word model, with labels \(\varphi,b\), gives
\[
W(t_1)=b\varphi,\qquad
W(t_2)=\varphi b.
\]
Thus the stated weak bound-variable axioms do not identify these endpoints.

There is also an exact useful transpose calculation. Define
\[
C/b
=
\Lambda_X\!\left(
e_B\circ(H\otimes b)
\right)
:H\longrightarrow C/X.
\]
Strict naturality in the context variable gives
\[
\boxed{
\Lambda_X(t_2)=(C/b)\circ\varphi.
}
\tag{9}
\]
Since currying is an isomorphism of hom-categories, (8) transposes to
\[
\Lambda_X(\alpha):
\Lambda_X(t_1)
\Longrightarrow
(C/b)\circ\varphi.
\tag{10}
\]

Equations (9)–(10) locate the issue precisely: this comparison is the directed bound-variable naturality that was deliberately retained.

I have not proved either
\[
\mathcal G(P\otimes X,C)(t_1,t_2)=\{\alpha\}
\]
or
\[
\mathcal G(P\otimes X,C)(t_2,t_1)=\varnothing.
\]

The tensor-only schedule theorem does not establish these statements merely by treating \(e_B\) as an additional generator. One must also control 2-cell expressions obtained by currying, uncurrying and η-expansion. The counterexample above shows why preserving a fixed closure tree cannot supply that argument directly.

## 5. The mapping-space qualification in Question 4

Question 4 assumes less than the hom-category currying used in the finite-dimensional setting. Mapping-space biclosedness alone does not supply a currying equivalence between the full external hom \(\omega\)-categories, including their noninvertible cells.

Gagna–Harpaz–Lanari’s Remark 2.20 makes this distinction explicit in dimension two: their Cartesian mapping objects do not generally satisfy the proposed Gray currying isomorphism, whereas the corresponding maximal Kan complexes do. [arxiv.org](https://arxiv.org/html/2006.14495v1?utm_source=chatgpt.com) Campion’s Theorem A constructs a monoidal biclosed structure on the ambient \(\infty\)-category \(\mathsf{Cat}_n\); it does not state the proposed free-algebra schedule decomposition. [arxiv.org](https://arxiv.org/html/2311.00205v1?utm_source=chatgpt.com)

The elementary information-loss example is
\[
[1]^\simeq
\cong
\{0,1\}_{\mathrm{discrete}}^\simeq,
\]
although the first category has a morphism \(0\to1\) and the second does not. An equivalence of cores alone cannot determine the noninvertible comparison cells.

This does not refute the proposed products of \(\nu(K_P)\)-homs. It means that establishing them requires an argument controlling the full higher homs, beyond the stated mapping-space adjunction.

**The proved obstruction is (7): a single ordinary interchanger, followed by evaluation, changes whether generators can all be represented without currying.** That prevents closure-tree component invariance under a normalization that fixes the tensor-only fragment.
