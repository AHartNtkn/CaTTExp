# A formalizable proof that ν(K) is free on its atoms, for loop-free unital bases

*A self-contained problem. It assumes no knowledge of the project that posed it. The result is known (Steiner 2004). What is asked for is a proof short and elementary enough to be machine-checked.*

## Background

We use Steiner's augmented directed complexes (R. Steiner, *Omega-categories and chain complexes*, HHA 6 (2004), [math/0403237](https://arxiv.org/abs/math/0403237); Ara–Maltsiniotis, [1607.00668](https://arxiv.org/abs/1607.00668), §2).

**Complexes.** An augmented directed complex K is a chain complex of free abelian groups Kₙ (n ≥ 0), with an augmentation ε : K₀ → ℤ and a distinguished basis Bₙ of each Kₙ. Kₙ* is the monoid of non-negative combinations of Bₙ. For a chain c, supp(c) is its set of basis elements with non-zero coefficient. We write ∂c = (∂c)₊ − (∂c)₋ with (∂c)₊, (∂c)₋ ∈ Kₙ₋₁* of disjoint supports.

**Cells.** An n-cell of ν(K) is a table x = (x₀⁻, x₀⁺, …, xₙ⁻, xₙ⁺) such that:
- xₖ^± ∈ Kₖ*;
- xₙ⁻ = xₙ⁺;
- ∂xₖ^± = xₖ₋₁⁺ − xₖ₋₁⁻ for 1 ≤ k ≤ n;
- ε(x₀^±) = 1.

Boundaries truncate the table. For ∂⁺ₖx = ∂⁻ₖy the composite x #ₖ y is x + y − ∂⁺ₖx entrywise: the common entries below k, (xₖ⁻, yₖ⁺) at k, and xⱼ^± + yⱼ^± above k. This makes ν(K) a strict ω-category (single-set presentation).

**Atoms.** The atom ⟨b⟩ of b ∈ Bₙ has ⟨b⟩ₙ^± = b, ⟨b⟩ₖ⁻ = (∂⟨b⟩ₖ₊₁⁻)₋ and ⟨b⟩ₖ⁺ = (∂⟨b⟩ₖ₊₁⁺)₊.

**Hypotheses on the basis.**
- *Unital:* ε(⟨b⟩₀⁻) = ε(⟨b⟩₀⁺) = 1 for every b.
- *Loop-free:* for each p ≥ 0, on basis elements of dimension > p, the relation a <ₚ b iff supp⟨a⟩ₚ⁺ and supp⟨b⟩ₚ⁻ meet generates a strict partial order (Steiner Def. 3.5).
- *Strongly loop-free:* the relation a ∈ supp(∂b)₋ or b ∈ supp(∂a)₊ generates a strict partial order on the whole basis (Def. 3.6).

The motivating instances are the complexes λΘ of finite globular pasting diagrams and finite globular sets without loops, and their tensor products, with the Leibniz boundary ∂(a ⊗ b) = ∂a ⊗ b + (−1)^{dim a} a ⊗ ∂b. Their bases are unital and strongly loop-free. In a convenient explicit presentation, each pasting diagram is built by "start with one 0-cell; at a current cell x of type A, add a new cell y of type A and a new cell f : x → y", and tensor products carry an explicit lexicographic total order with the negative faces before and the positive faces after.

## Statement

Let K have a loop-free unital basis.

- **(N1) Atom generation.** Every cell of ν(K) is an iterated composite of atoms (and of their iterated boundaries/identities).
- **(N2) Freeness.** For every strict ω-category C and every assignment φ sending each atom ⟨b⟩ (dim b = n) to an n-cell φ(b) of C, with ∂^±ₙ₋₁ φ(b) = Φ(∂^±ₙ₋₁⟨b⟩), there is exactly one strict functor Φ : ν(K) → C with Φ⟨b⟩ = φ(b). Here Φ on lower-dimensional cells is defined by induction. Equivalently (Steiner Thms 5.7 and 6.1), ν(K) is presented by its atoms with the relations fixing their boundaries.

## What is known

Steiner proves (N1) as Thm 5.6, through:
- the decomposition index (Prop. 5.4: a cell of index r ≥ 0 splits along #ᵣ into cells of lower index, each congruent to an atom);
- Prop. 5.5 (index −1 means an atom, using unitality).

He proves (N2) as Thm 5.7 by induction on the decomposition index. Uniqueness uses standard forms (Prop. 4.2) and transpositions of consecutive atoms (Props. 5.8, 5.9, Lemma 5.10). Thm 6.1 deduces the presentation.

These proofs are long, and they reason about arbitrary decompositions of a cell into atoms. A formalisation wants a proof by induction on explicit data: chains, an explicit order on the basis, and well-founded measures.

Useful known tools:
- **(Rad)** Every xₖ^± is a sum of distinct basis elements. Forest, HHA 2022, Lemma 3.4.5; Campbell, [2605.09427](https://arxiv.org/abs/2605.09427), Prop. 2.20; Steiner, *Opetopes and chain complexes*, [1204.6723](https://arxiv.org/abs/1204.6723), Thm 4.1, with a direct proof.
- **(F2)** For b ∈ supp(x_{m+1}^±), x_m⁻ is disjoint from (∂b)₊ and x_m⁺ from (∂b)₋. Forest Lemma 3.4.11; Campbell Prop. 2.23.
- **A cut lemma.** For a linear extension of the order, the partial sums of a cell's top chain cut the cell into a composite (an atom-free proof of (Rad), (F2) and "support determines the cell" for the tensor complexes above is known along these lines).

## Questions

**A short proof of (N1) in the strongly loop-free case (known, given for reference).** Suppose the basis is listed b₀, …, b_{N−1} so that supp(∂b_i)₋ ⊆ {b_j : j < i} and supp(∂b_i)₊ ⊆ {b_j : j > i}. Then every cell is a composite of atoms, by the following induction on a level s.
- Suppose the rows of x above s+1 are those of an atom ⟨a⟩ (or zero). Then row s+1 is ⟨a⟩_{s+1} + w with w ≥ 0, so the rows above s are those of ⟨a⟩ + Σ_{c ∈ w} ⟨c⟩ (Steiner Prop. 5.2).
- Peel off the least of these atoms in the basis order: x = y #ₛ z. The rows of y above s are those of that one atom, and the rows of z above s are those of the rest (Steiner Prop. 5.1 for two pieces; the order gives the disjointness it needs).
- At s = 0, unitality makes the cell an atom (Prop. 5.5).

Uniqueness in (N2) follows from this: two functors that agree on atoms agree on composites of atoms.

**Q1.** Does (N1) for merely loop-free bases (Def. 3.5) have an equally short proof? Optional; every instance we need is strongly loop-free.

**Q2.** The existence half of (N2) is the main question. Given a strict ω-category C and an assignment φ of atoms as in the statement, define Φ(x) by the peel decomposition above, peeling the least atom first. Then show:
- Φ(x) does not depend on the level used;
- Φ(y #ₖ z) = Φ(y) #ₖ Φ(z) for arbitrary composable cells y, z, not only those produced by peeling;
- Φ commutes with boundaries.

The difficulty is that the decomposition of y #ₖ z is unrelated to the decompositions of y and z. An argument by induction on explicit data is wanted, for example a lemma showing that peeling the least atom commutes with composition up to interchange. Alternatively, give a short proof of Steiner's Thm 5.7 for this case.

**Q3.** Could existence instead come from a presentation? For example: show that ν(K) is isomorphic to the strict ω-category freely generated by the atoms, with the boundary relations, using generation (N1) and a normal form computed from tables.

**Q4.** If (N2) in general has no short proof, the special cases needed are:
- (Q4a) K = λΓ for a finite loop-free globular set Γ. Here atoms are the generators, and (N2) says ν(λΓ) is the free strict ω-category on Γ.
- (Q4b) K = λΓ ⊗ λD¹ (the Gray cylinder), and the quotient of ν(K) that collapses each end Γ ⊗ {0}, Γ ⊗ {1} to a point is ν of the quotient complex.

## Why it matters

Freeness of ν(K) on its atoms is what lets computations made at the level of chain complexes (for example lax colimits, joins and Gray cylinders) be transferred to strict ω-categories, and it is the step that lets general results about strict ω-categories be applied to the models ν(K). A machine-checked version needs a proof by induction on explicit data. Chains there are finite multisets of basis elements over a decidable total order, so proofs by induction on lists, extremal elements and counting are the easiest to check.

## What would count as a solution

- An elementary proof of the existence half of (N2), written at the level of chains, with each step checkable.
- Or proofs of Q4a and Q4b.
- Or the shortest known route through the literature, with each lemma stated precisely.

## Literature status (2026-11-18)

- (N1), (N2): Steiner 2004, Thms 5.6, 5.7, 6.1, for loop-free unital bases. Thm 5.11 gives the equivalence with ω-categories with loop-free atomic bases. Prop. 7.2 and Thm 7.3 cover the tensor product.
- Ara–Maltsiniotis 1607.00668, App. A: the tensor on strict ω-categories extending Steiner's.
- Forest 2022 and Campbell 2605.09427: radicality and (F2) for Steiner complexes.
- No machine-checked proof of (N1) or (N2) was found.

# Researcher Response

**Yes. The useful intermediate result is a unique-lifting theorem.** Prove it by induction on the decomposition index, using finite-list sorting for the only rearrangement step. Then obtain the requested functor as the inverse of a projection. This proves all three compatibility properties in Q2 and works for merely loop-free bases.

The proof below is a chain-and-list formulation of Steiner’s argument. Its additional ingredient beyond generation is a local interchange lemma, proved explicitly in §4. The corresponding published results are Proposition 4.2, Propositions 5.8–5.9, Lemma 5.10, and Theorem 5.7. [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com)

## 1. Table notation and the explicit cut

Write \(A_b=\langle b\rangle\). Extend every table by zero rows above its dimension, and write
\[
x\equiv_r y
\]
when their rows in degrees **strictly greater than \(r\)** agree. Thus \(\equiv_{-1}\) is equality. The zero table is allowed in this notation, although it is not a cell of \(\nu K\).

Define
\[
\delta(x)=
\min\{r\ge -1:\ x\equiv_{r+1}0
\text{ or }x\equiv_{r+1}A_b\text{ for some }b\}.
\]

Two elementary facts will be used repeatedly.

### 1.1 Atom coefficients are determined by the higher rows

If two finite sums of atoms agree above degree \(r\), their coefficients on all atoms of dimension \(>r\) agree.

To prove this, subtract the sums and choose the greatest dimension \(d>r\) at which an atom has a nonzero coefficient. The degree-\(d\) row is then a nonzero linear combination of distinct elements of \(B_d\), a contradiction.

This is a descending induction on dimension. In particular, it determines the atom multiset associated with a decomposition at a fixed level.

### 1.2 An ordered atom list determines its factors

Suppose
\[
x\equiv_r A_1+\cdots+A_m,
\qquad |A_i|>r,
\]
and assume
\[
A_{i,r}^{+}\wedge A_{j,r}^{-}=0
\qquad(i>j).
\tag{1}
\]

Define chains
\[
h_0=x_r^-,
\qquad
h_i=h_{i-1}+A_{i,r}^{+}-A_{i,r}^{-}.
\tag{2}
\]

Define tables \(x_i\) by
\[
(x_i)_j^\alpha=
\begin{cases}
x_j^\alpha,&j<r,\\
h_{i-1},&j=r,\ \alpha=-,\\
h_i,&j=r,\ \alpha=+,\\
A_{i,j}^\alpha,&j>r.
\end{cases}
\tag{3}
\]

Then
\[
x=x_1\#_r\cdots\#_r x_m,
\qquad
x_i\equiv_r A_i.
\tag{4}
\]

Here is the positivity check, which is the only non-immediate part. For a cut after \(i\), put
\[
P^\alpha=\sum_{j\le i}A_{j,r}^\alpha,
\qquad
R^\alpha=\sum_{j>i}A_{j,r}^\alpha.
\]
The boundary equation gives
\[
h_i=x_r^-+P^+-P^-
    =x_r^++R^--R^+.
\]
If a coefficient of \(h_i\) were negative, that basis element would have positive coefficients in both \(P^-\) and \(R^+\). This contradicts (1). Hence \(h_i\ge0\).

The remaining table equations follow from
\[
h_i-h_{i-1}=A_{i,r}^+-A_{i,r}^-,
\qquad
\partial A_{i,r}^+=\partial A_{i,r}^-.
\]
For \(r=0\), augmentation is preserved because
\(\varepsilon A_{i,0}^-=\varepsilon A_{i,0}^+\).

Moreover, **whenever a decomposition (4) exists with the specified ordered list, its factors must have exactly the rows (3)**. Below \(r\), composition preserves the common rows; above \(r\), the factors are specified; at \(r\), their successive boundaries are forced by (2).

Thus we have both:

- existence for a list satisfying (1);
- uniqueness of factors for any specified ordered list.

These are the table formulas behind Steiner’s Propositions 5.1 and 5.8. [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com) [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com)

## 2. Q1: the same generation proof works with level-dependent orders

Let \(\delta(x)=r\ge0\). There are two cases.

If \(x\equiv_{r+1}0\), then
\[
x_{r+1}^-=x_{r+1}^+=w\ge0.
\]
Expand \(w\) in the basis. The associated \((r+1)\)-atoms give
\[
x\equiv_r A_1+\cdots+A_m.
\]

Otherwise, there is a unique atom \(A\) of dimension \(>r+1\) with
\[
x\equiv_{r+1}A.
\]
The chain equations imply
\[
x_{r+1}^- - A_{r+1}^-
=
x_{r+1}^+ - A_{r+1}^+
=w.
\tag{5}
\]
Since the two rows of \(x\) are nonnegative and
\[
A_{r+1}^-\wedge A_{r+1}^+=0,
\]
equation (5) forces \(w\ge0\), coefficient by coefficient. Expand \(w\) in the basis. The resulting list consists of \(A\), once, together with \((r+1)\)-atoms.

In both cases:

\[
x\equiv_r A_1+\cdots+A_m,
\qquad
m\ge2,
\tag{6}
\]
every listed atom has dimension \(>r\), and at most one has dimension \(>r+1\). The inequality \(m\ge2\) follows from the minimality of \(r\).

Choose a linear extension of the loop-free order \(\le_r\) on this finite list and sort the list. Its ordering satisfies (1), so §1.2 gives
\[
x=x_1\#_r\cdots\#_r x_m,
\qquad
\delta(x_i)\le r-1.
\tag{7}
\]

For the base case \(\delta(x)=-1\):

- If all positive-degree rows vanish, \(x_0^-=x_0^+\) is a nonnegative chain of augmentation \(1\), hence a single basis element.
- Otherwise, \(x\equiv_0 A\) for a positive-dimensional atom \(A\). As in (5),
  \[
  x_0^--A_0^-=x_0^+-A_0^+=w\ge0.
  \]
  Unitality gives \(\varepsilon w=0\). Every degree-zero basis element has augmentation \(1\), so \(w=0\) and \(x=A\).

Induction on \(\delta(x)+1\) proves N1.

**Strong loop-freeness is unnecessary here.** It merely permits the same basis order at every level. Ordinary loop-freeness supplies the order needed for each individual cut. This is the decomposition-index argument of Steiner’s Propositions 5.2–5.5, with its chain calculations made explicit. [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com)

For finite, effectively presented bases, the construction uses finite-chain arithmetic and finite sorting. No well-foundedness of the basis order is required.

## 3. The finite-expression lemma needed for existence

We now prove the following intermediate theorem.

> **Unique-lifting theorem.**  
> Let \(P\) be a strict \(\omega\)-category composition-generated, dimension by dimension, by generators \(e_b\). Suppose
> \[
> \theta:P\longrightarrow\nu K
> \]
> is a strict functor satisfying
> \[
> \theta(e_b)=A_b,
> \]
> with the generators indexed bijectively by the basis and with dimensions preserved. Then every table \(x\in\nu K\) has exactly one inverse image under \(\theta\).

“Composition-generated, dimension by dimension” means that every cell of dimension at most \(n\) has an expression using only compositions and generators of dimension at most \(n\).

The proof needs a normalization lemma about finite expressions.

### 3.1 Standardization lemma

Every composition expression equals either a generator or an expression
\[
\xi=\xi_1\#_r\cdots\#_r\xi_m,
\qquad m\ge2,
\tag{8}
\]
such that:

1. each \(\xi_i\) has a composition expression with exactly one generator of dimension \(>r\);
2. across these expressions, at most one generator has dimension \(>r+1\).

Here is the structural induction.

Suppose the expression is \(Y\#_k Z\), and first standardize its two children.

If the chosen expression for \(Y\) uses only generators of dimension \(\le k\), then \(Y\) is a unit for this composition, so \(Y\#_k Z=Z\). Treat \(Z\) similarly.

Otherwise, both expressions have a generator of dimension \(>k\). Set
\[
r=(\text{second-largest generator degree in the two expressions})-1.
\]
Then \(r\ge k\).

For either child:

- if it has no generator of degree \(>r\), it is an \(r\)-cell;
- if it has exactly one, use the whole child as one factor;
- if it has at least two, its existing standardization has cut exactly \(r\).

For the last assertion, if its existing cut is \(s\), its second-largest generator degree is \(s+1\). The definition of \(r\), together with the presence of two degrees \(>r\), forces \(s=r\).

Write the resulting lists as \(Y_1,\ldots,Y_p\) and \(Z_1,\ldots,Z_q\). If \(k=r\), concatenate them. If \(k<r\), units and interchange give
\[
\begin{aligned}
Y\#_k Z
={}&
(Y_1\#_k d_r^-Z)\#_r\cdots\#_r
(Y_p\#_k d_r^-Z)\\
&\#_r
(d_r^+Y\#_k Z_1)\#_r\cdots\#_r
(d_r^+Y\#_k Z_q).
\end{aligned}
\tag{9}
\]
An empty group is omitted. When a child has no high generator, it equals its own \(r\)-boundaries, so the same formula applies.

Express the boundary cells in (9) using generators of dimension \(\le r\). They introduce no additional generator of dimension \(>r\). This proves the lemma.

This is the finite-expression content of Steiner’s Proposition 4.2. [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com)

### 3.2 What standardization implies about its image

If an expression has exactly one generator \(e_b\) of dimension \(>r\), then
\[
\theta(\text{expression})\equiv_r A_b.
\tag{10}
\]

Prove (10) structurally. At a composition indexed by \(k\), the child without \(e_b\) has dimension \(\le r\).

- For \(k\le r\), its image and the common \(k\)-boundary vanish above \(r\).
- For \(k>r\), that child is a unit, so the composite equals the other child.

Consequently, the image of a standardization (8) satisfies
\[
\theta(\xi)\equiv_r A_{b_1}+\cdots+A_{b_m}.
\tag{11}
\]
Above degree \(r+1\), at most one atom remains. Thus
\[
\delta(\theta\xi)\le r.
\]
But \(\delta(\theta\xi)<r\) would make (11) congruent above \(r\) to zero or one atom, contradicting §1.1 and \(m\ge2\). Therefore
\[
\boxed{\delta(\theta\xi)=r.}
\tag{12}
\]

This identifies the cut of every standardized inverse image directly from its table.

## 4. The local swap lemma

Assume that every table of decomposition index \(<r\) has a unique inverse image under \(\theta\).

Suppose
\[
\xi=\eta\#_r\zeta,
\qquad
\theta\eta\equiv_r A,
\qquad
\theta\zeta\equiv_r B,
\tag{13}
\]
where \(|A|,|B|>r\), and assume
\[
A_r^+\wedge B_r^-=0.
\tag{14}
\]

We will show that the same \(\xi\) has an \(r\)-decomposition with atom labels \(B,A\).

### 4.1 The chain calculation produces a lower cut

Put
\[
x=\theta\xi,
\qquad
h=(\theta\eta)_r^+=(\theta\zeta)_r^-,
\qquad
w=h-A_r^+-B_r^-.
\]
The table equations give
\[
x_r^-=A_r^-+B_r^-+w,
\qquad
x_r^+=A_r^++B_r^++w.
\tag{15}
\]

We claim \(w\ge0\).

Suppose its coefficient at some basis element were negative. Since
\[
h=A_r^++B_r^-+w\ge0,
\]
that basis element has a positive coefficient in \(A_r^+\) or \(B_r^-\).

If it has a positive coefficient in \(A_r^+\), disjointness
\[
A_r^-\wedge A_r^+=0,
\qquad
A_r^+\wedge B_r^-=0
\]
makes its coefficient in the first chain of (15) negative.

If it has a positive coefficient in \(B_r^-\), disjointness
\[
B_r^-\wedge B_r^+=0,
\qquad
A_r^+\wedge B_r^-=0
\]
makes its coefficient in the second chain negative.

Both are impossible. Hence \(w\ge0\).

If \(r=0\), augmentation of the first equation in (15) gives
\[
1=1+1+\varepsilon w,
\]
which is impossible. Thus \(r>0\).

Expand \(w=\sum_j c_j\) in \(B_r\). Then
\[
x\equiv_{r-1}
A+B+\sum_j A_{c_j}.
\tag{16}
\]
Sort this finite list using a linear extension of \(\le_{r-1}\), apply the cut formula, and group at a position between the distinguished \(A\)-factor and \(B\)-factor. This gives either
\[
x=u\#_{r-1}v
\quad\text{or}\quad
x=v\#_{r-1}u,
\tag{17}
\]
with
\[
u\equiv_r A,
\qquad
v\equiv_r B.
\]
In particular,
\[
\delta(u),\delta(v)<r.
\]

### 4.2 Lift the lower cut and apply interchange

Treat the first order in (17); the other is the same calculation with the factors reversed.

Let \(U,V\) be the unique inverse images of \(u,v\). Their common \((r-1)\)-boundary has dimension at most \(r-1\), hence decomposition index \(<r\). Uniqueness at that lower index proves that \(U\#_{r-1}V\) is defined.

Put \(q=r-1\). Units and interchange give
\[
\begin{aligned}
U\#_q V
&=(U\#_q d_r^-V)\#_r(d_r^+U\#_q V)\\
&=(d_r^-U\#_q V)\#_r(U\#_q d_r^+V).
\end{aligned}
\tag{18}
\]

The first line has atom labels \(A,B\) above \(r\). Its image is \(x\). By the fixed-list uniqueness of §1.2, its two factor images equal \(\theta\eta,\theta\zeta\). These individual images have index \(<r\), so the induction hypothesis identifies the factors themselves with \(\eta,\zeta\).

Therefore the second line of (18) is a decomposition of the original \(\xi\), with labels \(B,A\).

**Uniqueness at index \(r\) has not been used.** Every use of uniqueness concerned an individual factor or a lower-dimensional boundary.

This proves the local step in Steiner’s Proposition 5.9 and Lemma 5.10. [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com)

## 5. Prove unique lifting by two integer measures

Induct on
\[
\delta(x)+1\in\mathbb N.
\]

### Base case

If \(\delta(x)=-1\), §2 says \(x=A_b\). Its designated generator \(e_b\) is an inverse image.

Any other inverse image can be standardized. A nontrivial standardization would have image of nonnegative decomposition index by (12). Therefore every inverse image equals a generator, and the bijection on generators makes it equal to \(e_b\).

### Existence at index \(r\ge0\)

Use the sorted cut
\[
x=x_1\#_r\cdots\#_r x_m
\]
from §2. Each factor has a unique inverse image \(\xi_i\).

The common boundary
\[
d_r^+x_i=d_r^-x_{i+1}
\]
has dimension at most \(r\), hence decomposition index at most \(r-1\). Its inverse image is unique, so
\[
d_r^+\xi_i=d_r^-\xi_{i+1}.
\]
Thus
\[
\xi_1\#_r\cdots\#_r\xi_m
\]
is an inverse image of \(x\).

### Uniqueness at index \(r\)

Take any inverse image \(\xi\). Standardize it. Equation (12) forces its cut to be \(r\), and §1.1 forces its atom-label multiset to equal that of the chosen sorted cut of \(x\).

Sort its label list toward the chosen linear extension of \(\le_r\).

For adjacent inverted labels \(a,b\), a nonzero intersection
\[
A_{a,r}^+\wedge A_{b,r}^-
\]
would imply \(a<_r b\), contradicting their inversion. Hence the local swap lemma applies.

Each adjacent swap decreases the ordinary inversion count by one. At \(r=0\), the positivity argument in §4 shows that an inverted adjacent pair cannot exist.

After sorting, fixed-list uniqueness identifies the factor images with the chosen \(x_i\). Lower-index uniqueness then identifies the factors themselves with \(\xi_i\). Hence the inverse image of \(x\) is unique.

This proves the unique-lifting theorem.

The recursive measures are explicit:

| Argument | Measure |
|---|---|
| Standardizing an expression | Structural induction on its finite expression tree |
| Constructing and identifying inverse images | \(\delta(x)+1\) |
| Rearranging a list at fixed index | Its finite inversion count |

The lower cut in §4 uses the explicit formula (3); it does not start a second uncontrolled decomposition argument.

## 6. Q2: construct the extension as a graph

First make the boundary data concrete. Using N1, choose expressions \(W_b^\pm\) in lower-dimensional atoms for
\[
d_{|b|-1}^\pm A_b.
\]
Your inductive compatibility condition says that these expressions evaluate in \(C\) and satisfy
\[
d_{|b|-1}^\pm\varphi(b)=W_b^\pm(\varphi).
\tag{19}
\]
This condition can be supplied dimension by dimension exactly as in N2.

In \(\nu K\times C\), let \(P\) be the closure under compositions of the pairs
\[
e_b=(A_b,\varphi(b)).
\]

Equation (19), followed by induction on generator dimension, expresses every boundary of \(e_b\) as a composite of generator pairs of the appropriate dimensions. The strict boundary laws then show that \(P\) is closed under boundaries.

They also establish dimensionwise composition-generation: if \(\xi\in P\) has dimension at most \(n\), apply \(d_n^-\) to any expression for \(\xi\), push it through the compositions, and replace generator boundaries by their lower-dimensional expressions.

The first projection
\[
\theta:P\longrightarrow\nu K
\]
therefore satisfies the unique-lifting theorem. Define
\[
\boxed{\Phi=\operatorname{pr}_C\circ\theta^{-1}.}
\tag{20}
\]

A bijective strict functor has a strict inverse. Explicitly, injectivity gives
\[
d_j^\alpha\theta^{-1}(x)=\theta^{-1}(d_j^\alpha x).
\]
For composable \(y,z\), it first gives
\[
d_k^+\theta^{-1}(y)=d_k^-\theta^{-1}(z),
\]
and then
\[
\theta^{-1}(y\#_k z)
=
\theta^{-1}(y)\#_k\theta^{-1}(z).
\]

Applying the second projection proves all the requested properties:
\[
\boxed{
\Phi(d_j^\alpha x)=d_j^\alpha\Phi(x),
\qquad
\Phi(y\#_k z)=\Phi(y)\#_k\Phi(z).
}
\tag{21}
\]

Every atom expression for \(x\), including any terminating legal peel decomposition, evaluates to the second coordinate of the unique pair over \(x\). Thus evaluation is independent of the peeling level, admissible ordering, and bracketing.

For the specified binary “peel the least atom” implementation, use the lexicographic measure
\[
\bigl(\delta(x)+1,\ \text{length of the current atom list}\bigr).
\]
The peeled factor has lower index. The remaining factor either has lower index or has the same index with a shorter list.

This also explains why the projection construction is useful: arbitrary boundaries need not lower the decomposition index. Their compatibility follows from the inverse functor after unique lifting has been proved.

## 7. Q3: the presentation route works as well

Let \(F\) be the strict \(\omega\)-category generated by dimensioned generators \(e_b\), with immediate boundaries prescribed by the chosen words \(W_b^\pm\).

Construct it dimension by dimension. At each stage, the already established lower-dimensional isomorphism ensures that the two attaching cells are parallel.

There is a canonical functor
\[
F\longrightarrow\nu K,
\qquad
e_b\longmapsto A_b.
\]
The boundary equations make \(F\) composition-generated dimension by dimension. Hence the unique-lifting theorem proves
\[
\boxed{F\cong\nu K.}
\]

The table-based normal form is precisely the recursive sorted decomposition of §2. Sections 3–5 prove that every expression equals that normal form. This supplies the injectivity step needed beyond N1.

This is the presentation conclusion of Steiner’s Theorem 6.1. [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com)

## 8. Q4a and Q4b

### Q4a: globular generators

For \(A=\lambda\Gamma\), under the stated loop-free unital hypothesis, the immediate boundaries of the atom indexed by \(b\in\Gamma_n\) are
\[
d_{n-1}^-A_b=A_{sb},
\qquad
d_{n-1}^+A_b=A_{tb}.
\]
Thus the presentation in §7 is exactly the free strict \(\omega\)-category presentation on the globular set \(\Gamma\). Therefore
\[
\boxed{\nu(\lambda\Gamma)\cong F_{\mathrm{str}}(\Gamma).}
\]

### Q4b: collapse the two ends to separate points

Write \(I=\lambda D^1\), with basis
\[
e_-,e_+\in I_0,
\qquad
u\in I_1,
\qquad
\partial u=e_+-e_-.
\]

Define endpoint collapse as the augmented-directed-complex pushout
\[
Q=(A\otimes I)
\amalg_{A\oplus A}
\bigl(\mathbb Z[p_-]\oplus\mathbb Z[p_+]\bigr),
\tag{22}
\]
where the maps from the two copies of \(A\) to their points are their augmentations.

Explicitly,
\[
Q_0=\mathbb Z\{p_-,p_+\},
\qquad
Q_{n+1}\cong A_n.
\]
Write \(\sigma a\) for the shifted copy of \(a\). Then
\[
\partial(\sigma a)=
\begin{cases}
\varepsilon(a)(p_+-p_-),&a\in A_0,\\
\sigma(\partial a),&|a|>0.
\end{cases}
\tag{23}
\]
This is the directed suspension \(\Sigma A\).

Its atoms have rows
\[
(A_{\sigma a})_0^\alpha=p_\alpha,
\qquad
(A_{\sigma a})_j^\alpha
=
\sigma(A_a)_{j-1}^\alpha
\quad(j\ge1).
\tag{24}
\]
They are unital. Loop-freeness at level \(j\ge1\) is inherited from level \(j-1\) of \(A\). At level zero, the dependency relation is empty: every positive-dimensional atom has source \(p_-\) and target \(p_+\), and these are distinct.

It remains to verify what the quotient map \(q:A\otimes I\to Q\) does to atoms.

The tensor atom formula specializes to
\[
(A_{a\otimes u})_0^\alpha
=
(A_a)_0^\alpha\otimes e_\alpha,
\]
and, for \(j\ge1\),
\[
(A_{a\otimes u})_j^\alpha
=
(A_a)_{j-1}^\alpha\otimes u
+
(A_a)_j^\alpha\otimes e_{(-1)^j\alpha}.
\tag{25}
\]
Rows beyond the dimension of \(A_a\) are zero. The sign \((-1)^j\alpha\) means that the endpoint is switched when \(j\) is odd. This is Steiner’s tensor-atom calculation in Example 3.10; the same example gives the strongly loop-free unital tensor basis. [arxiv.org](https://arxiv.org/html/math/0403237v2?utm_source=chatgpt.com)

The map \(q\) kills positive-dimensional endpoint chains and sends
\[
a\otimes e_\alpha\longmapsto\varepsilon(a)p_\alpha
\quad(a\in A_0),
\qquad
a\otimes u\longmapsto\sigma a.
\]
Applying it to (25), and using unitality at degree zero, gives the exact equality
\[
\boxed{(\nu q)(A_{a\otimes u})=A_{\sigma a}.}
\tag{26}
\]
Every endpoint atom \(A_{a\otimes e_\alpha}\) maps to the identity at \(p_\alpha\).

Now form the categorical endpoint-collapse pushout
\[
R=
\nu(A\otimes I)
\amalg_{\nu A\amalg\nu A}
(D^0\amalg D^0).
\tag{27}
\]
The functor \(\nu q\) induces
\[
\pi:R\longrightarrow\nu Q.
\]

The two designated points and the images of the mixed atoms \(A_{a\otimes u}\) composition-generate \(R\). The inherited atomic boundary expressions make this generation dimensionwise. By (26), \(\pi\) sends these generators bijectively to the atoms of \(Q\). Their dimensions are preserved: their images in \(\nu Q\) have the original dimensions, so they cannot have become lower-dimensional in \(R\).

Apply the unique-lifting theorem once more:
\[
\boxed{
R\cong\nu Q=\nu(\Sigma A).
}
\tag{28}
\]

Thus the cylinder quotient follows from the same elementary theorem. The argument establishes this particular pushout calculation without requiring a general colimit-preservation property of \(\nu\). For empty \(\Gamma\), definitions (22) and (27) explicitly add the two designated points; for nonempty \(\Gamma\), they are the stated separate collapses of the two ends.

# Verification of the researcher response (2026-11-18)

**Verdict: correct.** Every step was checked at the level of chains. The response proves the existence half of (N2) for merely loop-free unital bases, answers Q1 (generation without strong loop-freeness), Q3 (ν(K) is the polygraph on its atoms) and Q4a, and proves Q4b for any A whose tensor A ⊗ λD¹ has a loop-free unital basis (true for strongly loop-free unital A, in particular λΓ for a loop-free globular Γ). The argument is Steiner's (Props. 4.2, 5.1–5.5, 5.8–5.10, Thms 5.6, 5.7, 6.1), reorganised around one theorem with three explicit measures, which is what the formalisation needs.

**Structure (the order to formalise it in).**
1. *Cut formula and fixed-list uniqueness (§1.2).* For x ≡_r A_1 + ⋯ + A_m with A_{i,r}⁺ ∧ A_{j,r}⁻ = 0 for i > j, the tables (3) are cells and x = x_1 #_r ⋯ #_r x_m; conversely any decomposition with that ordered label list has exactly these factors. Checked: a negative coefficient of h_i at b needs b in P⁻ (some j ≤ i) and in R⁺ (some i′ > i), contradicting (1); the row-r and augmentation equations follow from ∂A_{i,r}⁺ = ∂A_{i,r}⁻. Fixed-list uniqueness holds because rows below r are common, rows above r are prescribed, and row r is forced by (2). This is the existing cut lemma plus its converse.
2. *Atom coefficients are determined above r (§1.1).* Take the largest dimension d > r with a nonzero coefficient difference; the degree-d row is a nonzero combination of distinct basis elements. Correct.
3. *(N1) for loop-free bases (§2).* With r = δ(x) ≥ 0: either x ≡_{r+1} 0, or x ≡_{r+1} A for a unique atom of dimension > r+1, and then x_{r+1}^± − A_{r+1}^± = w ≥ 0 coefficientwise because A_{r+1}⁻ ∧ A_{r+1}⁺ = 0 (atoms are cells, so their rows below the top are the negative and positive parts of one chain). Repeated labels are harmless (an atom's own rows are disjoint, and <_r is irreflexive). m ≥ 2 follows from minimality of r. Sorting by a linear extension of <_r gives (1). Base case: unitality and ε = 1 on degree-0 basis elements force x to be an atom. Correct; strong loop-freeness is indeed not needed.
4. *Standardisation of expressions (§3.1).* By structural induction every expression is a generator or ξ_1 #_r ⋯ #_r ξ_m (m ≥ 2), each factor with exactly one generator of dimension > r and at most one of dimension > r+1 overall, where r + 1 is the second-largest generator degree. Checked: r ≥ k because both children have a generator above k; a child with two generators above r has existing cut s with s + 1 equal to its second-largest degree, which is squeezed to r; the redistribution (9) is the interchange law (Y_1 #_r Y′) #_k Z = (Y_1 #_k d_r⁻Z) #_r (Y′ #_k Z) for k < r, and the inserted boundaries use generators of dimension ≤ r (dimensionwise generation).
5. *Image of a standardisation (§3.2).* θ(ξ) ≡_r ΣA_{b_i}, hence δ(θξ) ≤ r, and δ < r is excluded by item 2 and m ≥ 2. So the cut of any standardised inverse image is δ(x), read off the table. Correct.
6. *Swap lemma (§4).* For η #_r ζ with labels A, B and A_r⁺ ∧ B_r⁻ = 0: w = h − A_r⁺ − B_r⁻ ≥ 0 (checked both cases of a negative coefficient), r = 0 is impossible by augmentation (1 = 2 + εw), and x ≡_{r−1} A + B + Σ A_{c_j} gives a lower cut u #_{r−1} v (or v #_{r−1} u) with u ≡_r A, v ≡_r B by grouping the sorted factors. Lifting u, v uniquely (index < r), the two interchange forms (18) of U #_{r−1} V have label lists (A, B) and (B, A); fixed-list uniqueness plus uniqueness below index r identifies the first with η #_r ζ. Uniqueness at index r is not used. Correct.
7. *Unique lifting (§5).* Strong induction on δ(x) + 1, with an inner induction on inversion count. Existence: lift the sorted cut factorwise; the common boundaries have index ≤ r − 1 so their lifts agree. Uniqueness: standardise, the cut is r (item 5), the label multiset is fixed (item 2), adjacent inversions are never <_r-related, so the swap lemma applies; at r = 0 no inversion can occur. Base case: a nontrivial standardisation would have index ≥ 0, so every lift of A_b is a generator e_c, and c = b. Correct.
8. *Existence of Φ (§6).* P ⊆ ν(K) × C generated by the pairs (A_b, φ(b)), with the boundary condition (19) supplied by induction on dimension (Φ on lower cells is pr_C ∘ θ⁻¹ restricted, and Φ(d⟨b⟩) is the evaluation of any atom expression W_b^± for d⟨b⟩). θ = pr_1 is bijective by item 7, so Φ = pr_C ∘ θ⁻¹ is a strict functor with Φ⟨b⟩ = φ(b), commuting with boundaries and all compositions. Uniqueness is the existing argument from (N1). Correct. This answers all three bullets of Q2 at once and makes the "peel the least atom" evaluation a corollary (measure (δ + 1, list length)).
9. *Q3 (§7).* The polygraph F on generators e_b with attaching words W_b^± is built dimension by dimension; it is generated dimensionwise and maps generators to atoms, so item 7 gives F ≅ ν(K) (Steiner Thm 6.1). Correct.
10. *Q4a.* In λΓ, ⟨b⟩'s lower rows are those of A_{sb} and A_{tb}, so the presentation of item 9 is the free strict ω-category on Γ. Correct, given the prompt's hypotheses on Γ.
11. *Q4b.* The quotient complex Q of λΓ ⊗ λD¹ collapsing both ends is the directed suspension Σ(λΓ): Q_0 = {p₋, p₊}, Q_{n+1} = A_n, ∂(σa) = ε(a)(p₊ − p₋) or σ(∂a). Its basis is unital and loop-free (levels j ≥ 1 shift from A; level 0 is empty because p₋ ≠ p₊). From the tensor atom formula (25) (only the endpoint terms depend on the sign convention, and they are killed), νq(⟨a ⊗ u⟩) = ⟨σa⟩ exactly, and endpoint atoms go to identities. The categorical end-collapse pushout R is generated dimensionwise by the two points and the images of the mixed atoms (this uses (N1) for ν(λΓ ⊗ λD¹), whose basis is strongly loop-free and unital), their dimensions are preserved because their images in ν(Q) have the original dimensions, and item 7 gives R ≅ ν(Q). Correct.

**What it means for A5.** The existence half of (N2) now has a proof by induction on explicit data: structural induction on expression trees (item 4), strong induction on the decomposition index δ (computable from the table: compare with 0 and with each atom above a level), and inversion count on finite lists (item 7). It also removes the need for an ordered (strongly loop-free) basis in (N1), and gives (N3)'s ν(λΓ) = Free(Γ) and the Gray-cylinder collapse as corollaries of the same theorem. A formalisation needs a representation of P (or of the polygraph F) with an expression type for item 4; the graph construction of item 8 avoids proving well-definedness of Φ directly.

Follow-up: no new outside prompt. The formalisation is handed to the A5 owner.
