# Directed pasting types for Gray-closed structure: which 2-cells between planar proofs?

*A self-contained problem. No knowledge of the project that posed it is assumed. The smallest open case is Question 1.*

## Background

**Unbiased type theories from contractible types.** Mimram (*An unbiased simply typed combinatory logic*, CSL 2026) presents cartesian closed categories without λ-abstraction or application as primitives. Instead:
- a decidable class of **pasting types** is singled out, each having exactly one inhabitant up to βη;
- for every pasting type there is a constant coh_A : A;
- any two terms of a pasting type are equal.

All combinators and all βη-equations arise this way. The style comes from the type theory CaTT for weak ω-categories (Finster–Mimram, LICS 2017). There, "pasting contexts" are contractible, and the coherence rule produces *cells* (not equations) between parallel composites. The hope is that pasting-type theories have higher-dimensional versions in which the equality rule becomes a rule producing higher cells.

**The planar (non-symmetric) 1-dimensional case is settled.** Take formulas built from atoms with ⊗ and the two residuals B\A ("a B on the left gives A") and A/B, with no unit. Sequents Γ ⊢ C have nonempty ordered Γ.
- A sequent is **balanced** if each atom occurs exactly twice, with opposite polarities.
- **Theorem (coherence).** In the free unit-free biclosed monoidal category on the atoms, a balanced sequent has at most one morphism, and exactly one when it is provable in the Lambek calculus with product.
  - This is a non-symmetric analogue of Kelly–Mac Lane, *Coherence in closed categories* (JPAA 1, 1971).
  - Proof idea: factorization lemmas for cut-free derivations, plus connectivity of the axiom-link graph.
- **Consequence:** the theory with coh over balanced provable sequents, closed under type substitution, presents the free biclosed monoidal category.

**The higher target: Gray tensor products.** The lax Gray tensor product ⊗ on (∞,ω)-categories is monoidal biclosed and not symmetric (Campion, arXiv 2311.00205):

```
Map(A ⊗ B, C)  ≃  Map(A, Fun^lax(B, C))     (mapping spaces).
```

The equivalence does **not** hold for mapping (∞,ω)-categories: Gagna–Harpaz–Lanari, arXiv 2006.14495, Rem. 2.20. In the strict setting, the Gray tensor of two arrows D¹ ⊗ D¹ is a square with one non-invertible 2-cell:

```
(f ⊗ b′) ∘ (a ⊗ g)   ⇒   (a′ ⊗ g) ∘ (f ⊗ b)          for f : a → a′, g : b → b′,
```

that is, "right factor first" ⇒ "left factor first" (one of the two conventions). In a Gray-monoidal (biclosed) 2-category, the composites of whiskered 1-cells applied to independent tensor factors are therefore related by **directed** interchange cells, not isomorphisms.

**Why the obvious higher criterion fails.** The proof assistant cccatt implements a directed higher criterion for Mimram's theories (source: github.com/smimram/cccatt, `src/pasting.ml`, commit 69bb11af). For a 2-dimensional goal t → u over a context with no 2-dimensional hypotheses, it accepts every pair of parallel terms of a pasting 1-type. For f, g as above, this accepts both interchange directions, so it presents the *pseudo* (invertible-interchange) structure, not the Gray one.

## Setting for the questions

**Signature.** Fix a set of generating 1-cells fᵢ : Pᵢ → Qᵢ between formulas (in ⊗, \, /, no unit), each to be used exactly once. A **1-term** is a planar multimorphism Γ → C in the free biclosed monoidal category on the atoms and these generators. It is built from:
- structural maps, which are coh's of balanced provable sequents, closed under type substitution;
- the generators.

**Event order.** A 1-term t applies the generators in some order σ(t), its event order. Between consecutive events the structural part is unique, by the coherence theorem.

Two events are **independent** if neither's output is (transitively) an input of the other. Independent events occupy disjoint wire intervals, so planarity gives them a left/right position.

**Subtlety: closures.** When a generator is applied inside a curried argument (a closure passed to a residual hypothesis, or a residual goal), use the following normal form. Curry is strictly natural in the context: Λ(f) ∘ h = Λ(f ∘ (X ⊗ h)). So push every event on a captured wire *inside* the closure. Then treat each closure containing events as one compound event at the outer level, with its own internal event order. This gives a **nested event order**.

**Inversions.** inv(t) is the set of independent pairs (e left of e′, at the same nesting level) with e′ applied before e, collected over all levels.

**Candidate criterion G.** A 2-cell t ⇒ u between 1-terms of the same balanced sequent (and the same generators) is a coherence iff
- the nesting structure agrees; and
- inv(u) ⊆ inv(t).

**What is known about G:**
- It yields the lax naturality cell of evaluation and not its inverse. Take φ : P → C/B and b : X → B. Then t₁ = ev∘(φ⊗B)∘(P⊗b) (b first) and t₂ = ev∘(C/B⊗b)∘(φ⊗X) (φ first). Here inv(t₁) = {(φ, b)} and inv(t₂) = ∅, so G gives t₁ ⇒ t₂ only.
- t ⇒ u and u ⇒ t are both accepted iff σ(t) = σ(u), in which case the cell is invertible.
- For a single nesting level, the event orders are the linear extensions of a 2-dimensional poset: dependency, plus left/right. Inversion-set containment is reachability by oriented adjacent swaps. Those linear extensions form an interval of the weak Bruhat order (Björner–Wachs, *Permutation statistics and linear extensions of posets*, JCTA 58, 1991).

## Questions

1. **(Smallest open case: soundness and completeness in dimension 2, one nesting level.)** Let 𝒢 be the free Gray-monoidal biclosed strict 2-category on a set of objects and a set of generating 1-cells. Interchangers are non-invertible 2-cells, and the closed structure is an isomorphism of hom-categories, strictly natural. Is it true that:
   - for 1-cells t, u with the same source, target and generators, and no closures containing events, there is a 2-cell t ⇒ u in 𝒢 iff inv(u) ⊆ inv(t); and
   - such a 2-cell is then unique?
   Equivalently: is each hom-category of 𝒢 between such 1-cells the weak-Bruhat interval described above?
2. **(Closures.)** Is the nested event order an invariant of 1-cells of 𝒢? Does Question 1's statement hold level by level? In particular, is there an interchanger between an outer event and a compound (closure) event, and is it the only 2-cell relating orders across levels?
3. **(ω-version.)** For n fully independent events, conjecture that the k-cells between event orders are the cells of the hom ω-category of the strict Gray cube ν(D¹ ⊗ … ⊗ D¹) (Steiner complexes) between its bottom and top vertices. Its 1-dimensional part is the weak Bruhat order on Sₙ, and the higher Bruhat orders of Manin–Schechtman (see also Kapranov–Voevodsky, Ziegler) should appear in higher dimensions. Is this right? What is the general (dependent, planar, nested) version?
4. **(Comparison.)** Gepner–Heine (*Oriented category theory*, arXiv 2510.10504, Cor. 4.1.11) describe the morphism object of an oriented category as the presheaf (S, T) ↦ Map(S ⊠ X ⊠ T, Y), recording whether time sits on the left or right. Does criterion G (or its ω-version) present the free bioriented / Gray-closed structure in their sense?

## What counts as a solution

Any of:
- a proof or counterexample for Question 1;
- a precise invariant answering Question 2;
- a statement and proof (or a reference) for Question 3;
- a reference showing that hom-categories of free Gray monoids (or Gray-closed 2-categories) on 1-generators are weak-order intervals.

## Literature (searched 2026-11-18)

- **Pasting types:** Mimram (CSL 2026) for cartesian closed. No published linear, planar or Gray version was found. Mimram lists closed, linear and planar variants as future work.
- **Coherence for Gray monoids and Gray categories:**
  - Gordon–Power–Street, *Coherence for tricategories* (Mem. AMS 1995), where interchangers are invertible;
  - Forest–Mimram, *Coherence of Gray categories via rewriting* (FSCD 2018);
  - Bourke–Lobbia on skew closed structures for lax and pseudo transformations (arXiv 2212.12358).
  None treats the closed (residuated) case with directed interchange.
- **Weak order on linear extensions:** Björner–Wachs (1991); Manin–Schechtman, *Arrangements of hyperplanes, higher braid groups and higher Bruhat orders* (1989); Kapranov–Voevodsky, *Combinatorial-geometric aspects of polycategory theory* (1991).

# Researcher Response

**Question 1 is false as stated.** The inversion set forgets the dependency relation itself. There is a counterexample with two generators on one atomic wire, satisfying the balanced-boundary condition and using no closures.

There are also two separate corrections:

- The proposed inward-pushing rule does not by itself make closure nesting invariant under the closed equations.
- The fully independent \(\omega\)-case has a precise published description, but the cube’s hom \(\omega\)-category is not thin. Weak order describes reachability between its objects.

## 1. Counterexample to Question 1

Take one atom \(A\) and two generating 1-cells
\[
f,g:A\longrightarrow A.
\]
Consider
\[
t=g\circ f,\qquad u=f\circ g.
\]

These satisfy the stated hypotheses:

- The common sequent \(A\vdash A\) is balanced.
- Each generator is used exactly once.
- Neither expression uses a closure.
- The structural maps needed are identities.

Their event data are:

| Term | Event order | Dependency relation | Inversion set |
|---|---|---|---|
| \(t=g\circ f\) | \(f,g\) | \(f\prec g\) | \(\varnothing\) |
| \(u=f\circ g\) | \(g,f\) | \(g\prec f\) | \(\varnothing\) |

In each term, the first event’s output is the second event’s input. Thus the two events are dependent, and neither inversion set records their order. Criterion G accepts both directions.

### Neither 2-cell exists

Interpret the signature in a locally discrete biclosed 2-category: an ordinary biclosed category regarded as a 2-category whose only 2-cells are identities. Assign
\[
A=\{0,1\},\qquad f(x)=1-x,\qquad g(x)=0.
\]
Then
\[
\llbracket t\rrbracket(x)=0,
\qquad
\llbracket u\rrbracket(x)=1.
\]
These are distinct functions, so there is no 2-cell between them in either direction. By freeness, a 2-cell between \(t\) and \(u\) would have to map to such a 2-cell. Therefore
\[
\mathcal G(t,u)=\varnothing
\qquad\text{and}\qquad
\mathcal G(u,t)=\varnothing.
\]

Literal strictness can be accommodated without invoking strictification. Use the category with objects \(n\in\mathbb N\), arrows all functions
\[
\{0,1\}^{m}\longrightarrow\{0,1\}^{n},
\]
and tensor \(m\otimes n=m+n\), implemented by tuple concatenation. Its residual objects are
\[
m\backslash n=n\,2^m,
\qquad
n/m=n\,2^m,
\]
with evaluation and currying defined by a fixed truth-table enumeration. This is strictly monoidal and biclosed; make its hom-categories discrete. The separating functions above are endomorphisms of object \(1\).

Interchangers map to identities in this model. That is permitted: a free directed presentation does not require every interpretation to preserve the *absence* of an inverse.

Thus **a common boundary and common generator list do not determine a common dependency diagram**. This also refutes the preliminary assertion that mutual acceptance by G forces equal event orders.

## 2. A corrected one-level theorem

There is a precise positive theorem once the dependency data are fixed. It is a theorem about schedules and their interchange relations; identifying it with a fragment of a free biclosed completion requires an additional comparison theorem.

Fix a finite poset \(P\) on labels \(\{1,\ldots,n\}\). Fix the numerical order as the reference left/right order for incomparable labels. For a linear extension \(w\), put
\[
\operatorname{Inv}_{P}(w)
=
\{(i,j):i<j,\ i\parallel_P j,\ j\text{ precedes }i\text{ in }w\}.
\]

Define a category \(\mathsf S(P)\) as follows:

- Its objects are linear extensions of \(P\).
- Its generating arrows exchange adjacent incomparable labels \(ji\to ij\), where \(i<j\).
- Its equations are the commuting squares for swaps at disjoint positions and the braid hexagons for three mutually incomparable labels.

**Proposition.**
\[
\mathsf S(P)(w,v)=
\begin{cases}
\{\ast\},&
\operatorname{Inv}_{P}(v)\subseteq
\operatorname{Inv}_{P}(w),\\[2mm]
\varnothing,&\text{otherwise}.
\end{cases}
\tag{1}
\]

### Existence

Each generating arrow deletes exactly one inversion, proving necessity.

For sufficiency, suppose the inclusion holds and \(w\ne v\). Let \(x\) be the label at the first position where \(v\) differs from \(w\). Locate \(x\) farther to the right in \(w\), and move it left to the required position.

Every crossed label \(y\) precedes \(x\) in the current word but follows \(x\) in \(v\). Therefore:

1. \(x\) and \(y\) are \(P\)-incomparable, since both words are linear extensions.
2. \(x<y\), since otherwise this change would introduce an inversion present in \(v\) but absent from \(w\).

Consequently every required move is an allowed inversion-deleting swap. Repeat at the next differing position.

### Uniqueness

Fix the target \(v\). Every path to \(v\) deletes precisely the inversions absent from \(v\), and has length
\[
|\operatorname{Inv}_{P}(w)|-
|\operatorname{Inv}_{P}(v)|.
\]

Compare two possible first swaps.

If they act at disjoint positions, they extend to a commuting square.

If they overlap, the current word has a consecutive triple
\[
cba,\qquad a<b<c.
\]
Both first swaps being permitted means that \(v\) orders these labels as \(abc\). Since the current word and \(v\) are both linear extensions, all three labels are pairwise \(P\)-incomparable. The two branches therefore extend to the allowed hexagon
\[
\begin{aligned}
cba&\to bca\to bac\to abc,\\
cba&\to cab\to acb\to abc.
\end{aligned}
\]
All its swaps delete inversions absent from \(v\).

Induction on the remaining inversion difference now identifies any two paths: resolve their first swaps by the square or hexagon, choose a continuation to \(v\), and apply the induction hypothesis to the suffixes. This proves (1).

This establishes exactly where uniqueness comes from: **fixed dependencies, together with square and hexagon equations**. Inversion containment alone supplies neither the fixed dependencies nor the equations.

### “Weak-order interval” needs a labeling hypothesis

For a prescribed labeling, dimension at most two is not sufficient. The poset with sole strict relation \(1<_P3\) has dimension two, but
\[
\operatorname{LE}(P)=\{123,132,213\}
\]
has two weak-order maximal elements, \(132\) and \(213\).

The Björner–Wachs interval criterion requires, for every \(a<b<c\),
\[
a<_Pc\Longrightarrow a<_Pb\ \text{or}\ b<_Pc,
\]
and
\[
c<_Pa\Longrightarrow c<_Pb\ \text{or}\ b<_Pa.
\]
This is restated in Chatel–Pilaud–Pons, Proposition 26 of the arXiv version. A particular planar labeling may satisfy these conditions, but that must be established. Without it, the correct conclusion is **the induced opposite weak order on \(\operatorname{LE}(P)\)**. [arxiv.org](https://arxiv.org/pdf/1701.07995?utm_source=chatgpt.com)

## 3. Question 2: the stated closure normalization is insufficient

Use left currying
\[
\Lambda_X:
\mathcal G(X\otimes C,Y)
\cong
\mathcal G(C,X\backslash Y).
\]

Choose distinct atoms \(X,Y\), put \(U=X\backslash Y\), and declare one generator
\[
h:U\longrightarrow U.
\]
Let
\[
\operatorname{ev}:X\otimes U\longrightarrow Y.
\]

The closed \(\eta\)-equation and your context-naturality equation give
\[
\begin{aligned}
h
&=1_U\circ h\\
&=\Lambda_X(\operatorname{ev})\circ h\\
&=\Lambda_X\!\left(
\operatorname{ev}\circ(1_X\otimes h)
\right).
\end{aligned}
\tag{2}
\]

The boundary \(U\vdash U\) is balanced. The generator is used once.

In the first expression, \(h\) is an ambient event. In the last expression, \(h\) acts on the captured \(U\)-input of a closure.

More specifically, the middle expression exhibits a conflict between the proposed normalization rule and structural simplification:
\[
\Lambda_X(\operatorname{ev})\circ h
\quad\begin{cases}
\longrightarrow h,
&\text{by structural }\eta,\\[1mm]
\longrightarrow
\Lambda_X(\operatorname{ev}\circ(1_X\otimes h)),
&\text{by pushing the event inward}.
\end{cases}
\]
Neither result admits another application of the stated inward-pushing rule, yet their nesting trees differ.

Therefore **pushing captured-wire events inward does not by itself define an invariant of 1-cells**. A specified canonical \(\beta\eta\)-normalization could resolve this example; the example does not rule out such a stronger construction. It shows that the stated rule is insufficient.

There is also a direct \(\beta\)-equation changing nesting. For
\[
k:X\otimes C\longrightarrow Y,
\]
one has
\[
\operatorname{ev}\circ
\bigl(1_X\otimes\Lambda_X(k)\bigr)=k.
\tag{3}
\]
Treating the eventful closure as permanently indivisible is incompatible with this equality unless the proposed invariant first accounts for \(\beta\)-reduction.

### Interchanging an outer event with a closure

For a chosen closure 1-cell \(c:C\to U\) and an independent 1-cell \(a:D\to E\), the tensor structure does provide
\[
(c\otimes1_E)\circ(1_C\otimes a)
\;\Longrightarrow\;
(1_U\otimes a)\circ(c\otimes1_D).
\tag{4}
\]
It is the ordinary interchanger applied to the two 1-cells \(c\) and \(a\).

What does not follow is a level-by-level completeness theorem. Equations (2)–(3) already change which events are assigned to which levels, so “the only comparison across levels” needs an invariant notion of level before it becomes a well-defined claim.

## 4. Question 3: the independent cube has a precise answer

Let \(I\) be the directed interval complex and
\[
Q_n=\nu(I^{\otimes n}).
\]

There is a directly relevant reference:

**Kapranov–Voevodsky, [“Free \(n\)-category generated by a cube, oriented matroids, and higher Bruhat orders”](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/free_n_category_generated_by_a_cube_published.pdf), Theorems 3–4.**

Writing \(q_n\) for the top cell of \(Q_n\), their Theorem 3 identifies \(B(n,k)\) with the set
\[
\left\{
x\in(Q_n)_k:
d_{k-1}^{-}x=d_{k-1}^{-}q_n,\quad
d_{k-1}^{+}x=d_{k-1}^{+}q_n
\right\}.
\tag{5}
\]
Its order is induced by existence of a \((k+1)\)-cell. Theorem 4 identifies the Manin–Schechtman higher category with
\[
Q_n(0^n,1^n).
\]
These statements concern specified boundary conditions, and the order convention must be matched to the chosen orientation of the cube. [math.ias.edu](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/free_n_category_generated_by_a_cube_published.pdf?utm_source=chatgpt.com)

Thus the proposed connection with higher Bruhat orders is precise for the cubical model. The correction concerns thinness.

### Three events already give two distinct comparisons

The objects of \(Q_n(0^n,1^n)\) are paths in \(Q_n\), hence permutations. Its arrows are **2-cells of \(Q_n\)**.

For \(n=3\), consider the two composites
\[
\alpha:
321\Rightarrow231\Rightarrow213\Rightarrow123,
\]
\[
\beta:
321\Rightarrow312\Rightarrow132\Rightarrow123.
\]

They are distinct 2-cells in \(Q_3\).

Here is a direct chain calculation. Denote cube faces by words in \(\{0,*,1\}\): \(0,1\) specify fixed coordinates, and \(*\) specifies an interval coordinate. These words label basis elements, not scalar products. Steiner’s tensor differential is
\[
\partial(x\otimes y)
=
\partial x\otimes y+(-1)^{|x|}x\otimes\partial y.
\]
His construction of \(\nu K\) retains the chain coordinates of its cells. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

The degree-two chains of the two composites are
\[
a=
\mathtt{0**}+\mathtt{*1*}+\mathtt{**0},
\]
\[
b=
\mathtt{**1}+\mathtt{*0*}+\mathtt{1**}.
\]
They have the same boundary:
\[
\partial a=\partial b
=
p_{123}-p_{321},
\]
where
\[
p_{123}=\mathtt{*00}+\mathtt{1*0}+\mathtt{11*},
\qquad
p_{321}=\mathtt{00*}+\mathtt{0*1}+\mathtt{*11}.
\]

But \(a\ne b\). Moreover,
\[
\begin{aligned}
\partial(\mathtt{***})
&=
\mathtt{1**}-\mathtt{0**}
-\mathtt{*1*}+\mathtt{*0*}
+\mathtt{**1}-\mathtt{**0}\\
&=b-a.
\end{aligned}
\]
The top cube cell is consequently a 3-cell
\[
\alpha\Longrightarrow\beta.
\tag{6}
\]

Therefore:

- The **reachability order** on the objects of \(Q_n(0^n,1^n)\) is weak order, oriented by deletion of inversions.
- Its underlying 1-category is not the thin weak-order category, already for \(n=3\).

With chronological event words and your interchange convention, this reachability order is the opposite of the usual increasing-inversion weak order.

### Why this does not refute uniqueness in the 2-dimensional Gray tensor

One must distinguish retaining cells through dimension two from imposing the equations supplied by dimension three.

The **intelligent 2-truncation** \(\tau^i_{\le2}Q_n\) identifies parallel 2-cells joined by a 3-cell, and hence identifies \(\alpha\) with \(\beta\). Ara–Maltsiniotis define the \(2\)-categorical tensor by this truncation and identify it with the original directed Gray tensor:
\[
(D^1)^{\otimes_2 n}
\cong
\tau^i_{\le2}Q_n.
\]
See *Joint et tranches pour les \(\infty\)-catégories strictes*, §1.2 and Appendix A.25–A.31. [webusers.imj-prg.fr](https://webusers.imj-prg.fr/~georges.maltsiniotis/ps/joint.pdf?utm_source=chatgpt.com)

Applying the scheduling proposition from §2 to an antichain gives
\[
\bigl(\tau^i_{\le2}Q_n\bigr)(0^n,1^n)
\cong
\bigl(S_n,\supseteq_{\operatorname{Inv}}\bigr)
\]
as a thin category.

So uniqueness in the genuinely 2-dimensional cubical model and nontrivial higher Bruhat comparisons in the \(\omega\)-model are compatible. The former imposes the latter’s 3-cell boundaries as equations.

### A precise dependent version for fixed one-level data

For a fixed labeled dependency poset \(P\), define a directed chain subcomplex
\[
K_P\subseteq I^{\otimes n}
\]
using the following cube faces. A face is specified by:

- an order ideal \(J\subseteq P\), whose coordinates are \(1\);
- a subset \(S\subseteq\min(P\setminus J)\), whose coordinates are \(*\);
- all remaining coordinates equal to \(0\).

Its dimension is \(|S|\).

This is closed under taking faces. Replacing a star \(s\) by \(0\) removes \(s\) from \(S\). Replacing it by \(1\) replaces \(J\) by the order ideal \(J\cup\{s\}\). The unital and strong loop-freeness conditions restrict from the cube, so Steiner’s freeness theorem applies to \(\nu K_P\). [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

In this construction:

- Paths from \(0^n\) to \(1^n\) are precisely linear extensions of \(P\).
- Square faces exchange adjacent independent events.
- Three-dimensional faces supply the corresponding directed braid comparisons.
- For an antichain, \(K_P=I^{\otimes n}\).

The proof in §2 gives
\[
\bigl(\tau^i_{\le2}\nu K_P\bigr)(0^n,1^n)
\cong
\mathsf S(P).
\tag{7}
\]

This supplies a concrete dependent \(\omega\)-categorical scheduling model. It does not establish that adjoining residuals preserves these hom-categories, or that nesting can be recovered from closed 1-cells.

## 5. Question 4 and the meaning of strict closed naturality

**Criterion G as stated cannot present the proposed free structure**, because it already accepts the nonexistent comparisons in §1.

The Gepner–Heine presheaf
\[
(S,T)\longmapsto
\operatorname{Map}(S\boxtimes X\boxtimes T,Y)
\]
does record the two parameter positions. Their Corollary 4.1.11 compares it with the cartesian version and proves a monomorphism of bioriented categories. It is not a presentation theorem by event orders or inversion sets. [arxiv.org](https://arxiv.org/pdf/2510.10504?utm_source=chatgpt.com)

There is also an ambiguity in “the closed structure is an isomorphism of hom-categories, strictly natural.”

Suppose
\[
\Phi_{A,B;C}:
\mathcal G(A\otimes B,C)
\cong
\mathcal G(B,A\backslash C)
\]
is strictly natural both in the context parameter \(B\) **and in the bound parameter \(A\)**. For
\[
f:A\to A',\qquad g:B\to B',
\qquad k:A'\otimes B'\to C,
\]
consider
\[
p=k\circ(f\otimes B')\circ(A\otimes g),
\]
\[
q=k\circ(A'\otimes g)\circ(f\otimes B).
\]
Applying the two naturality equations in opposite orders gives
\[
\Phi(p)
=
(f\backslash C)\circ\Phi(k)\circ g
=
\Phi(q).
\]
Because \(\Phi\) is an isomorphism of categories, it is injective on objects. Thus \(p=q\). Taking \(k\) to be an identity gives
\[
(f\otimes B')\circ(A\otimes g)
=
(A'\otimes g)\circ(f\otimes B).
\tag{8}
\]

Under that strong interpretation, the two schedules are already equal as 1-cells. Their distinct inversion sets cannot be invariants of those 1-cells. Equation (8) alone does **not** show that a specified interchanger endomorphism is an identity.

This argument requires strict naturality in the bound parameter. It does not follow merely from a strict 2-adjunction for each fixed tensor factor. The distinction also prevents promoting the mapping-space adjunction to the required enriched statement; Gagna–Harpaz–Lanari explicitly distinguish those levels in Remark 2.20. [arxiv.org](https://arxiv.org/pdf/2006.14495?utm_source=chatgpt.com)

A repaired comparison therefore needs a precise closed signature, a normalization that accounts for \(\beta\), \(\eta\), and the relevant naturality equations, and a theorem identifying its directed cells with the proposed scheduling model. The fixed-poset theorem and the cubical higher-Bruhat theorem above establish the one-level scheduling results; they do not establish that comparison for the nested biclosed completion.
