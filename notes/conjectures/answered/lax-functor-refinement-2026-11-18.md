# Lax functors as a directed coherence: are comparison cells decided by supports?

*A self-contained problem. No knowledge of the project that posed it is assumed. The questions are the four parts of Conjecture LF in "Statement"; the smallest open case is part 2 for the free category on a finite directed acyclic graph that is not a poset.*


## Background

**Weak ω-categories and CaTT.** CaTT (Finster–Mimram, LICS 2017) is a dependent type theory whose models are weak ω-categories. Its single term former `coh` produces, for a *pasting context* Θ (a context presenting a globular pasting diagram) and two terms u, v over Θ that are parallel and each use every variable of Θ ("full support"), a cell `u → v`. Every such cell is invertible. Composition operations are the case where u and v use exactly the source and target boundary variables of Θ. In CaTT, "coherence" therefore means: *a cell exists between two parallel composites iff a support (free-variable) condition holds*.

**A directed variant.** One can ask for a directed version of this pattern: a rule producing a cell `u → v` (and not `v → u`) when a *support condition computed on a Steiner complex* holds. For the Gray tensor product of pasting diagrams this is known to be the right picture: in a free strict ω-category on a loop-free Steiner complex, cells are determined by their supports (Steiner 1993; for Gray tensors of pasting diagrams this follows from Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273, Prop. 8.3.17 and Thm 11.2.18), and these Gray tensors are free as (∞,n)-categories (Campion, arXiv 2311.00205, Cor. 3.5).

**Lax functors.** A (normalised) lax functor F : A ⇝ B between 2-categories assigns objects, 1-cells and 2-cells, with comparison 2-cells `F f ; F g → F(f ; g)` (here diagrammatic order) satisfying associativity and unit axioms, and `F 1 = 1`. Oplax functors reverse the comparison. A lax functor out of the terminal category, without normalisation, is a monad (Bénabou).

**Orientals and nerves.** Street's orientals O_n are the free strict ω-categories on the n-simplex (as a Steiner/parity complex). The Street nerve of an ω-category B has as n-simplices the strict ω-functors O_n → B. For a 2-category B, the simplices are exactly the normalised (op)lax functors [n] ⇝ B, where [n] is the ordinal poset (Street; Duskin; see e.g. Gagna below). For a small category A, write `c_∞ N(A)` for the strict ω-category obtained by gluing orientals along the nerve of A (the left adjoint of the Street nerve applied to N(A)).

## Statement

Fix a finite category A whose nerve has finitely many non-degenerate simplices (for instance the free category on a finite directed acyclic graph, or a finite poset). Let Λ(A) be the normalised Steiner chain complex of N(A) (the "oriental complex" of A), so that `c_∞ N(A)` is the free strict ω-category ν Λ(A) on it, when Λ(A) is a Steiner complex.

An **F-image term** over A is a formal composite in the free strict ω-category `c_∞ N(A)` of generators (each non-degenerate simplex of N(A) is a generator); its **support** is the set of generators it uses, recorded with dimensions.

**Conjecture LF.**
1. (*Steiner.*) Λ(A) is a loop-free unital Steiner complex, so `c_∞ N(A) = ν Λ(A)` and its cells are determined by their supports.
2. (*Directed coherence.*) For parallel cells u, v of `c_∞ N(A)` there is a cell u → v iff a decidable support condition holds; when it holds, the cell is unique. For a chain A = [k], in dimension 2 the condition says "the partition of the path 0 → k given by u refines that given by v", and the cells form the Gray cube `(D¹)^{⊗(k−1)}` as `Hom_{O_k}(0, k)`.
3. (*Weak version.*) The same holds in the free *weak* ω-category on the computad presenting `c_∞ N(A)`, up to equivalence: the comparison from weak to strict is an equivalence, and parallel cells are connected by a cell iff they are in the strict model, with contractible choices. (For A = [n] this is Maehara's theorem below.)
4. (*Normalised oplax functors.*) For every weak ω-category B, the ω-category of maps `c_∞ N(A) → B` (weak sense) is equivalent to an ω-category of normalised oplax ω-functors A ⇝ B, for any reasonable definition of the latter that restricts to the known ones in dimensions ≤ 3.

If LF holds, a type theory can have *lax-functor variables* F : A ⇝ B whose comparison cells are produced by a single directed coherence rule with a support side condition, exactly as CaTT's `coh` produces invertible coherences.

## What is known

- **Orientals are Steiner complexes and loop-free** (Steiner 1993, *The algebra of directed complexes*; Street 1987, *The algebra of oriented simplexes*). So part 1 holds for A = [n], and the support statement of part 2 then holds for O_n by Steiner's theory.
- **Homs of orientals** are cubes: `Hom_{O_n}(0, n)` is the (n−1)-dimensional Gray cube **[recall, to be checked]**.
- **Gagna, *On a notion of oplax 3-functor*, arXiv 2004.14220.** Normalised oplax 3-functors between strict 3-categories correspond bijectively to simplicial maps between Street 3-nerves sending certain "constraint" simplices with trivial top cell to such; for a 1-category A without split monomorphisms or split epimorphisms, `c_∞ N(A)` is described and its universal property verified (§5). This is part 4 in dimension ≤ 3, for strict B.
- **Maehara, *Orientals as free weak ω-categories*, arXiv 2102.09736.** The orientals are also free *weak* ω-categories on the same generating data; the proof identifies the Street nerves of orientals as fibrant replacements of simplices in Verity's model structure for complicial sets. This is part 3 for A = [n].
- **Dwyer–Kan-type rigidity for 1-categories** (free categories on graphs have discrete homs as ∞-categories) suggests that gluing orientals along N(A) does not create extra homotopy when A is loop-free, but this is not a proof.
- **Not known to us:** whether Λ(A) is loop-free for every finite A with finitely many non-degenerate simplices (the gluing along faces could create loops); whether part 2's uniqueness survives the gluing; any statement for B weak in all dimensions.

## What has been tried

- For A = [2]: `c_∞ N(A) = O_2` has a single 2-cell `f₀₁ ; f₁₂ → f₀₂`, and the conjecture is immediate.
- For A = [3]: `O_3` has four 2-cells and one 3-cell between the two composites `(f₀₁ ; α₁₂₃) · α₀₁₃` and `(α₀₁₂ ; f₂₃) · α₀₂₃`; the support condition picks out exactly this 3-cell. This is the associativity axiom of a lax functor, now a cell.
- For a non-poset A, e.g. the free category on `x → y → z` together with an extra edge `x → z`, Λ(A) is the union of two copies of O_2 sharing an edge; loop-freeness holds by inspection.

## Why it matters

Lax functors appear throughout higher category theory (monads, lax monoidal functors, lax actions). A type theory for weak ω-categories that only has strict or pseudo functors cannot state them directly. If the comparison cells of a lax functor are governed by a support condition, then a lax functor can be a *variable* in such a type theory, and all its coherence follows from one rule, in the same way that all the coherence of weak ω-categories follows from one rule in CaTT.

## What would count as a solution

A proof of parts 1–3 (part 4 can be taken as a definition), a counterexample (a finite loop-free A with Λ(A) not loop-free, or two parallel cells of `c_∞ N(A)` with the same support that differ), or references.

## Literature status (2026-11-18)

Searched: "lax functors orientals ω-categories Street nerve normal lax functor classifier". Found Gagna (2004.14220) and Maehara (2102.09736), described above; Verity's complicial sets (arXiv 1308.1532, *Complicial structures in the nerves of omega-categories*) for the nerve side. No statement of part 2 for general A was found.

# Researcher Response

**LF is false as stated, already for \(A=[3]\).** The distinction is between a cell being determined by its support and a cell being determined by its boundary. The first holds here; the second does not.

There is nevertheless a substantial positive result: **part 1 holds for every \(A\) satisfying your finiteness hypothesis, and fillers in every dimension admit an explicit finite support test.** The test enumerates the possible fillers rather than producing at most one.

| Part | Result |
|---|---|
| **1. Steiner** | True; \(\Lambda(A)\) is actually **strongly** loop-free and unital. |
| **2. Directed coherence** | Existence is decidable by a boundary equation on subsets of generators. Uniqueness fails in \(O_3\). The Gray-cube identification fails in \(O_4\). |
| **3. Weak version** | The cellular weak-freeness statement follows from Campion’s pasting theorem in its \((\infty,\omega)\)-categorical setting. Contractibility applies after specifying a strict cell, not merely its boundary. A literal CaTT comparison requires a separate identification of models. |
| **4. Oplax functors** | This can be taken as a definition after fixing the mapping \(\omega\)-category. Gagna supplies the strict-target comparison through dimension \(3\); “any reasonable definition” needs a precise comparison statement. |

I give the counterexample first, then prove the positive statements.

## 1. The uniqueness assertion already fails in \(O_3\)

Use your contraction convention
\[
\alpha_{ijk}:f_{ij};f_{jk}\Longrightarrow f_{ik}.
\]
Put
\[
p=f_{01};f_{12};f_{23},
\qquad q=f_{03}.
\]
There are two parallel \(2\)-cells
\[
\begin{aligned}
L&=(\alpha_{012}*_0 1_{f_{23}})*_1\alpha_{023},\\
R&=(1_{f_{01}}*_0\alpha_{123})*_1\alpha_{013},
\end{aligned}
\qquad
L,R:p\Longrightarrow q.
\]

They are distinct. Their sums of generating \(2\)-cells are
\[
w_2(L)=[012]+[023],
\qquad
w_2(R)=[013]+[123].
\]
Associativity, units and strict interchange preserve these sums, and the two sums differ. The generating \(3\)-cell relates \(L\) and \(R\); it does not identify them. These are exactly the tetrahedral composites displayed in Gagna’s Appendix D.0.2. [arxiv.org](https://arxiv.org/pdf/2004.14220?utm_source=chatgpt.com)

Thus
\[
\#\{\,\alpha:p\Rightarrow q\,\}=2.
\]

Their supports differ, so this is entirely compatible with support determining a cell. What fails is the inference
\[
\text{support determines a cell}
\quad\Longrightarrow\quad
\text{boundary determines a cell}.
\]

**Orientation convention.** The standard normalized differential
\[
\partial[012]=[12]-[02]+[01]
\]
gives the comparison \(f_{02}\Rightarrow f_{01};f_{12}\), opposite to your displayed convention. Reverse the \(2\)-cell arrows above when using that convention. The counterexample and all counts below are unchanged. The chain formulas below use the convention \(\partial=\text{target}-\text{source}\).

## 2. Part 1 holds for every category in the question

Here is a proof that does not require \(A\) to be a poset or a free category.

### 2.1. The finiteness hypothesis forces acyclicity

A nondegenerate \(n\)-simplex of \(N(A)\) is a composable string of \(n\) nonidentity arrows.

If the directed graph of nonidentity arrows had a directed cycle, repeating that cycle would produce nondegenerate simplices of arbitrarily large dimension. Therefore that graph is acyclic.

Choose a total ordering of the vertices of \(A\) extending reachability. Every nondegenerate simplex
\[
\sigma=
\bigl(a_0\xrightarrow{f_1}a_1\longrightarrow\cdots
\xrightarrow{f_n}a_n\bigr)
\]
then has
\[
a_0<a_1<\cdots<a_n.
\]

Consequently every face of \(\sigma\) is nondegenerate, and different faces are distinct: they have different vertex sequences. More generally, the map
\[
\Delta[n]\longrightarrow N(A)
\]
specified by \(\sigma\) is a simplicial monomorphism. Its vertex sequence determines each simplex of \(\Delta[n]\) uniquely.

### 2.2. Unitality

The directed chain complex generated by the faces of \(\sigma\) is therefore a copy of the standard simplex complex. Its inclusion into \(\Lambda(A)\) preserves positive and negative parts of boundaries.

The standard simplex calculation gives
\[
(\partial^-)^n\sigma=[a_0],
\qquad
(\partial^+)^n\sigma=[a_n].
\]
Both vertices have augmentation \(1\). Hence the basis of nondegenerate simplices is unital. The corresponding calculation for a standard simplex is Steiner’s Example 3.8. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

### 2.3. Strong loop-freeness

Let \(m\) be the number of vertices of \(A\). The chosen ordering defines a functor
\[
r:A\longrightarrow[m-1]
\]
that maps every nonidentity arrow to a nonidentity arrow.

On normalized chains, it sends each basis simplex \(\sigma\) to a basis simplex of the same dimension. Moreover,
\[
r(\partial^\pm\sigma)=\partial^\pm r(\sigma).
\]
There is no cancellation or identification among the faces of a single \(\sigma\), because their vertex sequences differ.

The standard simplex has a strong loop-free order. Pull its strict order back along \(r\). Every required signed-incidence comparison in \(\Lambda(A)\) maps to a strict comparison in that order. A cycle in \(\Lambda(A)\) would therefore map to a cycle in the standard simplex order, which is impossible.

Distinct simplices may have the same image under \(r\); leave those simplices incomparable. Global injectivity of \(r\) is unnecessary. This establishes strong loop-freeness using Steiner’s Definition 3.6 and Example 3.8. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

### 2.4. The canonical comparison is an isomorphism

For each simplex \(\sigma:\Delta[n]\to N(A)\), the induced chain map gives
\[
O_n\cong\nu C_*(\Delta[n])
\longrightarrow\nu\Lambda(A).
\]
These maps define a cocone, hence a comparison
\[
\theta:c_\infty N(A)\longrightarrow\nu\Lambda(A).
\]

The principal cells associated with nondegenerate simplices composition-generate \(c_\infty N(A)\): every oriental is generated by its face atoms, and degenerate simplices contribute no additional generators.

By the embedded-simplex observation, \(\theta\) sends the principal cell associated with \(\sigma\) to the atom \(\langle\sigma\rangle\). Thus it maps a composition-generating set dimension-preservingly and bijectively onto the atoms of \(\nu\Lambda(A)\).

**Steiner’s Theorem 5.7 says precisely that such a comparison is an isomorphism.** Therefore
\[
\boxed{c_\infty N(A)\cong\nu\Lambda(A).}
\] :chatgpt-content-reference{index="3"}

### 2.5. What support determines

For geometric support, take the set of basis simplices used by a cell together with their face data. This avoids dependence on whether identities and boundaries were written explicitly in a composite expression.

The signed face poset of \(N(A)\) is acyclic by the same projection to the standard simplex. Each simplex generates an oriented-simplex atom. Hadzihasanovic’s Proposition 8.3.17 and Theorem 11.2.18 therefore identify the cells with molecular subsets of this face poset. In particular, **a cell of a fixed dimension is determined by its full geometric support**. :chatgpt-content-reference{index="4"}

There is consequently no counterexample consisting of two distinct cells with the same such support under your hypotheses. The failure of LF is its stronger boundary-uniqueness requirement.

## 3. An exact finite support test in every dimension

The chain model gives a particularly simple replacement for part 2.

Let
\[
K=\Lambda(A),
\]
and let \(B_j\) be its basis of nondegenerate \(j\)-simplices. Write \(w_n(u)\in K_n\) for the top chain of an \(n\)-cell \(u\). It records its generating \(n\)-cells; it is zero when \(u\) is an identity on a lower-dimensional cell.

### Proposition

For parallel \(n\)-cells \(u,v\), there is a bijection
\[
\boxed{
\operatorname{Fill}_{n+1}(u,v)
\cong
\left\{
S\subseteq B_{n+1}:
\partial\!\left(\sum_{\sigma\in S}\sigma\right)
=
w_n(v)-w_n(u)
\right\}.
}
\tag{*}
\]

Here \(\operatorname{Fill}_{n+1}(u,v)\) means \((n+1)\)-cells with source \(u\) and target \(v\), including identity cells.

Thus:

- Every successful support \(S\) gives exactly one filler.
- Different successful supports give different fillers.
- There can be no successful support, one, or several.

### Proof

A cell of \(\nu K\) is a finite table of positive chains
\[
(x_0^-,x_0^+;\ x_1^-,x_1^+;\ldots)
\]
satisfying
\[
\partial x_{j+1}^-=\partial x_{j+1}^+
=x_j^+-x_j^-,
\qquad
\epsilon x_0^-=\epsilon x_0^+=1.
\]
These are Steiner’s Definitions 2.6 and 2.8. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

Because \(u,v\) are parallel, their rows below \(n\) agree. A filler with top chain \(z\in K_{n+1}^+\) must have the table
\[
(x_j^-,x_j^+)=
\begin{cases}
(u_j^-,u_j^+)=(v_j^-,v_j^+),&j<n,\\
(w_n(u),w_n(v)),&j=n,\\
(z,z),&j=n+1,\\
(0,0),&j>n+1.
\end{cases}
\]

All positivity and augmentation requirements already hold. The boundary equations below row \(n\) follow from those for \(u,v\). The only new equation is
\[
\partial z=w_n(v)-w_n(u).
\]
Conversely, any positive \(z\) satisfying that equation gives the displayed table and hence a unique filler.

Finally, Steiner’s Theorem 6.2(iii) states that every coordinate of a cell in a loop-free unital complex has coefficients \(0\) or \(1\). Thus the possible \(z\) are exactly sums over subsets \(S\subseteq B_{n+1}\), proving \((*)\). [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

### Decision procedure

Compute
\[
b=w_n(v)-w_n(u).
\]
Enumerate the subsets of \(B_{n+1}\), and retain exactly those satisfying
\[
\partial\sum_{\sigma\in S}\sigma=b.
\]

This requires at most \(2^{|B_{n+1}|}\) boundary tests. It decides existence, counts the fillers, and specifies each filler uniquely. No additional recognition test for molecules is needed.

The empty subset gives the identity precisely when \(u=v\). A nonempty successful subset gives a nonidentity \((n+1)\)-cell.

Equivalently, if \(D_{n+1}\) is the boundary matrix, the problem is the finite Boolean integer system
\[
D_{n+1}z=b,
\qquad z\in\{0,1\}^{B_{n+1}}.
\]

## 4. The requested DAG case has a concrete description

In your contraction convention, a formal \(1\)-cell is a composable word of nonidentity arrows of \(A\):
\[
u=[f_1];\cdots;[f_r].
\]
Write
\[
v=[g_1];\cdots;[g_s].
\]

Then
\[
u\Longrightarrow v
\]
exists exactly when there is a partition
\[
0=i_0<i_1<\cdots<i_s=r
\]
such that, for every \(j\),
\[
g_j
=
f_{i_{j-1}+1};\cdots;f_{i_j}
\quad\text{as an arrow of }A.
\tag{**}
\]

Necessity follows because each generating \(2\)-cell contracts two adjacent factors. Sufficiency follows by repeatedly contracting within each designated block.

Since the vertices along \(u\) are distinct, the intermediate vertices of \(v\) determine the cuts uniquely whenever they exist.

For \(A=\operatorname{Free}(G)\), condition \((**)\) becomes:

1. Expanding \(u\) and \(v\) into edges of \(G\) gives exactly the same edge path.
2. Every cut of \(v\) is a cut of \(u\).

This proves the refinement criterion in the free DAG case, including non-posets.

### Exact multiplicity: binary forests

Let
\[
m_j=i_j-i_{j-1}.
\]
The exact number of \(2\)-cells is
\[
\boxed{
\#\operatorname{Fill}_2(u,v)
=
\prod_{j=1}^{s} C_{m_j-1},
\qquad
C_t=\frac{1}{t+1}\binom{2t}{t}.
}
\]

To prove this, record each binary contraction by a binary-tree vertex. The contractions producing the \(j\)-th target factor form a planar full binary tree with \(m_j\) leaves.

Strict interchange identifies different execution orders of independent contractions. It does not identify different trees. Conversely, evaluating any such tree from its leaves to its root gives a \(2\)-cell, independently of the order chosen for independent contractions.

Distinct trees give distinct triangle supports: each triangle records an interval of the original word and the split used to combine its two subintervals. The tree can be recovered recursively from those splits.

The oriental specialization is the bracketing correspondence in Lack–Street, Proposition 6.1. Their Proposition 6.2 further characterizes existence of \(3\)-cells between these bracketings by Tamari inequalities. [arxiv.org](https://arxiv.org/pdf/1302.4488?utm_source=chatgpt.com)

### Why the Gray-cube claim fails at \(O_4\)

For four consecutive factors, there are five comparison \(2\)-cells:
\[
((ab)c)d,\quad
(a(bc))d,\quad
(ab)(cd),\quad
a((bc)d),\quad
a(b(cd)).
\]

Thus \(\operatorname{Hom}_{O_4}(0,4)\) has **five** \(1\)-cells from the longest path to the single long edge.

The Gray \(3\)-cube has **six** \(1\)-cells between its extreme vertices: one for each order of traversing the three coordinate directions. Its square \(2\)-cells relate these paths without equating them.

The discrepancy is strict interchange in \(O_4\). Contracting \(ab\) and contracting \(cd\) can be done in either order, but the two orders give the same \(2\)-cell \(\alpha_{ab}*_0\alpha_{cd}\). Of the six contraction schedules, two therefore give the balanced bracketing \((ab)(cd)\).

Consequently
\[
\boxed{\operatorname{Hom}_{O_4}(0,4)\not\cong(D^1)^{\otimes3}.}
\]

The five bracketings are joined by the directed pentagon of tetrahedral comparisons. Its two routes give distinct parallel \(3\)-cells, with respective top supports
\[
\{0124,0234\},
\qquad
\{0123,0134,1234\}.
\]
The generating \(4\)-cell relates those routes. Lack–Street display this explicitly in diagram (6.14). Thus uniqueness also fails if one restricts attention to associativity comparisons in dimension \(3\). [arxiv.org](https://arxiv.org/pdf/1302.4488?utm_source=chatgpt.com)

### Correction to the small non-poset example

For the free category on
\[
x\xrightarrow{a}y\xrightarrow{b}z,
\qquad x\xrightarrow{c}z,
\]
the arrows \(c\) and \(a;b\) are distinct. There is exactly one nondegenerate \(2\)-simplex, namely \((a,b)\), whose long edge is the arrow \(a;b\).

Hence its categorification is \(O_2\) with an additional \(1\)-generator \(c\), not two copies of \(O_2\).

## 5. The weak-freeness clause has a positive result, but not boundary contractibility

The relevant general reference is Campion’s **other** paper:

**Timothy Campion, _An \((\infty,n)\)-categorical pasting theorem_, arXiv:2311.00200, Theorem 5.11 and Remark 5.13.**

Theorem 5.11 says that the pushouts attaching generating globes of a torsion-free complex remain pushouts after passing from strict categories to weak \((\infty,N)\)-categories. Remark 5.13 explicitly includes loop-free Steiner complexes among those covered. [arxiv.org](https://arxiv.org/pdf/2311.00200?utm_source=chatgpt.com)

Apply this to the strong Steiner complex established in §2. Let \(P_A\) be its generating computad. Build its weak realization by the same successive globe attachments:
\[
W_{\le r}
=
W_{\le r-1}
\amalg_{\coprod_{\sigma\in B_r}\partial D^r}
\coprod_{\sigma\in B_r}D^r,
\]
where these are colimits in the chosen \(\infty\)-category of weak categories.

Campion’s theorem identifies each stage with the corresponding strict stage. Induction over the finite dimension gives
\[
\boxed{
W(P_A)\simeq\iota\bigl(c_\infty N(A)\bigr).
}
\]

This establishes the cellular \((\infty,\omega)\)-categorical weak-freeness statement for all the \(A\) in your question.

### What contractible choices means here

It means that, **after specifying a particular strict cell**, its weak realizations form a contractible homotopy fiber.

It does not say that all fillers of a prescribed boundary are equivalent.

For \(O_3\), the two \(2\)-cells \(L,R\) above are connected by a noninvertible \(3\)-cell. The category of those \(2\)-cells and their \(3\)-cells is \([1]\). Its maximal subgroupoid consists of two points. Although the geometric realization of \([1]\) is contractible, \(L\) and \(R\) are not equivalent cells.

Therefore a weak category equivalent to \(O_3\) must retain these two inequivalent alternatives. The blanket “with contractible choices” clause in part 3 is false.

Campion’s separate contractibility theorem, Theorem 4.21, concerns decompositions of a **specified composite cell**, which is the relevant distinction. [arxiv.org](https://arxiv.org/pdf/2311.00200?utm_source=chatgpt.com)

### The CaTT qualification

Maehara’s precise theorem is that
\[
\Delta[n]^\flat\longrightarrow N_{\mathrm{RS}}(O_n)
\]
is an inner complicial anodyne extension. It is a theorem in the complicial-set setting. [arxiv.org](https://arxiv.org/pdf/2102.09736?utm_source=chatgpt.com)

Neither that statement nor Campion’s theorem, by itself, identifies a particular algebraically free CaTT/Grothendieck weak \(\omega\)-category with the cellular realization \(W(P_A)\) above. If part 3 specifically means that algebraic construction, the translation requires a separate comparison theorem. The cited results establish the homotopical formulation just given.

## 6. Part 4 and the resulting directed rule

For strict \(B\), the adjunction gives
\[
\operatorname{Hom}_{\omega\mathrm{Cat}}
\bigl(c_\infty N(A),B\bigr)
\cong
\operatorname{Hom}_{\mathrm{sSet}}
\bigl(N(A),N_\infty(B)\bigr).
\]

Gagna’s Lemma 1.3.19 identifies simplices of the nerve of a strict \(3\)-category with normalized oplax \(3\)-functors from ordinals. His Theorem 4.0.6 gives the corresponding cellular–simplicial comparison, and Theorem 5.0.17 describes \(c_\infty N(A)\) for split-free categories. [arxiv.org](https://arxiv.org/pdf/2004.14220?utm_source=chatgpt.com)

For a \(1\)-category source, the data reduce to arrow images, comparisons for composable pairs, comparisons for triples, and the next coherence equations. Thus the strict-target interpretation through dimension \(3\) is available with Gagna’s definition.

For weak targets, fix the model and the intended transformations—for example, by choosing a Gray internal hom—and define
\[
\operatorname{Oplax}_{\mathrm{norm}}(A,B)
:=
\underline{\operatorname{Fun}}\bigl(W(P_A),B\bigr).
\]
Agreement with another definition then becomes a specific comparison theorem. Agreement for “any reasonable definition” cannot be asserted without specifying those definitions and their transformations.

The corrected support rule for the free classifier is exact:
\[
\frac{
u\parallel v
\qquad
S\subseteq B_{n+1}
\qquad
\partial\left(\sum_{\sigma\in S}\sigma\right)
=
w_n(v)-w_n(u)
}{
\operatorname{dcoh}_{S}(u,v):u\longrightarrow v
}.
\]

**The support \(S\) specifies the directed comparison.** The boundary equation checks its existence, and the comparison is unique for that specified support. Different successful supports remain distinct comparisons and may themselves be related by higher directed cells.

## Verification of the researcher response (2026-11-18)

I checked every step. The sources were read in their PDFs: Steiner, *Omega-categories and chain complexes* (math/0403237); Campion 2311.00200; Maehara 2102.09736; Gagna 2004.14220; Lack–Street 1302.4488.

**Verdict: correct.** Conjecture LF is false as stated: the uniqueness in part 2, the Gray-cube recall and "contractible choices" in part 3 all fail. Part 1 holds for every A in scope, part 2's existence has an exact finite test, and part 3 holds in its cellular (∞,ω) form. The directed rule has to carry its support: `dcoh_S`.

### V1. Uniqueness fails in O₃ (§1): correct

- `L = (α₀₁₂ ∗₀ f₂₃) ∗₁ α₀₂₃` and `R = (f₀₁ ∗₀ α₁₂₃) ∗₁ α₀₁₃` both have type `f₀₁;f₁₂;f₂₃ ⇒ f₀₃`. Their top 2-chains are `[012]+[023]` and `[013]+[123]`. The top chain is an invariant of a cell of νK, so L ≠ R.
- The prompt's own "What has been tried" for [3] describes the 3-cell *between* these two composites, which already contradicts "the cell is unique". Our prompt conflated "determined by its support" (true) with "determined by its boundary" (false).
- *Orientation.* Steiner Ex. 3.8 uses `∂ = ∂₀ − ∂₁ + ∂₂ − …`, so `∂[012] = [12] − [02] + [01]`. With ∂ = target − source, this gives `f₀₂ ⇒ f₀₁;f₁₂`, which is the oplax direction. As the response says, this does not change any count.

### V2. Part 1 for every A with finitely many non-degenerate simplices (§2): correct

- *Acyclicity.* A directed cycle of non-identity arrows (including a non-identity endomorphism, or a pair of mutually inverse arrows) yields non-degenerate simplices of every dimension. So the arrows go up in a total order of the objects, and every non-degenerate simplex has strictly increasing vertices. Then every face is non-degenerate (inner faces compose two arrows between distinct objects), the faces are pairwise distinct, and `Δ[n] → N(A)` is a monomorphism.
- *Unital.* Each simplex spans an embedded copy of the standard simplex complex, with no cancellation. Steiner Ex. 3.8 gives the unital calculation.
- *Strongly loop-free.* Steiner Def. 3.6: a <_N b whenever `a ≤ ∂⁻b` or `∂⁺a ≥ b`. The functor `r : A → [m−1]` given by the total order sends basis simplices to basis simplices of the same dimension, and face i to face i, so it preserves both generating relations strictly. A cycle in Λ(A) would map to a cycle in the standard simplex, which is strongly loop-free (Ex. 3.8). Correct; r need not be injective.
- *`c_∞N(A) ≅ νΛ(A)`.* Steiner Thm 5.7 states exactly that an ω-functor θ: C → νK, with C composition-generated by E, K with a loop-free unital basis and θ a dimension-preserving bijection from E to the atoms, is an isomorphism. The cocone `O_n = νC(Δ[n]) → νΛ(A)` over simplices of N(A) gives θ, and E is the principal cells of non-degenerate simplices. Correct.
- *Support determines cells (§2.5).* This agrees with our `steiner-support-determines-cells.md` (G3 closed) and with Steiner Thm 6.2(iii): coefficients are 0 or 1.

### V3. The exact finite test (*) (§3): correct

- By Steiner Def. 2.8, a cell of νK is a table `(x₀^±, x₁^±, …)` of positive chains, with `∂x_{j+1}^± = x_j^+ − x_j^-` (Def. 2.6) and `εx₀^± = 1`. An (n+1)-cell from u to v has rows below n equal to those of u and v, row n equal to `(w_n(u), w_n(v))`, and top row `(z, z)`. The only new condition is `∂z = w_n(v) − w_n(u)` with z positive. Thm 6.2(iii) makes z a 0/1 sum of basis elements. So fillers are in bijection with the subsets S of `B_{n+1}` solving the equation. Rechecked.
- *Not checked by the response, and true:* a non-empty S never gives a loop u → u. If `∂z = 0` with z > 0, take x ∈ supp z maximal for <_N. Each element of `∂⁺x` would have to cancel against `∂⁻x′` for some x′ ∈ supp z, giving x <_N x′. So "the empty subset is the identity, and only it, when u = v" holds.

### V4. The DAG case (§4): correct

- 1-cells are words of non-identity arrows. Every 2-cell is a vertical composite of whiskered generators, each contracting two adjacent factors into their composite in A. So `u ⇒ v` exists iff each factor of v is the composite in A of a block of u. The cuts are unique because the vertices along u are distinct. For `A = Free(G)` this is: same edge path, and the cuts of v are among the cuts of u.
- *Catalan count.* For one block of m factors the 2-cells are binary bracketings. These are the triangulations of an (m+1)-gon: `C_{m−1}`. Interchange identifies schedules, not trees. The product over blocks follows.
- *O₄ is not the Gray 3-cube.* `Hom_{O₄}(0,4)` has 5 one-cells from the longest path to the long edge (Catalan C₃). The Gray cube `(D¹)^{⊗3}` has 3! = 6 edge paths between its extreme vertices, all distinct as cells of ν, since they have different edge sets. The orders "1, 3, 2" and "3, 1, 2" give the same 2-cell `α₀₁₂ ∗₀ α₂₃₄` in O₄. The vertex counts agree (8 = paths 0 → 4), so the failure starts at 1-cells. **The [recall] "Hom_{O_n}(0,n) is the (n−1)-dimensional Gray cube" is false for n ≥ 4** (true for n ≤ 3).
- *Pentagon.* `∂[01234] = [1234] − [0234] + [0134] − [0124] + [0123]` splits as `{0124, 0234}` versus `{0123, 0134, 1234}`. Lack–Street diagram (6.14) shows exactly these two routes with the 4-cell (01234) between them. Prop. 6.1 is their bracketing bijection, and Prop. 6.2 says 3-cells between 2-cells exist iff the Tamari order holds (and Tam_m is T_m with its 2-cells identified). Both confirmed.
- *Non-poset example.* In the free category on `a : x→y`, `b : y→z`, `c : x→z`, the only non-degenerate 2-simplex is (a, b), whose long edge is a;b ≠ c. So `c_∞N(A)` is O₂ plus a free 1-cell c, not "two copies of O₂ sharing an edge". Our prompt was wrong.

### V5. Weak version (§5): correct

- Campion 2311.00200, **Thm 5.11**: for a torsion-free complex P of dimension n ≤ N, the pushout attaching the n-cells is preserved by `sCat_N → Cat^f_N`. **Rem. 5.13**: torsion-free complexes include all loop-free Steiner complexes (via Forest), in particular orientals and their subcomplexes. Λ(A) is finite-dimensional and loop-free (V2), so induction on dimension gives `W(P_A) ≃ ι(c_∞N(A))`. Confirmed.
- *"Contractible choices" fails.* In O₃, the cells from L to R form the walking arrow [1] (one non-invertible 3-cell). Its core is two points. Campion's Thm 4.21 (contractible `Sd(µ)`) is about decompositions of one *specified* composite µ. Confirmed.
- *CaTT.* Maehara's Thm 2.1 is that `Δ[n] → O(−, n)` is an inner complicial anodyne extension: a complicial-set statement. Neither it nor Campion compares with the free CaTT (Grothendieck–Maltsiniotis) weak ω-category. This is the project's standing semantic gap (`semantics-gaps.md`), not specific to LF.
- *Wrong citation in our prompt:* the Background section cites "Campion, arXiv 2311.00205, Cor. 3.5" for freeness. That is the Gray-tensor paper, and Cor. 3.5 there is a monoidality statement. Freeness is the pasting theorem 2311.00200 (Thm 5.11). This is the same error as in the gray-contexts prompt.

### V6. Part 4 (§6): correct

- Gagna Lemma 1.3.19: n-simplices of the Street nerve of a 3-category are normalised oplax 3-functors from [n]. Thm 4.0.6: the category of small 3-categories and normalised oplax 3-functors. Thm 5.0.17: `c_∞N(A)` for split-free A. All confirmed. Taking `Fun(W(P_A), B)` as the definition for weak B is the sensible reading.
- The response's "Gagna Appendix D.0.2" for the tetrahedral composites is the appendix item that displays O₀–O₃. Confirmed.

### V7. Consequences for the project

1. **The lax-functor rule must name its support.** `dcoh_S(u, v) : u → v` for `S ⊆ B_{n+1}` with `∂ΣS = w_n(v) − w_n(u)`. It is unique for the given S, and different S give different cells. This applies to `ordinary-math.md` §7.3 (refinement coherence). It is the same lesson as L: a directed coherence is decided by supports, not by boundaries.
2. **The decision procedure is finite and exact.** It is a 0/1 linear system `D_{n+1} z = b`, with no molecule recognition needed. In the 2-dimensional DAG case the existence test is the refinement criterion, and the count of solutions is a Catalan product.
3. **[recall] refuted:** "homs of orientals are Gray cubes" (`ordinary-math.md` §7.3, last sentence; ledger G4). In general `Hom_{O_n}(0,n)` is the Tamari-type (associahedral) structure of Lack–Street, not `(D¹)^{⊗(n−1)}`.
4. **Our prompt's non-poset example and its Campion citation were wrong.**
5. **Open:** the CaTT-side comparison for part 3 (part of the general semantic gap), and the definition of oplax ω-functors for weak targets.
