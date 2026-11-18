# Conjecture: Gray contexts in CaTT (composites of molecules, and Mikhail's Gray rules)

> **To send to a researcher, use [`outbox/gray-contexts.md`](outbox/gray-contexts.md)** (round 2, starting from the F-boundary case of the lax square). Round 1, its response and verification are in [`answered/gray-contexts-2026-11-18.md`](answered/gray-contexts-2026-11-18.md). This file keeps the history, earlier responses and verifications.

*Self-contained problem statement. Familiarity with the type theory CaTT (Finster–Mimram, LICS 2017, arXiv 1706.02866) is assumed, and the relevant parts are recalled in §1. Partial results are in §3. Status (updated 2026-11-18): G(2) is proved and existence in G(3) is proved (`../relative-coherence.md` §3); the rest reduces to the relative coherence property RC(n), n ≥ 3, for loop-free contexts. In §6 (formerly `gray-contexts-steiner.md`), parts (1)–(2) are open and part (3) is answered (§7).*

## 1. Background

**CaTT in brief.**
- Types are ⋆ and t →_A u.
- Contexts are lists of typed variables. By Benjamin–Markakis–Sarti (arXiv 2405.00398), contexts are exactly finite computads, and terms are the cells of the free weak ω-category on them.
- The only term former is coh_{P, t→_A u}[σ]. It requires P to be a **pasting scheme** (a globular pasting diagram) and σ a substitution into P, together with one of two side conditions:
  - **(coherence)** Var(t : A) = Var(P) = Var(u : A);
  - **(composition)** Var(t : A) = Var(∂⁻P) and Var(u : A) = Var(∂⁺P).
- Definitional equality is syntactic.

A variable's type may be a composite. For example, f : x → y, g : y → z, h : x → z, τ : g·f → h is a valid context, even though it is not a pasting scheme.

**Molecules and Gray products.**
- A **molecule** is a pasting diagram in Hadzihasanovic's regular directed complexes (*Combinatorics of higher-categorical diagrams*). Globes are molecules, and so are Gray products U ⊗ V of molecules. The cells of U ⊗ V are pairs x ⊗ y, with Steiner's boundary formula

  ```
  ∂^α(x⊗y) = (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^{dim x} α} y)
  ```

  Chanavat (arXiv 2505.01387), Prop. 2.16, gives the boundary formula at all levels.
- A **layering** of an n-molecule U is a decomposition of U as a sequence of n-dimensional atoms, each "whiskered" by lower-dimensional cells and pasted one after another.
- Chanavat, *A strengthened (∞,n)-categorical pasting theorem* (arXiv 2603.22242), gives several relevant results:
  - for **frame-acyclic** molecules, pre-layerings correspond to pre-orderings (Prop. 2.18);
  - the poset of subdivisions of a frame-acyclic molecule that is not an atom is contractible (Thm. 2.52; for an atom it is empty);
  - all molecules of dimension ≤ 3 are frame-acyclic, and so are all acyclic molecules;
  - as a consequence, frame-acyclic molecules have essentially unique composites in (∞,n)-categories.

## 2. Statements

To write a Gray product U ⊗ V as a CaTT context, each generator x ⊗ y needs a type ∂⁻(x⊗y) → ∂⁺(x⊗y). Both sides must be **CaTT terms** that compose the boundary molecules, and the type must be well formed. The two sides must have *syntactically* equal boundaries, since CaTT has no other definitional equality.

**Definition.** For a molecule U that has been presented as a CaTT context, a **U-composite** is a CaTT term t in that context with

```
Var(t) = Var(U)    and    t : ⌈∂⁻U⌉ → ⌈∂⁺U⌉
```

where ⌈−⌉ denotes a chosen U-composite of the lower-dimensional boundary, defined by induction on dimension.

**Conjecture G(n).** For every frame-acyclic molecule U of dimension ≤ n that is presentable as a CaTT context:
- **(existence)** U-composites exist;
- **(uniqueness)** any two U-composites are related by a CaTT term of type t → t′ that is invertible, i.e. has an inverse up to higher CaTT cells.

**Consequences and a stronger form.** (a) follows from G(n) for all n. (b) is a stronger statement; see the correction below.
- (a) For pasting schemes P, Q, the Gray product P ⊗ Q is presentable as a CaTT context. Its generators' types are built from U-composites of the boundary molecules, by induction on dimension.
- (b) Extending coh from pasting schemes to frame-acyclic molecules, with the same two side conditions, is a **conservative extension** of CaTT: every new term is equivalent to a CaTT term.

The converse holds: (b) implies G(n). *Correction (2026-11-18, from the verified researcher response below):* the forward implication "(∀n G(n)) ⇒ (b)" is **not established**. Molecular coherences over an m-molecule U include d-cells for every d > m, and G compares only the m-dimensional U-composites. The implication needs a higher filling statement for parallel full d-terms over U, i.e. the relative comparison property RC of `../relative-coherence.md`. So (b) is equivalent to RC for molecule contexts, and G is its top-dimensional part.

## 3. Partial results

### 3.1 G(1) (proof)

1-molecules are paths x₀ → x₁ → … → x_m, which are pasting schemes. Any two composites using all variables are full terms over a pasting scheme, so the coherence side condition gives the comparison cells in both directions.

### 3.2 Existence in G(2), hence Gray generators of dimension ≤ 3 (proof sketch)

Let U be a 2-molecule (dimension ≤ 3 implies frame-acyclic). Choose a layering S₁, …, S_k:
- each Sᵢ is a single 2-cell variable;
- it is whiskered on each side by paths, and the whiskering is a CaTT composite over a pasting scheme in which the 2-cell's boundary has been substituted.

Consecutive layers meet along composites of the same 1-molecule, possibly bracketed differently. Insert the comparison cells of G(1) between them, and at both ends to reach ⌈∂^±U⌉. The resulting vertical composite is a U-composite. ∎

Consequence: **every Gray generator of dimension ≤ 3 has a CaTT type.** The boundary of a dimension-3 generator is a 2-molecule. This covers D¹⊗D¹, D²⊗D¹, D¹⊗D² and the Gray cube D¹⊗D¹⊗D¹. It reproduces and extends Mikhail's construction (arXiv 2412.13310, §4.1), which handles Γ ⊗ D¹ for globular Γ.

### 3.3 Uniqueness in G(2), hence Gray generators of dimension 4

**Update 2026-11-18: proved.** The gap below is closed by Theorem A of [`../relative-coherence.md`](../relative-coherence.md): in *every* CaTT context, two parallel 2-terms with the same strict image are connected by a 3-term. U-composites of a 2-molecule have the same strict image (§3.1 there), so G(2) holds. Existence in G(3) follows by layering (§3.2 there), which is what actually types the Gray generators of dimension 4. The original sketch is kept below.

Two U-composites built from layerings L and L′:
- Layerings of a frame-acyclic 2-molecule correspond to linear extensions of a partial order on its 2-cells (Chanavat, Prop. 2.18).
- Any two linear extensions of a finite poset are connected by adjacent transpositions of incomparable elements. This is a standard fact.
- An adjacent transposition swaps two consecutive layers whose 2-cells are incomparable, i.e. side by side. The two composites are then instances, after substituting composite boundaries for 1-cell variables, of the two sides of the **exchange coherence** over the pasting scheme with two horizontally adjacent 2-cells. That coherence is invertible.
- The connecting G(1) cells differ between L and L′, but any two parallel G(1) cells are themselves related by coherences over a pasting scheme.

**Gap.** The cell built from these pieces has to be checked to have exactly the type t → t′ syntactically. That needs a careful bookkeeping argument, which we have not written.

Granting it, G(2) holds, and every Gray generator of dimension 4 (e.g. D²⊗D², D³⊗D¹, D¹⊗D¹⊗D¹⊗D¹) has a CaTT type.

### 3.4 Where the induction stalls

**Update 2026-11-18.** With Theorem A, existence in G(n) follows from RC(n−1) and uniqueness from RC(n) (`../relative-coherence.md` §3.3). RC(3) fails for non-loop-free contexts (Eckmann–Hilton, sketch in §7 there), so the remaining question is RC(n), n ≥ 3, on loop-free contexts. It is posed in `outbox/gray-contexts.md`.

For G(n) with n ≥ 3, two layerings of an n-molecule may differ by moves that are not single swaps of independent atoms. The relevant combinatorics is Chanavat's contractibility of the subdivision poset (Thm. 2.52). The missing step is to **translate a contractible poset of subdivisions into a family of CaTT cells**, with:
- a 1-dimensional CaTT cell for each edge of the poset;
- higher CaTT cells for its higher simplices;
- each realised as a substituted instance of a coherence over a pasting scheme.

This is a syntactic, "algebraic" form of Chanavat's homotopical pasting theorem. Chanavat's result is about (∞,n)-categories; CaTT's models are Grothendieck–Maltsiniotis weak ω-categories, where the pasting theorem has not been proved.

**Question (G-alg).** Does the conclusion of Chanavat's Thm. 2.52, contractibility of the subdivision poset of a frame-acyclic molecule, imply G(n) for CaTT, through an explicit translation of chains of subdivisions into substituted coherences?

## 4. Why it matters

Gray products of globes are the shapes of lax transformations and their higher analogues. A type theory in the CaTT style can name these shapes as contexts only if their generators can be typed by terms of the theory. G also decides whether allowing coherences over arbitrary frame-acyclic molecules, not just globular pasting schemes, adds anything.

## 5. What would count as a solution

Any of the following:
- a proof of G(n) for all n (equivalently, conservativity of molecular coh over CaTT);
- a proof of the bookkeeping step in §3.3 together with a positive answer to G-alg;
- a counterexample: two composites of a frame-acyclic molecule that are not related by any invertible CaTT cell.

*This file merges two earlier problem files: the former `gray-contexts-steiner.md` is now §6. §1–§5 ask the general syntactic question for pasting schemes. §6 asks whether one specific published rule set (Mikhail's) produces Gray contexts `M ⊗ Dⁿ` for every context M and every n. Problem N in `naturality-arbitrary-depth.md` is the case n = 1 for arbitrary contexts, stated as an explicit family of cells. G(n) for all n should imply N (see that file, §8); a verified review found that §8's argument fails as written for composition constructors, so the implication needs re-checking (open-issues D3a).*

## 6. Second form: Mikhail's Gray rules for arbitrary contexts

### 6.1 Background

**CaTT contexts are finite computads** (Benjamin–Markakis–Sarti, [arXiv 2405.00398](https://arxiv.org/abs/2405.00398)).
- A context lists variables `x : A`, where A is `⋆` or `t →_B u`, with t and u terms over earlier variables.
- A context presents the free weak ω-category on the corresponding computad (Dean–Finster–Markakis–Reutter–Vicary, Adv. Math. 2024).

**Mikhail's Gray rules** ([arXiv 2412.13310](https://arxiv.org/abs/2412.13310), §4.2) define, for a context M and each n ≥ 1, a judgment `M₁; …; M_{2n+1} gray M₁`. It is derived in two steps:
- duplicate each variable x of M into layers;
- at the layers 2i+1, add a connecting cell `p_x : s → t`.

The source and target of `p_x` are fixed only through free-variable conditions:
- **τCond:** `FV(s) = FV(x) ∪ ⋃{FV(p_y) | p_y in the current layer, y ∝ τ(p)…}`;
- **σCond:** the same condition, with x′ and the source;
- here `y ∝ t` means "y occurs linearly in t at top dimension", i.e. there is a unique path through operations and coherences.

The resulting context `M₁, …, M_{2n+1}` is meant to be `M ⊗ Dⁿ`. **Mikhail proves existence only for n = 1 (Thm 4.4).** The general existence of cones relies on his Conjecture 3.6.

### 6.2 Statement

1. **Existence.** For every finite CaTT context M and every n ≥ 1, there are layers `M₁ = M, M₂, …, M_{2n+1}` and connecting cells satisfying Mikhail's rules. Give an explicit formula for the types of the connecting cells, as composites of cells of M and of lower layers.
2. **Presentation.** Suppose M is a pasting scheme, or more generally that the free strict ω-category on M is a Steiner complex. Then the computad presented by `M ⊗ Dⁿ` generates, *as a strict ω-category*, the Steiner Gray tensor `𝒪(M) ⊗ 𝒪(Dⁿ)`.
3. **Weak version.** The free (∞,ω)-category on `M ⊗ Dⁿ` is the Gray tensor of the free (∞,ω)-categories on M and on Dⁿ. *Answered for pasting schemes; see §7.*

### 6.2a Caveat: the raw judgment is permissive

Mikhail's side conditions constrain free variables and the linearity of the *new* variable only. An external researcher showed that the analogous cone judgment admits non-canonical cones, which reuse earlier projections; see `lax-colimit-of-point.md`, verified counterexample. The Gray judgment has the same style of side condition, so it presumably admits non-canonical "Gray contexts" too. (1) should therefore ask for *some* derivation, given by an explicit formula. (2) is about that specified construction, not about every context the judgment admits.

### 6.3 Relation to §2

For M a pasting scheme, (1) is the existence half of G applied to the molecules ∂(x ⊗ y) with y a cell of Dⁿ, together with the requirement that the composites satisfy Mikhail's τCond and σCond. For M an arbitrary context, the generators' boundaries are themselves composites. Then (1) needs the naturality cells of `naturality-arbitrary-depth.md` (n = 1), or their analogues for Dⁿ.

### 6.4 What would count as a solution

A proof of (1) and (2), possibly by translating Mikhail's free-variable conditions into Steiner's basis description, or a counterexample context.

## 7. Literature status (searched 2026-11-18)

**G(n) and G-alg: open.** No paper on composites of non-globular molecules inside CaTT, or inside Grothendieck–Maltsiniotis weak ω-categories, was found. Related results:
- **The (∞,n) pasting theorem.** Chanavat, [arXiv 2603.22242](https://arxiv.org/abs/2603.22242), and Campion, [arXiv 2311.00200](https://arxiv.org/abs/2311.00200), prove the semantic analogue of G in (∞,n)-categories. No comparison between CaTT's models and (∞,ω)-categories is known, so this does not transfer.
- **Diagrammatic sets.** Hadzihasanovic, *Representable diagrammatic sets* ([arXiv 1909.07639](https://arxiv.org/abs/1909.07639)) and *Diagrammatic sets and rewriting in weak higher categories* ([arXiv 2007.14505](https://arxiv.org/abs/2007.14505)), take "every round molecule has a weak composite, unique up to equivalence" as the *definition* of a weak higher category. Chanavat–Hadzihasanovic, *Equivalences in diagrammatic sets* ([arXiv 2410.00123](https://arxiv.org/abs/2410.00123)), develop the calculus of equivalences there. So G asks whether CaTT models are "representable" in this sense.
- **Uniqueness only needs connecting cells to exist.** Benjamin–Markakis–Sarti, *Invertible cells in ω-categories* ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)), give a criterion and an algorithm for invertibility in computads, and show that invertible cells are closed under all operations. Benjamin–Champin–Markakis, *A type theory for invertibility in weak ω-categories* ([arXiv 2602.16602](https://arxiv.org/abs/2602.16602)), give ICaTT, a conservative extension of CaTT that witnesses invertibility syntactically. Coherence cells (full terms) are invertible, so in G the uniqueness half reduces to constructing *some* connecting cell from substituted coherences.

**§6 (Mikhail's rules).**
- **(1) and the matching half of (2): open.** Mikhail's thesis (*Type Theory for (∞,∞)-Categories, and Decomposition Spaces*, UAB; [record](https://ddd.uab.cat/record/321550)) has no general-n existence result.
- **The strict half of (2) is known.**
  - Ara–Lucas ([arXiv 1909.13564](https://arxiv.org/abs/1909.13564)), Cor. 3.11: the Gray tensor of two cofibrant (that is, free) strict ω-categories is free. The proof of their Prop. 3.7 shows that the tensor of strong Steiner complexes is freely generated by its atoms.
  - Campbell, *Parity complexes redux* ([arXiv 2605.09427](https://arxiv.org/abs/2605.09427)), shows that parity complexes are equivalent to strong Steiner complexes. This may help translate free-variable conditions into a basis description.
- **(3) is answered for pasting schemes M.** Campion ([arXiv 2311.00205](https://arxiv.org/abs/2311.00205)), Example 3.2 and Cor. 3.5: the inclusion of strongly loop-free Steiner complexes into flagged (∞,ω)-categories is strong monoidal for the Gray tensor. Independently: Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)), Thm 3.29. So the free (∞,ω)-category on the Steiner Gray tensor 𝒪(M) ⊗ 𝒪(Dⁿ) is Campion's Gray tensor M ⊗ Dⁿ. See `free-infinity-gray-of-pasting-diagrams.md`.

# Researcher Response

**G(2) can be proved, including the quantification over arbitrary full-support terms.** The proof needs a normalization argument in addition to the adjacent-swap argument in §3.3. That normalization can be constructed directly in CaTT.

This also gives **existence of composites in dimension 3**, hence types for Gray generators through dimension 4.

There is a separate problem with §6: **Mikhail’s printed support conditions fail for the walking-arrow context when duplication means a genuinely renamed copy.** This is a defect in the printed rules; the corrected geometric conjecture remains separate.

I do not obtain a proof of G in all dimensions or the requested general translation in G-alg.

## 1. Precise conventions

For the positive result, “a molecule presented as a CaTT context” has the cellwise meaning required by your proposed Gray construction:

- Each vertex, edge, and higher cell gives a distinct variable.
- An edge variable has the endpoints prescribed by the molecule.
- A higher variable’s declared source and target are composites of its actual boundary molecules.
- Restricting to a submolecule gives a valid context, with inclusion represented by a variable-preserving substitution.

In dimension 2, write the generators as
\[
\alpha_a:s_a\Rightarrow t_a,
\]
where \(s_a,t_a\) are arbitrary CaTT 1-composites of the input and output paths of the face \(a\). Units, arbitrary bracketings, and primitive operations of arbitrary arity are allowed.

I distinguish literal variables from support:
\[
\operatorname{Supp}(r:A)
=
\operatorname{Var}(r)\cup\operatorname{Var}(A).
\]
This distinction matters for a bare variable: \(\operatorname{Var}(\alpha)=\{\alpha\}\). These are the variable conventions used in *CaTT contexts are finite computads*. I address your literal \(\operatorname{Var}(t)=\operatorname{Var}(U)\) requirement at the end of the proof. [arxiv.org](https://arxiv.org/pdf/2405.00398?utm_source=chatgpt.com)

Throughout, \(r;s\) means “first \(r\), then \(s\),” with a fixed bracketing.

## 2. Proof of G(2)

### 2.1. Structural 2-cells over paths have all the coherence needed

Every CaTT 1-term \(f\) has a flattened directed edge word \(w(f)\):

- An edge variable contributes that edge.
- An identity contributes an empty word.
- A composition contributes the concatenation of its argument words.

The CaTT formation rules justify these cases: a primitive 1-term has a globular arity of dimension at most 1.

Every molecule of dimension at most 2 is acyclic, by Hadzihasanovic’s Proposition 8.4.3. Consequently, a directed edge word in its 1-skeleton is a path without repeated vertices. Let \(Q_p\) denote the globular pasting context of a path \(p\). A term whose flattened word is \(p\) restricts to this path context, after reordering and renaming its variables. [arxiv.org](https://arxiv.org/html/2404.07273v2?utm_source=chatgpt.com)

Choose a binary composite \(\widehat p\) of every path \(p\), taking
\[
\widehat{\epsilon_x}=1_x
\]
for an empty path. The full-support coherence rule over \(Q_{w(f)}\) gives an invertible 2-cell
\[
\nu_f:f\Rightarrow\widehat{w(f)}.
\]

Call a 2-term **structural** when its support has no 2-generator.

**Structural path lemma.** If \(r:f\Rightarrow g\) is structural, then
\[
w(f)=w(g)=p,
\qquad
\operatorname{Supp}(r)=\operatorname{Var}(Q_p).
\]
Therefore any two parallel structural 2-terms are connected by a CaTT 3-cell.

**Proof.** Induct on the construction of \(r\).

For a primitive arity of dimension at most 1, the generic source and target flatten to the same complete path. Substitution replaces its edges by composable edge words. Both resulting endpoints have the same concatenated word, and the substitution has precisely that path’s support.

For a primitive arity of dimension 2, a globular pasting scheme is a horizontal sequence of vertical chains
\[
\alpha_{ij}:f_{i,j-1}\Rightarrow f_{ij}.
\]
Every substituted 2-argument is structural. By induction, the words assigned to the \(f_{ij}\) in each vertical chain are equal. Concatenating the chain words proves both assertions.

Now let \(r,r':f\Rightarrow g\) be parallel structural terms. Both restrict to \(Q_p\), and both have full typed support there. Thus the term
\[
\operatorname{coh}_{Q_p,\;r\to_{f\Rightarrow g}r'}[\iota_p]
\]
is well formed, where \(\iota_p\) is the substitution including the path variables into the ambient context. ∎

This lemma handles a detail that ordinary bicategorical coherence alone would miss. A primitive ternary 1-composite is a different CaTT 1-term from a binary composite with parentheses. Its comparison with that binary composite is an additional structural 2-cell. The lemma supplies the required comparisons between such structural cells.

### 2.2. Use a quotient whose equalities already have CaTT witnesses

For exactly parallel 2-terms, define
\[
r\sim r'
\quad\Longleftrightarrow\quad
\text{there exists a CaTT 3-term }r\Rightarrow r'.
\]

Every 3-cell over a 2-dimensional computad is coinductively invertible: it has empty 3-dimensional generator support. This follows from Benjamin–Markakis, Proposition 35; Proposition 37 gives the corresponding necessary-and-sufficient criterion for finite-dimensional computads. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

It follows that \(\sim\) is an equivalence relation. It is preserved by binary composition: to lift a 3-cell through one argument of a binary 2-composition, use the globular pasting context obtained by replacing that argument’s 2-globe by a 3-globe.

The quotient therefore gives a bicategory \(B\), with:

- vertices as 0-cells;
- CaTT 1-terms as 1-cells;
- \(\sim\)-classes of 2-terms as 2-cells.

The bicategory laws follow directly from full 3-coherences over globular pasting schemes. Vertical associativity uses a vertical chain of three 2-cells; interchange uses a globular 2-grid; naturality of the associator uses a horizontal string of three 2-cells; the pentagon uses a path of four 1-cells. In each case the two expressions are syntactically parallel and have full support in the indicated generic context.

We now normalize its 1-cells as well. Define \(N\) by
\[
\begin{aligned}
N_0&=\{\text{vertices of }U\},\\
N_1&=\{\text{directed edge paths in }U\},\\
N_2(p,q)&=
\{r:\widehat p\Rightarrow\widehat q\}/\sim.
\end{aligned}
\]

Let
\[
\kappa_{p,q}:
\widehat p *_0\widehat q
\Rightarrow
\widehat{pq}
\]
be the chosen structural comparison. Define horizontal composition by
\[
[\alpha]\star[\beta]
=
\left[
\kappa_{p,q}^{-1};
(\alpha *_0\beta);
\kappa_{p',q'}
\right]
\]
for \(\alpha:\widehat p\Rightarrow\widehat{p'}\) and
\(\beta:\widehat q\Rightarrow\widehat{q'}\).

The structural path lemma supplies all compatibility equations for \(\kappa\). For example,
\[
(\kappa_{p,q}*_0 1);\kappa_{pq,r}
\]
and
\[
a_{\widehat p,\widehat q,\widehat r};
(1*_0\kappa_{q,r});\kappa_{p,qr}
\]
are parallel structural 2-terms, so they are equal in \(B\). The unit equations follow in the same way. Together with naturality of the bicategory constraints, these equations make \(N\) a **strict 2-category**.

For an arbitrary 2-term \(T:s\Rightarrow t\), its normalized class is
\[
\overline T
=
\left[\nu_s^{-1};T;\nu_t\right]
:
w(s)\Rightarrow w(t).
\]

No new equations have been imposed on CaTT syntax. Equality between representatives in these quotients means existence of an actual CaTT 3-cell.

### 2.3. Every CaTT 2-term normalizes to an expression in the atomic generators

Consider a primitive 2-term
\[
T=\operatorname{coh}_{P,A}[\sigma],
\qquad A=(s\Rightarrow t).
\]

First work in the generic pasting context \(P\).

If \(\dim P=2\), write \(P\) as a horizontal sequence of vertical chains. Compose each chain vertically, using an identity for a chain with no 2-generator, and compose the resulting terms horizontally with the chosen binary bracketing. This gives
\[
h_P:\widehat{w(s)}\Rightarrow\widehat{w(t)}.
\]
Set
\[
b_{P,A}
=
\nu_s;h_P;\nu_t^{-1}
:
s\Rightarrow t.
\]

Both
\[
c_{P,A}:=\operatorname{coh}_{P,A}[\mathrm{id}]
\quad\text{and}\quad b_{P,A}
\]
have exactly the type \(A\) and full typed support in \(P\). Hence
\[
\eta_{P,A}
=
\operatorname{coh}_{P,\;c_{P,A}\to_A b_{P,A}}[\mathrm{id}]
\]
is a valid 3-cell. Substituting \(\sigma\) gives
\[
T\Rightarrow b_{P,A}[\sigma].
\]

Each generic 2-generator is used exactly once in \(h_P\). Inductively normalize the substituted 2-arguments, using compatibility of \(\sim\) with composition. The structural path lemma identifies the resulting boundary transports with those defining composition in \(N\).

If \(\dim P\leq1\), the term is structural and its normalized class is an identity.

Thus:

> Every \(\overline T\) is a strict 2-categorical expression in the normalized atomic generators
> \[
> \overline{\alpha_a}
> =
> [\nu_{s_a}^{-1};\alpha_a;\nu_{t_a}].
> \]

This covers arbitrary CaTT terms, rather than only the terms initially constructed from layerings.

### 2.4. The external boundary forces every face to be used exactly once

Here is the additional combinatorial argument that makes the normalization useful.

For a regular 2-molecule:

1. Every edge is an input edge of at most one face.
2. Every edge is an output edge of at most one face.
3. The graph on faces, with \(a\to b\) when an output edge of \(a\) is an input edge of \(b\), is acyclic.
4. Every face has a nonempty input and output path.

These properties can also be checked directly by induction on the molecule construction. A 2-atom has two paths meeting only at their endpoints. A \(0\)-pasting identifies no edges. A \(1\)-pasting identifies an output path with an input path, introduces no second producer or consumer, and introduces cross-factor flow edges only from the first factor to the second.

Define
\[
\partial_2:\mathbb Z[U_2]\longrightarrow\mathbb Z[U_1]
\]
by
\[
\partial_2(a)
=
[\partial^+a]-[\partial^-a],
\]
where brackets denote edge sums.

**Claim.** \(\partial_2\) is injective.

Suppose \(z\neq0\) lies in its kernel. Choose a flow-minimal face \(a\) among those with nonzero coefficient in \(z\), and choose an input edge \(e\) of \(a\).

No other face consumes \(e\). Any face producing \(e\) precedes \(a\), so has coefficient zero by minimality. Consequently,
\[
(\partial_2z)_e=-z_a\neq0,
\]
a contradiction.

Now let \(E\) be the normalized atomic expression obtained from a term
\[
T:s_U\Rightarrow t_U,
\]
where \(s_U,t_U\) are the chosen external boundary composites. Let
\[
c(E)=\sum_{a\in U_2}m_a a
\]
count uses of its atomic generators.

Typing gives
\[
\partial_2c(E)
=
[w(t_U)]-[w(s_U)].
\]
Cancellation of internal edges in the molecule gives
\[
\partial_2\left(\sum_{a\in U_2}a\right)
=
[\partial^+_1U]-[\partial^-_1U].
\]
These right-hand sides agree. Injectivity therefore gives
\[
\boxed{m_a=1\quad\text{for every }a\in U_2.}
\]

Thus the proof does not assume that a support set records multiplicity. It proves the necessary multiplicity statement from the boundary.

### 2.5. Adjacent swaps now give the comparison

Strict interchange in \(N\) linearizes \(E\) into a vertical sequence of whiskered atomic generators.

If an edge is produced by \(a\) and consumed by \(b\), it is absent from the initial input boundary. A typed rewrite cannot consume it before it is produced. Hence the face sequence is a linear extension of the flow order.

Any two linear extensions are connected by adjacent swaps of incomparable elements. One proof is to move the first element of the desired extension left through the other extension; every crossed element is incomparable with it, and then induction applies to the remaining list.

Each swap is executable here. Suppose adjacent rewrites are \(a\), then \(b\), with \(a,b\) incomparable.

- Their input paths have no edge in common, by uniqueness of consumers.
- No output edge of \(a\) is an input edge of \(b\).
- Since the output path of \(a\) is nonempty, the contiguous input path of \(b\) after the first rewrite must already have existed unchanged before it.

The two rewrites therefore act on disjoint edge intervals, possibly meeting at an endpoint. Swapping them is precisely an interchange equation with surrounding whiskers. For a fixed face order, the rewrite positions are determined by their edge labels.

It follows that all normalized atomic expressions with the prescribed external boundary have the same value in \(N\).

For two original terms \(T,T'\), this gives
\[
\overline T=\overline{T'}.
\]
Cancelling their identical invertible boundary transports in \(B\) gives
\[
[T]=[T'].
\]
By the definition of \(\sim\), there is an actual CaTT term
\[
H:T\Rightarrow T'.
\]
It is coinductively invertible because the context has no 3-generators.

This closes the syntactic bookkeeping gap: the resulting cell has exactly \(T\to T'\) as its type.

### 2.6. Existence and literal variable support

Evaluate a layering using normalized atomic generators in \(N\), choose its CaTT representative, and transport back to the chosen \(s_U,t_U\). This gives a term
\[
T:s_U\Rightarrow t_U.
\]
It uses every face; its boundary and whiskering terms account for the remaining edges and vertices.

If literal \(\operatorname{Var}(T)\), rather than typed support, is required, apply the unary 2-composition operation over the 2-globe, substituting \(T\), its source and target, and their endpoints. The resulting \(T^\sharp\) has the same type and
\[
\operatorname{Var}(T^\sharp)
=
\operatorname{Var}(T)\cup
\operatorname{Var}(\operatorname{type}T)
=
\operatorname{Var}(U).
\]

Therefore **G(2) holds**, under the cellwise presentation specified in §1 above.

## 3. Existence in dimension 3 follows

There is a precise padding construction, so this consequence does not require G(3).

First choose binary CaTT compositions
\[
c_{r,k}(a,b)
\]
with exact boundary conventions. On the generic pasting context \(D^r\#_kD^r\), define them recursively:

- For \(r=k+1\), choose the composition whose source is \(s_k(a)\) and whose target is \(t_k(b)\).
- For \(r>k+1\), choose its source and target to be
  \[
  c_{r-1,k}(s_{r-1}a,s_{r-1}b),
  \qquad
  c_{r-1,k}(t_{r-1}a,t_{r-1}b).
  \]

The composition side condition permits these choices. In particular,
\[
s_kc_{r,k}(a,b)\equiv s_ka,
\qquad
t_kc_{r,k}(a,b)\equiv t_kb,
\]
and lower faces remain definitionally unchanged.

Now suppose a candidate 3-term has type
\[
z:s\Rightarrow t,
\qquad
s,t:a\Rightarrow b.
\]
Let the desired 1-boundaries be \(A,B\), and the desired 2-boundaries be
\[
S,T:A\Rightarrow B.
\]

G(1), applied in the respective boundary paths, supplies
\[
e^-:A\Rightarrow a,
\qquad
e^+:b\Rightarrow B.
\]
Define
\[
\widetilde z
=
c_{3,1}\bigl(c_{3,1}(1_{e^-},z),1_{e^+}\bigr).
\]
Its source and target are definitionally
\[
\widetilde s
=
c_{2,1}\bigl(c_{2,1}(e^-,s),e^+\bigr),
\qquad
\widetilde t
=
c_{2,1}\bigl(c_{2,1}(e^-,t),e^+\bigr),
\]
both of type \(A\Rightarrow B\).

These terms retain the exact supports of the two boundary molecules. G(2), applied separately in those boundary contexts, supplies
\[
p:S\Rightarrow\widetilde s,
\qquad
q:\widetilde t\Rightarrow T.
\]
Then
\[
\boxed{
c_{3,2}\bigl(c_{3,2}(p,\widetilde z),q\bigr)
:
S\Rightarrow T
}
\]
is the required composite.

To construct candidates, induct on a molecule’s pasting decomposition
\[
U=V\#_kW.
\]
Construct the two factor composites, promote a lower-dimensional factor by identities if necessary, and compose them along their identical chosen \(k\)-boundary. Apply the displayed padding afterward. An atom starts with its generating variable.

Support is preserved because each padding term is constructed in the relevant boundary context. Globularity places that boundary within every higher face affected by the padding. Submolecules of frame-acyclic molecules are frame-acyclic, so the restricted boundary instances remain within the inductive hypotheses. [arxiv.org](https://arxiv.org/html/2404.07273v2?utm_source=chatgpt.com)

Consequently:

- Every presented 3-molecule admits a composite with the prescribed compatible boundaries.
- A Gray generator of dimension 4 can be typed using composites of its 3-dimensional boundary molecules.
- Constructing generators in increasing dimension therefore gives the claimed CaTT presentations through dimension 4, including \(D^2\otimes D^2\) and the 4-cube.

This establishes existence in dimension 3, not uniqueness there.

## 4. What remains missing for G-alg

The proposed combinatorial obstruction needs adjustment.

For a frame-acyclic molecule and a fixed permissible layering dimension \(k\), layerings correspond to orderings. Connectivity by adjacent swaps is not restricted to dimension 2: Hadzihasanovic’s proof of Lemma 8.1.3 explicitly uses such swaps in arbitrary dimension, and Chanavat’s Lemma 2.16 gives the ordering–layering correspondence. [arxiv.org](https://arxiv.org/html/2404.07273v2?utm_source=chatgpt.com)

Thus, for **pairwise uniqueness**, one does not need to realize every higher simplex of the subdivision poset. It would suffice to prove:

1. Every term quantified over by G is comparable to a selected evaluation of a layering.
2. Every adjacent swap has a well-typed CaTT comparison between the selected evaluations.

Composing the comparisons along a finite path would finish pairwise uniqueness.

Chanavat’s Theorem 2.52 proves contractibility of \(\mathrm{Sd}(U)\) for frame-acyclic **non-atoms**; for atoms the poset is empty. It does not provide either of these CaTT constructions. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

The proof of G(2) above identifies a specific difficulty in extending the normalization argument. Its structural path lemma constructs 3-cells between structural 2-cells over a **1-molecule**, which is already a globular pasting scheme. The analogous step one dimension higher would require suitable 4-cells between 3-cells over **2-molecules**. G(2) only gives 3-cells between their 2-composites.

So the missing statement is more than a choice of bracketings: it includes higher coherence for boundary normalization over nonglobular molecules. I have not constructed that statement.

### The conservativity equivalence also needs a stronger formulation

For the same reason, the claimed implication
\[
\bigl(\forall n\,G(n)\bigr)\Longrightarrow\text{(b)}
\]
has not been established by the stated argument.

Let \(U\) have dimension \(m\). Extending the full coherence rule to \(U\) permits a coherence between full-support \(d\)-terms over \(U\) for \(d>m\). G only compares the **\(m\)-dimensional \(U\)-composites**. Applying \(G(d)\) to this same \(U\) does not change the dimension of a \(U\)-composite.

An elimination proof for all molecular coherences therefore needs a higher filling assertion of the form
\[
a,b\text{ parallel full-support }d\text{-terms over }\Gamma_U
\quad\Longrightarrow\quad
\exists\,H:a\Rightarrow b
\]
for all relevant \(d\ge m\), together with boundary transport and an induction on the extended syntax.

This identifies an unproved implication in the proposed equivalence; it is not a counterexample to that implication.

## 5. A walking-arrow obstruction to Mikhail’s printed rules

This calculation concerns the rules as printed in arXiv:2412.13310v2.

Take
\[
M=(a:\star,\ b:\star,\ f:a\to b)
\]
and its genuinely renamed copy
\[
M'=(a':\star,\ b':\star,\ f':a'\to b').
\]
The first connecting variables are
\[
u:a\to a',
\qquad
v:b\to b'.
\]

The printed definition of \(\delta\mathrm{Cond}\) selects a previous connector \(p\) using
\[
y\propto\tau(p)
\]
for both values of \(\delta\). The Gray rule applies \(\tau\mathrm{Cond}\) to the unprimed variable on the source side and \(\sigma\mathrm{Cond}\) to its primed copy on the target side. [arxiv.org](https://arxiv.org/html/2412.13310v2?utm_source=chatgpt.com)

At the \(f\)-step, suppose a connecting type
\[
p_f:s\to_A t
\]
satisfies those conditions.

**Source calculation.** Since
\[
\tau(f)=b,\qquad \tau(u)=a',\qquad \tau(v)=b',
\]
neither connector is selected. Linearity on variables requires literal variable identity. Hence
\[
\boxed{FV(s:A)=\{a,b,f\}.}
\]

**Target calculation.** Since \(\sigma(f')=a'\), the condition selects \(u\), giving
\[
\begin{aligned}
FV(t:A)
&=FV(f':a'\to b')\cup FV(u:a\to a')\\
&=\boxed{\{a,a',b',u,f'\}.}
\end{aligned}
\]

But \(f\propto s\) forces \(s\) to be one-dimensional and to use \(f\). A CaTT 1-term using only the arrow \(f:a\to b\) and identities has endpoints \(a,b\): this follows by the flattening induction used above. Therefore
\[
A\equiv a\to b.
\]
It follows that
\[
b\in FV(A)\subseteq FV(t:A),
\]
contradicting the target calculation.

Thus:

> With genuine copied types, no choice of \(s,t\) satisfies the printed conditions for the walking arrow.

The intended square
\[
p_f:(f;v)\Rightarrow(u;f')
\]
is a valid CaTT context. The contradiction comes from the printed recognition conditions.

### The copied-type ambiguity does not remove the problem

The displayed rule itself writes \(x':X\), without renaming \(X\), although Example 4.1 explicitly uses genuinely copied types such as \(f':a'\to b'\). [arxiv.org](https://arxiv.org/html/2412.13310v2?utm_source=chatgpt.com)

Taking the unrenamed type literally instead permits
\[
f':a\to b,\qquad p_f:f\Rightarrow f'.
\]
That satisfies the corresponding support constraints, but its strict category is not the Gray square. Its 1-skeleton has two parallel arrows \(a\to b\), together with \(a\to a'\) and \(b\to b'\); it has two terminal vertices. The Gray square has one terminal vertex.

So the two readings give different failures:

| Reading | Result |
|---|---|
| Genuine renamed copy | The printed support conditions prevent the walking-arrow extension. |
| Literally unchanged copied type | A derivation exists, but it does not present the Gray square. |

A necessary repair for the intended square is to rename copied types correctly and use
\[
y\propto\sigma(p)
\]
in the **Gray source-side** selector, retaining \(y\propto\tau(p)\) on its target side. This fixes the demonstrated example. It does not prove the repaired rules correct in every dimension.

### The printed “linear” predicate has another defect

Its recursive clause counts substitution arguments that are themselves declared linear, without excluding nonlinear uses in other arguments.

For a loop \(\ell:a\to a\), let \(c\) be binary composition. The printed recursion gives
\[
\ell\propto\ell,\qquad
\ell\not\propto c(\ell,\ell),\qquad
\ell\propto c(c(\ell,\ell),\ell).
\]
The last term uses \(\ell\) three times, but only its right argument satisfies the recursive linearity predicate. Thus that predicate does not enforce multiplicity one.

This is separate from the walking-arrow obstruction, which uses no repeated arrows.

## 6. Scope of the remaining literature claims

Mikhail’s Theorem 4.4 is stated for **globular contexts** and three layers, so even after repairing the displayed rules it does not establish arbitrary-context \(n=1\) existence. The later naturality construction of Benjamin–Markakis–Offord–Sarti–Vicary proves the depth-at-most-one construction; its theorem does not supply arbitrary-depth naturality. [arxiv.org](https://arxiv.org/html/2412.13310v2?utm_source=chatgpt.com)

The semantic Steiner statement in §7 remains valid in its stated strict setting: Campion’s Example 3.2 and Corollary 3.5 identify a strongly loop-free Steiner site whose inclusion into flagged \((\infty,\omega)\)-categories is strong monoidal. That establishes compatibility of the **strict Steiner tensor** with the semantic Gray tensor. It does not identify a context selected by Mikhail’s printed conditions with that strict tensor; that identification still requires the presentation result in §6(2). [arxiv.org](https://arxiv.org/html/2311.00205v1?utm_source=chatgpt.com)

---

## Verification of the researcher response (2026-11-18)

**Verdict: correct. G(2) is proved, the §3.3 gap is closed, existence in dimension 3 holds, and the obstruction to Mikhail's printed Gray rules is real.** This independently confirms the in-house proof of G(2) through Theorem A (open-issues D1, NGC thread); the two proofs have the same structure. The body of this file is owned by the NGC thread, so the corrections below are recorded here and passed to it, not applied to §§1–6.

**§2, G(2).**
- *2.1, structural path lemma.* A primitive 1-term has an arity of dimension ≤ 1, so its flattened word is a path. A molecule of dimension ≤ 2 is acyclic, so that path has no repeated vertex. Hence any two parallel structural 2-terms live over one path context and are connected by the coherence rule. This is the same argument as §2.1 of the verified ladder proof in `naturality-arbitrary-depth.md`. Correct. (I did not re-open Hadzihasanovic Prop. 8.4.3, which is cited for the acyclicity.)
- *2.2, quotients.* `∼` is an equivalence relation because a 3-cell over a 2-dimensional computad has no 3-generator in its support, hence is invertible. That is the content of the cited Benjamin–Markakis–Sarti criterion; I did not re-check the proposition numbers 35 and 37. Each listed bicategory law is a full coherence over the stated globular pasting context. Using the structural lemma to make the path-normalized N strict is sound. Correct.
- *2.3, normalization.* `coh_{P,A}[id]` and `b_{P,A}` are parallel and full over P, so they are related by a 3-cell. Substituting and recursing on the arguments gives every 2-term as an expression in normalized atomic generators. A 2-term over a 1-dimensional arity is structural. Correct.
- *2.4, each face used once.* The four properties of a regular 2-molecule hold (unique producer and consumer, acyclic flow, non-empty input and output paths).
  - Injectivity of ∂₂: take a flow-minimal face a with non-zero coefficient and an input edge e of a. No other face consumes e, and its producer precedes a, so has coefficient 0. Hence `(∂₂z)_e = −z_a ≠ 0`. Correct.
  - The telescoping identity gives `∂₂ c(E) = ∂₂(Σ a)`, so every multiplicity is 1. Correct. This does not assume that supports record multiplicity.
- *2.5, swaps.* A produced edge is not in ∂⁻U, so its consumer must come after its producer, and the face order is a linear extension of the flow order. For adjacent incomparable faces a then b, the input path of b is contiguous and cannot contain an output edge of a. Since a's output is non-empty, b's input cannot straddle it either. So the two rewrites act on disjoint intervals, and swapping them is an interchange. Linear extensions are connected by adjacent swaps. So `T̄ = T̄′`, hence `[T] = [T′]`, hence there is a CaTT 3-cell `T ⇒ T′` of exactly that type. Correct. This closes the §3.3 bookkeeping gap.
- *2.6.* Wrapping T in the unary 2-composite makes literal `Var` equal to typed support. Correct.

**§3, existence in dimension 3.**
- The recursive boundary conventions for `c_{r,k}` make the padded term's source and target definitionally the displayed `s̃` and `t̃`.
- `e^±` come from G(1). `p` and `q` come from G(2) in the boundary 2-molecules, which applies to any two parallel 2-terms with the prescribed boundary, not only to layer composites.
- Correct, under one implicit requirement: the composite `⌈V⌉` must be chosen once per submolecule V, so that factors sharing a k-boundary agree syntactically. The pasting induction needs this anyway.
- This gives existence for 3-molecules, hence types for Gray generators of dimension 4. It does not give uniqueness in dimension 3.

**§4, G-alg and conservativity.**
- The claim that pairwise uniqueness needs only (1) normalization to a selected layering and (2) a comparison for each adjacent swap is sound. I did not open the cited Hadzihasanovic Lemma 8.1.3 or the Chanavat Lemma 2.16 numbering.
- The obstruction one dimension up is identified correctly. Normalizing boundaries needs 4-cells between 3-cells over 2-molecules, and G(2) gives only 3-cells.
- **Correction to §2 of this file:** "(∀n G(n)) ⇒ (b)" is not established. Molecular coherences over an m-molecule U include d-cells for every d > m. G compares only the m-dimensional U-composites. The implication needs a higher filling statement for parallel full d-terms over the context of U. This is the same shape as the relative comparison property (RC) of `naturality-arbitrary-depth.md`.

**§5, Mikhail's printed Gray rules** (checked against arXiv 2412.13310v2, Def. 3.1, the δCond display on p. 14, and the `pgray` rules before Lemma 4.3).
- *Selector.* The printed δCond selects connectors with `y ∝ τ(p)` for both values of δ. The Gray rule applies τCond to x and σCond to x′, and writes `x′ : X` without renaming. Both confirmed.
- *Renamed reading.*
  - τCond gives `FV(s : A) = {a, b, f}`, because b is linear in neither τ(u) = a′ nor τ(v) = b′.
  - σCond selects u, because a′ ∝ τ(u). It gives `FV(t : A) = {a, a′, b′, u, f′}`.
  - Linearity forces s to be a 1-term built from f, so `A ≡ a → b`. Then b ∈ FV(t : A), a contradiction.
  - So no derivation exists. Confirmed.
- *Proposed repair.* With `y ∝ σ(p)` on the source side, τCond selects v, because b ∝ σ(v). The supports become `{a, b, f, v, b′}` and `{a, a′, b′, u, f′}`. These match the intended square `p_f : f;v ⇒ u;f′`. Confirmed for this example only.
- *Unrenamed reading.* `f′ : a → b` and `p_f : f ⇒ f′` satisfy the conditions. The resulting 1-skeleton has two sink vertices, a′ and b′, while the Gray square has one. So this reading does not present the Gray square. Confirmed.
- *Linearity predicate.* By Def. 3.1 (OP), `ℓ ∝ c(c(ℓ, ℓ), ℓ)` holds: only the right argument satisfies ∝, because ℓ is not linear in `c(ℓ, ℓ)`. So the predicate does not enforce multiplicity one. Confirmed.
- The selector defect and the degenerate unrenamed reading were also found independently, and machine-checked in Agda, as D3 and D4 of `notes/catt-lim-formalization.md`. The linearity-predicate defect is new.
- These defects are in the printed rules. Mikhail's Theorem 4.4 constructs specific contexts and is not refuted by them.

**§6, scope.** Mikhail's Theorem 4.4 is stated for globular contexts and n = 1. Confirmed.

**What this settles, and what it opens.**
- Settled: G(2), including the §3.3 bookkeeping (D1, already closed in-house); existence in dimension 3; Gray generators of dimension ≤ 4 are typed.
- Settled: Mikhail's printed Gray rules are defective in two ways (the source-side selector and the linearity predicate). Any formalization should use the repaired selector and a multiplicity-one linearity predicate.
- Open: uniqueness in G(3); G(n ≥ 3); G-alg; the conservativity implication, which needs higher filling (RC-shaped); and correctness of the repaired Gray rules in every dimension (D3).
