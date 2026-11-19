# Relative coherence in CaTT in every dimension: free weak ω-categories on loop-free computads are strict

*A self-contained problem. It assumes familiarity with globular weak ω-categories, strict ω-categories and polygraphs (computads), and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** A theorem that holds **in every dimension at once**, or a counterexample. Many individual cases are already settled (§3), each by a hand-built normal-form argument for one context and one dimension. Further individual cases (another grid, another cylinder, RC(4) for one more context) are not useful to us. The value is in a uniform argument, or in a precise obstruction showing that no uniform argument exists.

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, arXiv 1706.02866) is a dependent type theory whose models are weak ω-categories (Benjamin–Finster–Mimram, arXiv 2106.04475: models are exactly Grothendieck–Maltsiniotis weak ω-categories).

```
Types          A ::= ⋆ | u →_A v
Terms          t ::= x | coh_{P, A}[γ]
Contexts       Γ ::= ∅ | Γ, x : A
Substitutions  γ ::= ⟨⟩ | ⟨γ, x ↦ t⟩
```

- `dim ⋆ = −1`, `dim(u →_A v) = dim A + 1`, and a term of type A has dimension `dim A + 1`.
- A **pasting context** `P ⊢ps` presents a globular pasting diagram. It has boundaries `∂⁻P`, `∂⁺P`.
- **The only term former.** If `P ⊢ps`, `P ⊢ u →_A v` and `Δ ⊢ γ : P`, then `Δ ⊢ coh_{P, u→_A v}[γ] : (u →_A v)[γ]`, provided either
  - (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or
  - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality. There are no other equations.
- Binary composites `u ∗_k v` and whiskerings are composition coherences over two discs glued along a k-disc.
- Contexts are exactly finite computads, and the terms of Γ are the cells of the free weak ω-category on Γ (Benjamin–Markakis–Sarti, arXiv 2405.00398). Coherence terms are invertible in the coinductive sense (Benjamin–Markakis, arXiv 2406.12127).

### 1.2 Strict image and relative coherence

Every context Γ is a polygraph. Write `F(Γ)` for the free strict ω-category on it. Strict ω-categories are CaTT models, so every term t has a **strict image** `π(t) ∈ F(Γ)`: a coherence is sent to the unique strict composite of its arity.

> **RC(n) for Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

Because coherence terms are invertible, RC(n) is symmetric. Write **RC(∞)(Γ)** for "RC(n) holds for Γ for every n ≥ 1".

> **RC_id(n) for Γ.** As RC(n), with the connecting term required to have identity image: `π(T → T′) = 1_{π T}`. Write RC_id(∞) as above.

RC_id implies RC. They agree when every endo-(n+1)-cell on an n-cell of F(Γ) is an identity, which holds in the loop-free class of Question 1. With loops, plain RC is too weak: in (x; f : x → x; α : f ⇒ f), the pair (f, f) is joined by α itself, whose image is not an identity. Wherever loops can occur, RC_id is the statement that matters.

*Equivalent form (proved for every finite context).* Every strict cell of F(Γ) is the image of some term. Given that, RC_id(∞)(Γ) is equivalent to: **π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models**, and also to π_Γ being a weak equivalence (F(Γ) is gaunt: its only invertible cells are identities, since the multiset of top generators is additive). The trivial-fibration form says: for every pair of parallel (n−1)-terms u, v and every strict n-cell c : π(u) → π(v) there is an n-term t : u → v with π(t) = c. (Lift c with some boundary, then conjugate by RC_id connections, which have identity image.) 

### 1.3 Contexts we need

All of the following are finite. The full cylinders (Y = Var(Q)), the joins, the Gray products of globes and the orientals present strongly loop-free Steiner complexes (Steiner, *Omega-categories and chain complexes*, HHA 2004; Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*), so F(Γ) = ν(K) has cells determined by their supports. The partial cylinders (Y ≠ Var(Q)) are positive in every dimension (the source of x↑ has x⁻ as a factor and its target has x⁺); whether they are Steiner loop-free is not needed if Question 1 is answered for a class containing them.

- **Cylinders.** For a pasting context Q and an up-closed set `Y ⊆ Var(Q)` (if y ∈ Y occurs in the type of x then x ∈ Y), the context `Q↑Y` keeps each `x ∉ Y` and replaces each `x ∈ Y` by two copies `x⁻, x⁺` and a cell `x↑ : a_x → b_x`, where for x of dimension n

  ```
  a_x := ( … ((x⁻ ∗₀ (τⁿx)↑) ∗₁ (τⁿ⁻¹x)↑) … ) ∗_{n−1} (τx)↑
  b_x := (σx)↑ ∗_{n−1} ( … ((σⁿ⁻¹x)↑ ∗₁ ((σⁿx)↑ ∗₀ x⁺)) … )
  ```

  with every factor `w↑` for `w ∉ Y` omitted. For Y = Var(Q) the strict ω-category F(Q↑Y) is the Gray cylinder `D¹ ⊗ Q`. The smallest example is the **lax square** (x⁻, x⁺, y⁻, y⁺; x↑, y↑, f⁻, f⁺; F : f⁻ ∗₀ y↑ ⇒ x↑ ∗₀ f⁺).
- **Joins.** For a pasting context Q, `Cone(Q; c)` adds an object c and, for each variable t of Q of dimension m, a variable `p_t : p_{τt} → p_{σt} ∗_{m−1} (p_{σ²t} ∗_{m−2} ( … (p_{σᵐt} ∗₀ t)))` (with `p_x : c → x` for objects). F(Cone(Q; c)) is the Ara–Maltsiniotis join `c ⋆ Q`.
- **Gray molecules.** Gray products `D^{n₁} ⊗ ⋯ ⊗ D^{n_k}` of globes, and more generally pasting diagrams in Steiner's or Hadzihasanovic's sense, presented in CaTT by giving each cell the type `⌈∂⁻x⌉ → ⌈∂⁺x⌉` with chosen composite terms for its boundary molecules.
- **Orientals.** For example the **triangle** (x, y, z; f : x → y, g : y → z, h : x → z; α : f ∗₀ g ⇒ h).

## 2. Why it matters

RC is the single missing ingredient in four independent constructions in CaTT:
- **Naturality at every depth.** Every coherence term has a lax naturality cell with respect to every up-closed set of its variables (so every context Γ has a lax cylinder Γ ⊗ D¹) if RC(n) holds on every cylinder `Q↑Y` (the naturality cell of an n-dimensional coherence exists given RC(1), …, RC(n) on the cylinders).
- **Composites of pasting diagrams.** Every pasting diagram U in the class above has a CaTT composite (existence ⇐ RC(n−1) for U's (n−1)-skeleton), unique up to a higher cell (uniqueness ⇐ RC(n) for U).
- **Cones over every coherence.** A specified cone construction extends to every context if RC holds on every join `Cone(Q; c)`.
- **A model comparison.** For the triangle context, the free CaTT model is equivalent to the free strict 2-category in the sense needed for comparing CaTT models with (∞,ω)-categories iff RC(r) holds there for every r ≥ 3.

## 3. What is known

1. **RC(1) and RC(2) hold in every context.** A 1-term's strict image is its flattened path, and two 1-terms with the same path are full parallel terms over the path's chain context. For 2-terms: normalise to a vertical composite of whiskered 2-variables; runs without 2-variables pull back to a chain context; two composites with the same strict image are related by exchange moves (free 2-categories are 2-paths modulo exchange, Ara–Burroni–Guiraud–Lafont–Métayer, *Polygraphs*, arXiv 2312.00429, §4.1), and each exchange move is a coherence over "chain, 2-disc, chain, 2-disc, chain".
2. **Terms without top-dimensional generators.** If parallel n-terms have no variable of dimension ≥ 2 in their support, they pull back to the chain context of their path, where the coherence rule connects them. More generally (**support lemma**) `supp(π t) = supp(t)` in every context, and if t has no variable of dimension dim t in its support then supp(t) = supp(σt) = supp(τt). So a term whose strict image lies in a dependency-closed subcontext is literally a term of it, and parallel terms whose image is an identity on a cell w are joined by one coherence over supp(w) whenever supp(w) is a pasting context.
3. **RC(3) is known in these cases:** the lax square; the triangle; every cylinder `Q↑Y` (all pasting contexts Q, all up-closed Y), by a stable column sort whose critical branchings are disjoint squares and a three-event braid; the 2 × 2 and 2 × 3 grids (Gray products of paths); the 3-dimensional Gray cube D¹ ⊗ D¹ ⊗ D¹; joins over vertical chains of 2-discs. **Open in dimension 3:** the 3 × 3 grid, and general finite 2-dimensional contexts with an acyclic generating 1-graph in which every 2-generator has nonempty source and target paths (for example the context S with objects c, x, y, z, edges a : c → x, b : c → y, e : c → z, f, f′ : x → y, g, g′ : y → z, and 2-generators α : f ⇒ f′, β : g ⇒ g′, u : b ⇒ a ∗₀ f, s : e ⇒ b ∗₀ g; RC(3) for the join over two horizontally composable 2-discs is equivalent to RC(3) for S).
4. **Adjoining top generators (dimension 3).** Let Λ have dimension ≤ 2 and an acyclic generating 1-graph, and Γ = (Λ, z₁ : A₁ → B₁, …, z_k : A_k → B_k) with A_i, B_i parallel 2-terms of Λ. Then RC(3)(Γ) ⇔ RC(3)(Λ). Proof: 3-terms modulo 4-terms form a category; normalise with chosen comparisons r_A : A → (representative of πA); depth-1 naturality (Benjamin–Markakis–Offord–Sarti–Vicary, arXiv 2501.11620, Thm 3.1) shows that a change of 2-dimensional context does not change normalised evaluation; strict 3-cells are composites of elementary steps modulo replacement and adjacent exchange (*Polygraphs*, App. D, Props. D.3.9, D.3.12), and both moves preserve normalised evaluation.
5. **Adjoining top generators (dimension 4), conditionally.** If dim Λ ≤ 3, Λ has an acyclic generating 1-graph and satisfies RC(3) **and** RC(4), then adjoining 4-generators preserves RC(4). The argument uses RC(3) twice (to choose representatives and to compare formal 3-contexts), and it does not give the extension from RC(4) alone.
6. **The combinatorics of exchange in dimension 2 are settled.** Assume Γ has dimension 2, an acyclic generating 1-graph, and nonempty boundary paths for every 2-generator. For a strict 2-cell c, the 2-paths representing c are exactly the linear extensions of an event poset E_c (events = letter occurrences, ordered by "consumes an edge instance produced by"), exchange moves are swaps of adjacent incomparable events, and the graph of exchange moves, with squares (disjoint swaps) and hexagons (three pairwise incomparable events) as 2-cells, is simply connected (Squier's homotopy lemma for the descent rewriting towards a fixed linear extension). Both the square and the hexagon are single coherences over pasting contexts (`D² ∨₀ D² ∨₀ D²`, `D² ∨₀ D² ∨₀ D² ∨₀ D²`).
7. **What every known proof needs in the next dimension.** The case-by-case proofs choose normalisers ν_T : T → N(T) for n-terms and prove fusion: for every (n+1)-term H : T → T′, a comparison ν_T → H ∗_n ν_{T′}. For RC(n+1) one then needs an (n+2)-cell between any two such comparisons, i.e. coherence of the normalisation one dimension up. In every case so far that higher coherence had to be constructed separately ("5-dimensional fusion" for RC(4)), which is why the dimension has been advancing one step at a time.
8. **Loop-freeness is necessary.** In Γ = (x, a : 1_x ⇒ 1_x), the Eckmann–Hilton 3-cell `a ∗₀ a ⇛ a ∗₀ a` and the identity are parallel with equal strict image. The weak free object on Γ groupoidifies to S² while the strict one, B²ℕ, groupoidifies to K(ℤ, 2) (Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9, Ex. 4.10). So RC(3) cannot hold for every pair of parallel 3-terms of Γ, since π₃(S²) ≠ 0. Adjoining y and f : x → y gives a connected example with an acyclic 1-graph that retracts onto Γ. An acyclic generating 1-graph is therefore not enough: the obstruction is a generator whose source and target are both identities.
9. **The semantic analogue holds.** For strongly loop-free Steiner complexes K, and more generally for regular directed complexes with frame-acyclic molecules, the strict ω-category ν(K) is the free (∞,ω)-category on its atoms: attaching the atoms one at a time is a sequence of homotopy pushouts (Campion, *Pasting diagrams in higher categories are free*, arXiv 2311.00200; Chanavat, arXiv 2603.22242, Thm 3.17). Positive 2-polygraphs and regular 3-polygraphs are homotopy polygraphs in this sense (Chanavat, Cors. 3.38–3.39). No comparison between CaTT models and (∞,ω)-categories is known, so this does not transfer to CaTT by itself.

## 4. Questions

**Question 1 (main).** Let Γ be a finite CaTT context whose polygraph is the atom polygraph of a strongly loop-free Steiner complex with unital basis (this includes every full cylinder, every join `Cone(Q; c)`, every Gray product of globes and every oriental), or a partial cylinder `Q↑Y`. Prove RC(∞)(Γ). Equivalently, prove that π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models.

The proof should be uniform in the dimension. Any of these routes would do; we list them only as suggestions.
- **(a) Induction on generators, all dimensions at once.** Γ is built by adjoining one generator at a time along its boundary. Show that if π_Λ is a trivial fibration and z : A → B is a new generator satisfying a loop-freeness condition, then π_{(Λ, z)} is a trivial fibration. Item 4 is this statement in one dimension. The difficulty is item 7: a dimension-by-dimension normalisation needs ever higher coherences, so the inductive hypothesis should be the whole trivial fibration (a statement about cells of every dimension), not RC in a fixed dimension.
- **(b) Contractible fibres.** For each strict cell c, describe the "fibre" of π_Γ over c (terms with image c, and higher terms between them with identity image) as a weak ω-category or as a CaTT-definable object, and show it is contractible, for instance by exhibiting it as a retract of something built from pasting contexts, where contractibility is the coherence rule.
- **(c) Relative higher rewriting.** Guiraud–Malbos (*Higher-dimensional normalisation strategies for acyclicity*, Adv. Math. 2012) build acyclic polygraphic extensions in all dimensions at once from a convergent presentation and a normalisation strategy. A relative version, normalising CaTT terms towards the strict cells of F(Γ) using a convergent presentation of F(Γ) (item 6 is its 2-dimensional case), would give RC(∞).
- **(d) Semantics.** Combine item 9 with a proof that the free CaTT model on Γ presents the free (∞,ω)-category on Γ, and that a CaTT-model map inducing an equivalence of the presented (∞,ω)-categories satisfies RC. This needs a comparison between CaTT models and (∞,ω)-categories, which is open.

**Question 2 (the right hypothesis).** Determine the largest natural class of finite contexts for which RC_id(∞) holds. In particular:
- Does RC_id(∞) hold for every finite context whose polygraph is a homotopy polygraph (the strict F(Γ) is the free (∞,ω)-category on Γ), for example every positive 2-polygraph? Conversely, does RC_id(∞)(Γ) imply that Γ is a homotopy polygraph?
  - *Known reduction.* Let η be the unit, at the free CaTT model on Γ, of the realization adjunction between CaTT models and (∞,ω)-categories. On homotopy polygraphs, "η is a weak equivalence" is equivalent to RC_id(∞). On polygraphs that are not homotopical, "η is a weak equivalence" implies that RC_id(∞) fails. So the converse half follows from the statement that η is a weak equivalence for every finite context. A direct proof that RC_id(∞) fails for (x; α : 1_x ⇒ 1_x) is welcome; item 8 gives RC(3) failing there.
- Does RC(∞) hold for regular directed complexes with frame-acyclic molecules that are not Steiner loop-free (Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273, Ex. 8.3.12)?
- Chanavat (arXiv 2509.26563, Comment 2.67) gives a 4-dimensional regular directed complex whose molecules do not form a polygraph under strict composition, so that strict ω-categories impose more relations than the directed complex does. Does such a complex give a counterexample to RC(n) for some n, with Γ positive in every dimension?

**Question 3 (if Question 1 is out of reach, still in every dimension).** Prove RC(n) for **every n ≥ 3** for every finite 2-dimensional context with an acyclic generating 1-graph in which every 2-generator has nonempty source and target paths. Together with a version of item 4 for adjoining generators of any dimension ≥ 3 (preserving RC(n) for all n), this would answer Question 1 for every context whose higher generators sit over such a 2-skeleton.

## 5. What counts as a solution

- A proof of Question 1, or of Question 3 together with the all-dimensional extension theorem, under a stated hypothesis. Explicit terms are welcome but not required: an existence proof for the connecting cells is enough, provided it is a proof about CaTT terms (or about CaTT models, via the trivial-fibration form).
- A counterexample: a finite context in the class of Question 1 (or in a class named in Question 2) with two parallel n-terms of equal strict image and no (n+1)-term between them, with a proof that none exists (for example an invariant of a model). Where loops can occur, the counterexample should be to RC_id.
- A published reference.

## 6. Literature (searched 2026-11-18)

- No published result compares free weak ω-categories (Grothendieck–Maltsiniotis, Batanin–Leinster, or CaTT) on non-globular computads with the corresponding free strict ω-categories. For pasting diagrams the comparison is the definition of a coherator.
- Semantic analogue: Campion, arXiv 2311.00200; Chanavat, *A strengthened (∞,n)-categorical pasting theorem*, arXiv 2603.22242 (Thm 3.17; Cors. 3.38, 3.39; Comment 3.40 expects the extension to arbitrary regular and positive polygraphs, unproved).
- Chanavat, *Homotopy theory of stricter n-categories*, arXiv 2509.26563: strict and "stricter" n-categories differ from n = 4.
- Henry, *Regular polygraphs and the Simpson conjecture*, arXiv 1807.02627.
- Guiraud–Malbos, *Higher-dimensional normalisation strategies for acyclicity*, Adv. Math. 231 (2012).
- Benjamin–Markakis–Offord–Sarti–Vicary, arXiv 2501.11620: naturality of coherences at depth ≤ 1.
- Rice, PhD thesis, arXiv 2502.17068, §4.5: normalisers for semistrict CaTT over pasting contexts; the extension to arbitrary contexts is left open there.
- Benjamin, *Hom ω-categories of a computad are free*, J. London Math. Soc. (2025).

# Researcher Response

**I do not have a proof of Question 1 or Question 3, or a counterexample in the stated classes.** I also did not find a reference resolving them. The results I checked leave the required comparison for computads with composite boundaries unproved.

There are, however, two precise deductions about your proposed routes, and one obstruction to using the hom-freeness theorem.

## 1. An appropriate weak equivalence already gives exact lifting

For every finite-dimensional polygraph \(\Gamma\), the following implication holds:
\[
\pi_\Gamma\text{ is an algebraic }\omega\text{-weak equivalence}
\quad\Longrightarrow\quad
\pi_\Gamma\text{ is a trivial fibration}.
\]
Here “\(\omega\)-weak equivalence” means the notion for Batanin–Leinster weak \(\omega\)-categories used by Fujii–Hoshino–Maehara: essential surjectivity with prescribed parallel boundaries in every dimension. Their definitions of weak equivalence and trivial fibration appear in §4.1 of *\(\omega\)-equifibrations between strict and weak \(\omega\)-categories*. [arxiv.org](https://arxiv.org/html/2511.09849v1?utm_source=chatgpt.com)

The implication follows from two elementary observations.

**First, \(F(\Gamma)\) has only identity equivalences.** Let \(d=\dim\Gamma\). All cells above dimension \(d\) are identities. Descend on \(n\le d\), assuming every equivalence of dimension \(n+1\) is an identity. If an \(n\)-cell \(a\) is an equivalence, its inverse \(b\) and cancellation witnesses therefore give strict equalities
\[
a*_{n-1}b=1,\qquad b*_{n-1}a=1.
\]

For an \(n\)-cell \(u\), let \(w_n(u)\) count its generating \(n\)-cells, with multiplicity. This is well-defined: associativity, units and interchange preserve that count. It is nonnegative and additive under composition. Thus
\[
0=w_n(1)=w_n(a)+w_n(b),
\]
so \(w_n(a)=0\). An \(n\)-cell expression with no generating \(n\)-cells is a composite of identities, hence an identity. This completes the descending induction. In the terminology of the cited paper, \(F(\Gamma)\) is **gaunt**.

**Second, weak lifting into a gaunt target is exact lifting.** Suppose
\[
f:X\longrightarrow C
\]
is an \(\omega\)-weak equivalence and \(C\) is gaunt. Given parallel \((n-1)\)-cells \(x,y\) and
\[
c:f(x)\longrightarrow f(y),
\]
the definition supplies \(t:x\to y\) with \(f(t)\sim c\). The equivalence witnessing \(f(t)\sim c\) must be an identity, so \(f(t)=c\). Essential surjectivity on zero-cells likewise becomes actual surjectivity. These are precisely the trivial-fibration conditions.

Consequently, route **(d)** can be reduced to establishing that the **particular map**
\[
\pi_\Gamma:\operatorname{Free}(\Gamma)\longrightarrow F(\Gamma)
\]
is an algebraic \(\omega\)-weak equivalence. The remaining issue is transferring the homotopical pasting theorem to that assertion about CaTT. Chanavat’s Theorem 3.17 establishes homotopy pushouts in flagged \((\infty,\omega)\)-categories; it does not identify this CaTT map as an algebraic \(\omega\)-weak equivalence. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

## 2. Chanavat’s four-dimensional example does not supply the requested counterexample

The distinction between the two strict targets in Comment 2.67 matters.

For the regular directed complex \(P\) in that comment, put
\[
Q=\operatorname*{colim}_{x\in P}\operatorname{Mol}/P_x,
\]
with the colimit computed in strict \(\omega\)-categories. Chanavat establishes that \(Q\) is a polygraph, whereas \(\operatorname{Mol}/P\) is not, and that
\[
r^{>}Q\cong\operatorname{Mol}/P,
\]
where \(r^{>}\) is the reflection into stricter \(\omega\)-categories. Thus the additional equations arise upon applying
\[
Q\longrightarrow r^{>}Q.
\]
These are the actual constructions in Comment 2.67. [arxiv.org](https://arxiv.org/html/2509.26563v1?utm_source=chatgpt.com)

If a CaTT context \(\Gamma\) presents the polygraph \(Q\), its comparison map has target
\[
\pi_\Gamma:\operatorname{Free}(\Gamma)\longrightarrow Q.
\]
An equality after applying \(Q\to r^{>}Q\) need not be an equality in \(Q\). Therefore, the extra molecular equations do not establish the premise
\[
\pi_\Gamma(T)=\pi_\Gamma(T')
\]
required for an RC counterexample.

This rules out the direct inference from non-polygraphic molecular composition to failure of RC. It does **not** establish RC for \(Q\), or exclude a different counterexample derived from the same complex.

## 3. Hom-freeness does not preserve the comparison map needed for induction

Benjamin–Markakis prove that hom weak \(\omega\)-categories of free computads are free. They also explicitly show that the hom-computad construction does not preserve finiteness: even the context \((x:\star)\) produces a hom computad with countably many zero-dimensional generators, corresponding to the distinct identity and composite expressions. [Wiley Online Library](https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/jlms.70367?utm_source=chatgpt.com)

There is a further obstruction independent of finiteness. Write \(H\) for a computad presenting
\[
\operatorname{Hom}_{\operatorname{Free}(x)}(x,x).
\]
The zero-cells of \(H\) include the distinct terms
\[
\operatorname{id}_x,\qquad
\operatorname{id}_x*_{0}\operatorname{id}_x.
\]
They remain distinct zero-cells in \(F(H)\), because freely adjoining higher-dimensional generators does not identify zero-cells.

By contrast,
\[
\operatorname{Hom}_{F(x)}(x,x)
\]
has exactly one zero-cell. Hence
\[
F(H)\not\cong\operatorname{Hom}_{F(x)}(x,x),
\]
and, under the hom-freeness identification,
\[
\operatorname{Hom}(\pi_x)
\]
is not the canonical comparison \(\pi_H\).

Thus an induction hypothesis about \(\pi_H\) does not directly control the fibres of \(\operatorname{Hom}(\pi_\Gamma)\). An additional comparison is required even before addressing preservation of the loop-free hypothesis.

## Unresolved conclusion

I could not supply the remaining syntactic step: a construction that takes **arbitrary CaTT terms** to chosen normal terms, with their exact boundaries, and produces the comparison cells coherently in every dimension. Constructing a contractible resolution of strict decompositions does not supply those comparisons back in the free CaTT model.

Accordingly, this answer does **not** establish \(\mathrm{RC}(\infty)\) for the classes in Questions 1 or 3, either implication relating RC to homotopy polygraphs, or the frame-acyclic case in Question 2. It narrows the semantic route and explains why the cited four-dimensional example is not yet an RC counterexample; it is not a solution under §5.

# Followup 1

**I continued the proof search, but I still do not have a full resolution.** I found neither an all-dimensional CaTT contraction nor a counterexample satisfying your hypotheses.

The generator-induction attempt reaches a specific missing step. Assuming
\[
\pi_\Lambda:W\Lambda\longrightarrow F(\Lambda)
\]
is a trivial fibration in every dimension lets us choose old cells with prescribed boundaries throughout a proposed normalization. After adjoining \(z\), it does not supply the comparisons
\[
t\longrightarrow N(t)
\]
when \(t\) uses \(z\). For an arbitrary
\[
t=\operatorname{coh}_{P,A}[\gamma],
\]
a strict decomposition of \(\pi(t)\) does not determine a decomposition of \(\gamma\) into substitutions that can be recombined by the CaTT coherence rule. I could not establish that substitution-level construction, including its higher comparison cells. Treating it as automatic would leave the proof circular.

One additional reference is close enough to distinguish precisely. Dean’s *Globular Multicategories with Homomorphism Types*, Theorem 5.4.0.1, proves an all-dimensional acyclic-fibration strictification theorem for **fibrational homomorphism types**. Its proof uses a strict computation law. Example 4.2.1.5 obtains **weak** homomorphism types from a contractible globular operad, and the analogous strictification statement for those is listed separately as Conjecture 5.4.0.9. Thus that theorem cannot be applied to CaTT merely from operadic contractibility. [christopherjdean.github.io](https://christopherjdean.github.io/assets/pdf/CJDean_Thesis_Archive.pdf?utm_source=chatgpt.com)

I have not proved that your RC problem is equivalent to Dean’s conjecture, either. The additional investigation therefore does not justify declaring your assertion true, false, or established as an equivalent formulation of a known open problem. **Questions 1–3 remain unresolved in this answer.**

# Followup 2

**I have not proved the theorem or found a counterexample in the requested classes.** The additional work gives a precise uniform reduction and an arity lemma, but the required CaTT construction remains unproved.

## A sufficient attachment lemma

Write \(W\Lambda=\operatorname{Free}(\Lambda)\). Consider the following statement:

> **One-generator attachment lemma — unproved.**  
> Let \(\dim\Lambda\le m\), suppose
> \[
> \pi_\Lambda:W\Lambda\longrightarrow F(\Lambda)
> \]
> is a trivial fibration, and adjoin one \(m\)-generator
> \[
> \Gamma=(\Lambda,z:A\to B).
> \]
> For every \(n\ge m\), let \(T,T'\) be parallel \(n\)-terms with common strict image \(c\). If the underlying strict \(m\)-cell of \(c\) uses \(z\) at most once, then there is
> \[
> H:T\longrightarrow T',
> \qquad \pi_\Gamma(H)=1_c.
> \]

Here, when \(n>m\), \(c\) is an iterated identity on an \(m\)-cell, since \(\Gamma\) has no generators above dimension \(m\). “Uses \(z\) once” refers to its coefficient in that strict \(m\)-cell, not to the number of times the symbol \(z\) is printed in a higher term.

**This lemma would prove the strongly loop-free Steiner part of Question 1 by induction on generators.** Order the generators by dimension. Every dependency-closed prefix inherits a unital strongly loop-free basis. Steiner’s Theorem 6.2(iii) says that the chains defining a cell of \(\nu K\) have coefficients \(0\) or \(1\). Thus, after adjoining \(z\), every relevant strict cell satisfies the lemma’s multiplicity condition. Terms below dimension \(m\), and terms whose images omit \(z\), are handled by the old context and your support lemma. This induction would establish all dimensions simultaneously. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

That is a sufficient reduction, not a proof of the attachment lemma.

## What can be proved about arbitrary coherence arities

There is an arity restriction that supports this approach.

Let \(P\) be a globular pasting context, let
\[
\gamma:P\longrightarrow W\Gamma
\]
be a substitution, and suppose the full substituted strict \(m\)-boundary uses \(z\) exactly once. Mark an \(m\)-variable \(a\) of \(P\) when \(\pi(\gamma(a))\) uses \(z\).

Then the marked variables and their higher incident variables belong to exactly one subtree at depth \(m\) in the Batanin tree of \(P\). With their required lower globular boundary, they form a diagram
\[
\Sigma^m Q
\]
for a globular pasting diagram \(Q\).

**Proof.** Use the recursive decomposition
\[
P=\Sigma P_1\vee\cdots\vee\Sigma P_r.
\]
The \(z\)-count in the full \(m\)-boundary is the sum of the nonnegative counts contributed by these factors. A total of one selects exactly one factor with positive count. Repeat this argument in the selected factor, lowering the dimension at each step.

After \(m\) steps, one subtree \(Q\) remains. Its vertices correspond to \(m\)-variables of \(P\), and its edges correspond to \((m+1)\)-variables. The strict images of the source and target of every such edge agree, because \(F(\Gamma)\) has only identity cells above dimension \(m\). Therefore the \(z\)-count is constant along these edges. The 1-skeleton of \(Q\) is connected, so every vertex of \(Q\) has count one. Every other subtree at depth \(m\) has count zero. This proves the assertion. The recursive description of pasting diagrams used here is given in Benjamin–Markakis, §2. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

This accounts for the repeated appearances of \(z\) in higher boundaries: they belong to one suspended pasting diagram, rather than representing several strict uses of \(z\).

## The step that still fails

The arity lemma does **not** give a substitution through which the desired comparison can be evaluated.

For
\[
t=\operatorname{coh}_{P,A}[\gamma],
\]
the labels of the marked subtree are themselves terms involving \(z\). Their lower faces include old composite terms. The trivial-fibration hypothesis on \(W\Lambda\to F(\Lambda)\) supplies fillers between appropriate **old** terms, with prescribed boundaries and strict images.

What remains is to assemble those fillers into a comparison for the entire coherence constructor, simultaneously respecting every source and target incidence in \(Q\). Concretely, one needs to construct
\[
t\longrightarrow N(t)
\]
with lower faces equal to the comparisons already chosen for the faces of \(t\), and then do this in every dimension.

I have not constructed that operation. Applying the coherence rule directly would require a suitable pasting context and a well-typed substitution into it; identifying the marked subtree supplies neither of those for the assembled comparison. Assuming that the old fillers can be substituted through the constructor would assume the missing higher naturality.

## The finite-cutoff approach does not yet close the gap

One auxiliary construction is valid. For a fixed strict target \(S\), a relative cutoff \(R_q^S X\) can retain \(X\) through dimension \(q\) and, above \(q\), give each prescribed boundary and strict value a unique lift:
\[
(R_q^S X)_j
=
\left\{
(a,b,c)\ \middle|\
a\parallel b,\quad
c\in S_j,\quad
s(c)=p(a),\quad t(c)=p(b)
\right\},
\qquad j>q.
\]

Interpret generating CaTT operations in their construction order. An operation with output dimension at most \(q\) uses only retained cells, because its arity has no greater dimension. An operation with higher output has a unique value with its already interpreted boundary and prescribed strict image. This defines the relative reflector.

Consequently, a filler of dimension at most \(q\) obtained after this cutoff is an actual filler before it. But the construction supplies no new cells in those retained dimensions. A descending induction therefore still needs the attachment or substitution lemma above; the cutoff alone does not establish it.

**These results do not meet the solution criterion in §5. The one-generator attachment lemma, Question 1, and the all-dimensional assertion in Question 3 remain unresolved in my work.**

# Followup 3

I have not obtained a proof of RC\((\infty)\), a counterexample in the requested classes, or a reference resolving it. The continuation does establish two uniform results:

1. **Every partial cylinder in Question 1 already has a strongly loop-free unital Steiner presentation.**
2. **Strictification is cartesian under generator-preserving maps of positive CaTT computads, in every dimension.** This gives an exact reduction to finite positive polyplexes. In dimension \(2\), those polyplexes are strong Steiner, so the two-dimensional restriction of Question 1 is equivalent to RC\((\infty)\) for **all** finite positive \(2\)-polygraphs, without an acyclic-\(1\)-graph hypothesis.

Here are the proofs and the precise remaining gap.

## 1. Partial cylinders are strong Steiner

Let \(Q\) be a finite globular pasting diagram, let \(Y\subseteq\operatorname{Var}(Q)\) be upward closed under dependency, and put
\[
C=\operatorname{Var}(Q)\setminus Y.
\]
Then \(C\) is closed under globular faces.

Regard \(Q\) as its augmented directed complex. Define \(K_Y\) to have basis
\[
C\;\sqcup\;Y^-\;\sqcup\;Y^+\;\sqcup\;IY,
\]
where \(\dim(Ix)=\dim(x)+1\). Use the conventions
\[
c^-=c^+=c,\qquad Ic=0\qquad(c\in C).
\]
The differential is
\[
\partial x^\pm=(\partial x)^\pm,
\qquad
\partial Ix=x^+-x^- -I(\partial x),
\tag{1}
\]
and every degree-zero basis element has augmentation \(1\).

Equivalently, this is the quotient of \(I\otimes Q\) identifying \(c^-\) with \(c^+\) and killing \(Ic\), for \(c\in C\). Closure of \(C\) under faces makes (1) well-defined.

### 1.1 A strong order

Use the canonical total order on the variables of a globular pasting diagram, in which
\[
\sigma x<x<\tau x.
\]
For the recursive decomposition
\[
Q=\Sigma Q_1\vee\cdots\vee\Sigma Q_r,
\]
this order is
\[
o_0,\ \Sigma Q_1,\ o_1,\ \ldots,\ \Sigma Q_r,\ o_r.
\]
The suspension-and-wedge description is the Batanin-tree description of globular pasting diagrams. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

For a variable \(a\), define
\[
U(a)=\{b\mid a=b\text{ or }a\text{ is an iterated globular face of }b\}.
\]

**Claim.** \(U(a)\) is an interval in the canonical order.

This follows recursively:

- If \(a=\Sigma a'\) has positive dimension in \(\Sigma Q_i\), then
  \[
  U_Q(a)=\Sigma U_{Q_i}(a').
  \]
- If \(a=o_j\), then
  \[
  U_Q(o_j)=\Sigma Q_j\cup\{o_j\}\cup\Sigma Q_{j+1},
  \]
  with nonexistent endpoint summands omitted.
- The one-point diagram is immediate.

Because \(Y\) is upward closed, \(a\in Y\) implies \(U(a)\subseteq Y\). Consequently, whenever \(a,b\in Y\) are related by a face incidence, they belong to the same maximal contiguous \(Y\)-block.

For each such block \(B\), replace its position in the canonical order by
\[
B^-\ ;\ I(B)^{\mathrm{rev}}\ ;\ B^+.
\tag{2}
\]
Keep every variable of \(C\) in its original position.

This order satisfies every inequality required by strong loop-freeness:

- Incidences within either endpoint copy retain their original order.
- Incidences between \(C\) and a selected variable respect the position of the entire selected block.
- The endpoint terms in \(\partial Ix\) require
  \[
  x^-<Ix<x^+.
  \]
- If \(a=\sigma x\in Y\), then \(Ia\) has positive coefficient in \(\partial Ix\), requiring \(Ix<Ia\). This holds because the middle block in (2) reverses the original order.
- If \(a=\tau x\in Y\), then \(Ia\) has negative coefficient in \(\partial Ix\), requiring \(Ia<Ix\), again supplied by that reversal.

Thus \(K_Y\) is strongly loop-free.

### 1.2 Unitality

Endpoint basis elements have their usual globular faces, so their iterated signed boundaries have augmentation \(1\).

For \(x\in Y\) of dimension \(n>0\), the cylinder basis element satisfies
\[
(\partial^-)^j Ix
=
(\sigma^{j-1}x)^-+I(\tau^j x),
\tag{3}
\]
\[
(\partial^+)^j Ix
=
(\tau^{j-1}x)^++I(\sigma^j x),
\qquad 1\le j\le n.
\tag{4}
\]
The final iterates are
\[
(\partial^-)^{n+1}Ix=(\sigma^n x)^-,
\qquad
(\partial^+)^{n+1}Ix=(\tau^n x)^+.
\tag{5}
\]

For completeness, the induction behind (3)–(4), before the final degree-zero step, is the calculation
\[
\begin{aligned}
\partial\bigl((\sigma^{j-1}x)^-+I(\tau^j x)\bigr)
&=(\tau^j x)^--(\sigma^j x)^-\\
&\quad+(\tau^j x)^+-(\tau^j x)^-
-I(\tau^{j+1}x)+I(\sigma^{j+1}x)\\
&=(\tau^j x)^++I(\sigma^{j+1}x)\\
&\quad-(\sigma^j x)^--I(\tau^{j+1}x).
\end{aligned}
\]

The positive-chain calculation gives the same differential by globularity. If a cylinder term in this calculation is omitted, closure of \(C\) under faces also makes its lower cylinder terms zero and identifies its two endpoint copies. The calculation therefore remains valid.

Taking positive and negative parts introduces no further cancellation: the iterated source and target variables of a positive-dimensional cell in \(Q\) are distinct, and retained cylinder basis elements are distinct from endpoint basis elements.

Equation (5) proves unitality. For \(n=0\), it follows directly from
\[
\partial Ix=x^+-x^-.
\]

### 1.3 Identification with the specified cylinder presentation

Let
\[
q:I\otimes Q\longrightarrow K_Y
\]
be the quotient chain map.

Equations (3)–(5) show, row by row in Steiner’s atom tables, that
\[
\nu q(\langle Ix\rangle)=\langle Ix\rangle_{K_Y}
\qquad(x\in Y).
\]
For \(c\in C\), closure under faces instead gives
\[
\nu q(\langle Ic\rangle)=1_{\langle c\rangle}.
\]

Apply \(\nu q\) to the full-cylinder boundary formulas from the question. Each omitted factor \(w^\uparrow\), with \(\dim w=k\), becomes the identity that is a unit for the corresponding \(*_k\)-composition. Hence the resulting boundaries are exactly the stated \(a_x,b_x\).

Steiner’s presentation theorem now identifies the two presentations:
\[
\boxed{F(Q\uparrow Y)\cong\nu K_Y.}
\]
The theorem says that a loop-free unital complex presents the strict category freely generated by its atoms with their specified boundary expressions. This argument uses that presentation theorem; it does not assume that \(\nu\) preserves quotients. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

Therefore the additional “or a partial cylinder” clause in Question 1 is redundant at the level of strict atom presentations.

## 2. Cartesian strictification for positive computads

Write \(W\Gamma\) for the free CaTT model, \(S\Gamma\) for the strictified polygraph, and \(F(S\Gamma)\) for its free strict category.

Here a **positive CaTT computad** means that \(S\Gamma\) is positive. A map of such computads is **generator-preserving** if it sends variables to variables and preserves their weak attaching terms exactly.

### Theorem

For every generator-preserving map \(f:\Delta\to\Gamma\) of positive CaTT computads, the square
\[
\begin{array}{ccc}
W\Delta & \xrightarrow{Wf} & W\Gamma\\
\pi_\Delta\downarrow && \downarrow\pi_\Gamma\\
F(S\Delta) & \xrightarrow{F(Sf)} & F(S\Gamma)
\end{array}
\tag{6}
\]
is a pullback in every globular dimension.

Explicitly, given a term \(t\in W\Gamma_n\) and a strict cell \(d\in F(S\Delta)_n\) satisfying
\[
F(Sf)(d)=\pi_\Gamma(t),
\]
there exists exactly one term \(\widetilde t\in W\Delta_n\) such that
\[
Wf(\widetilde t)=t,
\qquad
\pi_\Delta(\widetilde t)=d.
\tag{7}
\]

No RC hypothesis is needed.

### 2.1 Strict diagram lifting

The strict input is Henry’s result that positive polygraphs form a good class and that composition operations on a good class are cartesian natural transformations. The relevant published statements are Remark 2.2.9, Corollary 2.3.13, and Corollary 2.4.9 of *Non-unital polygraphs form a presheaf category*. [dml.cz](https://www.dml.cz/bitstream/handle/10338.dmlcz/153413/HigherStructures_003-2019-1_6.pdf?utm_source=chatgpt.com)

We need the following consequence.

Let \(P\) be a globular pasting diagram with total strict cell \(p\), and let
\[
\delta:F(P)\longrightarrow F(S\Gamma)
\]
be a strict interpretation. A prescribed lift \(d\) of \(\delta(p)\) uniquely determines a strict interpretation
\[
\widetilde\delta:F(P)\longrightarrow F(S\Delta)
\]
lifting \(\delta\) and taking \(p\) to \(d\).

To prove this, decompose the total cell of \(P\) into its globular compositions. Cartesian composition uniquely lifts each pair of factors from a lift of their composite. Recurse through this decomposition.

The compatibility step is essential. When two factor diagrams meet along a lower pasting boundary, their lifted total boundary cells agree by composability. Their entire boundary diagrams then agree by the lower-dimensional uniqueness statement: both lift the same prescribed boundary diagram with the same prescribed total cell. Thus the lifted factor diagrams glue.

Identity promotions also lift uniquely. A generator-preserving map reflects identity cells, because a nonidentity \(k\)-cell has a nonzero sum of \(k\)-generator counts, and mapping generators to generators cannot erase that sum.

This strict lemma permits \(\delta\) to assign composites or identities to variables of \(P\). The map required to preserve generators is \(f\).

### 2.2 Induction on raw CaTT syntax

Prove (7) by lexicographic induction on
\[
(\dim t,\ \text{raw term size of }t).
\]

**Variables.** If \(t=x\), then \(d\) is a generator. One way to see this is Henry’s generic-polyplex description: a generator has a plex as its generic polyplex, and generator-preserving maps preserve that generic index. Thus \(d\) determines a generator \(\widetilde x\) mapping to \(x\). Its weak boundary is preserved because \(f\) is a map of CaTT computads. [dml.cz](https://www.dml.cz/bitstream/handle/10338.dmlcz/153413/HigherStructures_003-2019-1_6.pdf?utm_source=chatgpt.com)

**Coherence terms.** Suppose
\[
t=\operatorname{coh}_{P,A}[\gamma].
\]
Its strict image is the evaluation of the total strict cell of \(P\), with identity promotion when the output dimension exceeds \(\dim P\).

The strict diagram-lifting lemma supplies a unique strict diagram
\[
\delta:P\longrightarrow F(S\Delta)
\]
lifting \(\pi_\Gamma\gamma\), with the prescribed total \(d\).

For each variable \(a\) of \(P\), apply the induction hypothesis to the substitution term \(\gamma(a)\), prescribing strict image \(\delta(a)\). Its dimension is at most \(\dim t\); when equal, its raw term size is smaller. This gives labels \(\widetilde\gamma(a)\).

These labels satisfy the dependent typing equations **syntactically**. For example, the source of \(\widetilde\gamma(a)\) and the already lifted label required by the source of \(a\) have:

- the same image under \(Wf\);
- the same strict image in \(F(S\Delta)\).

They are lower-dimensional terms, so the uniqueness part of the induction identifies them. Targets are handled identically.

Consequently \(\widetilde\gamma\) is a valid substitution, and
\[
\widetilde t=\operatorname{coh}_{P,A}[\widetilde\gamma]
\]
satisfies (7).

For uniqueness, a generator-preserving substitution preserves the distinction between variables and coherence constructors, and preserves the generic \(P,A\) of a coherence constructor. Any other lift must therefore have the same outer constructor. Strict diagram uniqueness fixes its strict labels, and the induction fixes its weak labels.

This proves (6). The operations on the pullback are componentwise, so (6) is also a pullback of CaTT models.

## 3. Exact reduction to positive polyplexes

Two consequences make the preceding theorem applicable to the original problem.

### 3.1 Strict polygraph maps lift to weak presentations

Suppose \(C\) is a positive strict polygraph and
\[
q:C\longrightarrow S\Gamma
\]
preserves generators. There is a unique choice of weak attaching terms on the generators of \(C\), denoted \(\widetilde C\), and a generator-preserving map
\[
\widetilde q:\widetilde C\longrightarrow\Gamma
\]
strictifying to \(q\). Uniqueness is understood up to renaming and declaration order.

Construct this by dimension. Suppose the lower skeleton has been constructed. For a new generator \(b\), let \(q(b)=a\). The strict source and target of \(b\) map to the strictifications of the weak attaching terms of \(a\).

The pullback theorem on the lower skeleton uniquely lifts those attaching terms. Their lower boundaries agree by lower-dimensional uniqueness, so the lifts are parallel and can be used to declare \(b\). This constructs the next skeleton and its map to \(\Gamma\).

Thus this construction does not require choosing comparisons between alternative bracketings.

### 3.2 Locality of the trivial-fibration assertion

For a strict cell \(c\in F(S\Gamma)\), take its universal positive-polyplex map
\[
q_c:P_c\longrightarrow S\Gamma,
\]
with distinguished strict cell \(p_c\). Positive polyplexes and their generic factorizations are supplied by Henry’s familial representation of the strict-cell functor. [dml.cz](https://www.dml.cz/bitstream/handle/10338.dmlcz/153413/HigherStructures_003-2019-1_6.pdf?utm_source=chatgpt.com)

Give \(P_c\) the weak attaching terms just constructed, obtaining \(\widetilde P_c\). Then
\[
W(\widetilde P_c)
\cong
W\Gamma\times_{F(S\Gamma)}F(P_c).
\tag{8}
\]

It follows that
\[
\boxed{
\pi_\Gamma\text{ is a trivial fibration}
\iff
\pi_{\widetilde P_c}\text{ is a trivial fibration for every strict }c.
}
\tag{9}
\]

The forward implication is pullback stability.

For the reverse implication, consider a lifting problem with prescribed parallel boundary \(u,v\) and strict cell
\[
c:\pi_\Gamma(u)\longrightarrow\pi_\Gamma(v).
\]
Equation (8) uniquely lifts \(u\) over \(s(p_c)\) and \(v\) over \(t(p_c)\). These lifts are parallel: their lower boundaries agree in both factors of the globular pullback. A filler over \(p_c\) in \(W(\widetilde P_c)\) then maps to the required filler over \(c\).

The same argument transfers RC\((n)\) from the relevant \(\widetilde P_c\) to a parallel pair with strict image \(c\). This works in arbitrary dimension, including identity promotions above the dimension of the computad.

## 4. Consequence for every positive \(2\)-polygraph

Every finite positive \(2\)-polyplex has a strongly loop-free unital Steiner presentation.

Here is a direct proof.

A positive \(2\)-plex is a polygon between two nonempty directed paths. Its source and target paths have distinct internal generators and share only their endpoints. Order its basis by listing:

1. the common initial vertex;
2. the source-path edges and internal vertices in path order;
3. the \(2\)-generator;
4. the target-path edges and internal vertices in path order;
5. the common final vertex.

This is a strong order. Both boundary chains are directed paths, so the basis is unital.

Positive \(2\)-polyplexes are constructed from these polygons, paths, and points by the pushouts representing \(0\)- and \(1\)-composition. The representing-pushout description is part of Henry’s cartesian-composition result. [dml.cz](https://www.dml.cz/bitstream/handle/10338.dmlcz/153413/HigherStructures_003-2019-1_6.pdf?utm_source=chatgpt.com)

Gluing at a single vertex preserves acyclicity of the strong relation: a cycle traversing both factors would have to leave and return to that vertex through one factor.

For gluing along a directed boundary path, the basis of the common path is already totally ordered:
\[
v_0<e_1<v_1<\cdots<e_r<v_r.
\]
Any directed segment in either factor whose endpoints lie on this path must move forward in that order. A backward segment would form a cycle with the path in that factor. Therefore a cycle alternating between factors is impossible.

The boundary-path maps are embeddings, inductively: vertical composition retains the exterior boundary paths of its factors, and horizontal composition concatenates paths at one endpoint. The pushouts consequently identify no two distinct generators within a factor. The disjoint source and target edge sets of each polygon remain disjoint, preserving unitality.

Thus the resulting complex is strongly loop-free and unital. Its atom presentation is the original polyplex presentation, so Steiner’s theorem gives
\[
F(P_c)\cong\nu K(P_c).
\] :chatgpt-content-reference{index="6"}

Now let \(\Gamma\) be any finite positive \(2\)-dimensional CaTT context. For \(n\ge2\), a strict \(n\)-cell is an identity promotion of a strict cell of dimension at most \(2\). Its generic polyplex is therefore finite and at most \(2\)-dimensional.

Given parallel \(n\)-terms \(T,T'\) of equal strict image, equation (8) lifts them to parallel terms in the weak presentation \(\widetilde P_c\). That presentation is strong Steiner. Any RC\((n)\) filler there maps back to a filler between \(T,T'\).

Consequently, for each \(n\ge2\),
\[
\boxed{
\begin{aligned}
&\text{RC}(n)\text{ for every finite strong-Steiner context of dimension }\le2\\
&\qquad\Longleftrightarrow\\
&\text{RC}(n)\text{ for every finite positive context of dimension }\le2.
\end{aligned}}
\tag{10}
\]
The reverse implication holds because strong unital atom presentations are positive. The proof is uniform in \(n\), so (10) also holds with RC\((\infty)\).

The generating \(1\)-graph of \(\Gamma\) need not be acyclic. The generic polyplex has separate generators for its path positions; its map to \(\Gamma\) may identify them.

## What remains unresolved

These results establish exact lifting under generator-preserving maps and exact reduction to generic polyplexes. They do not establish contraction of the resulting fibres.

The missing assertion is still:

\[
\text{For every finite strong-Steiner weak presentation }\widetilde P,
\quad
W(\widetilde P)\longrightarrow F(P)
\text{ has all prescribed-boundary lifts.}
\]

In particular, the pullback theorem does not prove preservation under adjoining a generator: adjoining a generator is a pushout operation, and no stability theorem for that operation has been established here. The higher comparisons needed to normalize terms involving the new generator remain unconstructed.

Thus the partial-cylinder hypothesis is now absorbed into the strong-Steiner hypothesis, and the positive-\(2\)-polygraph case has an exact all-dimensional reduction to it. **The contraction required to resolve Question 1, and hence the requested full resolution, remains unproved in this work.**

# Followup 4

**I have not obtained a full resolution of Question 1 or Question 3, or a counterexample in the requested classes.** The additional work gives an exact, all-dimensional description of the pullback over a Steiner generator. It isolates a specific attachment lemma that remains unproved.

## 1. An exact description over one Steiner generator

Write \(W\Gamma=\operatorname{Free}(\Gamma)\). Suppose
\[
\Gamma=(\Lambda,z:a\to b),
\qquad \dim z=m\ge 1,
\]
is the atom polygraph of a strongly loop-free unital Steiner complex, and \(z\) is a top-dimensional generator.

Let \(\mathbb D^m\) denote the **strict** \(m\)-globe, with top generator \(d\), and let
\[
j:\mathbb D^m\longrightarrow F(\Gamma)
\]
select \(\pi(z)\). The lower generators of \(\mathbb D^m\) are sent to the entire iterated faces of \(\pi(z)\); these faces can be composite.

Form pullbacks in CaTT models:
\[
E_z=W\Gamma\times_{F(\Gamma)}\mathbb D^m,
\qquad
E_{\partial z}=E_z\times_{\mathbb D^m}\partial\mathbb D^m.
\]

Then there is an isomorphism of CaTT models
\[
\boxed{
E_z\cong E_{\partial z}[\widehat z],
}
\tag{1}
\]
where the right side is the free extension by the single \(m\)-cell
\[
\widehat z:(a,d^-)\longrightarrow(b,d^+).
\]

Moreover,
\[
\boxed{
E_{\partial z}
\cong
W\Lambda\times_{F(\Lambda)}\partial\mathbb D^m.
}
\tag{2}
\]

Consequently, if \(\pi_\Lambda\) is a trivial fibration, then
\[
E_{\partial z}\longrightarrow\partial\mathbb D^m
\]
is a trivial fibration.

Here \(E_{\partial z}[\widehat z]\) means a free extension of a **model**. No freeness or finiteness assertion about \(E_{\partial z}\) is needed.

### The strict lemma behind (1)

For a pasting context \(P\), write \(\operatorname{tot}_n(P)\) for its total strict composite, promoted by identities to dimension \(n\), where \(n\ge\dim P\).

**Atomic-arity lifting lemma.** Suppose
\[
\delta:F(P)\longrightarrow F(\Gamma),
\qquad
\delta(\operatorname{tot}_n(P))=1^{\,n-m}\pi(z).
\]
There is a unique strict diagram
\[
\widetilde\delta:F(P)\longrightarrow\mathbb D^m
\]
such that
\[
j\widetilde\delta=\delta,
\qquad
\widetilde\delta(\operatorname{tot}_n(P))=1^{\,n-m}d.
\tag{3}
\]

The restriction to a **globular pasting arity** is essential to the proof.

### Proof of the atomic-arity lemma

Identify \(F(\Gamma)\) with \(\nu K\). Use Steiner’s table notation
\[
c=(c_0^-,c_0^+,c_1^-,c_1^+,\ldots).
\]
The entries are nonnegative chains satisfying
\[
\partial c_{i+1}^\epsilon=c_i^+-c_i^-.
\]
For composition \(c=u\mathbin{\#_k}v\), entries above \(k\) add; the \(k\)-source comes from \(u\), and the \(k\)-target comes from \(v\). These are the defining formulas for \(\nu K\). [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

Put
\[
c=1^{\,n-m}\pi(z).
\]

First consider a strict factorization
\[
c=u\mathbin{\#_k}v.
\]

For \(i<m\), the supports of \(c_i^-\) and \(c_i^+\) are disjoint. A basis element in an iterated negative boundary precedes \(z\) in the strong order, whereas one in an iterated positive boundary follows \(z\).

If \(k<m\), then at dimension \(m\),
\[
z=u_m^\epsilon+v_m^\epsilon.
\]
Nonnegativity and the coefficient \(1\) of \(z\) put the entire top chain in one factor. Suppose it is \(u\).

Descend through \(m-1,\ldots,k+1\). At each level,
\[
u_i^\epsilon\le c_i^\epsilon,
\qquad
u_i^+-u_i^-=c_i^+-c_i^-.
\]
Disjointness of the two supports forces
\[
u_i^\epsilon=c_i^\epsilon,\qquad v_i^\epsilon=0.
\]
At level \(k\), the composition formula gives \(u_k^-=c_k^-\), and the boundary equation gives \(u_k^+=c_k^+\). Thus
\[
u=c,
\qquad
v=\text{the \(k\)-identity on }\tau_kc.
\]
The other case is symmetric.

If \(k\ge m\), the entries above \(k\) vanish in both factors. Both factors are identity promotions of their common \(k\)-face, so
\[
u=v=c.
\]

Thus a factorization of an identity on \(z\):

- below dimension \(m\), has one factor carrying \(z\), with directional units on either side;
- at or above dimension \(m\), has every factor equal to the same identity on \(z\).

This alone is insufficient. An identity on a composite face, such as \(1_{f*_0g}\), can itself be decomposed using the proper factors \(f\) and \(g\).

The globular tree prevents that decomposition from appearing in the wrong place. At the first branching depth \(k<m\), the pasting tree decomposes into an ordered list of branches, each a \((k+1)\)-fold suspension. Exactly one branch evaluates to \(c\). Earlier branches evaluate to the \(k\)-identity on \(\sigma_kc\), and later branches to the \(k\)-identity on \(\tau_kc\).

Each such suspended branch has one entire formal \(k\)-source and one entire formal \(k\)-target. Since its total is a \(k\)-identity, recursion through its compositions forces every higher label to be the appropriate identity on that entire face. Its lower labels are then forced by globularity. It cannot independently expose proper factors of the face.

Remove those unit branches and repeat on the branch carrying \(z\). Eventually the remaining arity is
\[
\Sigma^m Q.
\]
All its compositions are in directions at least \(m\), so every maximal label is an identity promotion of \(z\). All lower labels are its entire globular faces.

Replace these labels by \(d\), its formal faces, and their identities. The replacements agree along every glued boundary, giving (3). The same argument forces every label of any proposed lift, proving uniqueness. ∎

### Proof of the model isomorphism

There is a canonical model map
\[
p:E_{\partial z}[\widehat z]\longrightarrow E_z
\]
given by the inclusion on \(E_{\partial z}\) and by
\[
\widehat z\longmapsto(z,d).
\]

Construct its inverse on a cell \((t,e)\in E_z\).

Every strict cell of \(\mathbb D^m\) is either a boundary cell or an identity promotion of \(d\).

If \(e\) is a boundary cell, use the corresponding element of \(E_{\partial z}\). If \(t=z\), use \(\widehat z\). Otherwise, when \(e=1^{\,n-m}d\), write
\[
t=\operatorname{coh}_{P,C}[\gamma].
\]
Apply the atomic-arity lemma to the strict diagram \(\pi\gamma\). It gives the unique diagram \(\widetilde\delta\) into \(\mathbb D^m\). Recursively interpret the pairs
\[
\bigl(\gamma(x),\widetilde\delta(x)\bigr)
\]
and retain the same outer coherence constructor.

The recursion uses lexicographic induction on dimension and raw term size. Same-dimensional substitution entries are proper subterms. The lower-dimensional induction establishes preservation of faces and operations, so the recursively interpreted entries form a substitution with syntactically matching dependent types.

This interpretation preserves every CaTT operation:

- If its strict output belongs to the globe boundary, none of its strict inputs can use \(d\), since strict composition cannot erase that generator. The operation evaluates in \(E_{\partial z}\).
- Otherwise, uniqueness in (3) identifies its given strict input diagram with the diagram used by the recursive interpretation.

The two composites are identities: one by raw-term induction, the other by the universal property of the free extension. This proves (1).

Finally, if \((t,e)\in E_{\partial z}\), the strict image of \(t\) has support excluding \(z\). Your support lemma implies that \(t\) is literally a term of \(\Lambda\). This gives (2), and pullback stability gives the trivial-fibration assertion. ∎

## 2. The precise attachment statement still needed

The preceding theorem reduces contraction over a strict generator to the following sufficient statement.

> **Globular-boundary attachment statement.** Given a trivial fibration of CaTT models
> \[
> p:B\longrightarrow\partial\mathbb D^m
> \]
> and a chosen attaching sphere in \(B\) over the two \((m-1)\)-faces, adjoining its \(m\)-cell produces a trivial fibration
> \[
> B[\widehat z]\longrightarrow\mathbb D^m.
> \tag{G}
> \]

For the application above, it would suffice to establish (G) for the particular models \(B=E_{\partial z}\).

**I have not proved (G).** The free-extension description identifies all the terms that must be contracted, but does not construct the contractions. In particular, it does not justify treating the extension as a homotopy pushout in CaTT models.

There is also a scope limitation: even a proof of (G) would settle the pullback over \(z\) and its identities. A strict composite involving \(z\) and old generators requires a further argument. The theorem above does not identify that pullback with the pullback over a globe.

## 3. A separate all-dimensional naturality lemma

The other completed construction removes the dimension bound when the selected variables are maximal in the dependency order.

**Lemma.** Let \(P\) be a pasting context and let \(Y\subseteq\operatorname{Var}(P)\) consist of variables that occur in no other variable’s boundary. Every term over \(P\), in every dimension, has a naturality term over \(P\uparrow Y\) with its full cylindrical boundary and the prescribed strict cylinder image.

There is no restriction on
\[
\dim t-\dim y.
\]

**Proof.** Set \(R=P\uparrow Y\). Lemma B.6 of Benjamin–Markakis–Offord–Sarti–Vicary says that \(R\) is again a pasting context. Hence ordinary pasting coherence makes
\[
\pi_R:WR\longrightarrow F(R)
\]
a trivial fibration in every dimension. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

There is a strict quotient
\[
q:I\otimes F(P)\longrightarrow F(R)
\]
that retains the two copies and connector for each selected variable, identifies the copies of each unselected variable, and sends its connector to an identity. The boundary equations are preserved because no unselected variable has a selected variable in its boundary.

For a strict cell \(c\), let
\[
C(c)=q([1]\otimes c).
\]

Now choose \(t^\uparrow\) by induction on \(\dim t\). Make each choice once for each raw term, so that equal iterated faces receive equal choices. The already constructed naturality terms of the proper faces of \(t\) determine the two **fully whiskered** boundary terms \(a_t,b_t\), using the formulas in §1.3 of your question. They are parallel, and induction gives
\[
\pi_R(a_t)=\sigma C(\pi_Pt),
\qquad
\pi_R(b_t)=\tau C(\pi_Pt).
\]
The trivial fibration \(\pi_R\) supplies
\[
t^\uparrow:a_t\longrightarrow b_t,
\qquad
\pi_R(t^\uparrow)=C(\pi_Pt).
\]

Selected variables use their prescribed connectors; unaffected terms use identities. Once the lower boundary choices are fixed, parallel choices with equal strict image admit higher comparisons by the same lifting property. This works in every dimension. ∎

This construction supplies comparisons after substitution of a diagram into \(R\). It does not establish compatibility under arbitrary substitutions that change the weak boundary of a selected variable.

That distinction is visible already with
\[
u=(f*_0g)*_0h,\qquad v=f*_0(g*_0h),
\qquad \alpha:u\to v,
\]
and an adjoined cell
\[
z:v\to k.
\]
Although \(\pi(\alpha)\) is an identity,
\[
\alpha*_1z:u\to k
\quad\text{and}\quad
z:v\to k
\]
have different weak boundaries. Removing the strict-identity factor requires transport of the adjoining cell. Maximal-variable naturality handles changes with the relevant boundary fixed; it does not supply all the compatibility required by that transport.

**The unresolved obligations are therefore explicit:** prove the required attachment preservation, and extend the contraction from generator images to arbitrary strict composites. Neither the fibre description nor the maximal-variable lemma establishes those obligations, so neither currently proves the requested \(RC(\infty)\) theorem.
