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

*Equivalent form (proved for every finite context).* Every strict cell of F(Γ) is the image of some term. Given that, RC_id(∞)(Γ) is equivalent to: **π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models**, and also to π_Γ being a weak equivalence (F(Γ) is gaunt: its only invertible cells are identities, since the multiset of top generators is additive). The trivial-fibration form says, i.e. for every pair of parallel (n−1)-terms u, v and every strict n-cell c : π(u) → π(v) there is an n-term t : u → v with π(t) = c. (Lift c with some boundary, then conjugate by RC connections, which have identity image.) 

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
