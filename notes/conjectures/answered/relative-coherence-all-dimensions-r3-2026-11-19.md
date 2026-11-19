# Relative coherence in CaTT in every dimension: free weak ω-categories are strict exactly on homotopical computads

*A self-contained problem. It assumes familiarity with globular weak ω-categories, strict ω-categories, polygraphs (computads) and Steiner complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** One theorem valid in every dimension: the exact class of finite computads on which the free weak ω-category is strict (in the sense of §1.2), ideally "exactly the homotopical ones". Individual new cases (one more context, one more dimension) are not useful to us. Several exact reductions are known (§3, items 9–14), and the higher-bubble obstruction now holds in every dimension (item 21). The exact-class question remains for bubble-free contexts.

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

All of the following are finite. The full cylinders (Y = Var(Q)), the joins, the Gray products of globes and the orientals present strongly loop-free Steiner complexes (Steiner, *Omega-categories and chain complexes*, HHA 2004; Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*), so F(Γ) = ν(K) has cells determined by their supports. The partial cylinders (Y ≠ Var(Q)) also present strongly loop-free unital Steiner complexes (§3 item 9), and they are positive in every dimension (the source of x↑ has x⁻ as a factor and its target has x⁺).

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

RC is the single missing ingredient in several constructions in CaTT: lax naturality of every coherence with respect to every up-closed set of its variables (equivalently a lax cylinder Γ ⊗ D¹ for every context Γ); composites, unique up to higher cells, for non-globular pasting diagrams (Gray products of globes, joins); cones over every coherence; and the comparison of the free CaTT model on a computad with its strict free ω-category, which is the unit condition in comparing CaTT models with (∞,ω)-categories.

## 3. What is known

1. **RC(1) and RC(2) hold in every context.** For 2-terms: normalise to vertical composites of whiskered 2-variables; two composites with the same strict image are related by exchange moves (Ara–Burroni–Guiraud–Lafont–Métayer, *Polygraphs*, arXiv 2312.00429, §4.1), and each move is one coherence.
2. **Support lemma.** supp(π t) = supp(t) in every context, and if t has no variable of dimension dim t in its support then supp(t) = supp(σt) = supp(τt). Parallel terms whose image is an identity on a cell w are joined by one coherence over supp(w) whenever supp(w) is a pasting context. For a pasting context P, π_P is a trivial fibration (this is the coherence and composition rule).
3. **RC(3) is known** for the lax square, the triangle, every cylinder Q↑Y, the 2 × 2 and 2 × 3 grids, the Gray cube D¹ ⊗ D¹ ⊗ D¹, and joins over vertical chains of 2-discs. Each proof is a hand-built normalisation for one context; in each, RC(n+1) needed a separately constructed coherence of the normalisation one dimension up.
4. **Adjoining top generators in dimension 3.** If Λ has dimension ≤ 2 and an acyclic generating 1-graph, and Γ adds 3-generators between parallel 2-terms of Λ, then RC(3)(Γ) ⟺ RC(3)(Λ) (using depth-1 naturality, Benjamin–Markakis–Offord–Sarti–Vicary, arXiv 2501.11620, Thm 3.1). In dimension 4 only a conditional version (assuming RC(3) and RC(4) for Λ) is known.
5. **Exchange combinatorics in dimension 2 are settled.** For a 2-dimensional context with an acyclic generating 1-graph and non-empty boundary paths, the 2-paths representing a strict 2-cell c are the linear extensions of an event poset, and the graph of exchange moves with squares and hexagons as 2-cells is simply connected; squares and hexagons are single coherences.
6. **Loops obstruct.** In Γ = (x; a : 1_x ⇒ 1_x) the Eckmann–Hilton 3-cell a ∗₀ a ⇛ a ∗₀ a and the identity are parallel with equal strict image, and no 4-term joins them (the weak free object groupoidifies to S², the strict one B²ℕ to K(ℤ, 2), and π₃(S²) ≠ 0).
7. **Gaunt targets.** F(Γ) is gaunt for every finite Γ (generator counts), so an FHM ω-weak equivalence into F(Γ) is a trivial fibration. RC_id(∞)(Γ) ⟺ π_Γ is a trivial fibration ⟺ π_Γ is a weak equivalence.
8. **Homotopical computads.** Γ is *homotopical* when the comparison from the free (∞,ω)-category on Γ (generators attached by homotopy pushouts) to F(Γ) is an equivalence. Strongly loop-free Steiner complexes with unital basis, and regular directed complexes with frame-acyclic molecules, are homotopical (Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242, Thm 3.17). **A finite 2-polygraph is homotopical if and only if F(Γ) has no bubble** (no non-identity 2-cell 1_x ⇒ 1_x); in particular every 2-polygraph whose 2-generators all have non-empty target (or all non-empty source) is homotopical, loops and cycles in the 1-graph allowed. Bubble-freeness is undecidable. For a homotopical context, RC_id(∞)(Γ) is equivalent to the unit of the realization adjunction between CaTT models and (∞,ω)-categories being a weak equivalence at the free CaTT model on Γ.
9. **Partial cylinders are strong Steiner.** For Y ⊆ Var(Q) up-closed, the complex K_Y obtained from the Steiner tensor I ⊗ λQ by identifying c⁻ = c⁺ and killing Ic for c ∉ Y is strongly loop-free and unital, with ∂⁻-iterates (∂⁻)^j Ix = (σ^{j−1}x)⁻ + I(τ^j x), (∂⁺)^j Ix = (τ^{j−1}x)⁺ + I(σ^j x) (omitted terms zero); so F(Q↑Y) ≅ ν(K_Y).
10. **Cartesian strictification.** Call Γ *positive* if every generator of dimension ≥ 2 of its polygraph has non-identity source and target. For every generator-preserving map f : Δ → Γ of positive CaTT contexts (variables to variables, attaching terms preserved), the square Free(Δ) → Free(Γ) over F(Δ) → F(Γ) is a pullback in every dimension: a term t of Γ and a strict cell d of F(Δ) over π(t) have exactly one lift. (Proof: Henry's theorem that composition is cartesian on positive polygraphs, *Non-unital polygraphs form a presheaf category*, Cor. 2.3.13, 2.4.9, plus induction on terms.)
11. **Reduction to polyplexes.** For a strict cell c of F(Γ), Γ positive, let P_c → Γ be its generic (Henry) polyplex, with the uniquely lifted weak attaching terms. Then π_Γ is a trivial fibration iff every π_{P_c} is; the same holds for RC(n) and RC_id(n) for each n. Positive 2-polyplexes are strong Steiner, so **RC(n) for every finite positive context of dimension ≤ 2 is equivalent to RC(n) for every finite strong-Steiner context of dimension ≤ 2** (no hypothesis on the 1-graph).
12. **The fibre over one generator.** If Γ = (Λ, z : a → b) is a strong Steiner atom polygraph with z of top dimension m, then Free(Γ) ×_{F(Γ)} 𝔻^m is the free extension, by one m-cell, of Free(Λ) ×_{F(Λ)} ∂𝔻^m (𝔻^m the strict m-globe mapped onto π(z)). So the trivial-fibration property over the cell π(z) would follow from: *adjoining an m-cell to a trivial fibration B → ∂𝔻^m, along an attaching sphere over the two faces, gives a trivial fibration B[ẑ] → 𝔻^m.* That statement is unproved, and it does not cover strict composites of z with other generators.
13. **Arity lemma.** If a coherence coh_{P,A}[γ] has a substituted strict boundary using a top generator z exactly once, the variables of P labelled by terms involving z form one suspended subtree Σ^m Q of P's Batanin tree.
14. **Maximal variables.** If Y ⊆ Var(P) consists of variables occurring in no other variable's boundary, P↑Y is a pasting context, and every term over P (any dimension) has a naturality term over P↑Y with its full cylinder boundary. This does not give compatibility under substitutions that change a selected variable's boundary.
15. **Not counterexamples.** Chanavat's 4-dimensional regular directed complex (arXiv 2509.26563, Comment 2.67) has a polygraph Q whose strict free category differs from the "stricter" one, but the extra equations appear only in Q → r^>Q, so they do not give equal strict images in F(Q). Benjamin–Markakis's hom-computads (hom weak ω-categories of free computads are free) do not transport π: for (x), the hom computad has distinct 0-cells id_x and id_x ∗₀ id_x, while Hom_{F(x)}(x, x) has one.
16. **A related open conjecture.** Dean (*Globular multicategories with homomorphism types*, thesis, Thm 5.4.0.1) proves an all-dimensional acyclic-fibration strictification for fibrational homomorphism types with a strict computation law; the weak analogue is his Conj. 5.4.0.9. No equivalence with RC is known.

17. **Two-dimensional bubbles obstruct RC.** Let Λ be a finite context of dimension ≤ 2 such that F(Λ) has a non-identity 2-cell c : 1_x ⇒ 1_x. Then there are parallel 3-terms T, T′ with π(T) = π(T′) and no 4-term T → T′ at all, so RC(3)(Λ) fails. Proof:
    - Choose a 2-term U with π(U) = c, and correct its boundaries by coherences over the context (x) to get a : 1_x ⇒ 1_x literally, with π(a) = c.
    - Take T = eh(a, a), the Eckmann–Hilton 3-term a ∗₁ a → a ∗₁ a (Benjamin–Markakis, arXiv 2402.01611, §6.1), and T′ = 1_{a∗₁a}.
    - Interpret Λ in the double delooping 𝒢 of the strict braided monoidal groupoid with objects ℕ, End(p) = ℤ, ⊗ = + and braiding β_{p,q} = pq. Every 1-cell goes to the unique 1-cell, and every 2-generator to 1.
    - 𝒢 is a Gray category, so it is an algebra of the Gray-category 3-operad. That operad is contractible with top-dimensional uniqueness (Batanin–Cisinski–Weber, arXiv 1209.2776, Ex. 3.6, §4.5, Ex. 5.7), and extended by identities it is a CaTT model with only identity 4-cells.
    - There, [[T]] = ±N² and [[T′]] = 0, where N > 0 is the number of 2-generators in c.
18. **Heredity.** If Δ ⊆ Γ is dependency-closed, RC_id(n)(Γ) ⇒ RC_id(n)(Δ): an identity-image filler H has supp(H) = supp(πH) ⊆ Var(Δ), by item 2. With item 17: if F(Γ_{≤2}) has a bubble, then RC_id(3)(Γ) fails, whatever the higher generators of Γ. For finite contexts of dimension ≤ 2: RC_id(∞) ⇒ RC(3) ⇒ bubble-free ⇔ homotopical.
19. **Higher endo-cells obstruct homotopicality.** If F(Γ) has a non-identity n-cell q : 1^{n−1−k}_c ⇒ 1^{n−1−k}_c (0 ≤ k ≤ n − 2, c a k-cell), then Γ is not homotopical. Proof: the n-skeleton inclusion is discrete Conduché, so homotopicality passes to Γ_{≤n}. Counting n-generators gives F(Γ_{≤n}) → Bⁿℤ, and q gives Σ^{n−2}B²ℕ → F(Γ_{≤n}). Steenrod powers then detect nonzero mod-p cohomology of the groupoidification in unboundedly many degrees, while the free cellular n-skeleton has dimension n. The converse ("no such endo-cell ⇒ homotopical") is proved in dimension 2 (item 8) and for positive-to-one polygraphs in every dimension, and is open in general.
20. **Why the dimension-2 argument does not directly extend.** For an n-cell q on 1_b with b an (n−2)-cell, the analogous detecting model would be an n-fold delooping of a braided-type monoidal groupoid, i.e. an E_n structure. For n ≥ 3 that forces a symmetry (β² = 1), so the obvious ℤ/2-valued version β_{p,q} = pq mod 2 detects only odd generator counts, and no explicit CaTT model of that shape (a weak (n+1)-category with one cell below dimension n − 1) is known to us.

21. **Higher bubbles obstruct relative coherence in every dimension.** An n-cell on an identity with positive n-generator count prevents π from being a trivial fibration. In a CaTT model of lists and colour-preserving bijections, the suspended Eckmann–Hilton term exchanges two nonempty blocks, while the identity fixes their positions. This includes composite bubbles of even weight and bubbles over positive-dimensional cells. [Proof](higher-bubbles-relative-coherence-2026-11-19.md)

## 4. Questions

**Question 1 (main: the exact class).** Prove that for every finite CaTT context Γ,

> RC_id(∞)(Γ)  ⟺  Γ is homotopical,

equivalently (item 7) that π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models exactly when the polygraph of Γ is homotopical. Or give a counterexample to either direction with a separating invariant.

- **(⇐, the contraction).** This is the main content. By item 11 the positive case reduces to generic positive polyplexes, and by item 12 the strong-Steiner case reduces to one attachment statement plus composites. Routes that would do:
  - (a) prove the attachment statement of item 12 for arbitrary trivial fibrations B → ∂𝔻^m of CaTT models (a homotopy-pushout property of free cell extensions of CaTT models), and extend it from a single generator to strict composites;
  - (b) describe the fibre of π_Γ over each strict cell as a CaTT-definable object and show it is contractible;
  - (c) a relative Guiraud–Malbos normalisation strategy towards the strict cells of F(Γ), producing all higher comparisons at once;
  - (d) an equivalence with Dean's Conj. 5.4.0.9 or another named open statement.
- **(⇒, the remaining necessity question).** Item 21 settles the obstruction for higher endo-cells. It remains to prove that a bubble-free context satisfying RC_id(∞) is homotopical, or exhibit a counterexample. Sufficiency of bubble-freeness for homotopicality would imply this direction.

**Question 2 (fallback for (⇐), still every dimension).** If Question 1(⇐) is out of reach, prove RC_id(∞) for every finite context that is positive in every dimension, or at least for every finite strong-Steiner context, and give the counterexample that separates the classes if one exists.

**Question 3 (fallback, every n).** Prove RC_id(n) for every n for every finite 2-dimensional context that is bubble-free (equivalently homotopical, item 8). By item 11, for positive ones it suffices to treat finite strong-Steiner 2-dimensional contexts. Together with an extension theorem for adjoining generators of any dimension ≥ 3 (preserving RC_id(n) for all n), this answers Question 1(⇐) for every context whose higher generators sit over such a 2-skeleton.

## 5. What counts as a solution

A proof of either direction of Question 1, of Question 2, or of Question 3 with the extension theorem; a counterexample in one of the named classes, with a proof that no connecting term exists (for example an invariant of a model); an equivalence with a named open problem; or a published reference. An existence proof of the connecting cells is enough, provided it is a proof about CaTT terms or CaTT models.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Batanin–Cisinski–Weber, *Multitensor lifting and strictly unital higher category theory*, arXiv 1209.2776 (Ex. 3.6, Ex. 5.7: the Gray-category operad is contractible).
- Benjamin–Markakis, arXiv 2402.01611, §6.1 (the Eckmann–Hilton term).

- Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (Thm 3.17, Cors. 3.38–3.39, Comment 3.40) and arXiv 2509.26563.
- Henry, *Non-unital polygraphs form a presheaf category*, Higher Structures 3(1) (2019); Henry, *Regular polygraphs and the Simpson conjecture*, arXiv 1807.02627.
- Guiraud–Malbos, *Higher-dimensional normalisation strategies for acyclicity*, Adv. Math. 231 (2012).
- Benjamin–Markakis–Offord–Sarti–Vicary, arXiv 2501.11620 (naturality at depth ≤ 1; Lemma B.6).
- Benjamin–Markakis, arXiv 2402.01611 and *Hom ω-categories of a computad are free*, J. London Math. Soc. (2025).
- Fujii–Hoshino–Maehara, arXiv 2511.09849 (ω-weak equivalences and trivial fibrations).
- Dean, thesis (globular multicategories with homomorphism types), Conj. 5.4.0.9.
- Delpeuch–Vicary, arXiv 1804.07832; Heidemann, arXiv 2411.04870 (used for the 2-dimensional homotopicality theorem of item 8).
- No published comparison of free weak ω-categories with free strict ones on non-globular computads was found.


# Researcher Response 1

## Higher bubbles obstruct relative coherence in CaTT

A nonidentity cell on an iterated identity obstructs relative coherence in every dimension. The obstruction exchanges two copies of the cell. A CaTT model that remembers the individual positions in a list distinguishes this exchange from the identity, including when each copy has even length.

**Theorem.** Let Γ be a finite CaTT context, let π be strict interpretation, and suppose that its free strict ω-category contains an n-cell
\[
q:1_b\longrightarrow 1_b,\qquad q\ne 1_{1_b},\quad n\ge2,
\]
where b is an (n−2)-cell, possibly itself an iterated identity. Then π is not a globular trivial fibration. Hence Γ fails RC_id(∞) by §3, item 7.

The literal boundary in the hypothesis matters. We first construct a model in which the suspended Eckmann–Hilton operation on a nonempty list acts nontrivially. We then use the assumed lifting property to obtain the precise weak boundary required by that operation.

### A CaTT model of lists and bijections

Fix n and a set C of colours. Below dimension n take one cell in each dimension. An n-cell is a finite list in C. An (n+1)-cell between lists is a bijection of their position sets preserving colours. Above dimension n+1 take only iterated identities. We will interpret CaTT in these globular sets, naturally in recolourings C → C′. In particular forgetting colours keeps the underlying bijection. This last point lets us use different colours for the two inputs of a term even if their uncoloured values agree.

Here are two facts about a globular pasting context P. They concern the **generic** P, before substitution can identify any variables. Truncate its Batanin tree at height n, writing P′ for the resulting globular shape. The projection of P into the free strict category on P′ identifies n-variables joined by (n+1)-variables and sends all higher variables to identities. Call each n-variable of P′ a slot.

1. For any strict n-cell of P, its list of n-generator occurrences projects injectively to the slots, and the two n-faces of a higher cell use exactly the same slots. For injectivity, write a tree as a string of suspended subtrees. A strict positive-dimensional cell runs over a subinterval of that string and is a tuple of cells, one in each traversed factor. In the iterated hom description this lowers the dimension by one. The factors have disjoint slots. At dimension zero a cell selects a single vertex, which projects to the sole vertex of the height-zero truncation. Identities contribute no top occurrences in positive dimension. This also proves the assertion for subintervals of length zero. Equality of the two projected n-faces follows because the projected higher cell is an identity.
2. Given a labelling of P in the displayed globular set, one can give **distinct auxiliary colours** to all positions at one chosen n-variable per slot and propagate them to all n-variables of that slot. Each generating bijection then preserves auxiliary colours. To see this, use the same string-of-suspensions decomposition while n is positive. Its factors meet only at vertices and impose independent conditions on the positions. At n = 0 the vertices to be labelled form a string. Between two consecutive vertices each arrow label is a bijection. These bijections agree: the arrows are the vertices of the intervening subtree, whose 1-skeleton is connected, and each edge of that subtree is labelled by a 2-cell forcing equality of the parallel bijections. Thus one transports along an ordinary string of bijections, backwards using inverses when necessary. A one-vertex string entails no transport. Using disjoint sets of auxiliary colours for different slots proves the claim. Pairing each auxiliary colour with the original colour gives a labelling which recolours to the original one.

We define the interpretation by recursion on the CaTT coherence heads. Variables are projections. A head applied to a substitution acts on its evaluated arguments, so the ordinary substitution equation holds by construction. Strict interpretation in the generic globular arity tells us which strict cell the head denotes. These are the usual CaTT syntax and strict soundness used in the problem. [Finster–Mimram](https://arxiv.org/abs/1706.02866)

- Below dimension n the value is forced. For a head of dimension n, order the n-generator occurrences of its generic strict cell and concatenate the corresponding input lists in that order. The empty collection gives the empty list. For the binary vertical composite use first-input-then-second-input order. All choices are made on the syntax of the head, independently of the labels. In any term, substitution consequently concatenates one input block per occurrence in its strict expression: occurrence counts add under strict composition and are zero on identities.
- For an (n+1)-head evaluate its two boundary terms on the labelling with auxiliary colours from fact 2. By fact 1 and the concatenation rule, each output list contains exactly once each position from the common occupied slots. Match equal auxiliary colours. This is a bijection between the original lists and preserves their original colours. Renaming the auxiliary colours or changing the chosen representative of a slot leaves every match the same, since propagation along bijections identifies the same pairs of positions. The result commutes with every recolouring, including passage to one colour.
- For an (n+2)-head the two parallel (n+1)-terms in its type evaluate to bijections with the same endpoints. Evaluate them first on the labelling with auxiliary colours. Both preserve colours, and the common source and target have no repeated auxiliary colours by fact 1. There is at most one such bijection. Forgetting the auxiliary colours therefore gives equal boundary bijections in the original labelling, so the identity on that bijection has the required type. In still higher dimensions parallel identities coincide. This supplies every head, including heads applied to substitutions that repeat an argument.

In particular the interpretation of the identity on a list is the identity bijection: in its generic disc both boundary lists are the same ordered list of distinct auxiliary colours. This constructs a set-valued CaTT model for every palette.

As a finite check on the two tree arguments, quotient the (n+1)-arrows of a shape by the parallel pairs identified by its (n+2)-generators. Each connected component on n-variables must be a directed path. Independently close the atomic Steiner tableaux under composition, retaining generator multiplicities, and check injectivity into those components for every top row. The checker covers 309,677 strict cells in all 2,056 trees with at most eight edges (run `python3 tools/relative_coherence_slots.py 8` from the repository root). The dimension-independent arguments are facts 1 and 2 above. [Reproduce the check](../../../tools/relative_coherence_slots.py)

### The suspended Eckmann–Hilton operation

Benjamin and Markakis construct a term on two n-cells a, b with literal source and target the same identity on an (n−2)-cell. Its type is
\[
\mathrm{eh}_{n-2}(a,b): a*_{n-1}b\longrightarrow b*_{n-1}a.
\]
The generic term and its suspensions are given in [Benjamin–Markakis, §§6.1 and 6.3](https://arxiv.org/pdf/2402.01611#page=41).

Give a and b lists of lengths r and s with r+s pairwise distinct colours. Their lower-dimensional boundaries have the unique values required. The source list consists of the first block followed by the second and the target consists of the second followed by the first. The only colour-preserving bijection is the block exchange. Recolour to a singleton. By naturality the same operation on lengths r and s has exactly that underlying permutation. In particular on two copies of length m > 0 the first position moves to position m+1. This detects even m as well as odd m.

### Applying the obstruction to a composite strict cell

Work first in the n-skeleton Λ of Γ. If π for Γ is a trivial fibration then RC_id holds in every dimension in Λ by heredity (item 18 of the problem). Hence π for Λ is also a trivial fibration by item 7. The n-cell q and its boundary already belong to this skeleton.

Lift b to a weak term d by globular boundary lifting, lifting its faces first. Form the weak identity i on d. Since π(i) = 1_b, another boundary lift gives a term a **of literal type** i → i with π(a) = q. This use of the trivial-fibration hypothesis avoids any assumption that a particular expression for q lifts with the desired endpoints.

Interpret Λ in the one-colour model, sending each n-generator to a list of length one. All lower generators have forced values, so these assignments respect their types. The length of any n-term is the number of n-generator occurrences in its strict image. This holds on variables and follows on heads from concatenation and substitution. A strict n-cell expressed without n-generators is an identity, by induction on strict composition. Thus a has length m > 0, also when q is composite.

Set p = a *_{n−1} a. The weak (n+1)-terms eh_{n−2}(a,a) and 1_p are parallel and have the same strict image, because the strict category on Λ has only identities above n. A globular trivial fibration must lift the identity on that common image between these specified terms. In the list model the first term exchanges two length-m blocks and the second fixes all 2m positions. There is no (n+2)-cell between different bijections. This contradicts the required lift and proves the theorem.

**Scope.** This settles the higher-endo-cell obstruction in Question 1 for every dimension, base cell and positive generator count. RC_id(∞) and homotopicality therefore both imply bubble-freeness. The question whether those two properties coincide on bubble-free contexts remains open.

### A counterexample to unrestricted generator extension in Question 3

Take the globular 2-disc Δ with objects x,y, arrows f,g : x → y and a 2-generator β : f ⇒ g. This is a bubble-free 2-dimensional pasting context, so it satisfies RC_id in all dimensions by item 2. Adjoin a single 3-generator α : 1_f ⇒ 1_f, using the same weak identity on f at both ends. Call the resulting context Γ. The generator has strict weight one. Here the obstruction gives a specific failure of RC(4), without any lifting assumption. Put p = α *₂ α. The 4-terms eh₁(α,α) and 1_p have literal boundary p → p and the same strict image. Interpret Γ in the one-colour model above with n = 3 and α the one-position list. The two terms act on two positions by the transposition and the identity respectively. Every 5-cell in the model is an identity. Hence no 5-term connects this pair.

The same construction works in each attachment dimension m ≥ 3. For m > 3 take b to be the (m−2)-cell obtained by iterating the identity on f, and adjoin α : 1_b ⇒ 1_b. The one-colour model in dimension m separates eh_{m−2}(α,α) from the identity, so RC(m+1) fails. Thus the unrestricted preservation assertion in Question 3 is false even for one attachment to a globular 2-disc. This leaves the question for the 2-dimensional base itself, and for extensions required to be homotopical.

### An exact lifting criterion for the remaining necessity question

Write A for the free CaTT model of Γ, C for its free strict ω-category viewed as a CaTT model, and q : KC → C for the universal computadic replacement. In dimension zero KC has a generator for each object of C. In positive dimension it has a generator for each parallel pair u,v of cells of KC one dimension below and each cell c : q(u) → q(v) in C. That generator has boundary (u,v) and image c, so q has all globular boundary lifts. [Dean–Finster–Markakis–Reutter–Vicary, §5](https://arxiv.org/abs/2208.08719) and [Markakis, §5](https://arxiv.org/abs/2303.11978)

There is a specified generator inclusion i : A → KC over C. Inductively send each generator x to the generator labelled by π(x) and the already embedded boundary of x. Different generators of the same dimension have different strict images, as witnessed by their top-generator counts. Thus this is injective on generators. Its image is closed under boundaries by construction, so KC is obtained from A by freely attaching its remaining generators in dimension order.

**Split criterion.** RC_id(∞)(Γ) holds exactly when there is a strict CaTT map r : KC → A with ri = id_A and πr = q. Indeed, if π has globular boundary lifting, extend the identity of A across each remaining generator of KC by lifting its label against its already assigned boundary. This gives r. Conversely, given parallel cells of A and a strict cell c to lift, apply i to the boundary, use q to lift c, then apply r. Its boundary is the prescribed pair since ri = id_A, and its image is c since πr = q. The same argument in dimension zero uses the empty boundary.

This has a consequence for the *inductive* notion of homotopicality in Question 1. Write L for the ordinary realization followed by passage to the inductive (∞,ω)-category. Let e : LA → NC and d : LKC → NC be induced by π and q via the realization adjunction, using the canonical algebraic structure on the nerve of the gaunt C. The cellular description of realization identifies e with the comparison defining homotopicality. Naturality gives d ∘ Li = e, and, whenever the split criterion holds, e ∘ Lr = d and Lr ∘ Li = id. Thus e is a retract of d over NC. In particular, reconstruction at this single strict target (d an equivalence) implies the necessity direction for Γ. [Realization and identification of e, §A.4](../../models-comparison-extensions.md) and [definition of the reconstruction map, Known (III)](../outbox/catt-models-unit-condition-r4.md)

More precisely, under RC_id(∞)(Γ), homotopicality is equivalent to the existence of a morphism s : NC → LKC satisfying d ∘ s ≃ id and s ∘ e ≃ Li. If e is an equivalence, take s = Li ∘ e⁻¹. Conversely Lr ∘ s is a two-sided inverse for e by the displayed identities. A section of d alone gives only the right inverse. The unresolved geometric step is to produce the section with its specified behaviour on LA. The algebraic lifts defining r prove the split criterion but do not provide that section.

# Verification (2026-11-19)

Status: **verified**. The response proves three things. Each was checked independently against the problem as sent.

**1. Higher bubbles obstruct RC_id(∞) in every dimension (Q1 ⇒ for endo-cells): correct.**
- *The list model is a CaTT model.* Below dimension n there is one cell, so every head of dimension < n is forced, and every n-head has a well-typed value (any fixed order of the generic cell's n-generator occurrences will do). For an (n+1)-head with boundary terms u, v over P, the two generic strict images project to the same cell of F(P′), and each slot occurs at most once (fact 1). The auxiliary colouring of fact 2 then gives a well-defined colour-preserving bijection. Fact 2's consistency uses only that an (n+2)-variable forces its two boundary bijections to be equal, which holds because the model has no other (n+2)-cells. For an (n+2)-head, both boundary bijections preserve auxiliary colours between lists without repeats, so they are equal, and naturality in recolouring carries this to the original labelling. Heads above n+2 are identities. Substitution holds by construction. "Output = one input block per occurrence in the strict image" holds by induction, since occurrence counts are additive under strict composition and zero on identities. This is the only induction the argument needs.
- *Fact 1 reproduced.* `python3 tools/relative_coherence_slots.py 8` gives "2056 trees, 309677 strict cells: transport paths and injectivity on occupied slots verified" (2 s). The paper argument via the string-of-suspensions decomposition is also correct.
- *The separation.* With pairwise distinct colours, the only colour-preserving bijection from a·b to b·a is the block exchange. By naturality, recolouring to one colour keeps that permutation, so eh(a, a) acts as the exchange of two length-m blocks, which is not the identity for m > 0. This is how the model avoids the β² = 1 problem of the earlier note (item 20): the sign is replaced by a permutation, which detects every m > 0 and not only odd m.
- *The reduction.* Heredity (item 18) passes the trivial-fibration property to the n-skeleton Λ. Boundary lifting then gives a with literal type i → i, which is the boundary eh needs, and π(a) = q. The length of a is the n-generator count of q, which is > 0 because a cell with no n-generators is an identity. eh(a, a) and 1_{a∗a} are parallel and have the same image, since F(Λ) has only identity (n+1)-cells. So a trivial fibration would give an (n+2)-cell between distinct bijections, which is a contradiction.
- Consistent with item 17 at n = 2, and with HPOL's Theorem N (row B24): endo-cells obstruct both RC_id(∞) and homotopicality. So on any context that has one, both properties fail and Q1 holds there trivially.

**2. Q3's unrestricted extension theorem is false: correct.** Adjoining α : 1_f ⇒ 1_f to the 2-disc creates a strict 3-cell on an identity of the 1-cell f, so item 1 applies directly with n = 3. The direct argument is also right: eh₁(α, α) and 1_{α∗₂α} are parallel 4-terms with identity image (F(Γ) has nothing above dimension 3). In the n = 3 model they are the transposition and the identity, and the model's 5-cells are identities. The same holds for every m ≥ 3. The extended context is not homotopical (item 19), so this does not touch the extension theorem restricted to homotopical (or bubble-free) attachments. That restricted version is what Q3 should ask.

**3. Split criterion and retract: correct.**
- *i is a generator inclusion.* Different generators of one dimension have different strict images (each image contains its own generator exactly once), so i is injective on generators. Its image is closed under boundaries. KC is A with the remaining generators attached in dimension order.
- *RC_id(∞) ⟺ there is a retraction r with ri = id and πr = q.* (⇒): extend the identity generator by generator, lifting each label against the boundary already assigned, which uses item 7. (⇐): lift through q and push forward by r.
- *e is a retract of d over NC.* d∘Li = e (from qi = π), e∘Lr = d (from πr = q), and Lr∘Li = id. Retracts of equivalences are equivalences, so RC_id(∞)(Γ) together with "d is an equivalence at C = F(Γ)" implies Γ is homotopical. The characterisation through a section s with d∘s ≃ id and s∘e ≃ Li was checked in both directions.
- Two inputs are taken from the project's own notes and not re-proved here: identifying e with the homotopicality comparison (`models-comparison-extensions.md` §A.4) and the definition of the reconstruction map (`catt-models-unit-condition-r4.md`, Known (III)). Whether d is an equivalence for free strict targets is open. It is a special case of the unit condition (E11, UCL).

**What is left open.** (⇐), the contraction, is untouched. (⇒) on bubble-free contexts now reduces to reconstruction at the single gaunt target C = F(Γ), or to producing the section s. Q2 is untouched. Q3 must be restated for homotopical attachments. Follow-up: [`relative-coherence-all-dimensions-r4-2026-11-19.md`](relative-coherence-all-dimensions-r4-2026-11-19.md) (answered).

# Researcher Response 2

## Finite generator dimension and the realization unit

Let Γ have generator dimension at most D, let A be its free CaTT model and let C = F(Γ). Write X for the inductive (∞,ω)-category presented by the realization of A, and e : X → NC for its comparison. Write Q for coinductive completion. Then **e is an equivalence exactly when Qe is an equivalence**. In particular, on a context satisfying RC_id(∞), an equivalence after coinductive completion of the reconstruction map LKC → NC in Response 1 already suffices for inductive homotopicality.

Indeed, the fully faithful inclusion of (∞,D)-categories into inductive (∞,ω)-categories is left adjoint to the D-core, so it preserves colimits. Every globe of dimension at most D and its boundary belong to its image. Starting with the empty category and taking the homotopy pushouts that attach the generators of Γ therefore constructs X inside that image. The nerve NC lies there too, since C has only identities above D. Every (∞,D)-category is coinductively complete. The units X → QX and NC → QNC are thus equivalences, which proves the assertion for e. For the consequence, apply Q to the retract in Response 1 and use closure of equivalences under retracts. No dimension bound on KC is needed. [Ozornova–Rovelli–Walde, Lemmas 4.4 and 5.22, Definition 5.25 and Corollary 5.31](https://arxiv.org/html/2603.11005v1)

This gives a test for a counterexample to either implication. Write η for the unit on A and W for the FHM weak equivalences. The equality S₀(e)η = π, the comparison test S₀(e) ∈ W iff Qe is an equivalence, and two-out-of-three give the following table. [Comparison test and unit identity, §A.4](../../models-comparison-extensions.md)

| Assumption on Γ | Equivalent conditions |
| --- | --- |
| Γ satisfies RC_id(∞) | Γ is homotopical iff η ∈ W. |
| Γ is homotopical | Γ satisfies RC_id(∞) iff η ∈ W. |

In the first row a failure has a specific witness. By the definition of essential ω-surjectivity, either some object of the semantic CaTT model lacks an algebraic representative up to equivalence, or there are parallel terms a,b of A and a semantic cell z : ηa → ηb which is inequivalent to ηt for **every** t : a → b. In the latter case the strict image S₀(e)(z) already has a lift between a and b by RC_id(∞). The missing assertion concerns the prescribed geometric z. The bound D on generating dimensions allows homotopy in arbitrarily high dimensions and gives no cutoff for this test. [Fujii–Hoshino–Maehara, definition of ω-weak equivalence](https://arxiv.org/abs/2406.13240)

## Simultaneous algebraic lifts of all strict simplices

Suppose π : A → C has globular boundary lifting. For a strict simplex σ : Oₙ → C, where Oₙ is Street's n-th oriental, call an algebraic lift a strict CaTT map h : K Oₙ → A with πh = σq. Here K and its counit q are the computadic replacement of Response 1. The pairs (σ,h) form a simplicial set by functoriality of K. **Forgetting h is a trivial fibration of simplicial sets onto the Street nerve of C.** In particular every compatible choice of lifts on a simplicial subset extends over the whole nerve.

To prove the boundary lifting assertion, fix σ and compatible lifts on all its proper faces. A face O(F) for a subset F of the vertices embeds in Oₙ, and the intersection of two such images is O(F ∩ G). In Steiner's tableaux for the simplex chain complex, membership means that every chain in the tableau is supported on simplices with vertices in F. This proves the intersection formula, including the empty intersection. [Steiner, *Orientals*, §3](https://arxiv.org/abs/math/0601383)

The embeddings K O(F) → K Oₙ are inclusions of subcomputads with the same intersection formula. In dimension zero this follows on vertices. Inductively a generator belongs to a face precisely when its strict label belongs to that face and its two boundary terms belong to the face subcomputad. A term belongs to a subcomputad exactly when its generating variables do, by the free syntax. These two observations establish the formula dimension by dimension. The face lifts consequently agree on every common generator and determine a single map on the subcomputad generated by all the proper faces. Freely attach the remaining generators in dimension order. For each one the assigned boundary is already parallel, and σ applied to its strict label gives a cell over that boundary. The globular lifting property of π supplies its value. Dimension zero uses the empty boundary. This proves lifting against every ∂Δ[n] → Δ[n]. Attaching the nondegenerate simplices of a simplicial inclusion in increasing dimension gives the asserted relative extension. [Dean–Finster–Markakis–Reutter–Vicary, computadic replacement](https://arxiv.org/abs/2208.08719)

These lifts solve the compatibility problem for algebraic maps out of K Oₙ. To yield the geometric section in Response 1, one would still have to interpret the lifted simplices as maps from the geometric orientals, compatibly with the prescribed map on X. Maehara's comparison identifies the strict oriental nerve as a fibrant replacement of a complicial simplex. It gives no comparison from that simplex to the realization of the CaTT computad K Oₙ. Thus neither the simplicial lifting theorem nor the finite-dimensional comparison proves Question 1. [Maehara, Theorem 2.1](https://arxiv.org/abs/2102.09736)

# Verification of Response 2 (2026-11-19)

Status: **verified**.
- *e ≃ Qe for finite generator dimension D.* The inclusion of (∞,D)-categories into inductive (∞,ω)-categories has the D-core as right adjoint, so it preserves the homotopy pushouts that build X from globes of dimension ≤ D. NC lies in (∞,D) because C has only identities above D. (∞,D)-categories are coinductively complete. So the units at X and NC are equivalences, and e is an equivalence iff Qe is. Applying Q to the retract of Response 1, "Q d_C an equivalence" suffices for RC_id(∞) ⇒ homotopical. The r4 response proves the same statement independently and shows that the inductive d_C is never an equivalence for nonempty C.
- *The table.* From S₀(e)η = π, from "S₀(e) ∈ W iff Qe is an equivalence" (§A.4, taken from the project's notes), and from 2-out-of-3 for W: given RC_id(∞) (π ∈ W), Γ is homotopical iff η ∈ W; given homotopical, RC_id(∞) iff η ∈ W. Both rows check. The witness paragraph only unpacks essential ω-surjectivity.
- *Simultaneous lifts of strict simplices.* The face suborientals satisfy O(F) ∩ O(G) = O(F ∩ G) (Steiner tableaux). By induction on dimension, K O(F) ⊆ K Oₙ are subcomputads with the same intersection formula: a generator lies in a face iff its label and its boundary do. So compatible face lifts glue on the union, and the remaining generators of K Oₙ are lifted one at a time by boundary lifting. This gives the RLP against ∂Δ[n] → Δ[n], so forgetting h is a trivial fibration onto the Street nerve. As the response says, this does not produce the geometric section s.
