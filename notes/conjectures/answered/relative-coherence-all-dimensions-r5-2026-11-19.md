# Relative coherence in CaTT in every dimension: free weak ω-categories are strict exactly on homotopical computads

*A self-contained problem. It assumes familiarity with globular weak ω-categories, strict ω-categories, polygraphs (computads) and Steiner complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** One theorem valid in every dimension: the exact class of finite computads on which the free weak ω-category is strict (in the sense of §1.2), ideally "exactly the homotopical ones". Individual new cases (one more context, one more dimension) are not useful to us. Bubbles obstruct strictness in every dimension (item 20), so the question is the comparison on bubble-free contexts. It has two halves. The first is the contraction, homotopical ⇒ strict. The second is necessity, which now reduces to one statement: the *coinductive* reconstruction map at free strict targets is an equivalence (items 22–23). The inductive reconstruction map is known to fail. Several exact reductions are known (items 9–14, 22–25).

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
20. **Higher bubbles obstruct RC_id(∞) in every dimension.** Suppose F(Γ) has an n-cell q : 1_b ⇒ 1_b, q ≠ 1, n ≥ 2, where b is an (n−2)-cell (possibly itself an iterated identity). Then π_Γ is not a trivial fibration, so RC_id(∞)(Γ) fails. Composite q of even weight and b of positive dimension are included. Proof:
    - *A list model.* Fix n and a set C of colours. Take one cell in each dimension below n, finite lists in C as n-cells, colour-preserving bijections of positions as (n+1)-cells, and identities above. This is a CaTT model, natural in recolourings. Every n-head concatenates its input lists, one block per n-generator occurrence of its generic strict cell, in a fixed order. Every (n+1)-head matches positions: give the positions in each *slot* distinct auxiliary colours, transport them along the labelled bijections, and match equal colours. A slot is a class of n-variables of the pasting context joined by (n+1)-variables. Two facts about generic pasting contexts make this well defined: each strict n-cell uses each slot at most once, and the two n-faces of a higher cell use the same slots. Both are proved by the decomposition of a Batanin tree into suspended subtrees, and checked by machine on all trees with at most 8 edges. (n+2)-heads are well defined because colour-preserving bijections between lists without repeated auxiliary colours are unique.
    - *The separation.* With distinct colours, the suspended Eckmann–Hilton term eh_{n−2}(a, b) : a ∗_{n−1} b → b ∗_{n−1} a (Benjamin–Markakis, arXiv 2402.01611, §§6.1, 6.3) must be the block exchange, and by naturality it stays the block exchange after recolouring to one colour. For a = b of length m > 0 this is not the identity.
    - *The reduction.* By heredity (item 18), pass to the n-skeleton Λ. Boundary lifting gives a with literal type 1_d → 1_d and π(a) = q. Send each n-generator to a one-element list, so a has length m = (number of n-generators in q) > 0. Then eh(a, a) and 1_{a∗a} are parallel, have the same identity image, and are separated in the model.
21. **The unrestricted extension theorem is false.** Adjoin α : 1_f ⇒ 1_f (a 3-generator on the weak identity of f) to the 2-disc (x, y; f, g : x → y; β : f ⇒ g). The 2-disc satisfies RC_id(∞) (item 2), but the extended context fails RC(4) by item 20 with n = 3. The same works in each attachment dimension m ≥ 3. So adjoining generators can preserve RC_id(∞) at best for attachments that keep the context homotopical.
22. **Split criterion and the reduction of necessity to reconstruction.** Let A = Free(Γ), let C = F(Γ) as a CaTT model, and let q : KC → C be the computadic cofibrant replacement. KC has one generator for each parallel pair (u, v) of cells of KC and each strict cell c : q(u) → q(v) (Dean–Finster–Markakis–Reutter–Vicary, arXiv 2208.08719, §5; Markakis, arXiv 2303.11978, §5). Sending each generator x of Γ to the generator labelled by π(x) and its already-embedded boundary gives a generator inclusion i : A → KC over C. KC is A with the remaining generators freely attached.
    - **RC_id(∞)(Γ) holds iff there is a strict CaTT map r : KC → A with r i = id_A and π r = q.** (⇒) extends id_A across the remaining generators by boundary lifting. (⇐) lifts through q and applies r.
    - Let L be realization from CaTT models to (∞,ω)-categories, and N the nerve. Let e : LA → NC and d : LKC → NC be induced by π and q. Then e is the comparison defining homotopicality, and d is the *reconstruction map* of the strict target C. We have d ∘ Li = e. Under the split criterion we also have e ∘ Lr = d and Lr ∘ Li = id, so **e is a retract of d over NC**. Hence RC_id(∞)(Γ) together with "d is an equivalence for C = F(Γ)" implies that Γ is homotopical. More precisely, under RC_id(∞)(Γ), Γ is homotopical iff there is s : NC → LKC with d ∘ s ≃ id and s ∘ e ≃ Li.

23. **Inductive reconstruction fails; coinductive reconstruction suffices.** With the notation of item 22, the inductive reconstruction map d_C : L(KC) → NC is **not** an equivalence for any nonempty strict C. Proof:
    - Let D be the free strict ω-category with one object p, a loop ℓ, and in each dimension k ≥ 2 one generator for each ordered parallel pair of (k−1)-cells. D is gaunt, because top-generator counts are additive, and D → 1 has boundary lifting in every dimension.
    - K1 has one object v and a loop generator u. Sending u to ℓ and to 1_p gives two maps L(K1) → ND. They restrict to different points of the discrete space Map(D¹, ND), so they lie in different components, while Map(N1, ND) is a single point. So d₁ is not an equivalence.
    - For nonempty C, 1 → C → 1 exhibits d₁ as a retract of d_C.
    
    However, D → 1 is an FHM weak equivalence, so Q(ND) ≃ 1, where Q is coinductive completion. For Γ of generator dimension ≤ m, both ends of e lie in (∞,m)-categories. That subcategory is coreflective, with the m-core as right adjoint, so it is closed under the colimits building LA, and its objects are coinductively complete (Ozornova–Rovelli–Walde, arXiv 2603.11005, Lemmas 4.4, 5.22–5.23). Hence **e is an equivalence iff Qe is**, and by the retract of item 22, **RC_id(∞)(Γ) together with Q d_{F(Γ)} being an equivalence implies that Γ is homotopical**. Equivalently, with η the unit at A and W the FHM weak equivalences: given RC_id(∞), Γ is homotopical iff η ∈ W; given homotopicality, RC_id(∞) holds iff η ∈ W.
24. **Simultaneous algebraic lifts of strict simplices.** Suppose π : A → C has globular boundary lifting. Call a strict CaTT map h : K Oₙ → A with π h = σ q an *algebraic lift* of a strict simplex σ : Oₙ → C (Oₙ is Street's oriental). The pairs (σ, h) form a simplicial set, and forgetting h is a trivial fibration onto the Street nerve of C. Proof: the face suborientals satisfy O(F) ∩ O(G) = O(F ∩ G) (Steiner's tableaux), and the subcomputads K O(F) ⊆ K Oₙ satisfy the same formula. So compatible face lifts glue, and the remaining generators lift one at a time. This does not give the geometric section s of item 22, which needs a comparison from geometric simplices to the realizations of K Oₙ.
25. **The dimension-3 exchange step reduces to a wedge lemma.** Assume (H): Γ is finite, of dimension ≤ 2, has an acyclic generating 1-graph, and every 2-generator has nonempty source and target paths. Then the 2-paths representing a strict 2-cell are exactly the linear extensions of an event poset, and exchange moves are swaps of adjacent incomparable events (item 5).
    - Under (H), a contiguous antichain of events in a 2-path spans, in its generic polyplex (item 11), a wedge A₁ ∨₀ ⋯ ∨₀ A_k of single-generator contexts glued at cut vertices. So, by the polyplex reduction, the part of RC(3) that concerns permuting such a block is exactly **the wedge lemma**: RC(3)(A₁ ∨₀ ⋯ ∨₀ A_k) follows from RC(3)(A_i) for each i.
    - For k = 2 this is known: two independent letters with a cut vertex are handled by horizontal normal forms and one interchange coherence.
    - The rest of RC(3) under (H) consists of forced-order statements: letters joined by connectors that cross their boundary blocks, whose fibres have a single linear extension. This includes a fusion statement comparing normalisers along substitution. These are of the kind already proved for cylinders and grids.
    - The smallest wedge with k = 3 is the polyplex of the hexagon triple in the 3 × 3 grid: three lax squares glued at two cut vertices. Its key ingredient is the three-factor interchange (α ∗₀ β ∗₀ γ) · (α′ ∗₀ β′ ∗₀ γ′) ⇛ (α·α′) ∗₀ (β·β′) ∗₀ (γ·γ′).

## 4. Questions

**Question 1 (main: the exact class).** Prove that for every finite CaTT context Γ,

> RC_id(∞)(Γ)  ⟺  Γ is homotopical,

equivalently (item 7) that π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models exactly when the polygraph of Γ is homotopical. Or give a counterexample to either direction with a separating invariant.

- **(⇐, the contraction).** This is the main content. By item 11 the positive case reduces to generic positive polyplexes, and by item 12 the strong-Steiner case reduces to one attachment statement plus composites. Routes that would do:
  - (a) prove the attachment statement of item 12 for arbitrary trivial fibrations B → ∂𝔻^m of CaTT models (a homotopy-pushout property of free cell extensions of CaTT models), and extend it from a single generator to strict composites;
  - (b) describe the fibre of π_Γ over each strict cell as a CaTT-definable object and show it is contractible;
  - (c) a relative Guiraud–Malbos normalisation strategy towards the strict cells of F(Γ), producing all higher comparisons at once;
  - (d) an equivalence with Dean's Conj. 5.4.0.9 or another named open statement;
  - (e) by item 22, construct for every finite homotopical Γ a retraction r : KC → A over C with r i = id, for example by contracting the fibres of π over the cells of C, or by a homotopy-pushout property of attaching the generators of KC that are not in A. Item 24 gives compatible algebraic lifts over all strict simplices, which may help organise the choices;
  - (f) a **wedge theorem in every dimension**: RC_id(∞)(A₁ ∨₀ ⋯ ∨₀ A_k) from RC_id(∞)(A_i), for contexts glued at cut vertices (and its analogue for gluing along higher cells where the gluing is a cut), together with a forced-order normalisation for the remaining fibres, which have a single linear extension. In dimension 3 under (H) this is exactly item 25, and with the polyplex reduction (item 11) it would give the positive 2-dimensional case of Question 3.
- **(⇒, necessity on bubble-free contexts).** By item 20, RC_id(∞) already forces bubble-freeness in every dimension. Prove that a finite context with RC_id(∞) is homotopical, or give a bubble-free, non-homotopical context with RC_id(∞), together with a separating invariant. By items 22–23, it suffices to prove that the **coinductive** reconstruction map Q d_C : Q L(KC) → Q NC is an equivalence for every free strict ω-category C = F(Γ) on a finite polygraph. The inductive d_C never is (item 23). A proof for all gaunt C, or for all C, is preferred. Equivalently, prove that the unit η at Free(Γ) is an FHM weak equivalence whenever RC_id(∞)(Γ) holds, or produce the section s of item 22. A proof that bubble-freeness implies homotopicality in every dimension would also settle this direction.

**Question 2 (fallback for (⇐), still every dimension).** If Question 1(⇐) is out of reach, prove RC_id(∞) for every finite context that is positive in every dimension, or at least for every finite strong-Steiner context, and give the counterexample that separates the classes if one exists.

**Question 3 (fallback, every n).** Prove RC_id(n) for every n for every finite 2-dimensional context that is bubble-free (equivalently homotopical, item 8). By item 11, for positive contexts it suffices to treat finite strong-Steiner 2-dimensional contexts. Then prove an extension theorem: adjoining generators of any dimension ≥ 3 to a context with RC_id(∞), **such that the result is still homotopical** (or still bubble-free in every dimension), preserves RC_id(∞). Item 21 shows the condition is needed. Together these answer Question 1(⇐) for every homotopical context whose 2-skeleton is homotopical. For contexts satisfying (H), item 25 reduces the dimension-3 case to the wedge lemma plus forced-order statements. The useful answer is a proof of those for every k and in every dimension n, not a further single wedge.

## 5. What counts as a solution

A proof of either direction of Question 1 (for (⇒), coinductive reconstruction at free strict targets suffices), of Question 2, or of Question 3 with the restricted extension theorem; a counterexample in one of the named classes, with a proof that no connecting term exists (for example an invariant of a model); an equivalence with a named open problem; or a published reference. An existence proof of the connecting cells is enough, provided it is a proof about CaTT terms or CaTT models.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Ozornova–Rovelli–Walde, arXiv 2603.11005 (coinductive completion; (∞,m)-categories are coinductively complete).
- Street, *The algebra of oriented simplexes* (orientals); Steiner, *Orientals*, arXiv math/0601383 (tableaux of face suborientals).

- Dean–Finster–Markakis–Reutter–Vicary, arXiv 2208.08719, §5, and Markakis, arXiv 2303.11978, §5 (computadic cofibrant replacement).

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

## Coinductive reconstruction gives the 0-truncation

Let $C=F(Γ)$ for a finite context, $A=\mathrm{Free}(Γ)$, and let $Q,L,N$ be as in items 22–23. In the ∞-category of coinductively complete $(∞,ω)$-categories, **both comparison maps exhibit their common target as the 0-truncation of their source**:

$$
QL(KC)\xrightarrow{Qd_C}NC,\qquad QLA\xrightarrow{Qe}NC.
$$

Here 0-truncation has its mapping-space meaning. An object $Z$ is 0-truncated if every space of maps into $Z$ is a 0-type. Such an object can have nonidentity directed cells in arbitrarily high dimensions. The assertion about $Qd_C$ also holds for any strict $C$ whose discrete Θ-nerve is coinductively complete.

**Algebraic descent.** Suppose $p:X\to C$ is a globular trivial fibration of CaTT models with strict codomain. Let $D$ be a strict ω-category in which every coinductively invertible positive-dimensional cell is an identity. Then precomposition is a bijection

$$
\mathrm{Hom}_{\mathrm{str}\,ω\mathrm{Cat}}(C,D)
\longrightarrow \mathrm{Hom}_{\mathrm{CaTT}}(X,D).
$$

To prove it, fix $h:X\to D$ and any two $n$-cells $u,v$ with $p(u)=p(v)=c$. Their boundaries in $X$ can differ. Use the CaTT presentation of the globe cylinder $I\otimes\mathbb D^n$ with its two endpoint globes. The endpoint variables have their globular types, and the cylinder is obtained from their disjoint union by freely adjoining the mixed generators in increasing dimension. Below, map the strict cylinder to $C$ by collapsing $I$ and selecting $c$. Above, prescribe $u$ and $v$ on the two endpoint globes. For each mixed generator its two attaching terms now evaluate to parallel cells in $X$ with the prescribed images in $C$. Boundary lifting for $p$ extends the assignment across that generator. This includes $n=0$, when the unique mixed generator is an edge. [Globe-cylinder presentation, item 6](canonical-gray-terms-r5-2026-11-19.md)

Every mixed generator maps under the collapse to an identity. Cells in $X$ over identities are coinductively invertible. Indeed a reverse cell over the same identity lifts against the reversed boundary. Both composites admit cancellation witnesses over identities by another application of boundary lifting, so the class satisfies the coinductive inverse condition. The strict map $h$ preserves this inverse data. Consequently the composite cylinder labelling in $D$ sends every mixed generator to an identity.

Since $D$ is strict, this labelling evaluates the strict Gray cylinder. For a face generator $x$ of the globe, its cylinder generator has source and target obtained by whiskering $x^-$ and $x^+$ with the mixed generators on their lower faces, as in §1.3. In $D$ these lower whiskerings are by identities. Starting with vertices and proceeding up the globe, the two faces of the mixed generator therefore evaluate to the two endpoint values of $x$. The mixed generator itself is an identity, so those values coincide. At the top this gives $h(u)=h(v)$.

Boundary lifting makes $p$ surjective on cells, by first lifting a labelling of the boundary of a globe and then its top cell. Thus $h$ descends uniquely as a globular map $\bar h:C\to D$. For each CaTT operation, lift its whole labelled globular pasting arity through $p$, one variable at a time. On this lift the equation expressing preservation of the operation by $\bar h$ is the corresponding equation for $h$. This proves that $\bar h$ preserves all operations, including identities and binary composites, as required.

**Truncation.** The 0-truncated objects of the coinductive theory are exactly its discrete complete Segal Θ-nerves. Indeed if $Z$ is 0-truncated, evaluating at any Θ-shape $P$ gives the 0-type $\mathrm{Map}(QP,Z)$. Taking components then gives an equivalent set-valued presheaf. Its Segal bijections are the strict ω-category nerve conditions. Conversely, mapping into a set-valued presheaf gives 0-types, also in the full subcategory of local objects. Completeness forces invertible cells in a discrete nerve to be identities, and coinductive completeness does so for coinductively invertible cells. The latter condition uses the coinductive inverse criterion, which in a discrete strict nerve evaluates on the cells and compositions of the strict category itself. For our finite $Γ$, $NC$ is discrete by gauntness and coinductively complete by the dimension bound in item 23. [Berger, Theorem 1.12](https://math.univ-cotedazur.fr/u/cberger/nerve.pdf) · [Ozornova–Rovelli–Walde, Propositions 5.29 and 5.42](https://arxiv.org/html/2603.11005v2)

Test $Qd_C$ against any such target $ND$. Locality identifies maps out of $QL(KC)$ into $ND$ with maps out of $L(KC)$. These form a discrete space whose points, by the realization adjunction at a gaunt target, are the strict CaTT maps $KC\to D$. Maps $NC\to ND$ form the discrete space of strict ω-functors $C\to D$. On these sets precomposition with $Qd_C$ is precomposition with $q:KC\to C$, a bijection by algebraic descent. This proves the universal property of 0-truncation. For $Qe$ the same calculation gives precomposition with $π:A\to C$, a bijection already by freeness: an assignment of the generators of $Γ$ in a strict target evaluates every attaching term at its strict image and extends uniquely to a strict ω-functor from $F(Γ)$. [Realization at discrete gaunt targets, Known (II)](../outbox/catt-models-unit-condition-r4.md)

**The remaining geometric test.** For $Z=QL(KC)$, reconstruction at $C$ is now equivalent to

$$
\pi_j\!\left(\mathrm{Map}(\mathbb D^n,Z),z\right)=0
\quad\text{for every }n\geq0,\ j\geq1,\ z\in\mathrm{Map}(\mathbb D^n,Z).
$$

Indeed these vanishings say precisely that the spaces of globe labellings are 0-types. The Segal condition computes the space of labellings of any pasting shape as a limit of those spaces. Hence the entire Θ-presheaf is 0-truncated, and its truncation map is an equivalence. The converse follows by evaluating a 0-truncated target on globes. The identical test with $Z=QLA$ characterizes homotopicality of $Γ$ by item 23. In particular, necessity in Question 1 would follow from vanishing for $QLA$ under $\mathrm{RC}_{\mathrm{id}}(∞)$. The base point and sphere in this test can be arbitrary geometric data. The cylinder descent proof identifies maps into discrete targets and leaves this positive-degree vanishing open.

# Verification (2026-11-19)

Status: **verified, partial**. The response identifies both comparison maps as 0-truncations, which turns both directions of the homotopical comparison into one vanishing statement.
- *Algebraic descent: correct.* Let p : X → C be a globular trivial fibration and D strict, with coinductively invertible positive cells being identities. A CaTT map h : X → D descends through p:
  - Two cells u, v over the same c are joined by a lifted globe cylinder. Its mixed generators lie over identities, so they are coinductively invertible: a reverse and the cancellation witnesses lift over identities by boundary lifting. Hence they map to identities in D, and evaluating the strict cylinder in D gives h(u) = h(v).
  - The descended map preserves operations, by lifting labelled arities.
  - p is surjective by boundary lifting, so the descent is unique.
- *0-truncated objects are the discrete complete Segal Θ-nerves*, with coinductive completeness forcing coinductively invertible cells to be identities (Berger Thm 1.12; Ozornova–Rovelli–Walde Props. 5.29, 5.42; taken from the literature as cited). NC is such an object for finite Γ (gaunt, dimension bound).
- *Universal property.* Maps from QL(KC), or from QLA, into ND are strict CaTT maps from KC, or from A, into D. Precomposition with q is bijective by descent (q is a trivial fibration), and precomposition with π is bijective by freeness. So **Qd_C and Qe are both 0-truncation maps**. Correct.
- *Consequence.* **Γ is homotopical iff QLA is 0-truncated, iff π_j Map(𝔻ⁿ, QLA) = 0 for all n ≥ 0 and j ≥ 1.** Reconstruction at C is the same statement for QL(KC). The descent argument settles maps into discrete targets only. The vanishing of positive homotopy is the open geometric content.

Follow-up: [`outbox/relative-coherence-all-dimensions-r6.md`](../outbox/relative-coherence-all-dimensions-r6.md).

# Researcher Response 2

## A geometric sphere can be tested on the support of its strict label

Write $X_Γ=L\mathrm{Free}(Γ)$ and $C_Γ=F(Γ)$. For a strict $n$-cell $c$, let $E_Γ(c)$ be the homotopy fibre over $c$ of the map from $\mathrm{Map}(\mathbb D^n,X_Γ)$ to the discrete set of strict $n$-cells of $C_Γ$. Let $Δ$ consist of the generators used by $c$ and their iterated boundary dependencies. Then the inclusion induces an equivalence

$$E_Δ(c)\ \simeq\ E_Γ(c).$$

In particular, if $Γ$ satisfies $\mathrm{RC}_{\mathrm{id}}(∞)$ and every generator in the support of $c$ has dimension at most two, **$E_Γ(c)$ is contractible**. This includes every strict label on the 0-, 1-, and 2-globes of a finite context of arbitrary dimension, as well as iterated identities on those labels.

**Proof.** More generally take any dependency-closed $Δ\subseteq Γ$. The support of an identity is the support of its base, and the support of a defined composite is the union of the supports of its factors, counting boundary dependencies throughout. These rules respect the strict unit, associativity and exchange equations. Membership in $C_Δ$ is equivalent to having support in $Δ$. Consequently a factorization of a cell of $C_Δ$ in $C_Γ$ has both factors in $C_Δ$. Identity factorizations lift as well, and the inclusion makes the lifts unique. Thus $C_Δ\hookrightarrow C_Γ$ is discrete Conduché, so pullback along it preserves colimits. [Loubaton, Theorem 2.2.2.10](https://arxiv.org/pdf/2406.05425)

Apply this pullback to the homotopy pushouts attaching the generators of $X_Γ$. A generator in $Δ$ retains its whole globe and attaching boundary. For a generator outside $Δ$, every cell of its globe outside the boundary is the top generator or an iterated identity on it. All of these have images outside $C_Δ$. Thus the pulled-back globe and its pulled-back boundary coincide, even if several boundary faces have the same image. It follows by induction over the attachments that $X_Δ\simeq X_Γ\times_{NC_Γ}NC_Δ$. For these finite contexts the realizations and strict targets are already coinductively complete by item 23. Applying $\mathrm{Map}(\mathbb D^n,-)$ preserves the pullback. Taking its fibre at any $c$ in $C_Δ$ gives the asserted equivalence. [Skeletal pullback calculation, §§3.1–3.2](fibration-presentations-all-dimensions-2026-11-19.md)

Now choose $Δ$ to be the support of $c$. Item 18 gives $\mathrm{RC}_{\mathrm{id}}(∞)(Δ)$. If $\dim Δ\le 2$, the bubble obstruction and the finite 2-polygraph theorem (items 8 and 18) give homotopicality of $Δ$. Its comparison is therefore an equivalence. Evaluation on any globe is still an equivalence, and its fibre over $c$ is contractible.

**Where the necessity test first remains open.** Suppose a counterexample to necessity has as few generators as possible, and let $m$ be its generator dimension. Then $m\ge3$, and some strict $m$-cell using every generator has a fibre with a nonzero positive homotopy group. Indeed Response 1 detects failure on a globe, over some strict label. Its support inherits RC and has the same fibre, hence minimality forces full support. A globe of dimension below $m$ cannot have such a label. A globe of dimension $n>m$ gives the same test as the $m$-globe: both targets of evaluation ($X_Γ$ and $NC_Γ$) are $(∞,m)$-categories, and intelligent $m$-truncation sends $\mathbb D^n$ to $\mathbb D^m$. In particular the fibre is unchanged on passing from the iterated identity label to its $m$-dimensional base. For a full-support $m$-cell the pullback above returns $Γ$ itself. Proving vanishing in these fibres, or finding a nonzero class in one, would decide necessity. [Loubaton, Construction 2.2.1.40 and Proposition 2.2.1.43](https://arxiv.org/pdf/2406.05425)

# Researcher Response 3

## A positive, bubble-free 3-computad with a circle as a full-support fibre

Positivity in Question 2 is insufficient. There is a finite positive context $Γ$ with acyclic generating 1-graph whose lower skeleton satisfies $\mathrm{RC}_{\mathrm{id}}(∞)$, but in which two parallel 4-terms of identical strict image have no connecting 5-term. It also disproves the bubble-free variant of the extension in Question 3. Its geometric comparison and its algebraic relative coherence both fail.

**The context.** On four objects in a line take edges $f_0,f_1:0\to1$, $g:1\to2$ and $h_0,h_1:2\to3$. Take parallel pairs
$\alpha_0,\alpha_1:f_0\Rightarrow f_1$ and $\beta_0,\beta_1:h_0\Rightarrow h_1$. Write juxtaposition with an edge for whiskering. Attach just
$$
 A:\alpha_0g\longrightarrow\alpha_1g,\qquad
 B:g\beta_0\longrightarrow g\beta_1 .
$$
Use the CaTT binary whiskerings for these attaching terms. Every generating face is nonidentity. A nonidentity 2-cell strictly increases the number of occurrences of $f_1,h_1$ in its boundary path. A nonidentity 3-cell strictly increases the number of occurrences of $\alpha_1,\beta_1$ in its boundary 2-cell. These counts are additive under contextual substitution, so there are no bubbles. Every strict cell in the lower skeleton has support in a globular pasting consisting of a horizontal string of edges and 2-discs. Indeed a 2-cell can use at most one of the two $\alpha$'s and at most one of the two $\beta$'s. By items 2 and 7 the lower skeleton has relative coherence in every dimension. Items 1 and 4 now give RC through degree three on $Γ$. All strict endomorphisms in positive dimensions are identities here, so the identity-image conditions hold in those degrees.

**The geometric calculation.** Write $E$ for the discrete pair, $J=[1]$, $Q$ for the walking parallel pair of arrows, and $D$ for the walking 2-cell, with inclusion $Q\hookrightarrow D$. Use cartesian iterated enrichment for $(∞,3)$-categories. All pushouts in this calculation are homotopy pushouts. The object sets in both enrichment steps are discrete: the only arrows between distinct objects go forward in a line or a square, and all endomorphism objects are terminal. Thus completion adds no object equivalences. [Haugseng, rectification and comparison with iterated enrichment](https://arxiv.org/abs/1312.3881)

Put $X=L\mathrm{Free}(Γ)$. Its successive outer hom objects along the line are $Q,1,Q$. Each of the two hom objects spanning two edges is $D$. The remaining hom object is
$$
 X(0,3)=(D\times Q)\underset{Q\times Q}{\amalg}(Q\times D)
 \quad\text{in }\mathrm{Cat}_{(∞,2)} .
$$
To verify the formula, start with the free enriched line. Composition along it gives the products of the consecutive homs. Attaching $A$ extends the hom from 0 to 2 along $Q\to D$ and forces its right composites with $Q$. Attaching $B$ extends the hom from 1 to 3 in the same way and forces its left composites with $Q$. There is no path containing both of these length-two intervals. The only triple composition to specify is along the original three edges. Its associativity gives precisely the identification over $Q\times Q$ in the pushout. Equivalently, maps into any enriched target with the four objects prescribed specify the two compositors with their homotopy of agreement on the triple product. Strings of nonidentity edges have length at most three. This verifies the enriched universal property. The free inner cells represented by $Q\to D$ have exactly the two prescribed whiskered faces. Choices of their semantic identification with the CaTT whiskerings are contractible in the lower skeleton, which is homotopical by item 8.

The four objects of this inner pushout are $f_i g h_j$. Its four side homs are all $J$. Its diagonal hom $V$ from $f_0gh_0$ to $f_1gh_1$ is the following pushout in $\mathrm{Cat}_∞$:
$$
 V=(J\times J)\underset{P}{\amalg}(J\times J),\qquad
 P=(J\times E)\underset{E\times E}{\amalg}(E\times J).
$$
Here is the calculation of the diagonal, where the distinction between the two squares matters. In the three input objects $D\times Q$, $Q\times Q$ and $Q\times D$, the diagonal homs are respectively $J\times E$, $E\times E$ and $E\times J$. Their colimit is $P$. In each input there are two routes along sides between the opposite objects. The product of the side homs for *each* route is that input's diagonal hom, with its canonical product compositor. The colimit of the old route products is therefore $P\amalg P$, mapping by the fold to $P$. After taking colimits on sides, the two route products are $J\times J$ and $J\times J$. Extending the two compositors takes the pushout along $P\amalg P$, giving the formula. This is the universal property for the four-object enriched square: specifying its diagonal hom and a compositor from each route supplies all nonidentity compositions, since there are no length-three routes inside this square.

Present $V$ by two simplicial squares $\Delta^1\times\Delta^1$ glued along their four perimeter edges. This computes the pushout since the perimeter presents $P$ and its inclusions are monomorphisms in the Joyal model structure. Its vertices $u_{ij}$ are the strict 2-cells given by $\alpha_i$, $g$ and $\beta_j$ in horizontal order. There is one strict 3-cell $c:u_{00}\to u_{11}$: strict interchange identifies the two serial orders of $A,B$, and each order can be performed in either of the two simultaneous diagrams. Equivalently, the identical enriched pushout calculation with strict categories gives the ordinary commutative square for the diagonal. The label $c$ uses every generator, including $g$.

The mapping space of $V$ from $u_{00}$ to $u_{11}$ is a circle. In the necklace rigidification there are four vertices: the two perimeter routes and one diagonal edge from each square. Each of the four triangles joins its diagonal to its perimeter route, giving a four-cycle. There are no higher nondegenerate flags: on a route from these endpoints a necklace has room for at most one interior vertex. This also proves that each identity and each perimeter edge has a contractible mapping space over its label. The spaces of choices of the two lower globular boundaries are discrete up to equivalence in this calculation. Hence the circle is the actual geometric fibre over $c$. [Dugger–Spivak, §§4–5](https://arxiv.org/abs/0910.0814)

**Separating CaTT terms.** Fix two 1-terms $s,t$ lifting $f_0gh_0,f_1gh_1$ with common bracketing. There are two intermediate 1-paths $f_1gh_0,f_0gh_1$. Choose a weak representative of each. Each intermediate path supplies a map into $Γ$ from the globular pasting context of two 3-discs composable along a 1-disc. In the first map the rows are $A$ whiskered by $h_0$, then $B$ whiskered by $f_1$. In the second they are $B$ whiskered by $f_0$, then $A$ whiskered by $h_1$. For literal matching along the cut, choose the row's two 2-faces over their indicated strict labels with the prescribed 1-boundaries, then its 3-cell over the indicated whiskered generator. Boundary lifting in dimensions two and three follows from RC through degree two and strict surjectivity as in §1.2. In particular no assertion in degree four is needed to choose these maps.

In the generic two-disc context, compose a face of each disc along dimension one to obtain four corners. Composing one disc with one face gives their four side 3-terms. The two serial composites of sides are parallel 3-terms. The coherence head over the whole pasting context between them is a 4-term, since both composites have full support. Orient it from the route changing $\alpha$ first to the route changing $\beta$ first, reversing the generic orientation on the second copy as necessary. Applying the two substitutions gives tiles $H$ and $K$. Their images are the two square homotopies in $V$. Indeed the realization of the generic paste is its strict nerve by item 8. Composition of its two rows maps its square into $V$ by the compositor at the chosen intermediate object. The row labellings agree up to contractible choice with the given ones: their individual 3-cell fibres are perimeter-edge mapping spaces, and their common 1-cut has discrete fibre. The globe pushout for the generic paste therefore identifies the two maps up to homotopy over their labels. Within the generic square the homotopy between its perimeter routes is unique up to homotopy relative endpoints. Thus each tile goes through the diagonal of its own square in the four-cycle.

For clarity, the two tiles can be compared with *literal parallel endpoints* in CaTT. Write $U^H_p,U^K_p$ for the 2-terms at each corner $p$. They all have the fixed outer boundaries $s,t$. Choose $k_p:U^H_p\to U^K_p$ over the identity by RC in degree two. For each perimeter edge $p\to q$ with respective 3-terms $l_H,l_K$, choose a 4-term
$$
 k_q\circ l_H\ \Longrightarrow\ l_K\circ k_p .
$$
This uses RC in degree three, already proved for $Γ$. Here $\circ$ denotes composition of 3-cells over a 2-face. Let $H_1,H_2$ be the two serial 3-composites in the first tile and $K_1,K_2$ the corresponding ones in the second. From $k_{11}\circ H_1$ to $K_2\circ k_{00}$ form two 4-terms. The first uses the first tile whiskered by $k_{11}$ and then the edge comparisons on route 2. The second uses the edge comparisons on route 1 and then the second tile whiskered by $k_{00}$. Insert associators between the consecutive comparisons with the displayed common bracketing. These are ordinary bicategorical pastes in the twice-iterated hom, using CaTT composition, whiskering and associators. Both terms have strict image $1_c$.

Realization sends these pastes to the corresponding pastes of paths in the mapping space. One can check the operations separately: each binary composition, unit or associator comes from its generic globular paste, where the comparison with the semantic composite is unique up to homotopy over its label by homotopicality. Substitution transports those comparisons. The associativity and unit comparisons agree on iterated pastes by the same check in the generic paste of the inputs. This only uses the interpretation of terms in $X$. In $V$ the $k_p$ represent identities, and each individual edge comparison lives over a single perimeter edge, whose mapping space is contractible. Consequently these choices give the canonical endpoint identifications on the two perimeter routes. The first resulting path goes from one route to the other through the first diagonal. The second goes through the other diagonal. Traversing one and returning along the other has winding number one. A 5-term between the two 4-terms would interpret as a homotopy of those paths relative to their endpoints. The winding number excludes it.

Thus $Γ$ fails $\mathrm{RC}_{\mathrm{id}}(4)$ and plain $\mathrm{RC}(4)$. This answers the positivity assertion in Question 2 negatively and separates positivity from the homotopical strong-Steiner class. The implication from relative coherence to homotopicality still requires a contraction under its relative-coherence hypothesis or a counterexample satisfying that hypothesis.

The [reproducible finite check](../../../tools/relative_coherence_middle_wire.py) checks all 15 declarations, the four sides of the generic exchange, the two instantiated exchange terms, and their four corner comparisons. It independently enumerates the diagonal necklaces and triangles and finds a connected graph with four vertices and four edges. Run the following commands from the repository root to repeat the combinatorial check and the Agda check of the terms. The side comparison terms use the existence theorem in item 4. The pushout calculation and the winding-number separation are mathematical proofs above.

```sh
python3 tools/relative_coherence_middle_wire.py
mkdir -p /tmp/cattexp-rc-middle-wire
python3 tools/relative_coherence_middle_wire.py --agda > /tmp/cattexp-rc-middle-wire/MiddleWire.agda
agda --no-libraries -i src -i /tmp/cattexp-rc-middle-wire /tmp/cattexp-rc-middle-wire/MiddleWire.agda
```
