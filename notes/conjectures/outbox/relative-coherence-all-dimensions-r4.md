# Relative coherence in CaTT in every dimension: free weak ω-categories are strict exactly on homotopical computads

*A self-contained problem. It assumes familiarity with globular weak ω-categories, strict ω-categories, polygraphs (computads) and Steiner complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** One theorem valid in every dimension: the exact class of finite computads on which the free weak ω-category is strict (in the sense of §1.2), ideally "exactly the homotopical ones". Individual new cases (one more context, one more dimension) are not useful to us. Several exact reductions are known (§3, items 9–14 and 22). Non-identity cells on iterated identities ("bubbles") are now known to obstruct strictness in every dimension (item 20). The open question is the comparison on bubble-free contexts. It has two halves: the contraction (homotopical ⇒ strict), and the necessity of homotopicality, which now reduces to one reconstruction statement (item 22).

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

## 4. Questions

**Question 1 (main: the exact class).** Prove that for every finite CaTT context Γ,

> RC_id(∞)(Γ)  ⟺  Γ is homotopical,

equivalently (item 7) that π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models exactly when the polygraph of Γ is homotopical. Or give a counterexample to either direction with a separating invariant.

- **(⇐, the contraction).** This is the main content. By item 11 the positive case reduces to generic positive polyplexes, and by item 12 the strong-Steiner case reduces to one attachment statement plus composites. Routes that would do:
  - (a) prove the attachment statement of item 12 for arbitrary trivial fibrations B → ∂𝔻^m of CaTT models (a homotopy-pushout property of free cell extensions of CaTT models), and extend it from a single generator to strict composites;
  - (b) describe the fibre of π_Γ over each strict cell as a CaTT-definable object and show it is contractible;
  - (c) a relative Guiraud–Malbos normalisation strategy towards the strict cells of F(Γ), producing all higher comparisons at once;
  - (d) an equivalence with Dean's Conj. 5.4.0.9 or another named open statement;
  - (e) by item 22, construct for every finite homotopical Γ a retraction r : KC → A over C with r i = id, for example by contracting the fibres of π over the cells of C, or by a homotopy-pushout property of attaching the generators of KC that are not in A.
- **(⇒, necessity on bubble-free contexts).** By item 20, RC_id(∞) already forces bubble-freeness in every dimension. Prove that a finite context with RC_id(∞) is homotopical, or give a bubble-free, non-homotopical context with RC_id(∞), together with a separating invariant. By item 22, it suffices to prove that the reconstruction map d : L(KC) → NC is an equivalence for every free strict ω-category C = F(Γ) on a finite polygraph. A proof for all gaunt C, or for all C, is preferred. Alternatively, produce the section s of item 22. A proof that bubble-freeness implies homotopicality in every dimension would also settle this direction.

**Question 2 (fallback for (⇐), still every dimension).** If Question 1(⇐) is out of reach, prove RC_id(∞) for every finite context that is positive in every dimension, or at least for every finite strong-Steiner context, and give the counterexample that separates the classes if one exists.

**Question 3 (fallback, every n).** Prove RC_id(n) for every n for every finite 2-dimensional context that is bubble-free (equivalently homotopical, item 8). By item 11, for positive contexts it suffices to treat finite strong-Steiner 2-dimensional contexts. Then prove an extension theorem: adjoining generators of any dimension ≥ 3 to a context with RC_id(∞), **such that the result is still homotopical** (or still bubble-free in every dimension), preserves RC_id(∞). Item 21 shows the condition is needed. Together these answer Question 1(⇐) for every homotopical context whose 2-skeleton is homotopical.

## 5. What counts as a solution

A proof of either direction of Question 1 (for (⇒), reconstruction at free strict targets suffices), of Question 2, or of Question 3 with the restricted extension theorem; a counterexample in one of the named classes, with a proof that no connecting term exists (for example an invariant of a model); an equivalence with a named open problem; or a published reference. An existence proof of the connecting cells is enough, provided it is a proof about CaTT terms or CaTT models.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

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

## Inductive reconstruction fails even at the terminal strict category

Let 1 be the terminal strict ω-category, and let K, L and d be as in item 22. **The reconstruction map d₁ : LK1 → N1 is not an equivalence in inductive (∞,ω)-categories.** Consequently d_C fails to be an inductive equivalence for *every* nonempty free strict target C in Question 1, including every oriental. The argument also explains why this counterexample does not decide the reconstruction condition after coinductive completion.

Build a strict ω-category D with one object p and a freely generating loop ℓ. In each dimension k ≥ 2, freely attach one k-generator for each ordered parallel pair of (k−1)-cells in the preceding skeleton. The loop ℓ differs from the identity of p. Moreover, D is gaunt in the strict sense. In each positive dimension, the number of top-dimensional generators in a strict cell is additive under composition. A strict inverse forces that number to be zero, and a composite of identity cells is itself an identity. Thus the discrete Θ-nerve ND presents D in the inductive theory. Its space of maps from the 1-globe is discrete, with different points for ℓ and the identity. [Gaunt nerves and realization, Known (I)–(II)](catt-models-unit-condition-r4.md)

By the generator description of K in item 22, K1 has one object v and a freely generating loop u at v labelled by the strict identity of 1. Define two CaTT maps K1 → D which send v to p and send u respectively to ℓ and to the identity. Both assignments extend in every dimension. For each remaining generator its boundary terms have parallel images, and the construction of D gives a generator between those images. By the realization adjunction the resulting maps induce two maps LK1 → ND. Restrict them along the realized free weak 1-globe selecting u. This realization presents the geometric 1-globe, and the restrictions pick out ℓ and the identity. The restrictions lie in different components, so the original maps do too. In contrast, the mapping space from N1 to ND consists of the single object p. Precomposition with d₁ therefore fails to surject on components. [Realization on globes, Known (IV)](catt-models-unit-condition-r4.md)

For any nonempty gaunt strict C, choose a vertex to obtain strict maps 1 → C → 1 with identity composite. Functoriality of K and naturality of d exhibit d₁ as a retract of d_C in the arrow category. Equivalences are closed under retracts, which proves the general claim. The empty target has K∅ empty and d is an equivalence there.

For the coinductive comparison, the map D → 1 has globular boundary lifting by construction, including at objects and arrows. It is therefore an FHM weak equivalence. Detection by the semantic CaTT model gives Q(ND) ≃ 1. Thus this very test target loses its ability to distinguish the two maps after coinductive completion. For a finite Γ with generator dimension at most m, the two objects in e : LA → NC lie in (∞,m)-categories. Indeed, the inclusion of (∞,m)-categories has a right adjoint, the m-core, so it preserves the globe-attachment colimits constructing LA. Both objects are coinductively complete. Consequently e is an equivalence iff Qe is one, and item 22 still applies if **Qd_C** is an equivalence. [Detection, Known (IV)](catt-models-unit-condition-r4.md) and [Ozornova–Rovelli–Walde, Lemmas 4.4 and 5.22–5.23](https://arxiv.org/html/2603.11005v1)

For the one-vertex context, LA and NC are both a point and relative coherence holds. K1 has generators in unbounded dimensions. The counterexample decides the inductive reconstruction proposal in Question 1. The section required by item 22, coinductive reconstruction, and the characterization of relative coherence on bubble-free contexts remain open here.
