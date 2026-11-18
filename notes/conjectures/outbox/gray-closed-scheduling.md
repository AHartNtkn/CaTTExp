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
