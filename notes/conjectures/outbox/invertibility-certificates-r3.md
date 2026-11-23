# Is invertibility in free Gray-enriched ω-categories recursively enumerable?

## Setting

**Gray ω-categories.** Let ω-Cat be the category of strict ω-categories with the lax Gray tensor product ⊗ of Ara–Maltsiniotis (arXiv:1607.00668). A *Gray ω-category* is a category enriched in (ω-Cat, ⊗).
- Inside a hom, cells compose strictly.
- Composition across objects sends the top cell of x ⊗ y (x, y of positive dimension) to a directed interchanger, which in general is not invertible.

The weak analogue is an oriented (∞,ω)-category (Gepner–Heine, arXiv:2510.10504). Write f ; g for composition along the (n−1)-boundary in diagrammatic order.

**Invertibility (coinductive).** A cell f : x → y of dimension n ≥ 1 is *invertible* if there are cells g, g′ : y → x and invertible cells l : g ; f → 1_y and r : f ; g′ → 1_x. Equivalently, f is invertible if it lies in a set S of cells such that every member has candidates g, g′ and cancellations l, r with l, r ∈ S.

**Free models.** A *marked computad* (C, M) is a finite computad C with a set M of positive-dimensional generators. F(C, M) is the free Gray ω-category on C in which every marked generator is invertible: for each marked m, adjoin m⁻ˡ, m⁻ʳ, λ_m : m⁻ˡ ; m → 1 and ρ_m : m ; m⁻ʳ → 1, mark λ_m and ρ_m, and repeat. Its cells are presented by finite terms, and equality of terms is decidable in the strict case (Steiner/Ara–Maltsiniotis normal forms for Gray tensors of free objects). The weak version is defined in the same way among oriented (∞,ω)-categories.

**Inductive certificates.** Let Cert(C, M) be the least class of cells closed under the following rules:
1. marked generators and their adjoined inverses and units;
2. identities, and in the weak case coherence cells;
3. pasting composites inside a hom whose top constituents are in Cert;
4. images of the top cell of x₁ ⊗ … ⊗ x_k with some positive-dimensional xᵢ in Cert;
5. the recorded inverse package of a member;
6. inv-intro: f, if there are g, g′ and l : g ; f → 1, r : f ; g′ → 1 with l, r ∈ Cert.

Membership of a cell, given a finite derivation, is checked syntactically.

**What is known.**
- *Ordinary (non-Gray) case.* Every invertible cell of the free ω-category on a finite marked computad is in Cert. Cells of dimension above dim C are certified, so every invertibility tower becomes certified after finitely many levels.
- *Gray case: Cert is incomplete.* Take objects a, b; generators p : a → a, x : a → b, u : 1_a ⇒ p, v : p ⇒ 1_a; and a 3-cell f : 1_x ⇛ 1_x in the hom F(a, b). Mark four further generators:
  - a contraction u ; v ⇛ 1;
  - contractions of (pu) ; (pv) and (pv) ; (pu) to identities (pu means left whiskering by p);
  - a contraction of the whiskered cell p·f to an identity.

  Then f is invertible in F(C, M), but f ∉ Cert. The reason it is invertible: the cylinders Id ⇒ p· and p· ⇒ Id built from u and v have a composite that is invertible by rule 4, and change of base along u ; v ≅ 1 splits every based cell q with p·q invertible through an invertible cell. This produces an infinite reversal tower whose individual tiles u ⊗ q and v ⊗ q are never certified.
  - To see that f is not certified, take the two-object model with homs E, where E is the strict ω-category of bit-labelled cells composed by meet, with Gray multiplication by join. Designate only identities. The marks go to identities, but f does not, so no rule sound in every model with a designated class closed under 1–6 can certify f.
  - The alternating interchangers u ⊗ v ⊗ u ⊗ … ⊗ f give uncertified invertible cells in every dimension ≥ 3.
- *Coinduction is complete but infinitary.* Invertibility coincides with the following: a family of cells indexed by a set, with at each index two candidates and cancellations, each cancellation either in Cert or carried by a successor index. Along any branch the dimension increases, so a finite index set adds nothing to Cert. Validating an arbitrary program presenting such a family is undecidable (it can encode non-halting).
- *Undecidability.* Invertibility is not decidable uniformly in (C, M). It contains the unit problem of finitely presented monoids: one object, the generators as 1-cells, each relation u = v as a marked 2-cell. Whether a finite presentation presents a group is undecidable (Narendran–Ó'Dúnlaing–Otto, Discrete Math. 98 (1991)). Cert-membership with given derivations is semi-decidable.

## Questions

1. **(Main question.)** Is the set {((C, M), t) : t an invertible cell of F(C, M)} recursively enumerable, uniformly over finite marked computads? Equivalently: is there a certificate language with decidable checking that is sound for invertibility in every Gray ω-category and complete for invertibility in every free F(C, M)? Answer for strict Gray ω-categories and for the weak version.

2. **(If yes.)** Give such a language as Cert plus finitely many rules in the same style. For example, a *schematic coinduction* rule whose certificate is a finite recipe, uniform in a dimension parameter, that produces at each index the candidates and cancellations for the next, together with a finite proof that the recipe is well-typed and closes up. State its soundness and completeness theorems, and show how it certifies f in the example above.

3. **(If no.)** Prove it, for instance by reducing the complement of the halting problem (or another non-r.e. set) to invertibility in finite marked computads. Also identify the largest natural decidable fragment beyond Cert, such as towers that are eventually periodic up to suspension or whiskering.
