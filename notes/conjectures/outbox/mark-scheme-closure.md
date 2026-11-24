# Which coinductively declared cell structures are closed under the operations of a Gray-enriched ω-category, and which are properties?

*A self-contained problem. Background: weak and strict ω-categories, the Gray tensor, coinductive invertibility.*

## 1. Setting

**Ambient.** Work in either of two settings, and say which results hold in which:
- (strict) categories enriched in strict ω-categories for the lax Gray tensor of Ara–Maltsiniotis;
- (weak) oriented (∞,ω)-categories, i.e. categories enriched in Cat_ω for the lax Gray tensor (Gepner–Heine, arXiv 2510.10504; Campion, arXiv 2311.00205), with coinductive equivalences.

Inside a hom 𝒦(a, b), cells compose as in an ω-category. Across objects, composition 𝒦(a, b) ⊗ 𝒦(b, c) → 𝒦(a, c) is Gray, so for cells x, y of positive dimension in consecutive homs there is a directed interchange cell x ⊗ y, the **Gray cell**. Plain weak ω-categories are the one-object, no-crossing special case.

**Schemes.** A *scheme* P of dimension n is a finite list of clauses over a generic n-cell t : u → v (a cell of some hom). There are two kinds of clause.
- An *∃-clause* declares a new cell cᵢ : Aᵢ. Here Aᵢ is a type whose endpoints are built from t, its iterated boundaries and earlier clause cells, using only the ω-category operations of the hom (composites, identities, whiskerings, coherence cells). The clause may require cᵢ to carry a scheme again, P itself or another scheme of dimension n + 1.
- A *∀-clause* states that a cell s(t, y), built from t and a cell y ranging over all cells of some boundary shape, carries a scheme Q.

A *P-structure* on t is a choice of all ∃-clause cells, recursively, so an infinite tower, interpreted as a greatest fixed point (as for coinductive invertibility). Equivalently, a P-structure is a map out of the *walking P-cell* W_P, the colimit of the finite stages of the unfolded tower, extending t.

**Examples.**
- **Inv.** s, s′ : v → u; l : s ∗ t → 1_v [Inv]; r : t ∗ s′ → 1_u [Inv]. This is coinductive invertibility. W_Inv is a coinductive walking equivalence.
- **RInv.** s : v → u; r : t ∗ s → 1_u [RInv]. Coinductive right inverses.
- **LAdj.** s : v → u; η : 1_u → t ∗ s [LAdj]; ε : s ∗ t → 1_v [LAdj]; two triangle cells [Inv]. Adjoints at every level.
- **Idem** (t an endomorphism). c : t ∗ t → t [Inv].
- **Ps** (a ∀-scheme). For every y of positive dimension composed before t, the Gray cell y ⊗ t carries Inv. With the same clause on the boundaries of t, these are the pseudo transformations and modifications among lax ones.

**Known.**
1. *Inv is closed under everything.* Full coherence cells carry Inv. So do composites (and more generally pasting composites) of Inv-cells. This holds in weak ω-categories (Benjamin–Markakis, arXiv 2406.12127, Prop. 16 and Thm 33), and there the inverse of a composite is built syntactically by a meta-operation. In the Gray setting:
   - whiskerings of Inv-cells carry Inv;
   - a Gray cell x ⊗ y carries Inv when x or y does;
   - a Gray cell carries Inv when its later factor carries Ps.

   These are proved semantically, via Dᵐ ⊗ Eᵏ ≃ Dᵐ ⊗ Dᵏ⁻¹ for E the walking invertible cell.
2. *Not every scheme is closed under composition.* In the 1-category Set, Idem-structures are idempotents, and a composite of idempotents need not be idempotent.
3. *Inv is a property.* The space of Inv-structures on a cell is empty or contractible in the coinductive weak setting. W_Inv → Dⁿ⁻¹ is an equivalence there. It is not an equivalence in the raw inductive setting (Hadzihasanovic–Loubaton–Ozornova–Rovelli, arXiv 2404.14509).
4. *RInv is not a property.* Right inverses are not unique.
5. *∀-clauses cannot be certified from data.* Freely attaching a generic earlier cell y at the source of t makes "y ⊗ t invertible" equivalent to "t invertible". So a Ps-structure on t that is a consequence of data alone is just invertibility.

## 2. Questions

**Q1 (main: closure criterion).** Give a criterion on schemes, as decidable as possible from the clause list, that determines for each of the following operations whether P-structured cells are closed under it, in every model of each setting. The criterion should be a general theorem with explicit countermodels for the negative direction:
- (a) full coherence cells carry P;
- (b) whiskering a P-cell by any cell of lower dimension gives a P-cell;
- (c) a vertical composite of P-cells is a P-cell;
- (d) a pasting composite whose top-dimensional inputs are P-cells is a P-cell;
- (e) a Gray cell x ⊗ y is a P-cell when one factor, or a specified factor, is a P-cell.

We expect something like the following, and would like it proved or refuted.
- If every ∃-clause type is built from t and earlier clause cells only, then (a) holds.
- If, in addition, the clause types are "functorial in t", then (b) and (e) hold. Functorial means that the endpoints of each clause type are images of fixed shapes under the operations, so that a functor or a Gray whiskering transports clause cells.
- (c) and (d) hold when the clause types are additionally "multiplicative". This is the condition Inv, RInv and LAdj satisfy and Idem fails: the clause data for t₁ ∗ t₂ is assembled from the clause data of t₁ and t₂.

Please state the precise conditions, and whether they are also necessary.

**Q2 (syntactic admissibility).** In the cases where Q1 gives closure, is the P-structure on the composite (or Gray cell, or coherence) produced by a *uniform construction*? That is, a finite recipe from the P-structures of the inputs and coherence cells, applied at every level of the tower, as Benjamin–Markakis do for Inv in weak ω-categories. The question is most important for Inv itself in the strict and weak Gray settings, and for the Gray-cell rules of item 1 above. Are those rules admissible from the Inv clauses plus coherence cells? Or is there a Gray cell x ⊗ y with x Inv-structured whose Inv-structure cannot be given by any uniform recipe of this kind? A negative answer should come with the obstruction.

**Q3 (properties).** Characterize the schemes P for which the space of P-structures on any cell is empty or contractible, in the coinductive weak setting. Equivalently, for which W_P → Dⁿ⁻¹ is a monomorphism onto its image (the inclusion of a full sub-object)? Is LAdj such a scheme in the ω case, or only after truncation? Is there a syntactic sufficient condition, of the kind "every clause cell is uniquely determined up to an Inv-cell by the earlier ones"?

**What would help most.** One theorem covering Q1 for all schemes and all five operations, with the uniform-construction statement of Q2 as part of its positive direction, and the property criterion of Q3. Inv, RInv, LAdj, Idem and Ps should come out as instances.
