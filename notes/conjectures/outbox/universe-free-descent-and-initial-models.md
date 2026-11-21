# Descent for cocartesian fibrations and initial models of positive signatures in (∞,ω)-categories

## Setting and notation

Let `Cat_ω` denote the (∞,1)-category of (∞,ω)-categories (for definiteness, complete Segal Θ-spaces in the inductive sense, as in Loubaton, *Categorical theory of (∞,ω)-categories*, arXiv:2406.05425). Answers for the coinductive variant or for (∞,∞)-categories in the sense of Gepner–Heine are equally welcome; please say which one you use. `Cat_ω` is cartesian closed and also has the (lax) Gray tensor product `⊗`, closed on both sides.

For an (∞,ω)-category X:
- `Cocart(X)` is the (∞,1)-category of cocartesian fibrations over X (in the sense whose straightening is Loubaton's Thm 4.1.4.2 / Gepner–Heine's Thm 1.8.2, `Cocart(X) ≃ Fun(X, Cat_ω)`) and functors over X preserving cocartesian arrows.
- `Cat_ω/X` is the slice. Base change along `g : Y → X` is `g* : Cat_ω/X → Cat_ω/Y`.
- A colimit `X = colim_{k∈K} D_k` is **van Kampen for a class 𝓕 of maps** if (universality) for every `p : E → X` in 𝓕 the canonical map `colim_k (D_k ×_X E) → E` is an equivalence, and (effectiveness) restriction induces an equivalence from the full subcategory of `Cat_ω/X` on maps in 𝓕 to the limit over K of the corresponding full subcategories of `Cat_ω/D_k`, the limit taken along base change.
- An (∞,ω)-category is a **groupoid** if all its cells are invertible, and **n-truncated** if it is an n-truncated object of the (∞,1)-category `Cat_ω` whose cells above dimension n are invertible (so 0-truncated = discrete set).

Known facts, for orientation:
- Colimits in `Cat_ω` are not van Kampen for all maps: the pushout `[2] ≃ {0<1} ⊔_{1} {1<2}` is not preserved by base change along `{0<2} → [2]` (Ayala–Francis, *Fibrations of ∞-categories*, Higher Structures 4 (2020), Ex. 1.6).
- In the (∞,1) case, cocartesian fibrations descend along cocommas, sequential colimits and localisations, and straightening follows from descent (Sattler–Wärn, arXiv:2603.28688, Thm 5.7, Lemmas 6.1–6.2, Thm 8.1).
- A functor is a cocartesian fibration iff it is exponentiable and locally cocartesian (Gepner–Heine, arXiv:2608.02592, Thm 1.8.11). Loubaton proves that base change along classified left cartesian fibrations preserves colimits (Thm 3.2.3.15).
- Impredicative encodings of inductive types are correct only with a naturality condition (Awodey–Frey–Speight, arXiv:1802.02820); dinatural transformations `X^X → X^X` on Set form a proper class while Barr dinatural ones are exactly the iterates (Paré–Román, JPAA 128 (1998), §2.2 and Prop. 1).

## Questions

**1 (main).** Determine, for `Cat_ω`, the most general descent statement of the following form, and prove it.

(a) For every small diagram `D : K → Cat_ω` with colimit X, every colimit is van Kampen for the class of cocartesian fibrations: `Cocart(X) → lim_k Cocart(D_k)` is an equivalence, and base change along any cocartesian fibration `E → X` preserves all colimits.

(b) For every small diagram indexed by an ∞-groupoid K, the colimit is van Kampen for the class of **all** maps.

(c) For every ∞-groupoid Y in `Cat_ω` and every n ≥ −1, maps `E → Y` whose fibres are n-truncated descend uniquely along the unit `Y → τ_{≤n+1} Y`: base change along it is an equivalence between maps into `τ_{≤n+1} Y` with n-truncated fibres and maps into Y with n-truncated fibres.

(d) The oriented version: replacing `Cat_ω` by the oriented category of (∞,ω)-categories with lax transformations (Gepner–Heine, *Fibrations in oriented category theory*, arXiv:2607.18418), state and prove the analogue of (a) in which the gluing data are lax (oriented) rather than invertible, or show that only the invertible version holds.

Then characterise exactly which pairs (class of maps 𝓕 closed under base change, class of colimit diagrams) are van Kampen in `Cat_ω`. If a full characterisation is out of reach, prove (a)–(c) and give the boundary by counterexamples, in particular: is every colimit van Kampen for the class of exponentiable maps? (Ayala–Francis show exponentiable fibrations are classified by a flagged ∞-category; does that classification imply descent along all colimits, or only along those colimits that also compute colimits of maximal subgroupoids?)

**2.** Call a finite signature Δ over one sort X **strictly positive** if it is a finite list of operations and cells of the following kinds, where `S(X)` ranges over *source expressions* and `T(X)` over *target expressions*:
- source expressions are built from X and fixed (∞,ω)-categories by finite limits (including pullbacks over fixed objects), small colimits, `⊗` and `×` with fixed objects, and cotensors `[A, X]` with A fixed;
- target expressions are built from X and fixed objects by small colimits and by `⊗`, `×` with fixed objects (so they preserve colimits in X, or at least sifted colimits);
- an **operation** is a map `S(X) → T(X)`;
- a **cell** is a k-cell between two composites of operations, required invertible or not;
- a **mark** restricts X to a class closed under limits and filtered colimits and reflective in `Cat_ω`, e.g. "X is n-truncated".

A model is an object X with the operations and cells; model morphisms are maps commuting with the operations up to (coherent) cells, invertible where the signature's cells are, and the (∞,1)-category of models is `Mod(Δ)`.

Prove that `Mod(Δ)` has an initial object for every strictly positive Δ, and that the forgetful functor `Mod(Δ) → Cat_ω` preserves the initial object's universal property at every level (maps from the initial model to any model form a contractible space). Give the maximal syntactic class for which this holds, and an explicit signature just outside it with no initial model. Equivalently, in end notation: show that the strong-dinatural end `∫_{(A, σ) ∈ Mod(Δ)} A` (the limit of the forgetful functor) exists and is the carrier of an initial model.

Important instances, to check the class is right: free (∞,ω)-categories on graphs whose edges are labelled by objects (`ΣB_e → X` under two points); the n-truncation `(X n-truncated, A → X)`; the family `U → Θ₀` over the set of rose trees with fibre over `node(t₁…t_k)` the wedge `ΣU_{t₁} ∨ … ∨ ΣU_{t_k}` (so that the fibre over a tree T is the free (∞,ω)-category on the pasting diagram T), presented as a signature over a fixed base: `(X, p : X → Θ₀, a : Φ_p(X) → X over Θ₀)` with Φ_p built from pullbacks over Θ₀, wedges and suspensions.

**3 (fallback).** If Question 2 fails in the generality stated, give the largest subclass for which it holds, and show that initial models of strictly positive signatures are not derivable from finite limits, finite colimits and the descent statements of Question 1: a model of those (an (∞,1)-category with the corresponding structure) in which some strictly positive signature has no initial model.

## Why it matters

A type theory for (∞,ω)-categories without a universe (no object of all objects) has to state the consequences of a universe as rules. Question 1 would make one descent rule replace effective quotients, disjoint coproducts and the Grothendieck construction; Question 2 would make one initial-model rule replace truncations, free objects on labelled graphs, inductive objects and object-valued recursion along trees.

## What would count as a solution

For Question 1: proofs of (a)–(c), with (d) proved or refuted, and either a characterisation of the van Kampen pairs or counterexamples marking the boundary. For Question 2: a proof for the stated class, or a precise maximal class with a counterexample just outside it. A reference to the literature for any part counts, with the exact statement.
