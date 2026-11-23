# Conservativity obligations of the ⊢hpol fast path

*Owner: thread "Prove polygraphs homotopical iff bubble-free" (HPOL). Started 2026-11-23. Open-issues row B26. Spec: `spec/04-context-checking.md` §4.4.*

**Obligation.** The spec (§4.4) admits a base rule into the fast path only after this is proved in Agda: whenever the test accepts Γ, then F(Γ) ≃ Free(Γ). Then the trivial resolution (Γ′ = Γ, W′ = ∅) of §4.3 is valid. The proof must formalize the homotopicality result, not cite it (Chanavat, arXiv 2603.22242, Cor. 3.39, for the first rule). No rule has a formalized obligation yet, so the fast path is empty for now.

## 1. What can be formalized, and the decision

Free(Γ) is an (∞,ω)-category. The repository's Agda has no model of (∞,n)-categories (E11, gap S1). So "F(Γ) ≃ Free(Γ)" cannot be stated directly in Agda today. Each obligation is therefore split into three layers, and each layer is formalized on its own:

- **L1 (syntactic).** The test accepts exactly a named class of contexts.
- **L2 (combinatorial core).** For every strict cell c of F(Γ), a finite complex E(c) that models the fibre of Free(Γ) → F(Γ) over c is contractible. The certificate is a Stong dismantling: a sequence of beat-point removals ending in a point. This is a finite, purely order-theoretic statement, and the passage from it to contractibility of the order complex is elementary (Stong 1966). L2 is formalized in Agda.
- **L3 (bridge).** Γ is homotopical iff every fibre E(c) is contractible, and π₀ of the fibres gives the strict cells. This is where (∞,n)-category theory enters.

**Decision for L3: the internal route.** Inside the kernel a base is read through CaTT terms. The checker's fast path replaces weak terms over Γ by strict cells of F(Γ). That replacement is valid exactly when the strictification π_Γ from the free CaTT model on Γ to F(Γ) is a trivial fibration, i.e. **RC_id(∞)(Γ)**: parallel terms with the same strict image are joined by a term whose strict image is an identity, in every dimension (relative-coherence prompt, item 7). This is a statement about the project's own syntax, so it can be proved in Agda with no semantic citation: an Agda function produces the connecting terms, and the certified checker re-checks them. So L3 for a rule means: prove RC_id(∞) for every context the rule accepts. The semantic statement F(Γ) ≃ Free(Γ) then follows from the comparison between CaTT models and (∞,ω)-categories. That comparison is gap E11 (S1), and it is shared by every use of CaTT in the project, not specific to ⊢hpol.

The fallback, if the internal route stalls, is a combinatorial model of (∞,2)-categories in Agda (a Segal-type presheaf model on Θ₂ with finite data) with the dimension-2 theorem proved in it. That is a larger project, and it overlaps E11.

## 2. First rule: positive path 2-polygraphs

**L1: done** (`src/CaTTExp/Lim/Hpol.agda`, `--safe`, type-checked locally 2026-11-23).
- `PosPath2` specifies the class inductively. Its pieces are fresh names, objects, 1-cells between objects, and 2-cells α : s ⇒ t where s and t are `IsPath` derivations: nonempty binary `comp` trees of 1-cell variables with the endpoints of α.
- The decision procedure `hpolC` returns a derivation, so `hpol-sound : Γ ⊢hpol → PosPath2 Γ` holds by construction.
- `hpol-complete : PosPath2 Γ → Γ ⊢hpol` proves the converse, using `ends-unique` (a path's endpoints are determined by the term).
- The earlier informal claim "the test selects exactly this class" is now a theorem. All earlier examples still check.

**L2: plan and evidence.**
- *Model of the fibre.* Take a strict 2-cell c of a positive 2-polygraph. Its string diagram is rigid: no floating components, and every vertex has inputs and outputs. The 2-paths representing c are the linear extensions of its event poset P_c (relative-coherence prompt, item 5; the dimension-2 core of `homotopy-polygraphs-2026-11-19.md`). Its tier encodings are the ordered partitions of P_c into nonempty antichains compatible with the order, ordered by refinement. Call this poset Π(P_c). (In dimension 2 a tier is determined by its set of vertices, because planarity fixes the horizontal order.)
- **Lemma D (dismantling).** Let P be a finite poset and m a maximal element. Let Q_m = {π ∈ Π(P) : the last block of π is {m}}, so Q_m ≅ Π(P − m). Remove the elements outside Q_m one at a time, ordered by the key below. Write e(π) for the number of elements in blocks after m's block.
  - Order: decreasing e(π). Among equal e, those where m shares its block come first. Among those, finer partitions come first. Among the partitions where m is alone in its block, coarser ones come first.
  - When removed, each element is a beat point:
    - If m shares its block B, it is an *up* beat point. Its remaining refinements have the minimum …|B∖{m}|{m}|….
    - If m is alone in a non-final block B_i, it is a *down* beat point. Its remaining coarsenings have the maximum …|{m} ∪ B_{i+1}|….
  - By induction on |P|, Π(P) dismantles to a point, so it is contractible.
- *Evidence:* `tools/order_partition_dismantle.py` checks exactly this order and these partners on 600 random posets with at most 5 elements, with 0 failures. A greedy search finds every Π(P) dismantlable to a point (120 posets) and onto Q_m (150 posets).
- *Proof of Lemma D (HPOL, 2026-11-23).* Write x = …|B_i|… with m ∈ B_i. Write key(x) = (−e(x), 0 if m shares its block and 1 if m is alone, −ℓ(x) if shared and +ℓ(x) if alone), where ℓ is the number of blocks. "Present" means in Q_m or not yet removed, i.e. key ≥ key(x). Equal keys never interfere: a strict refinement or coarsening changes ℓ.
  - *Shared case.* y = …|B_i∖{m}|{m}|… is in Π(P): B_i is an antichain, and m is maximal, so nothing in B_i∖{m} lies above it. y refines x, e(y) = e(x), and m is alone in y, so y is present. Let z be a present strict refinement of x. Its m-block C is contained in B_i, and e(z) = e(x) + (elements of B_i in sub-blocks after C).
    - If e(z) > e(x), then key(z) < key(x). Also z ∉ Q_m, since z ∈ Q_m would mean e(z) = 0. So z is already removed.
    - If e(z) = e(x), then C is the last sub-block of B_i. If |C| ≥ 2, then key(z) < key(x) because ℓ(z) > ℓ(x), so z is already removed. If C = {m}, then z splits B_i∖{m} and then {m}, so z refines y.
    - Hence y is the minimum of x's remaining up-set.
  - *Alone case.* Here e(x) > 0, so B_{i+1} exists. y = …|{m} ∪ B_{i+1}|… is in Π(P): nothing in B_{i+1} is below m (it comes after m) or above m (m is maximal). y coarsens x and e(y) < e(x), so y is present. Let z be a present strict coarsening of x. Its m-block D is a union of consecutive blocks B_j ∪ … ∪ B_k with j ≤ i ≤ k.
    - If D = {m}, then e(z) = e(x) and ℓ(z) < ℓ(x), so key(z) < key(x) and z is already removed.
    - If k = i and j < i, then m is shared in z and e(z) = e(x), so key(z) < key(x) and z is already removed.
    - If k > i, then D contains {m} ∪ B_{i+1}, so z coarsens y.
    - Hence y is the maximum of x's remaining down-set.
  - *Conclusion.* After all removals, Q_m ≅ Π(P − m) as posets (drop the final block {m}). Π(∅) is a point. Induction on |P| gives a dismantling of Π(P) to a point. Removing a beat point gives a strong deformation retract of the order complex (Stong 1966), so Π(P) is contractible. A strict 2-cell with no vertices has P = ∅, and its fibre is a point.
- *To do:* the Agda formalization:
  1. finite posets as lists with a decidable order;
  2. ordered partitions and refinement;
  3. beat points and dismantling sequences;
  4. Lemma D;
  5. the event poset of a strict 2-cell of a `PosPath2` context.

**L3: open.**
- RC_id(∞) for positive path 2-polygraphs. Known: RC_id(3) holds iff F(Γ_{≤2}) is bubble-free (relative-coherence r10, item 39), and positive path 2-polygraphs are bubble-free.
- Higher degrees are open for contexts that are not strong Steiner. Finite strong-Steiner contexts satisfy RC_id(∞) (r8 Response 18), but a loop such as μ : a · a ⇒ a is not strong Steiner.
- The expected route: RC_id(∞) from contractible fibres. The fibres are L2, and the relative-coherence round's Response 14 shows the converse direction.

## 3. Remaining rules (§4.4 list)

Pasting contexts and their Gray tensors, graphs, positive-to-one polygraphs, orientals, no-matching positive 3-polygraphs, top weight ≤ 2, and the closure rules (suspension, graph assembly, adjoining 1-generators in dimension 2, vertex attachment). Each needs its own L1–L3. Pasting contexts and strong-Steiner contexts already have L3 on paper (r8 Response 18), so they are the next candidates after the first rule. Graphs (no 2-cells) are the simplest case: L2 is trivial (F(Γ) is the free category and every fibre is a point), and L3 needs RC_id(∞) for 1-dimensional contexts, which is not covered by the strong-Steiner theorem when the graph has cycles.
