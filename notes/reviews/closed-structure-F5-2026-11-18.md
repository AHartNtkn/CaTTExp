# Independent check of `closed-structure.md` F.5, Prop. F1 (2026-11-18)

*The proposition reviewed is Prop. F1 in `closed-structure.md` F.5, which is on branch `claude/project-thread-h659a3` (PR #61) and owned by the CLOSED thread. It claims that in the free strict Gray monoid with lax interchangers, there is a 2-cell t ⇒ u iff inv(u) ⊆ inv(t), and that it is unique. This is the monoidal core of Question 1 of `conjectures/outbox/gray-pasting-types.md`, which has been sent to a researcher. Compare any researcher answer to that question against this review.*

## Verdict

**Correct after one hypothesis fix and one restatement.** The proof's four steps hold for 1-cells with the same **string diagram**. With only "the same source, target and events", the statement is false.

## C1. The hypothesis is too weak: counterexample

Take generators `f, g : A → A`, and these 1-cells:

- `t = f ; g` and `u = g ; f`. Both run A → A with events {f, g}. They are dependent, so `inv(t) = inv(u) = ∅` and `inv(u) ⊆ inv(t)`. But no 2-cell t ⇒ u exists, because every generating 2-cell is an interchanger and interchangers only reorder independent events.
- Planar variant: on `A ⊗ A`, take `t = (f ⊗ A);(A ⊗ g)` (f on the left wire) and `u = (g ⊗ A);(A ⊗ f)` (g on the left wire). Both have empty inversion sets, and no 2-cell connects them.

**Fix.** Require t and u to have the same image in the free *strict* monoidal category, that is, the same planar progressive string diagram (Joyal–Street). Then the events are the nodes of that diagram, and repeated generators cause no trouble. The interchangers preserve the diagram, so "same diagram" is also necessary for any 2-cell to exist.

The same flaw is in the sent prompt `outbox/gray-pasting-types.md`, Question 1 ("same source, target and generators"). A researcher will probably answer it with this counterexample. The intended statement is the one with the same diagram.

## C2. Restatement of the conclusion

A hom-category of 𝒢₀ is a *disjoint union* of posets, one for each string diagram. Each component is an interval of the weak order. "Each hom-category is a poset, isomorphic to an interval" holds component by component.

## C3. The four steps (with the C1 hypothesis): correct

1. **Generators.** 𝒢₀ has no generating 2-cells, so its 2-cells are vertical composites of whiskered interchangers between generating 1-cells. The decomposition at composite 1-cells is part of the Gray monoid axioms. *Notational slip:* "X_{f, b⊗g} = b ⊗ X_{f,g}" puts b on the wrong side. For an object B between f and g, it should read `X_{f, B⊗g} = X_{f⊗B, g}`, or, with B outside, `X_{f, g⊗B} = X_{f,g} ⊗ B`. This does not affect the proof.
2. **One inversion per generator.** A whiskered `X_{f,g}` swaps two events that are adjacent in time and on disjoint wire intervals. It takes "right first" to "left first" and changes no other pair's order. So 2-paths remove inversions one at a time, and a 2-cell t ⇒ u needs `inv(u) ⊆ inv(t)`. Checked.
3. **Existence.**
   - *1-cells over a fixed diagram D are the linear extensions of D's precedence order P.* Any order compatible with precedence slices D, and distinct orders give distinct words of whiskered generators.
   - *P is 2-dimensional.* "Precedence, then left-first" and "precedence, then right-first" are linear orders whose intersection is P. This is the planar st-graph fact behind dominance drawings (Di Battista–Tamassia–Tollis) **[recall]**. It holds because incomparable nodes of a progressive planar diagram are separated by a cut, so one is consistently left of the other.
   - Björner–Wachs (JCTA 1991): for a 2-dimensional poset labelled by one realizer, the linear extensions form a weak-order interval **[recall: theorem number]**.
   - Inversion sets are value pairs, so containment is the *right* weak order, whose covers swap positions i, i+1, i.e. events adjacent in time. A saturated chain from u to t stays in [u, t], which lies inside the interval L(P). So each step swaps two incomparable, hence independent, events and is a whiskered interchanger. Checked.
4. **Uniqueness.**
   - A 2-path is a maximal chain of [u, t], since each step is determined by which adjacent pair it swaps. Maximal chains are reduced words of `u⁻¹t`.
   - Matsumoto–Tits connects any two reduced words by commutation and braid moves, through reduced words of the same element, so through 2-paths.
   - A *commutation move* is strict interchange in the hom 2-category.
   - A *braid move* reverses three consecutive events, so the three are pairwise incomparable, hence pairwise independent. Order their positions left to right as f, g, h. Naturality of `X_{f,−}` with respect to the 2-cell `X_{g,h}` in the right factor, together with the decomposition of `X_{f,−}` at the composites `(g⊗1)(1⊗h)` and `(1⊗h)(g⊗1)`, gives equality of the two hexagons. This is a Gray monoid axiom, and it holds for the lax tensor as well.
   - So any two 2-paths are equal. Checked.

## Consequences

- With the C1 fix, Prop. F1 settles the monoidal core of D11 Question 1. The closed-structure remainder (events inside closures, a premonoidal Theorem A) is still open, as F.5 says.
- When the gray-pasting-types response arrives, check it for C1. Then compare its Question 1 answer with this review.
