# A combinatorial model of free higher categories with directed interchange above degree four, or a proof that none exists

*A self-contained problem. Background:*
- *the setting, the theories T₁₂, V, V + S and their free objects F_E(Γ) on a finite pasting diagram Γ: §1–§2 of `notes/conjectures/answered/lax-interchange-every-dimension-r10-2026-11-20.md`, summaries (K43)–(K73);*
- *the explicit all-degree presentation that this problem builds on: `notes/conjectures/answered/directed-interchange-all-degree-presentation-2026-11-22.md`, Response 1 and its verification.*

*Notation is used as there.*

## What is known

- **Finiteness and decidability.** Each layer of F_E(Γ) with fixed faces and fixed top weight is finite, and equality in it is decidable. The all-degree presentation (Response 1, §1–§3) gives:
  - constructor schemas uniform in degree;
  - the equations of B, V and the switches, with explicit guards;
  - a positive conserved charge;
  - a finite box of contextual letters, bounded by the two faces.
- **What the top relations are above degree four.** In V, a top relation in degree d > 4 is one of:
  - the outer (cut-0) unary moving split;
  - the stationary split;
  - the transports.

  The switches R and the inner law act only inside lower labels. Guarded rows reduce to unit specializations on free objects (K58). Every other proper head (squares, positive-cut unaries, joins, seeds, raising bridges) is a free generator at the top.
- **Normal forms.** Two constructions are known, and both are procedures:
  - the first word per connected component of the one-step graph on a weight layer (r10 Response 3, (K65); formalized as `src/CaTTExp/Uniform/Present.agda`);
  - (K52)'s convergent rewriting systems, whose forbidden-factor lists are produced recursively.
- **The "closed form" of Response 1, §4.** It encodes a cell by its action on every transformation array in [N]^{A×[N]} that satisfies the pair list. This is correct but is only the regular-representation embedding of a finite quotient. It is not a description of the cells.
- **One case with a genuinely closed form.** In degree 5 on two-chain grids Σ[m] ∨ Σ[n] there are no top relations. A cell there is simply a typed list of δ, N_L, N_R, h₁ records over normalized lower labels (Response 1, §5).

## An attempt, and where it stops

Attempted 2026-11-23 in the S3a thread.

**Expanding orientation.** Orient each split from the direct unary to its two-letter expansion. This terminates: the letter count goes up, but the total charge is conserved and every letter has positive charge, so the letter count is bounded.

It is not confluent. Expanding a unary U(z₁z₂, g₁g₂) moving-first and stationary-first gives the four atomic pieces U(zᵢ, gⱼ) in two different orders. The two orders are equal in V because both equal the direct letter. No single top relation identifies them, because positional squares are letters, not equations.

**Contracting orientation.** Orient the other way, merging adjacent pieces. This terminates, since the length goes down. It is not confluent either. A three-piece word such as U(z₁,g₂) U(z₂,g₂) U(z₂,g₁) has two irreducible contractions:
- U(z,g₂) U(z₂,g₁), by a moving merge;
- U(z₁,g₂) U(z₂,g),  by a stationary merge.

Both are equal to the original word. *Caveat:* that this word is typed in the stated order of the two variations has not been checked against the state lists of Response 1, §2.

**Conclusion of the attempt.** In both orientations, the equivalence that the splits generate on words of atomic pieces is the real object of study. Its classes look like "linearisations of a family of rectangles with recursive guillotine cuts", but the L-shaped example shows that the order ideals involved need not be rectangles. I did not find the description.

## Questions

1. **(Atomic pieces.)** Fix a degree d > 4, a pasting diagram Γ, and normalized lower labels. Describe the equivalence that the moving splits, stationary splits and transports generate on typed words whose cut-0 unaries have atomic moving operand (a single (d−1)-letter) and atomic stationary edge. Give a combinatorial invariant that is complete for it. Candidates:
   - a heap or trace in the sense of Cartier–Foata, with contextual commutations;
   - a set of rectangles in the (moving piece) × (stationary edge) grid with recursive cut data, as in the decorated cut sequences of r10 Response 1;
   - a Steiner-complex datum.

   Equality must be decided by comparing the data.
2. **(Closed form.)** Using 1 and the freeness of all other heads, give a closed-form normal-form theorem for V above degree 4. A cell between fixed faces should be explicit data (a word in the free heads interleaved with the invariant of 1), with composition, whiskering and substitution as explicit operations on that data. Extend to V + S, where the switches act only on lower labels, and to T₁₂, where the auxiliaries of (K47) must also be treated.
3. **(Or impossibility.)** If no such description exists, prove a precise negative statement. Examples:
   - the forbidden-factor languages of (K52) are not regular uniformly in d;
   - the class sizes in a weight layer (the fibres of (K65)) are not given by any primitive-recursive formula in the boundary data;
   - the word problem for the split equivalence of 1, taken uniformly over Γ, has a lower complexity bound incompatible with any explicit data model.
4. **(Test cases.)**
   - Answer 1 explicitly for a single outer unary on a moving cell that is a composite of n atomic letters and a stationary path of k edges, as a function of n and k.
   - Say whether the number of classes of fully expanded words equals the number of guillotine partitions of an n × k grid, or something else.
   - Give the smallest Γ and d on which the L-shaped critical pair above is typed.

## What counts as a solution

Definitions precise enough to transcribe into Agda (no universes, `--safe`). That means:
- the data model as an inductive family over the lower labels;
- the map from words to data;
- a proof that the map is complete and sound for the equalities of V, V + S or T₁₂.

For question 3, the precise impossibility result with proof. Partial answers are welcome, for example question 1 alone, or V alone with d ≤ 6.

## Literature status

Not searched specifically for this prompt. Relevant directions:
- Zamolodchikov / higher Bruhat-order presentations of commuting squares;
- guillotine partitions and the combinatorics of rectangulations;
- trace monoids with contextual commutations;
- normal forms for free Gray categories (Forest–Mimram; Gurski).
