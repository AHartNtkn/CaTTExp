# An explicit all-degree presentation of free higher categories with directed interchange

*A self-contained problem. The setting and the results it builds on are stated in §1–§2 of `notes/conjectures/answered/lax-interchange-every-dimension-r10-2026-11-20.md` (summaries (K43)–(K73), each with a reference to its full proof). That file is the background for this one. Its notation is used here unchanged.*

## Background, in brief

Work with strict ω-categories in which interchange along k-cells, for each pair k < l, is replaced by a directed cell (an *elementary interchanger* χ). A finite pasting diagram Γ generates free objects F_E(Γ) for each *admissible* theory E on the fixed signature of the completed theory **T₁₂** ((K47)). The signature is:
- strict associative and unital composition;
- an elementary interchanger for every pair k < l;
- naturality cells for each varying argument, with orientation fixed by Leibniz signs;
- higher cells between routes;
- the auxiliaries of (K47): signed lifts of binary globe tensors at every cut, H_L, H_R, K, J and the shifted join.

Among the admissible theories:
- **V** is the least one ((K58)). It consists of the forced base B, with its defining pairs, and the guarded quotient equations of round 5.
- **V + S**, for S ⊆ {R, inner law}, adds the switched laws.

What is known about these free objects:
- They are finite in each degree at fixed boundaries, and equality and reachability in them are decidable ((K50), (K58), (K65), r10 Response 3).
- (K52) gives convergent rewriting systems for T₁₂ degree by degree, but its forbidden-factor lists are produced recursively and no closed description is known.
- (K65) and r10 Response 3 give normal forms for V + S by rank selection over the finite raw layers.
- Both constructions are *recursive procedures*. They are given relative to a raw syntax that is described in prose across several rounds: the signature, the contextual letters of each degree and their weights, the defining pairs of B, and the guards.

## Why it matters

A proof assistant (Agda, without universes, with `--safe`) is meant to check these free objects, not trust them. The generic part is already formalized:
- normal forms as the first word per component of a one-step graph, for any finite presentation;
- the finiteness of word universes from a positive conserved weight;
- the decision of directed reachability with supports.

What cannot be formalized as things stand is the input that this machinery needs in each degree: the raw syntax itself. Degree four exists. No uniform description of degree d does. A presentation that is explicit, finite in its schemas and uniform in d is what would let the whole tower be defined once by induction on degree, instead of degree by degree.

## Questions

1. **(Signature.)** Give the signature of T₁₂ as finitely many operation schemas, indexed by degree d, cut k, and the shape of the arguments. Give typing rules (source and target of each operation, as functions of the arguments' faces) such that the raw d-terms on a finite pasting diagram form an inductive family defined uniformly in d by induction on d. Say which schemas are new at each d and which are instances of a uniform rule.

2. **(Equations.)** State as finite schemas over the signature of question 1, uniform in d:
   - the defining pairs of B;
   - the guarded equations of V, with each guard as an explicit decidable condition on the arguments;
   - the switched laws R and inner law.

   Say which equations are one-step replacements inside a contextual word and which act only on lower labels (r10 Response 3 says that above degree 4 the new equations act only inside lower labels).

3. **(Contextual letters and weights.)** Give a closed description of the contextual d-letters between fixed normalized lower faces. Give an explicit positive weight on letters, conserved by every equation of question 2, and an explicit bound on the operands and whiskers of a letter in terms of the faces. The aim is a computable finite list of letters at fixed boundaries, given by a formula rather than by a search whose termination is argued separately.

4. **(Closed form above degree four.)** (K50) and (K52) record that no closed-form normal-form theorem is known above degree 4.
   - Give one for T₁₂, for V, or for V + S. One form it could take is a combinatorial model whose d-cells are explicit data, for example decorated cut sequences in a Steiner complex as in r10 Response 1, with equality decided by comparing that data.
   - Or show in a precise sense that none exists. For example: the forbidden-factor languages of (K52) are not regular uniformly in d, or the fibre sizes of (K65) are not given by any primitive-recursive formula in the boundary.

5. **(Degree five on grids.)** As a test case, give the answers to questions 1–3 explicitly for degree 5 on the suspended grids Γ_{m,n} = Σ[m] ∨ Σ[n]. Confirm or correct the claim that the 5-letters there are exactly the positional squares, whose composite-operand squares reduce to pastes of atomic squares (r10 Response 1, r9 Response 2).

## What counts as a solution

Definitions precise enough to transcribe into a proof assistant without choices left to the reader, with proofs of:
- the typing rules;
- conservation of the weight;
- finiteness of the letter lists;
- that the presentation defines the same free objects as the prose presentations of (K47) and (K58).

For question 4, either the normal-form theorem with proof, or the precise impossibility result. Partial answers are welcome, for example questions 1–3 for V alone, or for d ≤ 6.

## Literature status

Not searched specifically for this prompt. The relevant searches of r10 §6 (2026-11-18 to 2026-11-20) found no uniform-in-degree presentation of free Gray-like structures with directed interchange in every pair of dimensions.
