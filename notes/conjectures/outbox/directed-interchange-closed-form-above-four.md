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

# Researcher Response 1

**The normal form is a list of whole contextual letters.** Normalize the lower fields and the three outer 1-arrow transports. Forbid a neighbouring pair exactly when it is the two children of one native subdivision, with their actual pads. This is a condition on two records over the lower skeleton. The proposed mixed critical pair has no instance, in any degree or diagram. The exceptional step in the proof is at degree five, where the test for such a pair takes place in the degree-four equations. We give a finite exhaustion for that step below.

## The alphabet and the two tests

Fix the theory and the finite tree. Use the rank-ordered two-sided pads, chronological words, positive grades and finite lower box of the [all-degree presentation, §§1–3](../answered/directed-interchange-all-degree-presentation-2026-11-22.md#1-constructors-and-boundaries). Through degree four use the known lower equality. In larger degrees use the construction here by induction. Specialize units before collecting proper letters. A rigid letter is its full contextual record, including its constructor, operands and both pads at each rank. At an outer unary identify records by the 1-arrow transports (8). Here are concrete conventions for doing this.

* At the outer string put the two operands on the **whole** successive sides of a cut, moving exterior 1-arrows onto the operands. Keep all pads of rank at least two outside the head, with lower values collected. In left variation put the cut immediately before the first outer span on which the stationary 2-word has a step. In right variation put it immediately after the last such span. This means first and last in the outer string. Within the stationary 2-word keep chronological order, even when different spans are interleaved.
* To reach this cut, take each intervening inactive 1-arrow off the stationary word and put it on the moving operand. A 2-word is a list of generating advances with their 1-arrow placements. Its restriction to its active outer interval, together with the actual exterior 1-arrows, recovers it exactly. Thus all these transfers are instances of (8). Fixed 1-actions outside higher pads act on those pads by the collection rule. After collection (8) acts on the two fields at the bottom of the record.
* At the chosen cut the moving field is the extended moving value and the stationary field has the full remaining outer interval. Both are unchanged by any of the three transports, by associativity of fixed actions. Conversely the transfers just described take any spelling to those fields. This gives one record per transport class. One may also compute at an earlier cut on the moving side of a left variation if the moving value there extends to the specified value. For prescribed intervening 1-arrows the shorter value is unique: contract the added spans to an object. The same retraction works on the right in right variation. This observation requires no cancellation of chronological paths.

Write a *fork* as a parent record and its ordered pair of positive children. Make two tables, moving and stationary. Take the split formulas of [§2, item 2](../answered/directed-interchange-all-degree-presentation-2026-11-22.md#2-relations-and-guards), apply the parent pads, collect the child records and use the transport convention above. A pair passes its table test if it occurs in that order. These are explicit finite predicates in the lower fields: use the box for the exterior faces, enumerate the parent and its two typed axis factors, and compare the two computed child records. One can use the sum of the two child grades as the parent grade. The factor bounds are those for the expanded side of the fork. No top-word equality is used.

For example, for a left moving split write a letter as \((C,P,Z,Q)\), where \(C\) contains the stationary operand and the pads below the immediate pads \(P,Q\). If \(l_C,t_C\) are its source and target pure insertions, the junction tests, besides common \(C\) and composability, are
\[
       P_2=P_1 l_C(Z_1),\qquad Q_1=t_C(Z_2)Q_2 .
\]
The parent has fields \((C,P_1,Z_1Z_2,Q_2)\). The reversed state list gives the right-variable version. For a stationary split it is important to test the inherited pads **at every rank**, starting with the 2-pads. Its last rank uses the preceding cylinders on the two layers, as in the displayed stationary state list. [One-slot record calculation](../answered/lax-interchange-every-dimension-r10-2026-11-20.md#normal-forms-for-cylinders-on-one-stationary-slot)

## Gluing on one axis

Each successful test has one parent modulo transport. Two tests on the same axis on consecutive junctions of a triple extend to the same three-piece parent. We give the pad argument since both assertions concern equal lower *values*, which can have several spellings.

For moving cuts the stationary field fixes the transport cut. The context below the immediate pads is common. The left and right pure insertions distribute over the chronological product. Thus the two consecutive prefix tests compose, as do the two suffix tests, and either final merge takes the same outer prefix, composite operand and outer suffix. Read the indices backwards for the opposite processing order.

For stationary cuts first calculate with a common outer cut. In any one fork all children can be written at the parent's cut, with the same moving value. For two proposed parents of one pair, or two parents sharing a middle child, take the cut closer to the moving end of the outer string (the smaller cut for left variation). Both stationary words can extend to that cut. In the shared child, extend to its canonical cut and restrict back to the farther parent cut. This shows that the moving field at the farther cut is the field at the nearer cut extended by just the intervening 1-arrows. Those arrows are read on the shared child's layer. In the farther parent the moving field is this very field, since stationary subdivision fixes it. Transfer that extension to the stationary side of the parent by (8). The children obtained at the nearer cut are the same transport classes by functoriality. This works also if the stationary 1-arrows on the *other* child differ after its advance: the lower stationary cut supplies its own layer's 1-arrows there. Now the moving field is common and the parent stationary field is forced by concatenating the consecutive stationary pieces in operand order. The 1-boundaries for the two concatenations in a triple match by their pair tests.

Here is the higher-pad calculation at this common cut. It is also an alternative way of implementing the stationary test. Consider a list of consecutive stationary pieces. At each pad rank \(j=2,\ldots,d-1\), read the pieces in the order of their **rank-\(j\) flank list**. At rank two this is the stationary word order. At the next rank use the preceding stationary subdivision on the indicated hemisphere, in its chronological order; the right-variable reversal changes which child is visited first at the *new* rank. Thus the flank list is always the given order or its reverse. On the two required layers let \(D_i^-,D_i^+\) be the rank-\(j\) contribution of piece \(i\), with all its pads of ranks below \(j\) applied. At two these are the placed stationary pieces on the respective fixed layers. Higher up they are the steps of the preceding stationary subdivision on the appropriate moving faces. Superscripts here denote the layer used for the prefix or suffix. Number the indices in flank-list order, irrespective of the order of the top steps. If the parent has outer \(j\)-pads \(P,Q\), the pads of the child at \(i\) are
\[
           P D_1^-\cdots D_{i-1}^-,\qquad
           D_{i+1}^+\cdots D_h^+ Q.                                      \tag{1}
\]
For two pieces this says exactly that the first piece in flank-list order gets the other suffix, and the second gets the other prefix. At rank two it is (7) with fixed 1-arrows. For the induction, the old subdivision on a layer is a chronological list of steps separated by states with one pure hole. Elevating the hole transfers it past one step at a time, keeping the prefix of steps on the source layer and suffix on the target layer. This is the stationary state formula, read from the other end when prescribed. Dividing a consecutive sublist first leaves the exterior prefix and suffix on those same layers. A sublist kept as one contribution equals the product of its contributions by the **preceding** stationary subdivision, or by 2-composition at the bottom. Acting with the already determined lower pads distributes over this product. This proves (1), including its compatibility with grouping consecutive pieces. In particular one uses actual contextual contributions in (1), not the charges or the endpoints of the flanks. [Layer induction for stationary sublists](../answered/lax-interchange-every-dimension-r10-2026-11-20.md#shared-rectangular-schedules-of-exponential-width-in-outer-unary-cylinders)

To recover a parent at rank \(j\), take \(P\) from the first child in flank-list order and \(Q\) from the last. For a triple, induct upwards in \(j\), having glued the lower pads. The two overlapping pair tests now say precisely that, in flank-list order, the next left pad is the preceding left pad followed by its contribution, and the preceding right pad is the next contribution followed by the next right pad. The contributions in those tests are the restrictions of the same lower-rank list: this is the sublist identity in the preceding paragraph applied with the glued pads below \(j\). Substituting the two junction identities gives (1) for all three children. Grouping either adjacent pair gives exactly the fields of its tested parent, by the same product identity. The exposed left and right fields have the required attachment faces because they are the exterior fields of the first and last piece of this typed layer list. This proves existence and uniqueness at the next rank. In particular no step infers \(b=c\) from \(ab=ac\).

## Why the axes cannot overlap

A pair cannot pass both tests. A moving split repeats the same nonempty set of named stationary slots. A stationary split partitions such a set into disjoint nonempty subsets. A slot occurs only once along a 2-path on a globular tree. Both tests also preserve the choice of varying side.

Suppose instead that two tests share just their middle letter, one moving and one stationary. Inspect **the immediate pad of that letter**. As the last child in a left moving split its prefix ends in the pure insertion of the other moving piece. As the first child in a left stationary split its prefix ends in the preceding cylinder on the other stationary piece. Thus the same lower path would have spellings
\[
                            A\,I(v)=B\,J(X,c).                               \tag{2}
\]
Here \(I\) is a structural insertion, \(v\) is proper, and \(J\) is the preceding outer unary, with its inherited lower flanks. Its varying field \(X\) is the moving layer shared by the two moving pieces, up to the indicated outer 1-arrows. In particular it is the incident face of \(v\) on that side. For the other order of junctions use the suffix, with the two displayed factors **first**. For right variation reversing the moving and stationary state lists exchanges these prefix and suffix arguments. For example the middle of a right moving split is \(L_1 E_1 T_2\): its second child has the other pure insertion on the suffix side, while the first right stationary child has the other preceding cylinder on that same side. The fixed pads outside either fork only supply the paths \(A,B\) or their suffix counterparts. Transport normalizes the shared record without changing the immediate pad values.

Choose one traversed slot of \(c\), called \(b\). The pure insertion uses fixed actions on a cell on the moving side. Its active slots are disjoint from \(b\): the moving pieces are top-composable, hence have the same 1-boundaries and traverse the same 2-slots as their shared layer. In the stationary fork that layer is on the other side of the outer cut from \(c\). In particular passive 1-arrow extensions of an operand do not change this conclusion. Contract unused stationary slots and outer spectators, retaining \(b\) on a singleton exterior span. The tree contractions are substitutions. On the moving interval retain its diagram, collapsing only inactive exterior vertices if needed. A pure moving occurrence stays proper: all its positive inputs are on traversed moving slots, and restriction of a fixed exterior 1-extension retracts it. Equivalently this last assertion follows by induction on a spelling: every proper input has a proper 2-row, all its traversed slots occur in the enclosing rows, and the only discarded outer factors of the moving fields carry fixed vertices. The same argument works with left and right exchanged. After projection the marked preceding factor is one contextual unary on that singleton stationary slot.

If \(d-1\ge5\), classify a nonempty lower word by its **last** record, retaining just its varying side and stationary slot for a unary on a singleton. More precisely, on any unary remember the last stationary advance in its processing order, on either side, and on a rigid record use a separate symbol. This last-slot observation respects moving subdivision, which repeats the stationary word, and stationary subdivision, whose two ordered children partition its processing list consecutively. Transports and lower-field replacements preserve it. Fixed pads below the chronological rank leave the marked head in place. Use the first-slot version for initial factors. The preceding factor reads the marked slot \(b\). Every letter of the pure insertion has either a rigid symbol or an old stationary slot. This contradicts (2). This argument is independent of any confluence assertion in the lower rank.

### The end-piece test in rank four

For \(d=5\) the preceding factor is \(r(X,b)\) or \(t(b,X)\). Here the varying layer \(X\) is a 3-history. If the adjacent end of \(v\) is an input 4-globe, its terminal (respectively initial) globe tag already separates it: every positive top equation in rank four has structural heads on both sides. Otherwise select the actual end structural 4-letter in a spelling of \(v\). All its active 3-events belong to the event set of \(X\). Indeed each step is on a temporal subinterval of a 3-history parallel to \(X\), and the 3-events (slot advances and pair crossings) on a history are determined by its 2-boundaries. Fixed exterior 3-flanks merely enlarge that set. [Event-set lemma](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#researcher-response-4)

Reduce this test to at most five **pure sorting strands**. For an inner exchange retain one event from each of its two operands. A crossing costs two slots and a unary advance costs one slot and its advance. For \(r,t\) retain one varying event and one stationary slot. For \(h\) use the associated \(r\), retaining that event and a slot of its stationary face; a unit specialization of the other variation gives that proper \(r\). Collapse other slots, unrequested advances and higher input choices as in the retaining substitution. Replace a retained unary advance by a crossing on its two-strand bundle. The two slots of a retained crossing remain on distinct outer factors, so their crossing maps to a positive block crossing. Thus the selected structural letter still has a spelling as **one proper old structural letter**. Its fixed contexts are transported. These requests cost at most four old strands, and retaining the separate stationary slot costs one more. The new stationary strand is largest for left variation, smallest for right. All selected strands are traversed. Extend the outside 2-word interval to the full reversal by common fixed 3-history pads at the beginning and end. These are actions on both complete paths in (2). They preserve both displayed end pieces and their active event sets. [Retaining requests, Response 5](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#researcher-response-5) · [Bundle substitution and extension to the full reversal, Response 24](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#researcher-response-24)

Here is the finite lemma on that interval. Take a placed mixed edge \(g\) with just the extreme stationary strand and let \(W\) be its varying event set. At the target 3-history of \(g\), no spelling of any \(B g\) can contain a placed old edge \(e\) ending there whose active events are contained in \(W\). At the source the dual statement holds for \(g B\) and an initial old edge. The comparison of endpoints here is equality of 3-histories modulo (7). “Old” means the two active spatial operands omit the extreme strand. The strand can occur in any exterior pad.

The following finite exhaustion proves the lemma. It uses sets of **4-edge labels**, so it covers prefixes and suffixes of unbounded length, including arbitrary powers of loops.

1. List all adjacent-inversion histories from the descending permutation to the ascending one. At every temporal interval of each raw history enumerate two consecutive nonempty spatial subwords; enumerate their internal inversion histories, including empty ones, and insert each applicable square subdivision or \(\iota,r,t,h\) face. Identify histories under the square subdivisions (7). Use the existing [full-interval grounding](../../../scripts/e6/interchange_triangle_join_interval.py) on this entire vertex set. Its edge label retains the two endpoint classes, the head family, Gray triangles, ordered operand event pairs for inner and join edges, and the integer 4-weight. The use of these labels can identify extra edges.
2. Use its **equation** rows in both directions. For clarity about coverage, the one-to-two family patterns are \(r/rr,t/tt,i/ii,r/ir,r/ri,t/it,t/ti,r/hi\), and the triple identifies \(r/t\). The two sides have common endpoints, Gray chain and weight. An inner split partitions the product of event sets. In (14)–(17) the inner pairs are the varied events paired with the crossings of the added spatial slots against the fixed operand, in the displayed operand order. In the join factorization they are the two varying histories' product. The triple uses the three pairwise block crossings. These are exactly the necessary filters used by the grounding; fixed spatial and temporal pads are already included in the occurrences. Thus every native equation projects to one of these comparisons or to equality of labels. Taking both inner splits covers all switch settings. [Low equations (7)–(21)](../answered/lax-interchange-construction-or-impossibility-2026-11-19.md#2-the-equations-through-dimension-4)
3. For a proposed last \(g\), take every edge on every backward walk from its source and add \(g\). Close the set under this implication for every grounded equation: if all labels of one side belong, include all labels of the other side. Use both implications. By induction on a derivation, every label in every spelling of every \(Bg\) is in the resulting set. For a first \(g\) start instead with forward walks from its target. Both closures stabilize after at most the finite number of edge labels have been added.
4. For each old candidate at the appropriate endpoint test containment of its window's event set in \(W\), then test membership of its label in this closure. The following are the complete counts. The four candidate columns count the comparisons in source-left, source-right, target-left and target-right order, retaining the raw marked placements of \(g\), and deduplicating (old label, event set) at the endpoint.

| Strands | Raw histories | Edge labels | Source L | Source R | Target L | Target R | Members |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| 3 | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| 4 | 16 | 53 | 2 | 2 | 2 | 2 | 0 |
| 5 | 768 | 3,872 | 419 | 369 | 369 | 419 | 0 |

The [exhaustion](../../../scripts/e6/check_interchange_closed_form.py) supplies the loops for steps 3–4. After the retaining substitution the old letter of (2) is precisely one of the candidates: the pure insertion acts inside the varied old history, and its fixed actions preserve the old active window. Its purported other spelling ends (or begins) in the extreme-strand \(g\). The zero membership column contradicts that equality. This finishes the mixed-overlap proof, including the case where the two immediate pad spellings were quite different before projection.

## The data and its operations

Over the lower labels take the following indexed list family. It can be defined with indices for its two faces and its optional first record. An empty list has faces \(s,s\) and no first record. Cons a normalized record \(a:s\to u\) to a list from \(u\) to \(t\) if that list is empty or its first record \(b\) fails both fork tests against \(a\); the new first record is \(a\). The tests are Booleans. Equivalently use an ordinary typed list and a Boolean adjacency filter. This gives in particular the rigid records interleaved with lists of unary records satisfying the same local condition.

Contract a fork to its parent. Each step shortens the word. Disjoint steps commute, identical sites have the unique parent, same-axis neighbours glue by (1), and the end-piece lemma exhausts mixed neighbours. Consequently each word has a unique terminal list: induct on its length, joining any two first steps at their local common descendant and applying the induction hypothesis. By the upper presentation the proper top equations after transport normalization are precisely the forks in temporal contexts. The two switches change only lower field equality, and the free-object guards have their unit specializations. Thus equality of terminal lists is both necessary and sufficient for equality of cells. In particular an atomic moving record which *itself* admits a different lower factorization causes no exception. The split test compares its actual lower value. In \(T_{12}\) the proper shifted join, \(H_L,H_R,K,J,G,H\), and the higher bridges and principals carry their individual rigid tags and full lower fields. Unit inputs first use their declared values. This uses the same completeness of the [upper equation table](../answered/directed-interchange-all-degree-presentation-2026-11-22.md#2-relations-and-guards) as in \(V\).

There is also a direct interval formula for the map into this family. On an input of \(m\) collected records mark an interval \([i,j)\) if **one** whole record has a binary subdivision tree with exactly these transported leaves in order. Include singletons. Test this by the finite sum (Boolean disjunction) over ordered full binary tree shapes with \(j-i\) leaves, internal labels from the face box, and the two fork tables at each vertex. A rigid record has only its singleton tree. Every internal label has its subinterval's charge. Retain a cut between successive leaves exactly if it is in the interior of **no** marked interval. Read one root record for each interval between retained cuts, and keep the outside endpoints.

To prove the formula, a marked interval can be contracted first. Hence no cut internal to it occurs in the terminal word, measuring positions by cumulative positive charge. Conversely any contraction sequence to a terminal word is a forest on the original leaves, so each of its surviving blocks is marked. The positions and root records in these two arguments agree by uniqueness of the terminal list and positivity. This also proves that the required intervals always have roots and that their transport-normalized roots are unique. The formula enumerates trees on substrings of the *given input*. Its carrier needs just a two-record adjacency test. It requires neither a graph of words of the same weight nor a recursively completed forbidden list.

For chronological composition concatenate and apply this interval formula. A fixed whisker acts on each record by the rank-ordered collection rule and on the base of an empty word by its lower action; normalize the result by the same formula. For a globular substitution evaluate each input globe at its supplied image, recursively substitute in each head's lower fields and pads, specialize its units, and apply those pads to the resulting word. Concatenate in list order and apply the formula, using the new face box. This includes a rigid *input globe* whose image is an arbitrary path. These operations are well-defined since every fork and transport is an equation under these operations, and evaluation of a terminal list has that list as its normal data. This proves the identities for composition, actions and substitution by evaluation and the proved injectivity. Rank recursion, finite lists, finite trees on a fixed number of leaves, and bounded Boolean tests suffice throughout.

## Counting the rectangle test

For one outer unary with a prescribed moving spelling of \(n\) letters and a prescribed stationary word of \(k\) advances, a full subdivision on these axes has \(nk\) unit records. Every such subdivision gives **one class**, the single whole record with the original pads. For a zero axis the specified unit value gives the empty top word at its base. In particular counting cut trees, or counting guillotine partitions, counts choices of subdivision rather than cells.

There is a different count if “fully expanded” means *all schedules* of these \(nk\) named positions from the unadvanced to the fully advanced state, including schedules which are not expansions of the given parent. Here is an explicit function of \(n,k\) for that interpretation. Number the stationary rows and moving columns in processing order (reversing the appropriate physical lists). Start with \(c=(0,\ldots,0)\) of length \(k\). A block is a nonempty interval of rows with equal count \(u\) and a nonempty column interval \((u,v]\), \(v\le n\). Replace their counts by \(v\), retaining \(c_1\ge\cdots\ge c_k\). Sum one over all lists of zero through \(nk\) such blocks ending at \((n,\ldots,n)\), subject to the following two exclusions on neighbours:

* the same row interval and consecutive columns in processing order;
* consecutive row intervals in processing order and the same column interval.

This finite sum counts the classes. For example the values on \(3\times2,3\times3,3\times4\) are \(2,21,272\), respectively (transposing the axes gives the same count). For two stationary rows the expansions of the single parent spell exactly the concatenations of \(U^aD^a\), \(a>0\), of total width \(n\): a cut between the rows gives one such factor and a cut between columns concatenates two expansions. Hence for \(n>0\) just that one class has \(2^{n-1}\) different row schedules.

To justify the sum with actual lower labels, at a scheduled state place each preceding stationary factor on the moving layer specified by its count. Between neighbouring factors put the intervening consecutive moving letters in their pure insertion context. Moving an aligned rectangle in this shuffle is the native fork template, with its exterior pieces fixed, by the two state lists. Thus every allowed block and both indicated merges lift. Conversely start with two successive such blocks. A moving merge repeats the stationary slots, and the counts already force consecutive columns. In a stationary merge the rows must be consecutive: at rank two erase the moving side and read the 2-pads and the stationary word. On the scheduled pieces these are the prefix, the active sublist and the suffix in the original stationary word, and (1) concatenates adjacent sublists. No 2-slot repeats.

For this last merge alignment also matters when moving labels repeat. In left variation the first block processes the rows nearer the moving letters in the lower shuffle. Let its starting count be \(p\), and the count of the second group at that time be \(q\le p\). If \(q<p\), the immediate prefix of the first block in this shuffle ends in the pure insertion of the last of the intervening \(p-q\) moving letters. In a stationary fork that very prefix ends in the preceding cylinder on the second group's stationary sublist on layer \(p\). These are exactly the two end pieces of (2): the pure letter ends on layer \(p\). Thus \(p=q\). In right variation the reversed lower shuffle gives the initial-factor test on the suffix, with the moving stack numbered in its processing order. On aligned rows the two moving operands must agree after restricting to the old moving interval. Strict positivity of each moving letter then forces their terminal columns to coincide, by additivity of the grade from the common starting column. This proves the converse test even for nonunique lower factorizations. It also shows that normalizing scheduled words stays within these block lists. From a common state, a normal record recovers its rows by the named stationary slots, and its width by the grade of its restricted moving value. Thus distinct counted lists give distinct data. This count concerns schedules of the designated positions; arbitrary parallel paths with other heads or other moving factorizations use the general list family.

In particular there is **no smallest diagram or degree for the proposed L critical pair**. Even in the unit grid its lower-left and upper-right orders require the missing fourth corner between the proposed first and last steps. More importantly, (2) rules out the two simultaneous native contractions in arbitrary exterior contexts; the grid observation alone would not have proved that.

## Uniform finite-state recognition

The local record test has unbounded lower labels. In fact the nonregularity in question 3 also holds in a precise sense: no finite-state machine, uniform over the lower faces, recognizes the minimal forbidden factors of (K52), even on well-typed two-letter inputs on **one fixed diagram in degree six**. Give the machine a whole contextual record per input symbol, allowing an arbitrary transition function on these symbols. The same lower bound holds for a finite-alphabet serialization that encodes each record independently. This is compatible with finite automata on each bounded layer.

Use the doubled grid \(\Gamma_{2,4}\) and append one fresh stationary span \(\Sigma[1]\) with advance \(b\). On the grid the [two doubled 4-loops and their positional comparison](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#researcher-response-3) give a single rigid 5-letter from the word \(LE\) to \(EL\), both 4-endomorphisms at a common 3-history \(w\); here the early and late loops already include their respective fixed insertions. Act on the first, then the second pair of \(LELE\), giving two single rigid moving letters
\[
 z_1:X_0=LELE\longrightarrow X_1=ELLE,\qquad
 z_2:X_1\longrightarrow X_2=ELEL .
\]
All three \(X_i\) are 4-loops at \(w\). Write \(r=r(w,b)\). The old degree-five cylinder \(E_i=E(X_i,b)\) runs from \(r\,t(X_i)\) to \(l(X_i)\,r\), where \(t,l\) are the two pure 4-lanes for \(X_i\). Write \(L_s,T_s\) for the pure insertions of \(z_s\) in the source and target of this cylinder, respectively. The middle word of the degree-six moving split is \(D=L_1 E_1 T_2\), running from \(r\,t(X_0)\) to \(l(X_2)\,r\).

For any \(N\ge1\), form a common middle 5-path \(M=D_1\cdots D_N\). At site \(i=0,\ldots,N-1\) (so \(D_{i+1}\) is the site word), act on \(D\) by the fixed 4-pads \(l(X_2)^i\) and \(t(X_0)^{N-1-i}\). It runs between the successive rows
\[
                   l(X_2)^i\,r\,t(X_0)^{N-i}
           \quad\text{and}\quad l(X_2)^{i+1}\,r\,t(X_0)^{N-1-i}.
\]
Let \(A_i\) be the incoming 6-letter at that site moving \(E_0T_1\) to \(L_1E_1\); let \(B_i\) be the outgoing one moving \(E_1T_2\) to \(L_2E_2\). Keep the other site words as immediate pads. **Every** \(A_iB_j\) is typed through the very same \(M\).

Choose the shortlex-least single-record spelling in each transport orbit. On the diagonal the word is a moving fork and hence minimally forbidden. Off the diagonal it is normal. Indeed both moving operands are single rigid 5-occurrences, so neither lower operand admits a positive decomposition, and the stationary edge is atomic. A moving merge would require the prefix before the marked \(E_1\) in \(M\) to have the same grade at both sites. Its grade is \(i\,m_5(D)+m_5(L_1)\) at site \(i\), strictly increasing. The single-slot test excludes a stationary merge. No initial expansion or other positive top equation is available on an off-diagonal word. Its only equivalent spellings are independent transports and lower-field spellings, already minimized. These arguments about shortlex apply even before using the all-diagram confluence theorem.

For \(i\ne j\), reading \(B_i\) distinguishes the states reached after \(A_i\) and \(A_j\). A deterministic recognizer needs at least \(N\) states, for every \(N\); determinization gives the finite-state assertion. The diagonal uses the two proper singleton factors in normal form, so this separates the forbidden-factor language itself. The obstruction is memory for an occurrence's placement even under a composability promise. [Distinguishing-extension argument](https://www.cs.columbia.edu/~tal/3261/fall24/Handouts/3_Myhill_Nerode.pdf)

## Validation

Run `python3 -B scripts/e6/check_interchange_closed_form.py` from the repository root. It exhausts the rank-four end-piece test, compares the interval formula with block contraction on all 509 schedules of the three displayed rectangles, and checks all 1,496 composable pairs in the finite-state construction through 16 sites, including the pasted lower endpoints. The [two-axis checker](../../../scripts/e6/check_interchange_grid_contractions.py) independently compares contraction with contextual rectangular re-spelling on all 462 schedules of the \(3\times4\) interval. The [strip checker](../../../scripts/e6/check_interchange_strip_divisors.py) exercises the native signed subdivisions and unequal moving thicknesses. The all-degree gluing and separation argument above is a paper proof with a finite computational lemma; the full inductive family has not been formalized in Agda.
