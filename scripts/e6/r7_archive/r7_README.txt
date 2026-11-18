SEVENTH ROUND: FINITE COMPARISON GRAPHS AND PARTIAL TOP-LIFT EXACTNESS

Date: 2026-11-18

SCOPE

This archive gives a fixed-quiver source-joining theorem, concrete failures
of stronger closure claims, 320 specified hom-4 comparisons on the complete
240-word interval, a verified lower-dimensional Gray quotient, and four
identifications of selected fresh hom-4 lifts. It does NOT construct a
globular theory satisfying requirements 1-5. It does NOT prove support
injectivity after the new hom-4 equation, or exactness through hom-dimension 6.

All dimensions mentioned here are hom dimensions. The files from round 6
are unchanged dependencies, not new claims.

REPRODUCTION

Use Python 3.10 or later, without -O. All programs use the standard library.
Run these commands from the extracted directory:

    python3 r7_join_closure_check.py
    python3 r7_kernel4_check.py
    python3 r7_exactness_check.py

The second and third commands regenerate the round-7 JSON certificates.
Their existing outputs are included. The exactness program independently
enumerates all relevant nonnegative chain tableaux using a proved coefficient
sum bound; it does not assume that the selected path graph was already full.

FILES

  r7_join_closure_check.py
      Fixed-quiver finite history counts, FIFO/LIFO saturation agreement,
      directed acyclicity, actual two-sided critical pair, and failure under
      the actual comparison-category map tau -> h_z ; inner.
  r7_kernel4_check.py
      Enumerates 258 disjoint-operation comparisons D and 62 naturality
      comparisons N, including the eight pure-inner cube comparisons.
      Enumerates all 40,412 hom-3 paths, with arbitrary raw endpoints, and
      all specified 4-comparisons in their 3-prefix/suffix contexts.
  r7_kernel4_certificate.json
      Exact negative/positive boundaries, provenance, graph edges, and
      selected fresh-lift replacement witnesses.
  r7_kernel4_README.txt
      Definitions of D and N, orientations, counts, and the distinction
      between raw directed comparison and equality after the lower quotient.
  r7_exactness_check.py
      Three direct eliminations, the H_(2,1) factorization, exact hom-3
      quotient in a fixed pair of hom-1 boundaries, all 15 quotient W
      witnesses, and the selected higher top-boundary graph.
  r7_exactness_certificate.json
      Complete tableaux and equation witnesses. The key
      raw_lower_whiskering_factorization describes the new H equation.
  r7_exactness_notes.md
      Detailed mathematical account, including every path used for H_(2,1).
  triple_tensor_check.py
  r6_endpoint_lifts_check.py
  r6_endpoint_lifts_certificate.json
      Unchanged earlier-round dependencies.

FIXED-QUIVER SOURCE-ONLY THEOREM

Let Q be a finite quiver, with edges partitioned into inner edges E and
positive seed edges P. Suppose E is a DAG and there is a vertex function
phi constant on E and strictly increasing on P. For each seed alpha:s->t
and each literal E-edge path R:u->t, use an actual generator j[alpha,R]:s->u.
The empty-history generator is alpha itself. Impose, for e:u->v and R:v->t,

    j[alpha,e;R] ; e = j[alpha,R].

There are finitely many E paths. Saturating by prepending E edges creates
exactly these records, independently of the fair processing order.

Orient the equations from the two-letter side to the one-letter side.
Length strictly decreases. Each redex has edge sorts (positive,inner), so
two redexes cannot overlap in one edge. Disjoint reductions commute, and
the next contracted history is unique. Termination and this local argument
give a unique normal form for every path, including all equation contexts.

All original paths are irreducible; the original free path category embeds.
Every new positive generator strictly increases phi, so the completed graph
is a DAG. The vertices and actual generator IDs in a normal path determine
the path: its edges have a unique directed order in a DAG. These sets are
an injective support, with vertices distinguishing identity paths. Support
is computed AFTER normalization, not as union of arbitrary expression
supports.

After making E identities (also identifying their vertices), every
j[alpha,R] equals alpha. Mapping every such generator to alpha gives an
inverse to the original-category inclusion on the quotients. Thus this
completion preserves the original inner quotient exactly. It does not
prove the original quotient was the desired Gray category.

On the K14 graph: 240 vertices, 240 inner edges, 264 positive seeds,
877 positive history records, hence 613 new joins and 613 equations,
and 1,117 total generating edges. On the 54 weak E components, the
underlying simple directed graph of positive arrows has 116 edges and
is acyclic, yielding phi values 0,...,7. This does not identify parallel
positive generators in the relative quotient category.

This theorem requires a FREE input path category. Additional path equations
or higher globular compositions require a separate argument. K14 supplies
such a free input after its eliminated arrows are expanded.

COMPOSITE-IMAGE COUNTEREXAMPLE TO THIS COMPLETION

Use actual word vertices:
  x=bacrqp, u=abpcqr, w1=abcpqr, w2=bapcqr, v=bacpqr.
The inner graph has p:u->w1, e:w1->v, q:u->w2, c:w2->v.
The original tensor arrow tau:x->v has K14 factorization A;c,
where A=h_z:x->w2.

The comparison-category functor fixing the inner edges and sending tau
to A;c cannot extend to the source-only history completions. The source
completion has j[tau,e]:x->w1 with j[tau,e];e=tau. Its image would have
to be H:x->w1 with H;e=A;c. Contraction preserves the sequence of positive
seed IDs. H must therefore have exactly one positive generator rooted
at A. Its preceding inner path is empty by acyclicity. Write H=j[A,R];P.
For H;e to normalize to A;c requires the literal E-path equation
P;e=R;c, impossible since e and c are distinct final edges.

The executable check verifies the actual edges and the sole candidate
in both the five-vertex target and the full K14 target. This is a
comparison-category functor counterexample, NOT a demonstrated globular
substitution of the original pasting-diagram generators.

TWO-SIDED CRITICAL PAIR

Actual surviving K14 arrows:
  alpha:bapcqr->bapqcr (positive),
  e:abpqcr->bapqcr (inner),
  beta:abpqcr->abpqrc (positive).
With h;e=alpha and e;k=beta, the two-sided contraction system sends
h;e;k to both alpha;k and h;beta. Both are distinct irreducible
positive-positive words. Thus basic two-sided contractions are not
confluent. Adding alpha;k=h;beta might repair this critical pair; the
counterexample does not prohibit further equations or another normal form.

HOM-4 DATA AND LOWER QUOTIENT

D compares disjoint hom-3 operations, with right word interval first ->
left interval first. Eliminated old operations are expanded by K14.
N is a CHOSEN inner-naturality rule with an independent hom-2 letter.
It uses the composite-interchanger convention: sliding across a composite
word is the sequence of pairwise inner crossings. That convention has not
been derived from requirements 4 and 5.

All 320 boundaries are literally parallel and have equal full tensor
hom-3 tableaux. The generated directed comparison graphs are acyclic.
These facts do not establish all hom-4 coherence axioms or injectivity
after adding further hom-4 equations.

After imposing I=D=N=identity in the top atom's fixed hom-1 boundary
interval, the quotient has 54 hom-2 cells and 874 hom-3 cells, exactly all
positive tensor tableaux for those boundaries. It has a presentation by
116 hom-3 generating arrows and 54 nontrivial two-arrow equations.
There are 1,974 paths before those equations. D alone leaves 152
generating-arrow classes with only 116 tensor tableaux (36 split fibres).

All 15 fresh hom-4 lifts have old-W expressions in this LOWER quotient.
Those expressions supply well-typed quotient equations, not a proof
that the equations follow from I,D,N or lift to raw equations.

Three raw replacements are verified:
  A(1,0) = old W_xy(crq,-), followed by one disjoint comparison;
  A(3,2) = old W_xz(p,rb), followed by one disjoint comparison;
  A(6,5) = old W_xy(-,qrc), followed by two disjoint comparisons.

The fourth identification is a newly imposed, literally parallel hom-4
equation. Let P2=Bminus;R and P1=Bplus;R, ending Bminus,Bplus at u=apcqrb.
Let gamma:u->acpqrb->v=capqrb be an existing I;I path. Let L be the common
prefix crqbpa->crqpba->crqpab, and use old W_x with word prefix c and
suffix b. Existing forward comparisons give
  kminus:Bminus;gamma -> L;Wminus,
  kplus:Bplus;gamma -> L;Wplus.
Adjoin H:Bminus->Bplus and impose
  kminus ; L[W_x] = (H *_2 identity_gamma) ; kplus.
Define A(2,1)=H *_2 identity_R. All raw boundaries and full tableaux are
verified. Killing I,D,N turns the equation into H=L[W_x], by units alone.
No new hom-3 cell or hom-3 equality is imposed. A support theorem for
this hom-4 equation is NOT provided.

The other nine sinks are irrelevant to the chosen top atom's target,
but the whole-interval D,N comparisons have contexts reaching them.
Global coherence cannot be inferred from the top-target subinterval alone.

UNRESOLVED

Full raw equations for all 15 fresh lifts and their variations; hom-4 and
hom-5 support after these equations; exact quotient through hom-6;
all variations of all six K14 repair families; globular substitution
closure; the status of K15 before the quotient; a uniform higher tensor
construction or an impossibility theorem for requirements 1-3 and 5.
