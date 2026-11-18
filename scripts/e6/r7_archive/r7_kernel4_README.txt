DIRECTED KERNEL-FOUR COMPARISONS IN THE REPAIRED SIX-LETTER INTERVAL

Reproduce:
    python r7_kernel4_check.py

Dependencies: unchanged r6_endpoint_lifts_check.py and
r6_endpoint_lifts_certificate.json in the same directory.
Output: r7_kernel4_certificate.json.

SCOPE

The computation uses all 240 admissible words and all 504 normalized
three-edges. It enumerates every directed three-path with arbitrary raw
source and target: 40,172 nonidentity paths and 240 identities. Thus all
ten sinks participate; this is not restricted to paths ending at apqbrc.
An edge is the exact triple (source word, target word, generator kind).
A three-path is an ordered tuple of such edges. No two raw paths are
identified before the explicit four-comparisons below are applied.

All reported fibre counts fix the exact raw two-source and two-target
and then compare the tensor three-chain. This restriction matters: after
I-three-edges are identified with identities, formerly distinct raw
two-endpoints are equal and additional composites become available.
Consequently a disconnected raw fibre is not, by itself, an obstruction
to the eventual quotient. The separate r7 quotient checker addresses
that latter question.

D: DISJOINT OPERATIONS

For an edge, take the smallest contiguous half-open interval of word
positions on which its source and target differ. For two operations L,R
at the same word with disjoint intervals, the orientation is

    R ; L_after_R  ==>  L ; R_after_L.

This is the requested right-region-first to left-region-first direction.
The enumeration includes the original and repair operations, before
eliminated original operations are recursively expanded using the six
r6 equations. This retains the comparison when normalization makes an
operation composite. The normalized boundaries are exact raw paths.

There are 258 distinct directed comparisons. Of these, 50 use an
eliminated-edge expansion. Each record gives both operation intervals,
the original left and right edges, and both complete expanded paths.
For each comparison, the checker asserts equal raw endpoints and equal
tensor three-chain. Therefore assigning its tensor four-chain to zero
satisfies the chain-tableau boundary equation. It is sent to the
identity four-cell on that common three-cell.

C: PURE-I CUBES

There are eight contextual instances of the three-update cube. Their
orientation is leftmost-adjacent-swap first to rightmost-adjacent-swap
first, that is, positional swap sequence 010 ==> 101. Each three-edge
in these boundaries is an I-edge; the common tensor three-chain is zero.
These cells are explicitly an additional structural assumption relative
to the data in the r6 program.

N: I-NATURALITY

For a three-operation alpha:L=>R and a two-letter z supported on wires
disjoint from every letter of L, compare these routes:

    I-first:     move z across L by I-edges, then apply alpha;
    alpha-first: apply alpha, then move z across R by I-edges.

The orientation is fixed by the hom1 Gray tensor differential:

    alpha on left, z on right, degrees (2,1): I-first ==> alpha-first;
    z on left, alpha on right, degrees (1,2): alpha-first ==> I-first.

Here 'left' and 'right' in the degree pair refer to wire position.
The checker obtains the same orientation directly from whether the
allowed I-route moves z from the left end of the word segment to its
right end, or vice versa. Repair expansions are performed on alpha
and on its residual after the I-route. Equality of the resulting
three-chains is asserted for every record.

There are 62 distinct comparisons: 48 with an original T operation,
six with an h_p/h_q/h_r operation, and eight with an I operation.
The latter eight are exactly C, with exactly the same orientations.
Thus D+C+N has 320 distinct relations, and C is redundant once N is
assumed. N is conditional new four-data relative to the r6 program;
the finite computation does not silently treat it as already supplied.

GLOBAL COUNTS (FIXED RAW TWO-ENDPOINTS)

There are 5,818 fibres determined by (raw source, raw target, q3-chain).
All three directed comparison graphs are acyclic.

             Whiskered four-edges   Weak classes   Disconnected fibres
D                     54,634              7,881             1,409
D+C                   55,624              7,525             1,321
D+C+N                 60,961              5,955               131

A 'weak class' permits a zigzag of directed comparisons; it does not
assert the existence of a directed comparison in either direction.
Whiskering here means arbitrary three-path prefix and suffix. Every
such instance that remains in the finite 40,412-path domain is included.

PATHS FROM S=crqbpa TO ALL TEN SINKS

Sink       Paths  q3-chains   D classes   D+C classes   D+C+N classes
apqbrc     1226       25          51           48             25
apqcbr      221        9          19           17              9
bapqrc      331        9          21           20             12
braqpc      651        4          21           20              7
brcaqp       87        2          11            9              2
capqbr      213        6          18           17              6
cbapqr       39        2           6            4              3
cbraqp       20        1           4            3              1
raqpbc      240        4          13           12              6
rcaqpb       23        2           4            4              2

DIRECTED REPLACEMENTS OF THE SELECTED FRESH FOUR-LIFTS

The checker enumerates every exact three-whiskering of every prescribed
W-context on every one of the 1,226 raw S=>T paths. For each selected
A_(i,j;k), it tests whether there is a directed kernel path from P_i to
a W-source and from that W-target to P_j, with W's four-label equal to
basis label k. Reachability is exact in the finite acyclic graph.

Exactly three of the fifteen fresh lifts admit such a replacement:

    A_(1,0;16) := [W_xy with word prefix crq] ; kappa_106;
    A_(3,2;10) := [W_xz with word prefix p and suffix rb] ; kappa_133;
    A_(6,5;17) := [W_xy with word suffix qrc] ; kappa_64 ; kappa_60.

The brackets include the exact common three-prefix and three-suffix
recorded in models.D.padding. Their three-prefix lengths are 0,4,7.
The kernel steps have their own three-whiskerings, also stored there.
These are available directed replacements or defining equations for
fresh generators; they are not automatic equalities of previously
freely adjoined generators.

Their local comparisons are:

kappa_106:
    crqabp -T-> crqapb -mu-> acrqpb
      ==> crqabp -mu-> acrqbp -T-> acrqpb.

kappa_133:
    pacqrb -T(cq)-> paqcrb -T(pa)-> apqcrb
      ==> pacqrb -T(pa)-> apcqrb -T(cq)-> apqcrb.

kappa_64:
    bpaqcr -T(cr)-> bpaqrc -h_p-> abpqrc
      ==> bpaqcr -h_p-> abpqcr -T(cr)-> abpqrc.

kappa_60:
    bpacqr -T(cq)-> bpaqcr -h_p-> abpqcr
      ==> bpacqr -h_p-> abpcqr -T(cq)-> abpqcr.

Adding C or N supplies no further directed replacements for the chosen
r6 representatives. Under D+C+N, the following five fresh lifts admit
an undirected endpoint match to a W instance, but no directed padding:

    (17,12;2), (17,16;12), (20,8;3), (22,15;8), (24,17;6).

The remaining seven have no W instance between their q3-chain fibres
within the raw S=>T path interval:

    (2,1;13), (4,0;9), (5,4;15), (8,3;7),
    (15,13;11), (22,21;11), (23,22;14).

Again, these negative results keep raw two-endpoints fixed. They do not
exclude an old-W construction after lower-dimensional I-identifications.

A MINIMAL RAW FIBRE OBSTRUCTION AND THE CANCELLATION ISSUE

Let

    P = bcrqap -T(cr)-> brcqap -h_q-> bracqp;
    Q = bcrqap -mu-> bacrqp -T(cr)-> barcqp -I-> bracqp.

They have exactly the same raw endpoints and the same tensor three-chain

    0-1+2 + 20+1+.

The first basis label means degrees (0,1,2) with signs (-,+,empty);
the second means degrees (2,0,1) with signs (empty,+,+).
There are exactly two paths in this raw fibre. They lie in distinct
weak classes even in D+C+N. Among all disconnected raw fibres the
minimum sum of the two path lengths is five, attained by this pair.

Let gamma = (bracqp -I(ac)-> brcaqp), and put

    R = bcrqap -mu-> bacrqp -I(ac)-> bcarqp
        -I(ar)-> bcraqp -T(cr)-> brcaqp.

There is a directed fork

    R ==> P;gamma       (disjoint comparison 55),
    R ==> Q;gamma       (naturality comparison at cut 1).

Both P;gamma and Q;gamma are terminal under the generated four-rewrites
on their raw endpoints. Thus they admit a zigzag but no directed path
between them. Once the displayed kernel four-cells become identities
and gamma becomes an identity three-cell, the quotient equations imply
P=Q. That inference cannot be used as raw cancellation of gamma before
the quotient. This gives a concrete reason to keep raw directed padding,
weak kernel equality, and the quotient by I=identity separate.

CERTIFICATE FORMAT

Top-level arrays disjoint, coxeter, naturality contain exact local
negative and positive paths and their provenance. models.D, models.DC,
and models.DCN contain all 1,226 raw S=>T paths, the full directed
four-adjacency among them, old W instances, each selected lift's padding
result, all 25 top-fibre counts, and global statistics. A directed edge
stores (relation index, substitution cut). Relation indices use D,
D+C, or D+C+N concatenation, respectively. All arrays are zero-indexed.
