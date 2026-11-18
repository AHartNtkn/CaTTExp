# Seventh-round exactness results

All finite claims below are checked by `python r7_exactness_check.py`, after
`python r7_kernel4_check.py`. The checker leaves the sixth-round files unchanged.
Its complete witnesses are in `r7_exactness_certificate.json`.

## 1. Three raw directed eliminations

Write `;` for the order of composition of the displayed routes. If `u` and `v`
are hom-3 routes, `u[W]v` means the hom-4 cell obtained by replacing the negative
route of a specified old `W` by its positive route, with hom-3 prefix `u` and
suffix `v` unchanged. Every kernel square below has the prescribed direction
“right spatial interval first, then left” to “left first, then right.”

The following are well-typed definitions of three selected operations. They
can replace the corresponding independently adjoined `A` generators, including
every use in the six `F` boundaries.

### A(1,0)

Use `W_xy` with word prefix `crq`, whose negative and positive routes are

```
crqbpa -T-> crqpba -I-> crqpab -T-> crqapb
crqbpa -h_p-> crqabp -T-> crqapb.
```

Whisker by the common suffix beginning `crqapb -mu-> acrqpb` and continuing
`h_z; T; h_r; T` to `apqbrc`. Its source is precisely `P_1`. Its target differs
from `P_0` at the following square:

```
crqabp -T-> crqapb -mu-> acrqpb
             =>
crqabp -mu-> acrqbp -T-> acrqpb.
```

Here `mu` acts on the left block `crqa`; `T` acts on the right block `bp`.
Let the indicated whiskered square be `kappa_1`. Then

```
A(1,0) := [W_xy(crq,-)] ; kappa_1.
```

### A(3,2)

Use `W_xz` with word prefix `p` and suffix `rb`, inserted at the subroute
from `pcqarb` to `paqcrb` of `P_3`. Its positive route is
`pcqarb -h_q-> pacqrb -T-> paqcrb`. The resulting hom-3 target becomes `P_2`
after the square

```
pacqrb -T(cq)-> paqcrb -T(pa)-> apqcrb
                    =>
pacqrb -T(pa)-> apcqrb -T(cq)-> apqcrb.
```

The left block is `pa`; the right block is `cq`. Thus

```
A(3,2) := [W_xz(p,rb)] ; kappa_2.
```

### A(6,5)

Use `W_xy` with word suffix `qrc`, inserted near the end of `P_6`.
Its target becomes `P_5` after these two squares, in the displayed order:

```
bpaqcr -T(cr)-> bpaqrc -h_p-> abpqrc
                       =>
bpaqcr -h_p-> abpqcr -T(cr)-> abpqrc,

bpacqr -T(cq)-> bpaqcr -h_p-> abpqcr
                       =>
bpacqr -h_p-> abpcqr -T(cq)-> abpqcr.
```

In each square `h_p` acts on the left block `bpa`; `T` acts on the right.
Therefore

```
A(6,5) := [W_xy(-,qrc)] ; kappa_3 ; kappa_4.
```

The revised globular top lift uses twelve fresh nonkernel hom-4 generators,
nine unchanged literal old-W operations, three additional old-W operations
with the four indicated kernel squares, the same six fresh hom-5 generators,
and the same hom-6 generator. No hom-3 generator or equation is needed for
these replacements. The `F` boundaries are obtained by literal substitution,
so the original checks of parallelity and tensor tableaux still apply.

## 2. The fixed-raw-endpoint obstruction and its precise scope

Among all 1,226 raw hom-3 routes from `crqbpa` to `apqbrc`, there are 232
old-W route replacements. For these seven fresh operations there is no
old-W replacement with the same full hom-4 tensor tableau:

| Fresh operation | Tensor basis label |
|---|---|
| A(2,1) | 21-1+ |
| A(4,0) | 1+21+ |
| A(5,4) | 21+1+ |
| A(8,3) | 1-21+ |
| A(15,13) | 20+2 |
| A(22,21) | 20+2 |
| A(23,22) | 21+1- |

Consequently none of these seven has an expression obtained solely by
top-dimensional route replacement, using old W cells and zero-image hom-4
cells on this fixed hom-3 graph. The reason is that its image is a single
positive basis vector. Every such expression must use exactly one old W
cell of that label; all other factors must have zero image. The old W would
therefore be one of the enumerated replacements with the same source and
target 3-chains.

This statement does not exclude new hom-4 factors specified by equations
after lower-dimensional whiskering. Section 6 constructs exactly such a
factor for A(2,1), with the hom-3 graph unchanged. Killing I in hom-dimension
three also identifies hom-2 words and permits further compositions in the
quotient. Section 4 records old-W expressions for all seven after that step.

## 3. Exact hom-3 quotient in the fixed pair of hom-1 boundaries

Let D be the 258 explicitly enumerated disjoint hom-4 relations. Let N be
the 62 explicitly enumerated naturality hom-4 cells in
`r7_kernel4_certificate.json`. N compares a hom-3 operation with an independent
hom-2 letter. Its orientations are the stated `(2,1)` and `(1,2)` orientations.
This section assumes these N cells are part of the proposed interchange
theory, and sets D and N to identity hom-4 cells in the quotient.

First impose `I = identity` on hom-3 cells. The 240 raw hom-2 words give 54
hom-2 classes. The 264 non-I hom-3 generators remain as arrows between
those classes. Deleting I from D yields 122 one-arrow equations, 48 empty
equations, and 88 two-arrow equations. The one-arrow equations leave 152
generator classes, while their tensor tableaux take only 116 values.
There are 36 split tableau fibres.

This is an obstruction in the quotient itself. Every remaining equation is
homogeneous in the number of non-I arrows. A two-arrow equation cannot be
used in a word of length one. Thus these 36 pairs cannot be identified by
the D presentation. The pure-I Coxeter equations project to empty equations
and do not alter this calculation.

After adding N, the one-arrow equations identify exactly the 116 pairs
`(2-source, 2-target, tensor 3-basis label)`. The resulting arrow graph is
precisely the graph obtained by applying all tensor 3-basis differentials to
the 54 positive 2-chains. The nontrivial projected relations are 54
two-arrow equations. They give the following complete calculation:

| Quantity | Count |
|---|---:|
| Hom-2 classes | 54 |
| Generating hom-3 arrows after one-arrow equations | 116 |
| Nontrivial two-arrow equations | 54 |
| All hom-3 paths, including identities | 1,974 |
| Equivalence classes under the equations | 874 |
| Positive hom-3 tensor tableaux with these hom-2 endpoints | 874 |
| Tableau fibres disconnected by the equations | 0 |

Surjectivity is independently verified. The checker solves the equations
`f(d b)=1` for every tensor basis vector `b` in degrees two and three.
For a nonnegative chain `c` with `d c = delta`, this proves
`sum(coefficients(c)) = f(delta)`. The bound is six in degree two and at
most seven in degree three in this fixed pair of hom-1 boundaries.
Meet-in-the-middle enumeration then checks all nonnegative solutions of
the tableau equations. It produces exactly the same 54 hom-2 tableaux and
874 hom-3 tableaux. No atomic decomposition theorem is used as a premise.

The scope is the hom-3 truncation with the top tensor atom's fixed pair of
hom-1 boundaries. It is not a claim of exactness in every hom dimension
or in every boundary context.

## 4. All fifteen old-W comparisons after the hom-3 quotient

In the quotient of Section 3, there are 156 hom-3 paths between the classes
of `crqbpa` and `apqbrc`, with 26 distinct tensor 3-chains. The additional
3-chain, absent from the 1,226 raw paths at the chosen endpoints, is

```
0-1+2 + 0-21+ + 1+1+1- + 1+20+ + 1-0+2 + 20+1- + 21+0-.
```

The 132 quotient-path old-W instances realize all 42 elementary hom-4
tableaux between these 26 classes. For every fresh A, the certificate gives
an old-W expression and explicit hom-3 equation witnesses identifying its
boundary with the boundary of A. One chosen context for each is:

| A | W scheme | Word prefix | Word suffix | Context index |
|---|---|---|---|---:|
| (1,0) | W_xy | crq | empty | 20 |
| (2,1) | W_x | c | b | 4 |
| (3,2) | W_xz | p | rb | 30 |
| (4,0) | W_y | ac | empty | 8 |
| (5,4) | W_x | bc | empty | 2 |
| (6,5) | W_xy | empty | qrc | 22 |
| (8,3) | W_y | c | a | 10 |
| (15,13) | W_xz | r | pb | 33 |
| (17,12) | W_z | empty | ab | 12 |
| (17,16) | W_x | empty | bc | 0 |
| (20,8) | W_z | b | a | 16 |
| (22,15) | W_y | a | c | 7 |
| (22,21) | W_xz | r | bp | 31 |
| (23,22) | W_x | b | c | 1 |
| (24,17) | W_y | empty | ac | 6 |

For example, W_x with prefix `c` and suffix `b` has raw endpoints
`crqpab` and `capqrb`. It supplies the middle of the comparison
`P_2 => P_1` after projection. A suffix starting at `apcqrb` becomes
composable with it because

```
apcqrb -I-> acpqrb -I-> capqrb
```

identifies those hom-2 endpoints in the quotient. A relevant N equation is
the naturality of `T(pa)` with the independent update `c`:

```
pacqrb -T-> apcqrb -I-> acpqrb -I-> capqrb
                         =>
pacqrb -I-> pcaqrb -I-> cpaqrb -T-> capqrb.
```

After I and this N cell become identities, the two T arrows agree. Together
with the D equations, the projected W_x boundary is literally the selected
projected pair `P_2,P_1` in the 116-arrow presentation.

These computations make the additional equations

```
A(i,j) = certified old-W expression(i,j)
```

well-typed after the hom-3 quotient. They identify already parallel hom-4
cells, and therefore impose no further identification in hom-dimensions
zero through three. They are additional hom-4 equations. Equal tensor
tableaux alone do not derive them for independently adjoined generators.
In particular, the number of uses of one fresh A is preserved by all the
listed I, D and N equations, while its proposed old-W expression uses that
A zero times. This grading obstructs inferring the equation from I, D and
N alone.

## 5. The selected top ladder is unchanged in dimensions five and six

The complete quotient hom-4 graph has 26 vertices and 42 edges. Between
the two prescribed hom-3 top boundaries there are 20 hom-4 routes, all
mapping to the same six hom-4 chains as the original sixth-round
construction. The graph of tensor hom-5 basis operations is therefore
exactly the same six-edge graph on those six chains. It still has two
top hom-5 routes, with the same hom-6 tensor boundary.

The six existing F generators and Omega retain the required tensor images.
This statement verifies the selected top ladder. It does not establish
that all equal-image old-W hom-4 cells agree, that all higher interchange
axioms hold, or that the full K17 quotient is the entire Gray tensor.

## 6. A raw lower-whiskering factorization for A(2,1)

There is a further, fully typed relation involving one new hom-4 generator.
This supplies an explicit relation to an old W even though Section 2 has
no top-dimensional route replacement for this case.

Set `u = apcqrb` and `v = capqrb`. The selected routes have the same literal
suffix `R`:

```
R = apcqrb -T-> apqcrb -h_r-> apqbcr -T-> apqbrc.
```

Write `P_2 = B_minus ; R` and `P_1 = B_plus ; R`, with

```
B_minus = crqbpa -T-> crqpba -I-> crqpab -h_z-> pcqrab
                  -I-> pcqarb -h_q-> pacqrb -T-> apcqrb,

B_plus  = crqbpa -T-> crqpba -I-> crqpab -T-> crqapb
                  -mu-> acrqpb -h_z-> apcqrb.
```

Both are existing hom-3 routes from `crqbpa` to `u`. There is also the
existing directed hom-3 route

```
gamma = apcqrb -I-> acpqrb -I-> capqrb
```

from `u` to `v`. Let

```
L = crqbpa -T-> crqpba -I-> crqpab,
```

and use the old W_x with word prefix `c` and suffix `b`. Its two boundaries,
before the prefix L is inserted, are

```
W_minus = crqpab -h_z-> pcqrab -I-> cpqrab -I-> cpqarb
                   -T-> cpaqrb -T-> capqrb,

W_plus  = crqpab -T-> crqapb -mu-> acrqpb -I-> carqpb
                   -tau-> capqrb.
```

There are directed zero-image hom-4 composites

```
kappa_minus : B_minus ; gamma => L ; W_minus,
kappa_plus  : B_plus  ; gamma => L ; W_plus.
```

The first composite consists of the following three forward cells, applied
in this order and with their existing prefix/suffix whiskers:

1. N28, naturality of `T(pa)` with the independent update `c`:

   ```
   pacqrb -T-> apcqrb -I-> acpqrb -I-> capqrb
                         =>
   pacqrb -I-> pcaqrb -I-> cpaqrb -T-> capqrb.
   ```

2. D164, the disjoint comparison of the original `T(qa)` and `I(pc)`, with
   the original T expanded using the existing h_q repair equation:

   ```
   pcqarb -h_q-> pacqrb -I-> pcaqrb -I-> cpaqrb
                          =>
   pcqarb -I-> cpqarb -T-> cpaqrb.
   ```

3. D173, the disjoint comparison of `I(ra)` and `I(pc)`:

   ```
   pcqrab -I-> pcqarb -I-> cpqarb
                   =>
   pcqrab -I-> cpqrab -I-> cpqarb.
   ```

The second composite consists of D21, the disjoint comparison of the
original `tau(rqp)` and `I(ac)`, with tau expanded by the h_z repair:

```
acrqpb -h_z-> apcqrb -I-> acpqrb -I-> capqrb
                       =>
acrqpb -I-> carqpb -tau-> capqrb.
```

Adjoin a hom-4 generator

```
H : B_minus => B_plus
```

and impose the single additional hom-4 equation

```
kappa_minus ; L[W_x] = (H *_2 identity_gamma) ; kappa_plus.   (E)
```

Here `*_2` concatenates the underlying hom-3 routes. Both sides of (E)
have exactly the raw hom-3 source `B_minus ; gamma` and exactly the raw
hom-3 target `L ; W_plus`. Consequently this relation imposes no new
hom-3 equation. All four kernel cells are used in their forward direction.

Assign H the basis label `21-1+`. Its hom-3 negative and positive chains are

```
1-1-1+ + 1-20- + 20-1+ + 21-0+,
1+1-1+ + 1-20- + 20+1+ + 21-0-.
```

The checker verifies every tableau equation for H, equality of the tensor
images of the two sides of (E), and equality of the full tableau of
`H *_2 identity_R` with the original tableau of A(2,1). Therefore one may
replace the original independent A(2,1) by the definition

```
A(2,1) := H *_2 identity_R.
```

The six F boundaries are updated by literal substitution. Their source
and target hom-3 routes remain the same, so their parallelity is preserved.
This construction changes hom-4 data and imposes one hom-4 relation; it
does not change the hom-3 presentation.

When I, D and N become identities, (E) forces `H = L[W_x]` in the quotient,
and consequently forces the desired comparison for A(2,1). This equation
is imposed as part of the construction. The checking result establishes
typing and compatibility with the tensor map. It provides no hom-4 support
theorem, hom-4 normal-form theorem, or complete higher exactness theorem.
