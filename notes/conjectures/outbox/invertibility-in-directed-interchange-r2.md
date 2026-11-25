# Which operations propagate invertibility in algebras with directed interchange at every level? (round 2)

*A self-contained problem. Background: standard higher category theory, and the previous rounds listed below. This is the second round of this line. The first round's prompt, its response and the verification are in the repository file `notes/conjectures/answered/invertibility-in-directed-interchange-2026-11-21.md`, cited below as "round 1". The definitions of the theories V and V + S, the letters, and the operations h, W, K, J are those of round 1 and of the rounds it cites (`lax-interchange-every-dimension-r5` … `-r10` in the same folder). Everything round 1 settled is taken as known and is not re-asked.*

**What we are asking for.** We want one general statement that decides, for every operation of V and every setting S ⊆ {left split, right split}, whether the operation sends invertible operands to invertible cells in **every** algebra of V + S, not only in free algebras over pasting diagrams. The cases below are the ones a proof assistant's rules depend on. They should come out as instances of that statement, not be settled one at a time.

## 1. Setting (summary of round 1)

- V is the least admissible theory: the forced base B (structural operations, P, the face and unit declarations, the outer unary subdivisions in both variables, and their vertex transports) plus the guarded round-5 equations. V + S adds the unguarded left split and/or right split of the inner interchanger.
- Every d-cell of a free algebra F_{V+S}(Γ) is a ∗_{d−1}-path of contextual letters. The Gray projection π sends a letter to a whiskered generator of the free Gray-enriched category 𝔉(Γ) (an **outer** letter) or to an identity (an **inner** letter).
- Free algebras on pasting diagrams have no non-identity invertible cells (positivity, (M5)).
- For cells x₁, …, xₙ in consecutive homs, of hom-dimensions d₁, …, dₙ, the **Gray cell** G(x₁, …, xₙ) is the image of the top-atom lift over the wedge ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}. On ΣD² ∨ ΣD² this lift is W.
- **Known in every algebra:**
  - an outer cylinder (one factor of positive dimension, the other an edge) with an invertible moving input is invertible, from the outer unary subdivisions and the unit declarations;
  - an inner interchanger with an invertible left (right) input is invertible exactly when the left (right) split holds;
  - the join h(A, B) is invertible when A is and the inner interchanger ῑ₋ of the factorization r̄₁ = h · ῑ₋ is.
- **Known to fail:** the binary subdivision W(A₁ ∗ A₂, B) = paste of W(A₁, B) and W(A₂, B) fails in every setting, even after localization (round 1, the outer W-strip, with a label table).

## 2. The questions

**Q1 (factor rule for Gray cells).** Fix (d₁, …, dₙ) with at least two dᵢ ≥ 1, an index i with dᵢ ≥ 1, and a setting S. Is G(x₁, …, xₙ) invertible in every algebra of V + S whenever xᵢ is invertible? We expect the answer to depend on (d₁, …, dₙ), on i and on S. We would like the exact list.
- Is the case d = (1, 1) (the cut-0 crossing of two 2-cells) positive in every algebra, because its outer square subdivisions are unguarded?
- Is d = (2, 2), with W as the lift, negative?

**Candidate countermodel for (2, 2).** Start from round 1's outer W-strip table, keeping the long hom through degree 4: 3-values in ℤ, inner squares labelled xy, joins −ab, r, t and χ labelled 0. Then change three things:
- the short hom carrying A is replaced by one in which A has a two-sided inverse, with advance counts A ↦ 1 and A⁻¹ ↦ −1;
- 5-labels are taken in (ℕ, +);
- W(A, B) is labelled 1, and every other disk pair is labelled 0, including (A⁻¹, B) and (1, B).

Here A is invertible and W(A, B) is not. Is this an algebra of V + S? Round 1's check used two facts that change here: the short homs were chains, so two positive short advances are never spatially adjacent, and advance counts were positive, so every guard test ab was nonzero. If some guarded equation of V links W(A, B) to W(A⁻¹, B) through A ∗ A⁻¹ = 1, please give it. In that case the factor rule may hold after all.

**Q2 (pseudo factor).** Call a cell x **ps\*** if every mixed cell G(y, x′), for x′ x or a face of x of positive dimension and y of positive dimension composed before it, is invertible. If xⱼ is ps\* and some i < j has dᵢ ≥ 1, is G(x₁, …, xₙ) invertible in every algebra of V + S? This is the uniform analogue of the strict lemma "y ⊗ β is invertible when β is pseudo". Its strict proof uses the same binary subdivisions as Q1.

**Q3 (other outer letters).** Which further outer letters propagate invertibility from an operand in every algebra of V + S, and under which hypotheses on the inner letters of the target hom? The letters we have in mind are:
- W on composite operands;
- the auxiliary K and J;
- shifted joins;
- higher naturality and route cells.

The hypotheses on inner letters range from "all inner letters into the target object invertible" to none. A criterion stated in terms of which subdivision and factorization laws each letter satisfies would answer this.

**What would help most.** A characterization of the form: an outer letter propagates invertibility from an operand position in every algebra of V + S if and only if [a syntactic condition on the letter, the position and S], with the positive direction proved from the laws and the negative direction by explicit algebras. Round 1's per-letter semi-decision procedure certifies single positive instances. We want the general dividing line.

# Researcher Response 1

There are two distinctions concerning the requested decision. A binary principal
disk has a specified lift. For three or more factors the Gray atom alone does
not specify an operation of \(V\). In fact two principal bracketings of the
*same* atom have different answers to Q1. Also, the requested decision for
*every operation*, allowing composite operands in the partial theory, is
impossible. This already holds for one outer letter \(W\), one fixed switch
setting, and a fixed finite matching context. Below we give the exact decision
for principal disk trees, the counterexample to Q2, and the undecidability
reduction. The reduction and the disk-tree decision have different input domains.

## The factor rule for principal disks

Choose a planar binary bracketing of the consecutive globes. Give a leaf its
hom-dimension and each node the sum of the dimensions below it. At a vertex
factor use the pure action. At two positive factors use the principal disk in
the indicated order. For a specified positive leaf \(i\), the exact test is
\[
 \boxed{\quad\text{On the path from }i\text{ to the root, no node has
 two children of dimension at least two.}\quad}                         \tag{1}
\]
It works for all four settings, including when all inner letters are required
to be invertible. In particular the complete **binary** list consists of
\((1,p),(p,1)\), in *either* position, for every \(p\ge1\).
For left association, for every
\(k=\max(2,i),\ldots,n\), require \(d_k\le1\) or \(\sum_{h<k}d_h\le1\).
For the rule to hold for **all principal bracketings**, require that no cut
of the whole list has sum at least two on both sides. Such a cut can be
chosen at the root, and a bad cut of any subtree extends to one of the
whole list by adding the exterior slots. Below,
all inverses refer to composition at the immediate boundary.

Here are details of the positive proof, including the stationary-edge case.
Whiskering by an invertible cell at its own composition level is an
isomorphism on the corresponding homs, with inverse whiskering by its inverse.
Whiskering an invertible cell by any fixed context preserves its inverse.
In a subdivision into two steps, substitute \(e,e^{-1}\) and then
\(e^{-1},e\). Each paste is an identity by the unit law. The step on \(e\)
occurs first in one paste and last in the other. If its pads can be undone
by isomorphisms of the relevant homs, it follows that the unpadded step
has a right inverse and a left inverse. They coincide by associativity.

For the moving-input subdivision the pads added to the step are pure insertions
of a piece of the invertible input, hence invertible. For stationary subdivision
argue by induction on the moving degree \(p\). At \(p=1\), (K15) pads a
square by transported pieces of the subdivided edge. At the next rank the
stationary paste has middle state \(g_1^0 P_1[v]g_2^1\) in the notation of
round 5. Each step is the cylinder on one piece in its old pads, elevated by
identities, with the cylinder on a *face* of the moving input against the
other piece attached as a pad. The old pads are reversible by induction on
the construction of the contexts, and each new pad is invertible by the
induction hypothesis applied to the other piece or its inverse. The occurrence
\(P_1[v]\) belongs to the boundary of the step itself.
The right-variable recursion reverses the two steps in both substitutions.
This proves stationary propagation in every degree. Applying these facts and
the pure-action rule up the specified path proves sufficiency of (1).
[Moving subdivision](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#subdividing-the-varying-argument-of-a-unary-cylinder)
· [Stationary subdivision](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#unary-cylinders-on-an-edge-subdivided-in-two)

### The proposed signed strip

Yes. Use a suspension of the walking isomorphism for the left short hom.
Its two objects as a suspension remain distinct. The groupoid replaces the
*temporal* chain between them. Its only nonidentity advances are \(A,A^{-1}\)
of signed lengths \(1,-1\). Two such advances can cancel temporally. Two
nonidentity spatially composable advances would have to traverse the same
object interval twice, which is impossible. Thus transport of a short inner
square still has a zero factor. One can use walking isomorphisms on both sides.

In the long hom the two 4-faces of a disk have labels \(ab,-ab\), in that
order, over the common 3-value \(a+b\). Give the arrow between them the
requested natural-number label. Composition adds labels, with matching
4-faces for chronological composition. Through degree four the only
nonzero operation labels are \(xy\) and \(-ab\), and the low equations
are respectively bilinearity, \(-ab+ba=0\), and the zero correction
against a literal outer crossing. These identities hold over the integers.
In a mixed-paste law there is an identity premise **for each occurrence
on both sides**. Every occurrence with a nonzero 5-label has \(ab=1\)
and fails its own premise. For \(A;A^{-1}\) the direct test has value
zero, while the two tile tests have values \(b,-b\). At \(b=1\) the
conjunction fails.

For completeness, the rest of the round-1 extension works with
\(\mathbb N\). In the coordinate forgetting 5-labels take unique higher
fillers. In the label coordinate, on each pair of short disks assign the
chosen label to its single \((2,2)\)-atom. Through lower ranks all weights
in this coordinate are zero. Restrict this disk evaluation to faces and
pull it back on identity inputs. In particular \(K=W\) at a unit left
variation and \(J\) has the prescribed contextual \(W\) at two unit
variations. The two short homs have no proper higher variations. The
only degree-five equation with a surviving label outside the mixed-paste
tests is the unit factorization with the same \(W\) on both sides.
Higher faces in the label coordinate agree by disk restriction. All cuts
inside the long hom use the strict label operations and additional outer
spans are terminal. This verifies even the extension with only identities
*in the label coordinate* above five. The marked 5-arrow cannot have a
right or left inverse since \(1+z\ne0\) in \(\mathbb N\).
[Guard with its occurrence quantifier](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#an-inner-comparison-detecting-a-proper-outer-pair)
· [Disk and unit check](../answered/invertibility-in-directed-interchange-2026-11-21.md#the-two-strip-constructions-and-q4)

### A separating algebra in every arity

We give the construction since neither suspension of the strip nor failure
of subdivision alone proves necessity of (1). In particular a bracket with
a new outer edge must be able to carry a noninvertible value of a smaller
bracket. All following ranks unless called global are hom ranks.

Fix a node on the specified path whose child intervals \(L,R\) have totals
\(p,q\ge2\). Use objects \(0,\ldots,n\), forward intervals, terminal homs
at equal objects and empty backward homs. Write
\(D(J)=\sum_{h\in J}d_h\) for an interval of slots. Work over the polynomial
ring in indeterminates \(v_1,\ldots,v_n\) over \(\mathbb Z\). A value on
an interval uses only its own variables. Exterior vertex transport includes
the smaller polynomial ring in the larger. Write \(u(a)\) for setting
\(v_i=0\) in \(a\), and \(w(a)\) for evaluating \(u(a)\) at all ones.

**Rows.** There is one vertex in each forward hom. A cell of rank \(k\)
has signed homogeneous rows \(a_s\) of degree \(s\), \(1\le s\le k\).
Use \(a_0=1\) and zero above \(k\). Each pair of faces has the same
rows in their common ranks. Identities extend rows by zeros. Composition
at hom cut \(h\) keeps matching rows through \(h\) and adds rows above
\(h\). Require that all \(u(a_s)\) have nonnegative coefficients and
that the indices where these are nonzero form an initial segment starting
at zero. The signed rows themselves may cancel.

For disk evaluation assign to a pair of basis faces of ranks \(l,r\) the
product \(a_l(X)a_r(Y)\). Sum on each Steiner row with its multiplicities.
This defines a strictly Gray functorial evaluation on the signed rows.
The two hemispheres of every input face have equal row values, hence every
basis boundary evaluates to zero. Addition on pastes and associativity of
multiplication give subdivisions and rebracketings. In particular row \(s\)
of a principal disk is \(\sum_{l+r=s}a_l(X)a_r(Y)\), with rows above an
input's rank zero. The nonnegative initial-segment condition is preserved
by this convolution and by the composition rule. It holds on contextual
disk atoms as well, by expressing their tableaux as pastes of pure and
principal atoms.

**The low-dimensional guard.** Write \(\ell=a_1, m=a_2\). Refine a
rank-two cell at \(\ell\) by a moment \(j\) of polynomial degree three.
Chronological composition adds \((m,j)\), and padding by 1-rows of lengths
\(l,r\) adds \((r-l)m\) to \(j\). A rank-three cell between \((m,j)\)
and \((m,j')\) has in addition a degree-four polynomial \(z\), additive
on composition and unchanged by fixed pads. Keep the signed rows as a
separate coordinate. Beyond this truncated moment and \(z\) coordinate
take unique fillers on parallel faces. On a pure vertex transport keep
\(j,z\). The low mixed calls have values
\[
 \chi(a,b)=(\ell_a\ell_b,0),\qquad
 z_\iota(F,G)=m_Fm_G,\qquad z_r(F,b)=j_F\ell_b,\qquad
 z_t(a,G)=-\ell_a j_G,\qquad z_h=z_{\bar r_1}-m_Bm_A .
\]
The pair in the first entry is \((m,j)\). Prescribed 3-histories on the
two sides of a rank-three declaration have equal \(m\) by the signed
row calculation. This makes the entry a cell with exactly those faces.
For (K15), the opposite shifts in \(j\) on the two subcrossings cancel,
e.g. \(\ell_2\ell_1\ell_b-\ell_1\ell_2\ell_b=0\). For the four
varying-whisker laws the shift of \(z_r\) or \(z_t\) is
\(\pm m\,\ell_{\rm pad}\ell_{\rm edge}\), exactly the correcting square.
Its signs follow from \(r-l\) for \(r\) and its negative for \(t\).
Chronological subdivisions are distributivity, balancing retains \(m\),
both sides of the triple of edges have \(z=0\), and the join equation is
the last entry. Both inner splits hold. Fixed whiskering is functorial
since the shifts are additive in the pad and linear in \(m\).
These check the support-free \(P\) through global degree four. Every
higher parallel equation in this extra coordinate holds by uniqueness.
In particular, for two transported 2-histories, a nonzero product of
their masses prevents their bare inner square from being an identity.
[The signed grading equations of P](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#a-degree-five-sector-on-arbitrary-pasting-diagrams)

**Natural-number labels.** Alongside the signed rows use rows
\(b_s\in\mathbb N\) with the same face, identity and composition rules.
Set \(b_0=0\). A nonzero \(b_s\) is allowed only if \(s\ge4\) and both
\(u(a_1),u(a_2)\) are nonzero. Give a pure face its own label. For a
mixed pair of faces \(X,Y\) of positive ranks \(l,r\) use
\[
 b_l(X) w(a_r(Y))+w(a_l(X)) b_r(Y)+\delta(X,Y).                    \tag{2}
\]
The only possible nonzero \(\delta\) is on the specific intervals \(L,R\)
and ranks \(p,q\). There it is one under all the following conditions,
and zero otherwise.

1. On each child \(J\), the monomial \(\prod_{h\in J}v_h^{d_h}\) has
   nonzero coefficient in the operand's top signed row.
2. For each consecutive subinterval \(K\) of that child of total at
   least one, the operand's \(\ell\) restricted to variables in \(K\)
   is nonzero. For total at least two require the same of \(m\).
3. On the child missing \(i\), the unsigned first and second rows are
   both nonzero.

Evaluate the top and lower tableaux of **every** outer disk and auxiliary
by summing these basis values. At inner cuts evaluate this coordinate
strictly, so that an inner comparison contributes zero. This defines
typed operations prior to checking equations. On one classified disk
pair the assigned values are cocycles because replacing an input face by its
parallel face across a higher input preserves every row used in (2),
including the restrictions in the tests. Hence the tensor differential
evaluates to zero. This proves equality of the evaluated negative and
positive rows at every rank required for a cell, also for the contextual
tableaux of auxiliaries. Restrictions use the same values and degeneracy
in an active top slot has value zero. Thus the prescribed unit
specializations hold, including those retaining a lower disk. One can
equivalently perform this calculation by a strict functor on **one pair
of globes**, with each basis atom sent to its rows. It does not assert
naturality for replacing an input by a composite. A positive inherited
label retains its unsigned first and second rows in the two-hemisphere
tableau by the pure summands of the convolution. For a new label this
follows from condition 3. Lower pastes preserve these nonzero unsigned
rows by nonnegativity or matching. This proves closure under all the
indicated operations.

Here is the check of the equations on arbitrary assignments. In the
absence of \(\delta\), (2) is multiplication in the square-zero extension
of the unsigned weight ring, with \((w,b)(w',b')=(ww',wb'+bw')\). It is
additive in each slot and associative. Pure transports act by \((1,0)\).
Use the list of schemas in [round 8](../answered/lax-interchange-every-dimension-r8-2026-11-20.md#the-minimum-on-pasting-diagrams)
and the [three-factor guard](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#associativity-and-the-quotient-universal-property).

* The outer square and all unary subdivisions and vertex transports use
  the bilinear formula, since one rank is one. This also proves the
  basic whiskering formula for a unary since its single top basis occurrence
  has the same top input row after lower padding. The structural
  equations hold by the row composition rule. Inside a hom the label
  operations are strict, including both switches.
* In a guarded mixed paste every displayed top occurrence has both
  ranks at least two. If either inherited summand in (2) is positive,
  one input has a positive label and the other a positive unsigned
  top weight. Both consequently have nonzero \(m\), by the label
  restriction and the initial-segment condition. If \(\delta=1\),
  condition 2 gives the same conclusion. The guard therefore fails
  at that occurrence, since the polynomial ring is a domain. If all
  guards succeed every top summand on both sides is zero. This works
  even when an operand itself contains a labelled operation. Fixed
  lower contexts preserve top labels.
* The join, bridge-to-context and auxiliary factorization equations
  on a pair of disks hold in the label coordinate already on that
  *single* pair. Both routes evaluate the same Gray tableau there.
  Their comparison terms are principal atoms on faces in fixed lower
  contexts, pure insertions, or inner steps with zero top value.
  Thus they use the very same basis assignment. This includes the
  prefix test for \(K\), the identity-image \(H_R\), and the two
  unit specializations of \(J\). At shifted cuts use strict values.
* For a triple of positive ranks first expand the top labels of the
  two bracketings using (2). The terms without a new \(\delta\) agree
  by square-zero associativity, with the given input labels held fixed.
  A \(\delta\) from the first multiplication contributes only if the
  third input has positive unsigned top weight. Both arguments of
  that \(\delta\) have nonzero \(\ell,m\), and the third has nonzero
  \(\ell\) and, if of rank at least two, nonzero \(m\). For a \(\delta\)
  from the *last* multiplication one child is itself the principal
  disk of two arguments. Its top signed row is the product of their
  top rows in disjoint variables. Condition 1 forces their ranks
  individually to equal the sums of the \(d_h\) on their own spans,
  by homogeneity. Restricting the first or second convolution row to
  either span recovers that input row in the ranks in which it is
  required because all positive-degree rows from the other span vanish under
  the restriction. Condition 2 thus gives nonzero \(\ell\) for all
  three inputs and nonzero \(m\) for each of rank at least two.
  In either case the tested variation and the crossing of the other
  two 1-faces give guard value \(m_X\ell_Y\ell_Z\ne0\), for *any*
  eligible chosen variation \(X\). Thus every new contribution is zero
  whenever the triple equation is imposed. Total degree three never
  uses \(\delta\). With a vertex and two higher ranks the balancing
  or exterior test is the product of their masses, both preserved by
  transport across the vertex. A difference from a new \(\delta\)
  therefore also fails that test. Two vertices act by pure transport.

Equality of the immediate faces is a premise wherever the presentation
requires it. In checking a higher equation it suffices to compare the
top labels after those matches. This accounts for lower face differences
in the moment coordinate that a signed-row calculation alone would miss.

Assign to leaf \(h\) signed rows \(a_s=v_h^s\) through \(d_h\), zero
higher rows, and zero labels. Take \(j,z=0\) whenever needed, with
equal moment faces. To invert the leaf at \(i\), negate its top
signed row, which restricts to zero at \(v_i=0\), reverse its faces,
and negate its top moment or \(z\) if present. Higher reverse fillers
in that coordinate exist uniquely. In the signed rows of each node,
the generating polynomial of its sequence of rows is the product of
the leaf polynomials \(\sum_{s=0}^{d_h}(v_h T)^s\). This gives the
required top monomial and every required nonzero restricted first or
second row at \(L,R\). The child missing \(i\) retains both unsigned
rows. Thus (2) supplies one at the chosen node. At every ancestor the
other child's unsigned top weight is one, including a vertex partner.
The root label is positive. A two-sided inverse would add it to a
natural number to give zero. This proves necessity of (1).

The same models work under the inner-invertibility hypothesis. More
explicitly, for any substitution from a free diagram, a nonzero top
label implies a nonempty top Gray chain of the *original term*. Induct
on its construction. A new summand needs two nonzero signed top rows,
which factor through the Gray evaluation. An inherited one needs a
labelled face and a positive unsigned face, or a pure transport.
These supply a top basis occurrence in the generic Gray paste by the
induction hypothesis and positivity. Composition adds top occurrences
after Godement expansion. For an auxiliary do this on its prescribed
contextual tableau. Thus a letter with identity Gray image has zero
top label and zero signed top row. Reverse its faces in the moment
coordinate, negating the top group label when present. The resulting
cell is its inverse. This also covers inner instances of operations
at the outer cut.

## Dependence on the lift and the pseudo-factor question

On \((2,1,1)\) with the **first** input invertible, the left bracketing
passes (1) twice. The right bracketing is \(W(A,\chi(b,c))\) and fails
(1) at the root. In the Gray quotient their tableaux are the same top
atom by associativity. Thus no list depending only on \((d_1,\ldots,d_n),i,S\)
can give the verdict for an unspecified lift. Specifying an actual
boundary pair and a forced value, if one exists, is additional data.
The example distinguishes the operations without assuming the two
raw boundary pairs equal.

Q2 is **false in every setting**, even if a convention can choose the
more favorable of the two bracketings. On \((2,2,2)\) distinguish the
middle variable in the construction. It supplies the pseudo slot \(j=2\)
in Q2, with slot 1 as the earlier positive slot.
Take the exceptional node at the root. One may allow both root splits,
using their respective totals and tests in the definition of \(\delta\), since
the preceding verification applies summand by summand. Both root values
are positive. Nevertheless the middle input is ps*. For any positive
cell \(y\) before it and any positive face \(x'\) of that input, including
the input itself, \(w(a_{\dim x'}(x'))=0\) and its top label is zero.
The binary pair ends at object 2, whereas a new label requires the
interval ending at object 3. Hence its mixed label is zero by (2).
The signed top product has zero unsigned part. Negating that signed
row is allowed, reversing its moment data as above, so \(G(y,x')\)
is strictly invertible. This checks the quantifier over *all cells*
in the algebra. For a binary pair with the pseudo input last the
conclusion of course follows directly from the definition. It is
continuation past that pair, or a different bracketing, that the
general rule would have to justify.

## Other letters, and the limit on an exact decision rule

For the generic operations, the distinction is between a subdivision, a
factorization, and an identification *conditioned on identity*. Strict
invertibility makes the first usable with inverse operands. In a factorization
\(f=gh\) with \(f\) invertible, \(g\) is invertible exactly when \(h\)
is invertible, since either one gives an expression for the other using \(f\)
and its inverse. An invertible cell in an identity premise need not satisfy
that premise. Here are the consequences for the named families.

* **Composite disks.** The signed strip works if the marked operand is
  the composite itself or one of its pieces. Use \(A;1=A\), or suspend
  a groupoid with three distinct objects and give its arrows the differences
  of the heights \(0,1,2\). Mark the tile of width two against width one.
  Both pieces, their composite, and the other operand can all be invertible.
  Nonzero label still implies failure of that tile's guard. A particular
  composite forced to be an identity has the unit value.
* **\(K,J\).** Take both short advances invertible in the signed strip.
  Use identity left and right variations. The unit rules give
  \(K(1_A,B)=W(A,B)\) and \(J(1_A,1_B)=K(1_A,B)\), with the
  displayed contexts specialized to units. This simultaneously refutes
  propagation from every positive input position, even with all inner
  letters invertible. The same mechanism applies to a composite
  specialization retaining either letter. [Seed unit rules](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#the-two-variations-at-once)
* **Outer join.** For the left input \(A\), the factorization in (M4)
  gives exactly the test on the *particular* correcting square
  \(\bar\iota_-\). Requiring this square invertible suffices. The split
  that expands its \(A\)-slot also suffices by (M6). For the other
  input, put \(B=1\) to obtain \(r(A,\beta)\) in the strict free Gray
  disk on a proper \(A,\beta\). Its positive top chain has no inverse
  even though every inner letter is an identity.
* **Shifted joins.** These are inner at positive cuts. A hypothesis
  inverting all inner letters includes the join itself. The shifted
  law \(e=1\Rightarrow h=\bar r_1\) yields that conclusion
  when the correcting square is an identity. Even inverting every
  elementary square and imposing both switches does not give a
  one-input propagation rule there.
* **Higher naturalities and routes.** The principal disks, including
  the higher unary naturalities, obey (1). A proper auxiliary bridge
  identified with a contextual principal atom only under a guard has
  no one-input rule merely from that identification, even with all
  inner letters invertible if its generic Gray image is outer. On
  a successful guard it has exactly the invertibility of its specified
  contextual value. Bottom insertions in the bridge recursion are
  fixed whiskerings of the moving input. A route is a composite of
  its contextual steps, so inverses for the steps give an inverse
  in reverse order. The decision problem for arbitrary such terms
  with matching of composite operands is addressed below.

There is a stronger form of the mixed-disk exclusion on **unconstrained
pasting diagrams**. If a top occurrence on two spans evaluates on its
own disk pair to a contextual atom with both entries of rank at least
two, and its substituted top Gray chain on the diagram is nonzero,
no positive-rank operand of smaller rank suffices. This includes every
such outer \(W\) on composite inputs, and outer \(K,J\) instances
retaining their \(W\)-atom. It holds with all inner letters invertible.

To see this, use the signed construction only through the output rank
\(D\), with unrestricted signed rows, zero natural-number labels in
smaller ranks, and unique fillers on parallel boundaries above \(D\).
Every positive-rank cell below \(D\) now has an inverse. On the free
diagram assign each globular generator in short slot \(h\) row \(v_h^s\)
in each positive rank \(s\) through its dimension. Take equal moment
faces and zero additional moment data on globular generators. This is
a globular assignment since a generator has the specified generators
as its faces. On the two participating input faces select one basis
tuple from each top Gray chain contributing to the contextual atom.
Use their multidegrees as the \(d_h\) on their respective spans, and
give the selected pair the additional label by conditions 1 and 2 of
(2), with no condition 3. The selected monomials occur with positive
coefficients. To check condition 2, first take one of the selected
basis atoms. Contracting the variables outside a subinterval retains
the first and second rows of the corresponding product of leaf
polynomials whenever its retained degree is at least one and two,
respectively. In the surrounding strict atomic paste these nonzero
rows survive because composition either adds nonnegative rows, or retains
a matching row with the same polynomial at its two faces. This proves
the condition also on a composite input. The fixed whiskers on the
selected output retain its top label.

At the tested rank the mixed-paste and three-factor guard checks are
exactly those above. A positive triple cannot inherit a label from a
smaller-rank first multiplication here, so only the last-multiplication
case needs condition 2. Equations with a vertex use the two-mass test.
The single-disk check gives the values of auxiliaries even when the
substitution specializes a variation to a unit. Above the test rank
the prescribed parallel boundaries have unique fillers. A marked top
occurrence requires two nonzero signed top rows, so has nonempty
generic Gray chain. Hence every inner letter remains invertible.
This proves the exclusion directly for diagram operations, without
using any group presentation as a domain constraint.

We give details for the independence assertions, because in particular
a noninvertible *bare* inner square need not realize the correcting
square in an outer join. First, suppose the split on the \(A\)-slot
of \(\iota(B,A)\) is absent. Use a signed left short advance and an
ordinary right chain as in the strip, and give long 3-endomorphisms
values \((a,b)\in\mathbb Z\times\mathbb N\), adding on composition.
The pure actions take the two short advances to their respective
coordinates. Give 4-endomorphisms at each 3-value labels in the monoid
of maps \(\mathbb N\to\mathbb N\), with chronological composition.
All fixed lower pads keep the label. This defines sesquicategorical
whiskering because each lower action is an identity on the label coordinate
and Godement composition performs the two maps in its specified order.
The maps \(t(n)=n+1,\ s(n)=\max(n-1,0)\) satisfy \(ts=1\) chronologically
and \(st\ne1\). Use zero 3-value for \(\chi\), identity map for
\(r,t\) (the naturalities), and give an inner square on \(X,Y\) the map
\[
 s^{\,b(X)[a(Y)\ne0]} .
\]
Set the outer join on advances \(A,B\) to \(t^{\,b(B)[a(A)\ne0]}\).
The factorization is \(t^ks^k=1\). The split in the first argument
holds by additivity of \(b\), and either slot against a literal
crossing has zero exponent. Short internal squares transport with
zero exponent, spatial balancing keeps both coordinates, and all
varying-whisker corrections against a crossing are identities. These
are the low equations. Use unique fillers on every parallel boundary
above four. Units hold at exponent zero. The image of the join on
the generating pair is \(t\), which is not surjective. This supplies
the countermodel even with the switch on the other slot.

For a shifted join, suspend the two-span signed strip at the chosen
cut. In relative global degree four take labels
\(\mathbb Z\times\mathbb N\) under addition. Use \((xy,0)\) for the
correcting square, \((0,[ab\ne0])\) for the join, and zero for
the unary naturalities. Both short top inputs can be isomorphisms.
The sole shifted join identification at this rank has premise that
the correcting square is an identity. There \(ab=0\) and the two
values are zero. The square splits are distributivity. Exterior
transport from either short interval has a unit spatial operand.
Cuts outside the suspension have a terminal partner, and the relative
higher ranks have unique fillers on parallel boundaries. This verifies
the shifted table with every elementary square invertible. The relevant
squares here are zero, group-labelled, or uniquely reversible higher
fillers. Its join label has second coordinate one. [Shifted join law (B)](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#the-presentation-and-its-boundaries)

Here is the independence check for the outer auxiliary bridges other
than \(K,J\). It is useful when the atom on the right side of the
guarded equation is itself a unary cylinder. Use two proper outer
spans with the signed rows and moment coordinate above, now allowing
*all* signed rows (no unsigned-row restriction). All positive-rank cells
of these two coordinates are invertible. At the tested output rank add a single
\(\mathbb N\)-coordinate on the long span, additive on compositions
and preserved by lower pads. Above it take unique fillers on all
parallel faces, retaining the prescribed unit values. Use zero top
label on all principal operations, on inner comparisons, and on the
other proper auxiliaries. On the selected proper auxiliary give label
one when the two transported 2-masses have nonzero product and the
signed top row of its contextual Gray atom is nonzero. Use the unit
rules, including restriction to the specified fixed face, before
this assignment. Short spans have the same signed rows and moment data,
with zero added label.

To check this rank extension, a proper bridge above the bottom of
the raising recursion occurs as the head of its guarded comparison
to the fixed-context atomic representative. That representative uses
principal operations on faces. All mixed-paste, unary, and ternary
subdivisions at this rank concern principal operations. Thus a
proper marked occurrence cannot enter those equations as a top
piece, and its own comparison fails its mass test. For the seed
bridges \(G,H\) the same test is prescribed. For \(H_L\) the guard
in the variation of the factorization tests the suffix \(e^1\),
whose label in the moment coordinate is the same nonzero product.
The separate prefix equation for \(K\) involves the contextual \(W\)
and a positional comparison, both zero in this extension. \(H_R\)
has identity generic Gray image and belongs to the inner case.
Unit instances in this check use the declared smaller operation.
At a unit moving variation the recursive bridges are identities, and
at a unit fixed variation the smaller bridge is used up to its own
rank, and the extra rank is its identity. The 2-mass test on the
smaller bridge is unchanged whenever that specialization retains a
mark. In the \((3,3)\) seed a unit variation gives \(Z_A,Z_B\)
or an identity for \(G,H\), and \(J\) specializes to \(K\) or \(W\)
followed by \(H_R\). None introduces \(H_L\) in the prefix equation.
These are all the same-rank uses of the auxiliaries. The face
recursions give parallel faces for the higher declarations, so
unique fillers suffice there. Nonzero labels imply nonzero signed
Gray row for the marked occurrence. Thus an inner letter has top
label zero by the same top-occurrence induction used for (2).
Assign signed rows \(v_h^s\) in each positive input rank. The
generic proper outer bridge has a single positive contextual top
atom, so it receives one. Its inputs are invertible in the short
spans. This construction distinguishes failure of the guarded
identification from any failure of its principal representative.
[Seed comparisons](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#both-mixed-disks-in-the-next-degree)
· [All higher bridge comparisons](../answered/lax-interchange-every-dimension-r5-2026-11-20.md#quotient-equations-and-the-window-induction)

### No decision procedure for every partial operation

A term of the partial theory defines an operation on the assignments
where its indicated composites match. We exhibit one fixed finite
matching context and a computable family of single outer letters
\(\ell_w\) in it. The hypothesis is only that the **entire right
operand** of \(\ell_w\) is invertible. For every \(S\), even under
the additional requirement that all inner letters are invertible,
\[
  \ell_w\text{ has the universal right-input rule }
       \quad\Longleftrightarrow\quad w=1\text{ in }H,                 \tag{3}
\]
where \(H\) is a fixed finitely presented group with unsolvable word
problem. Such a group exists by the Novikov–Boone theorem.
[Boone, *The Word Problem*](https://www.jstor.org/stable/1970200)

Use 1-endomorphisms of an object \(X\) for the generators and their
formal inverses. Require the inverse words and defining relators to
equal \(1_X\) (for each generator \(g\) these inverse words are
\(gg^{-1}\) and \(g^{-1}g\)). Add a 1-cell \(e:E\to X\), parallel
1-cells \(u_0,u_1:X\to Y\), a 2-cell \(\alpha:u_0\to u_1\), and
a 3-loop \(Z:\alpha\to\alpha\). Require \(eZ=1_{e\alpha}\), with
juxtaposition denoting prewhiskering here. Let \(B\) be a global
3-cell in the following hom from \(Y\) to a fourth object. Set
\[
                            \ell_w=W(ewZ,B).
\]
These are ordinary finite matching requirements on partial terms.
For precision, they can even occur in the evaluation of a single
composite operand. For each word \(r\) required to be \(1_X\), the
term \(1_r *_1 1_{1_X}\) of degree two is defined exactly on that
match and then has 1-source \(1_X\). Insert the product of these
1-sources between \(e\) and \(w\). Likewise the 3-source of
\(1_{eZ} *_3 1_{1_{e\alpha}}\) is defined precisely on the stated
3-match and is then \(1_{e\alpha}\). Compose it chronologically
before the left operand, on the domain \(e\alpha=ew\alpha\).
The examples below satisfy that extra boundary match as well. This
explains how to read the reduction either in a finite partial Horn
arity or using the actual domain of a composite expression. When
\(w=1\) in \(H\), every assignment equalizes the word with \(1_X\).
The left operand is an identity and the disk is its unit instance.

For \(w\ne1\) we construct an algebra and assignment. Use the signed
two-span strip, now using in each short suspension a one-object arrow
group \(\mathbb Z\). Its unit 3-advance and its distinguished 3-loop
of value \(+1\) have the same 2-boundary. The suspended interval
still has two distinct objects. The signed-strip verification applies
to integer powers. Mark only \((+1,+1)\). A marked
tile still fails its own test. Both input loops are invertible.
In this table all inner letters are invertible. To see this also for
substituted letters, the signed 3-advance factors through a strict
Gray row evaluation (all edge weights and hence all crossing weights
zero, pure advance weights signed). A marked outer disk has two
nonzero such rows. A term with empty generic top Gray chain cannot
acquire a mark, by positivity of top occurrences before substitution.
All other long coordinates of a killed letter are group-valued or
reversible higher fillers.

Take indexed families of objects of this table. A 1-cell of families
is an index function and a component 1-cell at each index. Positive
higher cells exist only over the same index function and are
componentwise cells between the specified components. Compose functions
and evaluate each component after reindexing. Every operation of \(V+S\)
is defined by its component on the resulting string of indices. Indeed
the global 1-boundaries across a 2-cell have the same index function,
so varying the route never changes the indicated index. The structural
whiskerings act by function composition and component whiskering. A
matched premise matches at every component, where the law holds.
This proves the algebra axioms. Inverses at ranks above one are
componentwise. It suffices to use the full subalgebra on the families
in the following assignment.

At \(X\) take \(H\) copies of the first object of the strip. Let the
generators act by the regular action, with identity component arrows,
and let \(e\) pick the identity element. Take \(E,Y\) and the final
object to be singleton families of the corresponding strip objects.
Use constant families for \(u_0,u_1,\alpha\), with the two ends and
the sole advancing 2-arrow of the first short suspension. Put \(Z=0\)
at the identity index and \(Z=+1\) at every other index. All the
defining relations hold, \(eZ=0\), and \(ewZ=+1\). Put \(B=+1\)
in the second short span. Then \(\ell_w\) has label one. This proves
(3) without asking whether a proposed inverse can be found by search.

In particular, an algorithm deciding every letter on composite operands
as asked would decide the word problem by testing only \(W\). The same
reduction works if one requires any subfamily of the inner letters to
be invertible, since the positive case used only the unit law and the
negative model already inverts them all. Together with round 1's
finite-derivation criterion this gives a recursively enumerable,
undecidable propagation problem. Additional designated inner
invertibilities can be incorporated in that criterion by adjoining
the unique inverse at each required instance, also for newly formed
terms. A proposed inverse and its two cancellation derivations use
only finitely many such adjunctions. The countermodel for a failed
instance in this presentation is its initial term algebra.

The matching-context qualification in (3) matters. Its arity is not
an unconstrained wedge of globes. It proves no undecidability claim
for the numerical disk-tree test (1), or for a list restricted to
primitive heads on their generic arities. Conversely, a head table,
even one correct on every generic disk, cannot decide the composite
instances in (3). This is where the demand for a total generalization
of the round-1 semidecision fails.

## Validation

Run the [factor-rule checker](../../../scripts/e6/interchange_factor_rules.py)
with `python3 -B scripts/e6/interchange_factor_rules.py` from
the repository root. It composes the signed 5-arrows on 343 strip
assignments, checks 1,265 signed low-law and one-sided join instances,
and evaluates cocycles on both faces and 7,164 matching pastes of
actual Steiner cells from three disk pairs. Its sparse polynomial
calculation compares (1) with the countermodel at 1,208 tree/node tests
through four slots. In 153 signed triple assignments, eight have
different bracketing labels and every eligible triple guard fails in
each such case. Four assignments on the pseudo example mark both
bracketings while the binary pseudo tests have zero top label and zero
unsigned weight. It also tests a labelled preceding argument and a successful triple guard
whose bracketed 2-mass is nonzero. The checker evaluates the family construction
on 511 words in the regular action of the symmetric group on three
letters. The infinite-group step in (3) uses the group word-problem
theorem, not that finite calculation.

The round-1 invertibility check, the moment grading, the stationary
subdivision check, and the double-variation disk check also pass
(`interchange_invertibility.py`,
`interchange_path_grading.py`,
`interchange_gray_composition.py`, and
`interchange_double_variation.py` in the same directory).
The all-arity validation is the equation-schema verification above.
The finite computations test its face conventions, guard multiplicities
and counterexample evaluations.
