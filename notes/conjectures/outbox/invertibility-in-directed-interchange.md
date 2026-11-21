# Invertible cells in free higher categories with directed interchange

*A self-contained problem. The theories below are defined in full in the repository files `notes/conjectures/answered/lax-interchange-every-dimension-r5-2026-11-20.md` (Responses 1–34) and `notes/conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md` (Response 1); §1 fixes the notation and lists what is proved.*

**What we are asking for.** Free algebras of the admissible theories below have no non-identity invertible cells, and their interchangers are directed. We want to know what happens when some cells *are* invertible: (Q1) which structural cells become invertible when their inputs are, in every algebra; and (Q2) whether formally inverting all interchangers at cuts ≥ k makes cells with equal image in the k-quotient connected by invertible cells, i.e. a relative coherence theorem for each quotient of requirement 4. The main questions ask for the general statement, for every pasting diagram, every dimension, every cut and every setting of the two switches, or a counterexample.

## 1. Setting

**Composition.** Reflexive globular sets with partial compositions ∗ₖ of n-cells along k-cells (k < n), written in diagrammatic order, strictly associative and unital, with whiskering by lower-dimensional cells strictly functorial (ω-sesquicategories). For n-cells in interchange position along k < l, `L = (a ∗ₗ b) ∗ₖ (c ∗ₗ d)` and `R = (a ∗ₖ c) ∗ₗ (b ∗ₖ d)`. A strict ω-category requires L = R.

**The signature.** The T₁₂ signature of the cited round-5 answers: the sesquicategory operations; for every k < l an elementary interchanger, which for (l+1)-cells F : f ⇒ f′ and G : g ⇒ g′ in interchange position along a k-cell is the (l+2)-cell
```
ι(F, G) : (f ◁ G) ∗ₗ (F ▷ g′)  ⇛  (F ▷ g) ∗ₗ (f′ ◁ G);
```
one naturality cell per varying argument, with Leibniz-signed orientations; higher cells between routes of lower ones; and the auxiliary operations of the completion (binary joins h(A, B), lifts W(A, B) of binary globe tensors, H_L, H_R, K, J, shifted joins).

**Requirements.** A strict theory on this signature is *admissible* if its free objects F(Γ) on finite globular pasting diagrams Γ satisfy:
1. an explicit combinatorial description by generators with explicit boundaries;
2. two cells of the same dimension using the same generators, in an expanded basis, are equal;
3. every elementary interchanger exists and its reverse does not;
4. making every interchanger along a k-cell with k ≥ 1 an identity gives the free Gray-enriched category 𝔉(Γ) (homs ν(λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ) for Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ, Steiner's λ, ⊗, ν), and making every interchanger an identity gives the free strict ω-category ν(λΓ);
5. closure under substitution of cells for generators.

Write π₁ : F(Γ) → 𝔉(Γ) and π₀ : F(Γ) → ν(λΓ) for the two quotient maps of requirement 4, and π_G : 𝔉(Γ) → ν(λΓ) for the Gray-to-strict collapse.

**Letters.** Every d-cell of F(Γ) is a ∗_{d−1}-path of *contextual letters* (a d-dimensional operation applied to arguments, whiskered by lower cells). π₁ sends each letter to a whiskered generator of 𝔉(Γ) (an **outer** letter) or to an identity (an **inner** letter). Inner letters include the elementary interchangers along k ≥ 1 and their naturality and route cells. Outer letters include the whiskered variables, the cylinders of a moving globe against an edge (naturality cells r, t of the cut-0 crossing), the joins h(A, B) and the lifts W(A, B).

**Known results (all proved).**
- **(M1) The least theory V.** There is an admissible theory V (the forced base B plus the guarded round-5 equations) such that for every admissible E and every Γ the identity on letters gives a generator-preserving map F_V(Γ) → F_E(Γ) sending cells to cells and equalities to equalities. B contains the structural theory, the support-free presentation P of the cited answers, the face and unit declarations (an interchanger with an identity input is an identity), and the outer unary subdivisions in both variables at cut 0 (a cylinder of a composite moving globe, or against a composite edge, is the paste of the cylinders). (r8 Response 1.)
- **(M2) The two visible switches.** The left split of the inner interchanger ("inner composite-crossing law": ι(F₁ ∗ F₂, G) is the paste of ι(F₁, G) and ι(F₂, G)) and the right split R (the same for a composite right input) are each visible on pasting diagrams and independent. For S ⊆ {left split, R}, V + S is admissible. In V the binary splits at inner cuts are absent and the outer binary subdivisions are present only in guarded form. (r8 Response 1; r9 Responses 2–5.)
- **(M3) The strip.** On the strip C_{2,1} (inner cells A₁, A₂ composable, B in interchange position), the direct crossing u = W(A₁ ∗ A₂, B) and the paste v of W(A₁, B) and W(A₂, B) are parallel, π₁(u) = π₁(v), and in F_{V+S}(C_{2,1}) with the left split not in S there is no cell u ⇛ v and no cell v ⇛ u. A tagged algebra (tags in subsets of operand-length pairs, union under composition) separates u and v. (r5 (K44), (K51); r8.)
- **(M4) The binary join.** On ΣD² ∨ ΣD² with 2-cells A (first hom) and B (second hom), the join h(A, B) : S ⇛ U₀ satisfies r̄₁ = h(A, B) ∗ ῑ₋, where r̄₁ is a whiskered cylinder of A against the edge β₁ and ῑ₋ is a whiskered inner interchanger whose inputs are a whiskered A and a whiskered B. (r5 (K45); round-3 repair (F).)
- **(M5) Positivity.** Every non-identity cell of F_{V+S}(Γ) has positive conserved weight, so F_{V+S}(Γ) has no non-identity invertible cell. (r5 (K50).)
- **(M6) Elementary propagation.** In every algebra of every admissible theory: a cylinder with an invertible moving input is invertible (from (M1)'s unary subdivisions and unit laws); an inner interchanger ι(F, G) with F invertible is invertible if the left split holds in the algebra, and with G invertible if R holds (the inverse is (F ▷ g) ◃ (ι(F⁻¹, G) ▹ (F ▷ g′)), respectively ((f ◁ G) ◃ ι(F, G⁻¹)) ▹ (f′ ◁ G)). Consequently, by (M4), if A is invertible then h(A, B) is invertible iff ῑ₋ is, and both are when the matching split holds.
- **(M7) The Gray-to-strict level.** For strict Gray-enriched categories, an interchanger (mixed Gray generator) with an invertible positive-dimensional factor is invertible. In the (∞,ω) setting, Gray-enriched (oriented) categories whose composition inverts all mixed cells are exactly the Cat_ω-enriched ones (change of base along A ⊗ B → A × B).

**Definitions for the questions.**
- For an algebra 𝒦 of an admissible theory E and a map σ : F_E(Γ) → 𝒦, a cell is *invertible* if it has a strict two-sided inverse.
- For a pasting diagram Γ and a cut k ∈ {0, 1}, let I_k be the set of letters of F_{V+S}(Γ) sent to identities by π_k (for k = 1, the inner letters; for k = 0, every interchanger-type letter). Let F_{V+S}(Γ)[I_k⁻¹] be the algebra presented by F_{V+S}(Γ) together with, for each ℓ ∈ I_k, a new cell ℓ⁻ with the boundary of ℓ reversed and the equations ℓ ∗ ℓ⁻ = 1, ℓ⁻ ∗ ℓ = 1 (the free algebra on Γ in which the letters of I_k are inverted).
- For each tuple x₁, …, xₙ of cells in consecutive homs, the *Gray cell* G(x₁, …, xₙ) is the image under substitution of the top cell of F_{V+S}(ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}) lying over the top atom of 𝔉 (for ΣD² ∨ ΣD², the lift W).

## 2. Questions

**Q1 (main: propagation of invertibility).** Fix S ⊆ {left split, R}. Characterize the letters ℓ and argument positions for which "the argument is invertible ⇒ σ(ℓ) is invertible" holds for every algebra of every admissible theory satisfying V + S. In particular, decide, for every pasting diagram and every dimension:
- (a) whether, for every outer letter ℓ with π₁(ℓ) a whiskering of x₁ ⊗ … ⊗ xₙ, σ(ℓ) is invertible whenever σ(G(x₁, …, xₙ)) is (call this (IL));
- (b) whether an inner interchanger with an invertible input is invertible in setting S without the matching split (that is: is the converse of (M6) true, or is there an algebra of an admissible theory satisfying V + S, with F invertible and ι(F, G) not invertible?);
- (c) whether invertibility of all elementary inner interchangers whose cells lie in homs into a fixed object C implies invertibility of every inner letter in those homs (naturality cells, joins, route cells).

A complete answer for S = ∅ is the main result wanted; the other three settings next.

**Q2 (main: relative coherence for the quotients of requirement 4).** For which S does the following hold for every finite pasting diagram Γ and k = 1: if p, q are parallel cells of F_{V+S}(Γ) with π₁(p) = π₁(q), then F_{V+S}(Γ)[I₁⁻¹] has an invertible cell p ⇛ q? And the same for k = 0 with π₀, and for the Gray level: if p, q are parallel in 𝔉(Γ) with π_G(p) = π_G(q), does 𝔉(Γ)[mixed⁻¹] have an invertible cell p ⇛ q? A uniform answer for all three quotient maps (every dimension, every Γ), or a description of exactly which pairs fail, is the main result wanted.
- By (M3), for k = 1 and S without the left split the strip pair (u, v) has no cell either way before inverting; the question is whether inversion creates one.

**Q3 (invisibility).** For S = ∅ and every Γ: is every outer letter instance σ(ℓ) in F_{V+S}(Γ′) (σ a substitution between pasting diagrams) whose Gray cell is an identity itself an identity? Equivalently by (M5): does adjoining (IL) to V, as partial inverse operations defined when the Gray cell is invertible, leave every free algebra on a pasting diagram unchanged?

**Q4 (fallback).** Does the tagged algebra of (M3) remain an algebra of an admissible theory satisfying V when the tags are taken in the free abelian group on operand-length pairs (composition adding tags), instead of subsets under union? If so, in it every inner letter is invertible while u ≠ v and no cell connects them, which answers Q2 negatively for k = 1 and S ∌ left split. A proof that some law of V forces idempotent tags would also settle this.

## 3. What counts as a solution

A complete answer to Q1 or Q2 in every dimension, positive or negative (a countermodel that is an algebra of an admissible theory counts); an answer to Q3; or an answer to Q4.

## 4. Literature (searched 2026-11-21)

- Ara–Maltsiniotis, arXiv 1607.00668 (lax Gray tensor); Steiner, *Omega-categories and chain complexes*, HHA 2004.
- Gepner–Heine, arXiv 2510.10504, Thm 4.1.9 (Fun → Fun^lax is an inclusion); Campion, arXiv 2311.00205 (Gray tensor of (∞,n)-categories).
- Benjamin–Markakis–Sarti (invertibility of coherences in CaTT); Benjamin–Champin–Markakis (inverses in CaTT).
- Bourke–Lobbia, arXiv 2610.31448 (sharp coherence for lax interchange).
- Forest–Mimram, arXiv 2109.05369 (rewriting in Gray categories presented as 3-sesquicategories with interchangers); arXiv 2310.03503 (remarks on the interchange in Gray-categories). In both the interchangers are invertible from the start, which is the situation Q2 asks to reach by localization.
None of these treats invertibility in theories with directed interchange at inner cuts.

# Researcher Response 1

The two uniform quotients both fail relative coherence for **every** setting
of the switches. The same pair works for both quotients and all four
settings. It consists of a 4-loop and its identity on the four-crossing
grid. Relative coherence **holds** for the Gray-to-strict map. Thus the
obstruction already occurs in the first step from uniform to Gray.

For propagation, (IL) is false in every setting, already on substitutions
between free pasting diagrams. An elementary inner square has the
universal one-input propagation rule on a side precisely when the
corresponding split is imposed (as a rule for all inputs). Invertibility
of the elementary inner squares into an object does not suffice for the
other inner letters, even with both splits. Below we give the witnesses
and a presentation-theoretic characterization for individual letters and
positions, including contextual and degenerate instances.

## The four-crossing loop survives both localizations

Use three objects with short homs \([2],[2]\), terminal endomorphism homs
and empty backward homs. The long hom has a single global 1-cell and a
single 2-cell. Its global 3-cells are integers. Over each such integer
\(n\) the 4-cells are endomorphisms \((n,z)\), with \(z\in\mathbb Z\).
Only identities occur above dimension four. For top composition at
\(n\) add the labels. Under lower composition add the 3-values and
the 4-labels separately. An identity on \(n\) is \((n,0)\).
These operations give strict composition and functorial fixed whiskering
by associativity and commutativity of addition. The pure actions of the
short homs into the long hom have their unique lower values.

Give the outer crossing on short arrows of lengths \(a,b\) the 3-value
\(ab\). Give the inner square on long 3-cells \(x,y\) the 4-label
\(xy\) over \(x+y\). Its two schedules both have 3-value \(x+y\).
The following verifies this is a model of \(V+S\) on *arbitrary*
assignments, which is essential when inverses may occur in subsequent
operations.

* At the outer cut the only mixed disk with two proper inputs is a
  square on short arrows. Its unit and both subdivisions are the zero
  and distributive laws for multiplication. There is no string of
  three proper outer spans. Naturality, the join factorization and
  the varying-whisker equations specialize to units. In the latter
  equations the correcting inner square has a unit varying operand.
  A long input can have only a terminal outer partner.
* Inside the long hom one can equivalently describe the operations
  as genuine Gray composition at the cut of the inner square. The
  strict endohom there has one object, arrows \(x\in\mathbb Z\),
  and 2-endomorphisms labelled by integers at each arrow. The pure
  actions of this one object are identities. On the disk tensor use
  the mixed square labelled \(xy\), and identities on all higher
  mixed atoms. To see that these assignments define the composition
  functor, an arrow subdivision on either side adds the two labels by
  bilinearity. For a variation \(z:x\to x\), the two faces of its
  naturality atom have labels \(z+xy=xy+z\). The right variation
  has the same check. All higher parallel faces are equal above this
  rank. These are the generating disk faces, units and subdivisions
  of the strict Gray tensor. Associativity on three inputs holds on
  the pure atoms and the squares with a vertex factor, and the
  triple of arrows has identity top value in either bracketing.
  This gives all the higher declarations at this cut by their Gray
  values, including the contextual values of the auxiliary operations.
  At deeper cuts composition is strict. In particular both inner
  square splits hold.
* In degree four the restricted splits of \(P\) are among the two
  splits just checked. A fixed exterior interval on a proper outer
  pair is terminal. Transport from a short hom preserves all its
  identity inner squares. This checks balancing and the remaining
  low equations. In higher degrees the prescribed disk and auxiliary
  faces exist by the two preceding checks and their unit
  specializations. Any equation between defined parallel cells in
  degree at least five now holds. This includes the guarded laws of
  \(V\). Admissibility is needed for the *theory*, supplied by (M2).
  Its test algebra may have invertible cells.

Take \(\Gamma=\Sigma[2]\vee\Sigma[2]\), with generating arrows
\(a_1,a_2\) and \(b_1,b_2\) in its short homs. Expanding
\(w=\chi(a_1a_2,b_1b_2)\) in the two subdivision orders gives two
expressions for the same 3-cell. They differ in the order of the
middle crossings \(F=\chi(a_1,b_1)\) and \(G=\chi(a_2,b_2)\).
Whiskering \(\iota(F,G)\) by their common prefix and suffix therefore
gives \(H:w\to w\). This is the loop of round 5, (K34). Both
\(\pi_1\) and \(\pi_0\) send \(H\) to the identity on the image of
\(w\).

Under the generating assignment each middle crossing has value one.
The prefix and suffix translate the underlying 3-value and preserve
the 4-label. Thus \(H\) evaluates to \((4,1)\) and \(1_w\) to
\((4,0)\). Every marked letter for either localization evaluates to
an invertible cell. Indeed the short homs already have their strict
values, all mixed images in degrees three and four in the long hom
are group-valued, and higher images are identities. The assignment
extends across the specified inverses by their universal property.
There is no 5-cell from \((4,1)\) to \((4,0)\) in either direction.
This proves the two negative answers to Q2. It also distinguishes
every pair \(H^i,H^j\) for distinct nonnegative integers \(i,j\).

## The Gray-to-strict map

Fix an outer interval. Write \(A_i=\nu\lambda\Theta_i\) for its
factors, \(D=\bigotimes_i A_i\) for its strict Gray tensor and
\(P=\prod_i A_i\). The hom map in question is the comparison
\(c:D\to P\). Let \(L\) be the **strict ordinary globular
presentation** of \(D\) with two-sided top-composition inverses
adjoined to its mixed generating atoms. Its comparison to \(P\)
is denoted by \(c_L\). It suffices to find the comparison cell in
\(L\), since its presentation maps into the hom of the localization
in Q2. The dimensions in this argument are hom dimensions.

First, every positive-dimensional cell of \(L\) with identity
\(c_L\)-image has a strict inverse. Expand an expression in the
generating atoms, the adjoined inverses, identities and strict
compositions. At its top dimension count the positive basis chains
of its images in the individual Steiner factors. They add under
composition and are unchanged by fixed lower whiskering. An original
pure top atom contributes a basis element in its one active factor.
A mixed atom and its inverse contribute zero. An identity image
therefore excludes every pure top occurrence. All remaining top
occurrences have strict inverses. Lower whiskering preserves them,
and strict composition pastes them (in reverse order for top
composition). This argument applies also to terms whose lower faces
first match after adjoining inverses.

For existence we use the n-ary Gray-to-cartesian localization
theorem in the repository. It says that a weak functor out of
\(\bigotimes_i A_i\) carrying the mixed cells to equivalences factors,
up to equivalence of functors, through \(\prod_i A_i\).
Here the factors are pasting diagrams. Their strong Steiner tensor
represents precisely this weak Gray tensor, and their product has the
ordinary strict product as representative. These are the localization
and comparison results used in [the n-ary theorem, §3, step 1](../../invertibility-markings.md)
and [the binary theorem and verification](../gray-vs-cartesian.md).
The comparison with the strong Steiner tensor is also in
[Campion, Example 3.2 and Corollary 3.5](https://arxiv.org/abs/2311.00205).

Here are the details that turn this weak universal property into the
strict cell required in Q2. Regard the finite-dimensional strict
category \(L\) as a weak higher category. For fixed *strict*
objects its hom is represented by the corresponding strict hom of
\(L\), and the same is true after fixing successive parallel faces.
One construction is recursive enrichment, taking the same objects
and realizing each strict hom one dimension lower. Equivalently,
complete the iterated Segal nerve: completion is fully faithful on
the homs between existing objects. Inducting down the fixed faces
shows that an arrow between two such objects in an iterated hom has
a strict cell representative at those very faces. The induction
starts with discrete sets in dimension zero. Finite dimension is
available because adjoining strict inverses to atoms adds no proper
generators above the dimension of the tensor. For the hom-fibre
description of full faithfulness and the globe-boundary objects, see
[Rezk, Proposition 7.11 and §11.8](https://rezk.web.illinois.edu/cs-objects-revised-arxiv.pdf).

The functor \(j:D\to L\) inverts every intrinsic mixed globe cell:
its image under \(c\) is an identity, so the first paragraph gives
a strict inverse to its image under \(j\). Consequently its weak
realization factors through \(c\). If parallel \(p,q\) have
\(c(p)=c(q)\), their points in the space of globes with their
boundary fixed become connected under \(j\). Explicitly, take the
homotopy fibre of restriction from the mapping space of the globe
to that of its boundary. For the factorization through \(c\) the
two points already coincide. The equivalence from that functor to
\(j\) transports both along the *same* boundary path, giving the
connection in the fibre for \(j\). Thus they are equivalent objects
of the fixed iterated hom. Take a strict representative \(v:p\to q\)
of a comparison there. Its image in \(P\) is an endomorphism of
\(c(p)\). Each factor is loop-free, so this image is an identity.
The first paragraph gives a **strict two-sided inverse** for \(v\).
For hom objects, equality in \(P\) already means equality of the
object tuples. Empty and one-factor intervals have identity
comparisons. This proves the Gray assertion for every interval, pair
and dimension.

## An outer letter can contain an inner move in an operand

It matters in (IL) that the test uses the factors of the **Gray
generator**. A moving operand of a contextual letter can contain a
move which disappears in that generator.

Use the two outer hom diagrams
\[
       P=D^2\vee D^2\vee D^3,\qquad D^1 ,
       \qquad \Gamma=\Sigma P\vee\Sigma D^1 .
\]
In the first two consecutive intervals of \(P\) take the inner square
\(I\) on the two generating hom 2-cells. It is a hom 3-cell
(global 4-cell). Write \(x\) for the top of the third interval and
\(b\) for the edge of the other outer hom. Compose \(I\) and \(x\)
along their common **hom object**, using the specified Godement
order, and call the resulting hom 3-cell \(Z\). Let the letter be
the outer unary disk \(E(Z,b)\) of bidegree \((3,1)\). It is one
operation applied to arguments as allowed in §1.

In the strict first Gray hom \(I\) becomes an identity.
Consequently the top chain of the first operand is exactly \(x\).
The tensor tableau of the letter has the single top atom \(x\otimes b\)
with coefficient one. An atomic expression in the strict hom therefore
consists of this one atom in lower whiskers. The test cell in (IL)
is \(G(x,b)=E(x,b)\).

Contract the third interval \(D^3\) of \(P\) to its initial object,
keeping the first two intervals and \(b\). This is an assignment to
the free algebra on \(\Sigma(D^2\vee D^2)\vee\Sigma D^1\), including
all faces of the contracted globe. The image of \(G(x,b)\) is an
identity. The image of the letter is \(E(I,b)\). In the primary
round-5 table its outer-unary charge is
\[
                       m_4(I)\,|b|>0 .
\]
Here the weight of the bare inner square on two generating histories
is positive, and \(|b|=1\). These are precisely the degree-four
grading and the outer-unary formula of round 5, Responses 4, 9 and
12. In particular \(E(I,b)\) is proper in the minimum table by (M1).

For clarity, the same detection works if the two elementary splits are
imposed also at higher ranks. Keep the primary table on this last
diagram through degree four (both splits of the degree-four square
hold there). In degree five keep the two faces and the bit recording
positive charge of each cell that occurs. This is a quotient at that
degree: top composition takes disjunction, and fixed whiskering
preserves the bit. Every new degree-five elementary split has the
same bit on both sides. A proper direct square has proper operands,
hence a proper tile on splitting one of them; if a whole operand is
a unit, positivity and additivity give only unit tiles. The bit
quotient reflects identities. Its matches through degree four are
unchanged, so it preserves the guarded equations there and in degree
five: the parallelism premises are lower matches and the identity
tests are reflected. Extend by one filler on every parallel pair
recursively above degree five. All higher faces then type by the
boundary declarations and parallel equations hold by uniqueness.
This is a test algebra with both switches and with the indicated bit
equal to one. Hence the cell in the free table for each \(S\) is
proper, and by (M5) it has no inverse there. This gives the negative
answer to Q1(a) and to both formulations of Q3. Adjoining (IL)
would force a proper cell in this free algebra to become invertible.

## Input positions and the elementary tests

For Q1(b), suspend a three-object table with left short hom the
one-object arrow group \(C_2\), right short hom \([1]\), and long
hom the strict 2-category with one object, one arrow, and labels
\(0,1\) under maximum for its 2-endomorphisms. The pure actions on
arrows are constant. The marked inner square has label one on the
nonzero group element and the proper right arrow, zero otherwise.
Both schedules have the unique long arrow as boundary. Its left
input is its own inverse. The square has no inverse since the
maximum of one with either label is one. Every right subdivision
holds, since at most one piece in \([1]\) is proper. Interchanging
the two short homs and applying the same label rule gives the
right-input example with the left split on. This exchanges the
tables without reversing the prescribed direction of a square.

These are the cyclic tables of [round 7, Responses 2–3](../answered/lax-interchange-every-dimension-r7-2026-11-20.md#researcher-response-2).
To check the specific presentation \(V\), in the suspension every
outer pair has a terminal partner, so all outer unary laws, the
factorization and the restricted splits against a literal outer
crossing have their unit values. At the marked cut the only proper
disk on two spans is the displayed square. Additional spans are
terminal, and inside each strict hom the operations are strict.
Higher disk faces therefore reduce by the unit declarations.
Parallel cells above global degree four are equal, as all are
identities. This checks the guarded completion on arbitrary
assignments. Together with (M6) this proves necessity and sufficiency
of the matching switch for the universal elementary propagation rule.
Extra suspensions place the same example at deeper cuts.

For Q1(c), instead suspend a three-object Gray table with short
homs \(D^2,D^1\). Give its long hom one cell in degrees zero through
two and endomorphism monoid \((\mathbb N,+)\) in degree three,
with only identities above. All compositions of labels add. The
composition on the two short spans is the strict functor out of
\(D^2\otimes D^1\) sending the unique top atom to 1 and every
lower atom to its unique value. Its two boundary routes both have
the unique 2-value, so it exists by freeness on the disk atoms.
Pure actions are its restrictions with a vertex partner. This is
a Gray table, since every three-span composite has a terminal
partner. In the suspension all elementary squares are identities:
the only possible nontrivial mixed disk at the marked cut is the
\((2,1)\) naturality, and the other cuts act strictly or have a
terminal partner. The shifted join on a unit fixed variation takes
its prescribed unary value. More explicitly, the low \(P\) laws
are strict or unit specializations, the outer unary and transport
laws have terminal outer partners, and the shifted disks and their
contextual auxiliary equations are evaluated by the very same
strict disk-tensor functor. There is no positive binary subdivision
with two higher short operands. In degrees above the marked
naturality, parallel cells are equal. This verifies \(V\) and
both elementary splits. The naturality with label 1 lands in the
hom to the terminal suspension object and is noninvertible. Thus
even requiring all elementary inner squares everywhere to be
identities is insufficient.

**A criterion for individual positions.** The switch rule concerns a
whole operation. For a particular letter with specified arguments and
whiskers, the following two lists characterize exactly the positive
positions, including degeneracies. Compute the lists once per arity
and candidate argument term \(a\), independently of the letters to be
tested.

Use the generators of the arity, one fresh generator with the reversed
faces of \(a\), and the two cancellation equations for this generator
and \(a\). At stage \(N\) form the finite graph of top paths and
certified defining replacements in contexts with encodings of length
at most \(N\). Include structural equations, including evaluation of
a concatenation as a term. Use the schemas of \(V+S\) and the two
extra equations. Include a conditional replacement only with a finite
derivation of its premises. The length bound includes all formation,
face-matching and premise derivations. Thus paths first typable after
a cancellation are included. One may equivalently generate the graph
by bounded finitary Horn deduction. Use a fixed finite alphabet for
all these encodings.

In each component containing an empty path record **all first factors**
of its nonempty paths in a list \(P_N\), and **all last factors** in
\(T_N\). Keep endpoint types, and allow a factor to be a composite
term by using the corresponding grouping. Record identity terms as
singleton paths as well. Then the answer for the argument position
\(a\) is exactly
\[
                  \bigcup_{N\ge 0} (P_N\cap T_N)
                  \quad\text{restricted to the candidate letters.}
\]
This is a finite-certificate characterization. It gives an enumeration
and makes no assertion of a stopping bound for negative instances.

Indeed, connected paths represent the same arrow in the term model.
Conversely every equality in that model has a finite derivation:
terms modulo provable equality, with partial operations on provably
matching arguments, themselves form the initial model of the
presentation. Thus a recorded first factor \(f:s\to t\) has
\(fu=1_s\), and a recorded last factor has \(vf=1_t\), in chronological
order. If both occur then \(v=v(fu)=(vf)u=u\). Conversely a strict
inverse supplies both paths in identity components at some finite
stage. Every assignment with invertible \(a\) extends over the fresh
generator, and the term model itself is a test algebra of the
admissible theory \(V+S\). This proves both directions, without
restricting assignments to substitutions between pasting diagrams.
The criterion works with the Gray test term in place of \(a\) as well.

## The two strip constructions and Q4

There are two different dimensions involved in the strip terminology.
(K44) and (K51) decorate the *inner square* \(\iota\) on a suspended
pair of chains. Its base is a directed shuffle square. The outer
binary \(W\) on \(C_{2,1}\) has global degree five and Gray top
chain \((A_1+A_2)\otimes B\). We give the evaluations for both.

For the literal tag replacement in (K51), keep its directed long
grid and replace each subset by an element of
\(M=\mathbb Z^{(\{(a,b):a,b>0\})}\). Take zero on identities, add
on both compositions, and put \(e_{a,b}\) on a generating rectangle
on paths of lengths \(a,b>0\). This **is** a \(V\)-algebra. Strict
interchange of labels uses commutativity of addition. In the marked
suspension the short homs are chains, so at their cut only the square
has two proper operands. A higher disk on those spans restricts to
that same square on the surviving faces and takes the specified
identities. All cuts in an individual hom are strict. With a
terminal partner only the pure action survives. This verifies the
boundary and unit declarations even for nonzero decorations of
identity-base squares in the long hom. The outer unaries, the
outer factorization, balancing and the restricted splits have the
unit or strict instances checked for the cyclic table above. Parallel
cells above degree four are equal. Thus every remaining guarded law
holds, without an equation \(z+z=z\).

A proper square in this particular model still lacks an inverse:
forgetting the label would send an inverse to a reverse square in
the directed grid. To obtain the intended localization test, collapse
the base long hom through its arrows to a point and take \(M\) as
its monoid of 2-endomorphisms. The same check applies, and now the
inverse is negation. With short homs \([2],[1]\) the direct and
tiled inner squares have values \(e_{2,1}\) and \(2e_{1,1}\).
Every right split holds, and only identities exist one degree up.
The mirror has the analogous property for the other switch.

For the **outer** \(W\)-strip in (M3), the following table detects
the single tile even when both elementary splits hold. Keep the
two short homs of \(C_{2,1}\), namely \(\Sigma[2]\) and
\(\Sigma[1]\). In the long hom use the same underlying values as
in the four-crossing model through degree four. The pure actions
now send a short global 3-cell to its number of advances.
They send short arrows in hom degree one to the unique long
arrow. The actions respect composition because the advances form
chains. Use the following operations and labels.

| Operation | Value in the long hom |
|---|---|
| Outer \(\chi\) | 3-value zero |
| Inner square on long 3-values \(x,y\) | 4-label \(xy\) |
| Outer \(r,t\) | 4-label zero |
| Outer \(h(A,B)\) on advances of lengths \(a,b\) | 4-label \(-ab\) |
| Outer \(W(A,B)\) | 5-label \([a=2][b=1]\) |

A 5-cell exists between any two parallel long 4-cells and carries
an integer label. Fixed whiskers preserve that label, compositions
add, and the identity has label zero. Above degree five take the
product of two rules: in the underlying table forgetting the 5-label
use unique fillers on parallel boundaries, and in the label coordinate
use only iterated identities. In particular a 6-cell between parallel
5-cells exists exactly when their labels agree. Formally the long
structure is the product of the unique-filler extension of its
4-truncation with the strict table having a single cell below degree
five, integers in degree five, and only identities above. This
specifies both composition and all matching tests.

We check the operations in this table. Through degree four the two
schedules of an outer naturality have equal 3-value, the number of
advances of the moving input. Both sides of the join have 3-value
\(a+b\). The correcting square has label \(ba\), so the factorization
reads \(-ab+ba=0\). Each varying-whisker correction in (K30) has
a literal outer crossing as one operand, with 3-value zero. The
outer subdivisions and triple equation then have label zero, and
the inner splits hold by bilinearity. For the exterior transport of
an inner square from a short span, two positive short advances cannot
be spatially adjacent in that hom: both traverse its sole object
interval. Every such transported square therefore has a zero factor.
Inside the long span the balancing of the inner square just
transports the same two integers. These exhaust the low laws of
the support-free \(P\).

In the coordinate forgetting 5-labels every declared higher operation
exists uniquely on its prescribed parallel faces. For the label
coordinate use strict values inside all homs. On the proper short
pair all lower labels are zero. On **one pair of disks** with reduced
short degrees at most two the only possible atom of hom degree four
is its single \((2,2)\) atom. Assigning either integer to that
atom respects its faces and hence gives a functor on that disk
tensor by its free atomic presentation. Restrictions to proper
faces have no top label. For a higher identity input pull back the
same disk evaluation by its degeneracy: a unit moving variation
gives the identity on the surviving face, and a unit fixed variation
retains the specified lower operation on both faces. In particular
\(K=W\) at a unit left variation, and \(J\) reduces to \(K\) or
to the contextual \(W\) followed by the unit right join variation.
This is the disk and unit check for the two strip evaluations in
[round 7, “The strip and its two evaluations”](../answered/lax-interchange-every-dimension-r7-2026-11-20.md#the-strip-and-its-two-evaluations).
It works with addition since only the chosen single top occurrence
is labelled. A long span has only terminal adjacent outer spans.

It remains to check the degree-five *equations* where a label
could distinguish parallel sides. An outer unary in that degree
would require a proper short input of hom degree three, so both
unary subdivision and transport laws have zero top label.
Elementary inner splits have zero 5-label. The shifted join is
evaluated strictly in the label coordinate. For two proper advancing
short operands the inner test on their transported 3-faces has
4-label \(ab\ne0\), including when a higher identity restricts to
these faces. Thus the mixed-paste guard cannot impose a subdivision
of a labelled tile. If either advance is absent, all the tested
\(W\)-labels vanish. The special factorization for \(K\) at a unit
left variation has the same contextual \(W\) on both sides; the two
join variations have zero label. For \(J\) the mixed-paste test
uses the two 3-source histories, as above. A three-positive-span
test has no instance, and exterior or intervening terminal spans
preserve the value. These are the degree-five guard families of
[round 8, Response 1](../answered/lax-interchange-every-dimension-r8-2026-11-20.md#researcher-response-1).
In greater degree parallel cells are unique. Thus the constructed
table satisfies \(V\) and both switches.

Every killed letter evaluates invertibly in this table. On a short
span evaluation already uses the strict structure. On the long span
all 3- and 4-values have additive inverses, and the inverse of a
5-cell reverses its faces and negates its label. Higher fillers
reverse uniquely with the same identity-label condition. Hence the
assignment extends over either localization. The direct \(W\) of
(M3) has label one. Any paste of its two unit-width tiles has label
zero, also with lower fixed whiskers. No 6-cell connects them.
This answers the specific strip question using the parallel pair
as stated in (M3). The four-crossing proof of the uniform verdict
uses only the unguarded outer square subdivisions, so it is
independent of any strip lifting or choice of tiling.

## Validation

Run `python3 -B scripts/e6/interchange_invertibility.py` from the
repository root. The check constructs the two histories in the native
(K15) grid quotient, evaluates the signed labels and inverse laws,
and compares both strip calculations with their typed faces. For
the outer-letter substitution it checks the differential on every
face of the moving globe before and after contraction. On the
\((2,1)\) disk it checks the positive naturality label under every
defined composition. On \(D^1\otimes D^1\), \(D^2\otimes D^1\),
\(D^2\otimes D^2\) and \(D^3\otimes D^1\) it exhausts all 48
distinct ordered parallel pairs with equal product image and finds
a zigzag of mixed cells for each. The arbitrary-dimension conclusion
uses the fixed-boundary factorization proof above.

Four existing checks also passed: `interchange_loop_weights.py`
for the four-crossing loop and its first 100 powers,
`interchange_universality_check.py` for the cyclic tables and
one-sided splits, `marked_inner_crossing.py` for the directed
base and its 19,456 interchange rectangles, and
`interchange_weak_initiality.py` for the two signed strip
subdivisions. All four are in `scripts/e6/`.
