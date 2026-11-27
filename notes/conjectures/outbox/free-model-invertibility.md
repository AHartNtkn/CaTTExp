# Invertibility in free higher categories with directed interchange, after inverting some generators of a pasting diagram

*A self-contained problem. The theories below are defined in full in the repository files `notes/conjectures/answered/lax-interchange-every-dimension-r5-2026-11-20.md` (Responses 1–34), `-r8-` (Response 1) and `-r10-` (Responses 1–3); §1 fixes the notation and lists what is proved.*

**What we are asking for.** Let Γ be a finite pasting diagram and M a set of its generators. Form the free algebra on Γ in which the generators of M are made invertible. Which cells of the original free algebra become invertible? A proof assistant decides "this coherence is invertible" by asking exactly this question about one cell over one pasting diagram, with M the set of arguments already known to be invertible. Free algebras on pasting diagrams have no non-identity invertible cells, and the answer is known for single Gray cells; it is not known for an arbitrary cell. The main question asks whether the answer is **decidable**, uniformly in the diagram, the marked set and the cell, for every admissible theory between the least one and the strict Gray quotient, together with a characterization. Without the restriction to pasting diagrams the answer is negative (known result (U) below), so the question is exactly where pasting diagrams sit.

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
- **(M5) Positivity.** Every non-identity cell of F_{V+S}(Γ) has positive conserved weight, so F_{V+S}(Γ) has no non-identity invertible cell. (r5 (K50).)
- **(M6) Decidability.** For every S, Γ and degree, the vertices (cells of F_{V+S}(Γ) of a given dimension with fixed lower faces and weight) form a finite computable set, the generating letters between them are finite and listable, and equality of cells is decidable. (r10 Response 3.)
- **(G1) Gray cells.** For cells x₁, …, xₙ in consecutive homs of hom-dimensions d₁, …, dₙ, the *Gray cell* G(x₁, …, xₙ) is the image under substitution of the top cell of F_{V+S}(ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}) over the top atom of 𝔉, lifted along a planar binary bracketing tree of the factors (each node labelled by the sum of the hom-dimensions below it). For a principal disk tree, G is invertible in every algebra of V + S whenever xᵢ is invertible **iff** no node on the path from leaf i to the root has two children of dimension ≥ 2. The answer is the same in all four settings, and the same when every inner letter is also invertible. In particular the binary cases that propagate are exactly (1, p) and (p, 1), and (2, 2) does not.
- **(G2) Other letters.** An outer cylinder (one positive factor against an edge) with invertible moving input is invertible. An inner interchanger with an invertible left (right) input is invertible exactly when the left split (R) holds. The join h(A, B) is invertible from A exactly when the inner interchanger ῑ₋ of the factorization r̄₁ = h(A, B) · ῑ₋ is, and never from B alone. The letters K and J do not propagate from any positive position; W on composite operands does not.
- **(U) Undecidability off pasting diagrams.** (i) For one fixed finite *matching context* containing group relators (not a pasting diagram) and a computable family of single outer letters ℓ_w = W(ewZ, B), "ℓ_w is invertible whenever its right operand is" holds in every algebra iff w = 1 in a fixed finitely presented group with unsolvable word problem. (ii) For finite marked computads (C, M) in general, the set of pairs ((C, M), t) with t invertible in the free Gray ω-category on C with M inverted is not recursively enumerable, already for one fixed computad with a varying input; the construction simulates a Turing machine with loops in C.
- **(P) The strict ω-categorical level.** In the free strict ω-category ν(λΓ) on a pasting diagram Γ of dimension n, the total cell becomes invertible after inverting M iff every n-dimensional generator is in M (map to the strict ω-category with trivial cells below n and (ℕ, +) in dimension n, sending one unmarked top generator to 1 and every other generator to an identity).

## 2. Definitions

Fix an admissible theory E with V ⊆ E (in the sense of (M1)), a finite pasting diagram Γ, and a set M of positive-dimensional generators of Γ. Optionally fix a set O of objects of Γ.

- **The localization.** F_E(Γ)[M⁻¹] is the algebra presented by F_E(Γ) together with, for each m ∈ M, a new cell m⁻ with the boundary of m reversed and the equations m ∗ m⁻ = 1 and m⁻ ∗ m = 1. Write q : F_E(Γ) → F_E(Γ)[M⁻¹]. Equivalently, a cell c of F_E(Γ) has q(c) invertible iff σ(c) is invertible for every algebra 𝒦 of E and every map σ : F_E(Γ) → 𝒦 sending each generator of M to an invertible cell.
- **With objects.** F_E(Γ)[M⁻¹, O] additionally inverts every letter that π₁ sends to an identity and whose hom lands in an object of O (the inner letters into O).
- **Letterwise.** A cell of F_E(Γ) is a ∗_{d−1}-path of letters. Call c *letterwise invertible* if q of each letter of some path representing c is invertible.

## 3. Questions

**Q1 (main: decidability and characterization).** For every admissible E with V ⊆ E, including V + S for each S ⊆ {left split, R} and the Gray quotient 𝔉: is the set of triples (Γ, M, c), with Γ a finite pasting diagram, M a set of its generators and c a cell of F_E(Γ) such that q(c) is invertible in F_E(Γ)[M⁻¹], decidable? The same with O. A proof for all E in this range, in every dimension, or a counterexample (a pasting diagram on which invertibility is undecidable or not r.e.), is the main result wanted. If the answer depends on E, the dividing line between theories is wanted.

**Q2 (main, the expected route).** Is invertibility letterwise on pasting diagrams: is q(c) invertible iff c is letterwise invertible? And is invertibility of a single letter, applied to generators of Γ and whiskered, decided by a finite criterion on its tag, its operand positions, M, O and S that extends (G1) and (G2) to every native letter of V? If both hold, Q1 follows; please say whether it does. If letterwise invertibility fails, give a cell whose letters are not all invertible but which becomes invertible, and say what replaces the letterwise test.

**Q3 (fallback).** For Γ of dimension at most 4 (so cells of degree at most 5, where every native letter is known to be forced on its arity), decide Q1 and Q2.

## 4. What counts as a solution

A complete answer to Q1 for all E between V and 𝔉, positive or negative, in every dimension; or a complete answer to Q2; or an answer to Q3.

## 5. Literature (searched 2026-11-25)

- Ara–Maltsiniotis, arXiv 1607.00668 (lax Gray tensor); Steiner, *Omega-categories and chain complexes*, HHA 2004; Campion, arXiv 2311.00205.
- Benjamin–Markakis, *Invertible cells in ω-categories*, arXiv 2406.12127 (coherences are invertible; composites of invertible cells are invertible), and Benjamin–Champin–Markakis (inverses in CaTT).
- Fujii–Hoshino–Maehara, *Weakly invertible cells in a weak ω-category*, arXiv 2303.14907 (invertibility is closed under composition and coinductively characterized; no decision procedure).
- Forest–Mimram, arXiv 2109.05369 and 2310.03503 (Gray categories as 3-sesquicategories with invertible interchangers).
- Bourke–Lobbia, arXiv 2610.31448 (sharp coherence for lax interchange).

A search for localizations of free higher categories on pasting diagrams and decidability of invertibility found nothing further. None of these treats localizations of free algebras with directed interchange at inner cuts.

# Researcher Response 1

**Q1 is false for a fixed recursively enumerable admissible theory, on a fixed two-dimensional pasting diagram with one marked generator. Q2's letterwise equivalence also fails there.** Only the queried cell varies, and it always has degree five. Thus the dimension restriction in Q3 still admits both counterexamples.

More precisely, let \(P\) be any subset of \(\{3,4,5,\ldots\}\). We construct a theory \(E_P\), a marked diagram \((\Gamma,M)\), and a computable family of single contextual letters \(c_p\), indexed by the integers \(p\ge3\), such that
\[
               q(c_p)\text{ is invertible in }F_{E_P}(\Gamma)[M^{-1}]
                  \quad\Longleftrightarrow\quad p\in P.
\]
All the \(E_P\) have exactly the free algebras of \(V\) on unmarked pasting diagrams. The distinction arises on assignments of a strict inverse to the marked generator. We use the finitary partial Horn laws on the given signature allowed in the [definition of the minimum theory](../answered/lax-interchange-every-dimension-r8-2026-11-20.md#the-minimum-on-pasting-diagrams).

### Two loops and their crossing

Take \(\Gamma=\Sigma[2]\vee\Sigma[4]\). Write \(a_1,a_2\) and \(b_1,\ldots,b_4\) for the generating 2-cells of the respective short homs. Mark just \(a_1\). Subdivide the crossing of the two full strings into two chronological 3-cells, first crossing both \(a\)'s with \(b_3,b_4\), then with \(b_1,b_2\), with the stationary flanks in place. Each block has two expansions using the left and right subdivisions. They have the same first and last events and exchange their two middle events. The inner square on those middle events, padded by the first and last, is consequently a 4-endomorphism of the block. Denote the early and late 4-loops by \(X,Y\). They live on **consecutive** 3-cells. If \(a_1\) is an identity, one middle event in each block is an identity, so \(X,Y\) are identities by the square unit law. These are the two doubled blocks of the [degree-five grid presentation](../answered/directed-interchange-all-degree-presentation-2026-11-22.md#5-all-two-chain-grids-in-global-degree-five).

Use \(X^j\) for a chronological power of the loop, and put \(c_j=\delta(X^j,Y)\), the bare temporal square at cut two. Write its faces as \(YX^j\) and \(X^jY\), suppressing the fixed insertions of the other interval. Also use the following two-letter path \(d\):
\[
 YXXX \xrightarrow{\ c_1\text{ with suffix }X^2\ } XYXX
       \xrightarrow{\ c_2\text{ with prefix }X\ } XXXY .
\]
The three copies of \(X\) act on the same early interval. The prefixes and suffixes in this display are 4-cells. In particular the second move is a single square on a composite operand.

### The extension and its unmarked free algebras

For a term \(z\) on this grid let \(L(z)\) be the law which makes \(z\) an identity whenever \(a_1\) has a specified two-sided inverse. Quantify the grid variables and a variable \(a'\) with reverse boundary. Take both cancellation equations for \(a_1,a'\) as premises. In globular sorts the conclusion is \(z=1_{s z}\). Equivalently, first equate \(s z,t z\) under the premises, then give the parallel identity equation. This law uses only existing operations. Define
\[
                 E_P= V + L(d) + \{L(c_p)\mid p\in P\}.
\]

Consider *any* assignment of the premises in *any* \(F_V(\Theta)\) for a finite pasting diagram \(\Theta\). By (M5) the image of \(a_1\) is an identity. Thus both loops specialize to identities and every displayed conclusion holds. Each \(F_V(\Theta)\) is already an \(E_P\)-algebra, and the universal extension of any generator assignment into an \(E_P\)-algebra is the same homomorphism as for \(V\). This proves equality of the free algebras, including their substitution maps. Moreover the conclusions hold in every Gray algebra because \(\delta\) is an inner square. They hold in every strict algebra as well. Both quotient presentations of requirement 4 therefore retain their universal properties. This proves admissibility, preserves the values of both switch bits of \(V\), and places \(E_P\) between \(V\) and the Gray quotient. In the localization the inverse in the premise is available at the generating assignment. Hence \(q(d)\) and each \(q(c_p)\) for \(p\in P\) are identities.

### Algebras separating each omitted index

Fix an integer \(r\ge3\). We construct a \(V\)-algebra \(D_r\) satisfying \(L(d)\) and every \(L(c_p)\) for \(p\ne r\). We will also use \(D_\infty\), obtained by omitting the exceptional \(r\)-case below.

Use outer objects \(0,1,2\), terminal endomorphism homs and empty backward homs. Take the short homs to be the one-object arrow group \((\mathbb Z,+)\) and the ordinal category \([4]\), in that order, with identities in higher degrees. Write \(a\) for a signed arrow in the first and \(b\) for the length of an arrow in the second. The long hom has a unique global 1-cell and 2-cell. Its 3-cells are integers \(x\), and its 4-cells over \(x\) are endomorphisms \((x,u)\) labelled by integers. Chronological 4-composition at \(x\) adds the labels. At lower cuts add the 3-values and the labels separately. Use the following operations through rank four.

- Pure short actions into the long hom have their unique lower values. The outer square on short arrows has 3-value \(ab\).
- The cut-one square on long 3-values \(x,y\) has 4-value \((x+y,xy)\). Units have label zero. Use the prescribed unit cases of the outer naturalities and join.

These operations extend the four-crossing algebra to signed lengths in the first short hom. The outer subdivisions are the two distributive laws for \(ab\), valid also on cancellation of signed lengths. There are no proper short higher variations or three consecutive proper outer spans. The varying-whisker corrections have a unit varying operand and the outer join factorization specializes to its unit cases. The two inner subdivisions are distributivity for \(xy\). Transport from a short hom preserves its identity inner squares, and terminal exterior spans preserve the long values. These checks give the low equations on arbitrary assignments. [Four-crossing algebra](../answered/invertibility-in-directed-interchange-2026-11-21.md#the-four-crossing-loop-survives-both-localizations)

Over each long 4-cell take 5-endomorphisms labelled by the monoid of maps \(\mathbb N\to\mathbb N\), composed in chronological order. A fixed lower pad acts on the underlying cell and keeps the label. Each such action is functorial, and Godement composition performs the two maps in its prescribed order. Write \(T(n)=n+1\) and \(S(n)=\max(n-1,0)\). Chronologically \(TS=1\), while \(ST(0)=1\). Neither map is a unit. [Map labels for sesquicategorical whiskering](../answered/invertibility-in-directed-interchange-r2-2026-11-25.md)

On the cut-two square with long 4-operands \((x,u),(y,v)\), the two schedules have the **same** 4-value \((x+y,u+v)\). Give the square the label
\[
 B_r(u,v)=
 \begin{cases}
 T & v\ne0\text{ and }(u=v\text{ or }u=r v),\\
 S & v\ne0\text{ and }u=2v,\\
 1 & \text{otherwise}.
 \end{cases}
\]
For \(B_\infty\) omit \(u=rv\). Give each other proper mixed 5-head the identity map on its declared boundary. Use the specified values on unit specializations. Above degree five take a unique filler of every parallel pair in the long hom, recursively.

To verify the conditional equations of \(V\), allow arbitrary long cells in every assignment, including cells with negative labels.

1. At cut zero, a pair of nonterminal consecutive spans must be the two short homs. Their highest proper inputs are arrows. Thus the only proper mixed disk there is the outer square. Every higher identity input restricts to the prescribed lower face and identity. On a long input with a terminal partner there is just the pure action or its specified unit specialization. In particular the unguarded degree-five outer unary subdivisions and transports have identity map labels.
2. Inside the long hom the proper cut-one heads of degree five are the two unary naturalities and the shifted join. Naturality compares \(xy+u\) with \(u+xy\) for a varying loop at \(x\), and likewise at \(y\). The join compares the orders of \(u,v,xy\). Their 4-faces agree by commutativity of integer addition, so the assigned identity maps exist. The guarded shifted-join equation compares this join with a padded unary, both with identity map label, even when its correcting square passes the guard. At cut two the only mixed head of this degree is \(\delta\). Its unit cases have \(u=0\) or \(v=0\), giving the identity map. Larger cuts have no proper degree-five head.
3. In the remaining degree-five guard families the positive mixed disks, auxiliary factorizations and bracketings would need a higher short variation or a third proper outer span. Their unit branches give the indicated lower operation on both sides. In particular an outer mixed paste on a pair of short disks has no degree-five atom, and with a terminal partner the atomic lift restricts to the same pure action. The outer whiskering test likewise has only the unit stationary edge or a moving input in a short hom with no proper 4-cell. A cut-two square can occur in the *test* for the shifted join. There is no top equation subdividing this square in \(V\). Thus the checks impose no multiplicativity requirement on \(B_r\). At higher ranks the disk boundary recursion supplies parallel faces, the prescribed unit values have those faces, and uniqueness of the filler gives all parallel equations. Strict inversion of 5-cells is tested by equality in the map monoid. [Relation and guard table](../answered/directed-interchange-all-degree-presentation-2026-11-22.md#2-relations-and-guards)

Consider an arbitrary assignment of the grid in this algebra. If both block loops have nonzero labels, the two grid spans must map to the two short homs in order. Every other choice has a terminal partner, making the middle crossings identities. Write \(\alpha_i\in\mathbb Z\) and \(\beta_j\ge0\) for the short arrow values. Since the four right arrows compose in \([4]\), \(\sum_j\beta_j\le4\). Each loop exchanges two middle events, one on each left arrow and one on each right arrow of its block. Fixed whiskers retain the product of their 3-values. Consequently the labels of \(X,Y\) are respectively
\[
 u=\alpha_1\alpha_2\beta_3\beta_4,\qquad
 v=\alpha_1\alpha_2\beta_1\beta_2.
\]
If \(uv\ne0\), all four \(\beta_j\) are positive, hence all four equal one. In this case \(u=v\ne0\), including for negative signed lengths. If either label vanishes, all squares used in the added laws have identity map label. In the nonzero case the label of \(c_j\) is \(B_r(ju,v)\). The two padded moves of \(d\) therefore have labels \(T,S\), in that order, and compose to the identity. For each \(p\ge3\) with \(p\ne r\) the label of \(c_p\) is the identity. The schedules also agree in the underlying 4-table. This proves the asserted laws for every assignment of their premises.

Finally send each \(a_i\) to \(+1\) in the group and each \(b_j\) to the corresponding unit-length arrow in \([4]\). The mark has inverse \(-1\). Now \(u=v=1\). If \(r\notin P\), the universal property gives a homomorphism from the localization to \(D_r\) sending \(c_r\) to \(T\). The missing preimage of zero rules out a two-sided inverse. This proves the claimed equivalence. The same result holds in the version with \(O\) as input, already for \(O=\varnothing\), or for \(O=\{0\}\), since the initial outer object has only its terminal incoming endomorphism hom.

### Consequences for decision procedures and for letters

Take \(P=\{e+3\mid\text{machine }e\text{ halts on input }e\}\). Its laws can be enumerated by dovetailing the simulations. A decision procedure on the one diagram and mark would decide diagonal halting. Every r.e. set reduces to these queries. Given an input, compute the index \(e\) of a machine that ignores its own input and waits for the given input to appear in the enumeration, then output \(c_{e+3}\). [Open Logic Project, computable enumerability and the halting set](https://builds.openlogicproject.org/content/computability/computability-theory/non-comp-set.pdf)

Strict invertibility for this fixed effectively presented theory is r.e.-complete. For the upper bound, enumerate terms and finite derivations in the localized partial Horn presentation, including proofs of face matches and of conditional premises. Accept \(c:s\to t\) when some \(u,v:t\to s\) have proofs of \(cu=1_s\) and \(vc=1_t\). The term model gives completeness of the enumeration, and \(v=v(cu)=(vc)u=u\) proves soundness. For the object variant one can enumerate the extra inverse generators by enumerating original letters and checking their Gray projection and target object in the common unmarked free tables. Taking \(P=\{e+3\mid\text{machine }e\text{ diverges on input }e\}\) gives a fixed admissible theory for which the invertible members of the displayed family are not r.e. The recursively enumerable example already suffices for undecidability. On the displayed family the exact dividing line is recursiveness of \(P\).

For **letterwise invertibility**, even the single-law extension \(E_{\varnothing}=V+L(d)\) suffices. Use \(D_\infty\) at the same generating assignment. It satisfies the laws for every \(P\). The two contextual letters of \(d\) map to \(T\) and \(S\), so neither is invertible. To address the word *some* in the definition, apply the unmarked free-algebra result above. On this two-row grid the degree-five normal form in \(F_V(\Gamma)\) is the typed chronological list of contextual squares over the normalized lower labels. The only proper heads are the temporal squares, unit specializations reduce to the existing records or identities, and there are no positive top relations. In particular the one-square move on \(X^2\) is a different record from a pair of one-copy moves. Every path representing \(d\) has the same two proper records in the same order. Thus \(d\) has **no** letterwise invertible representative, although \(q(d)=1\). The implication from letterwise invertibility to invertibility always holds by reversing the list of inverses. The replacement in general is the two-sided cancellation criterion for the **whole path** just proved. For effective theories it supplies finite positive certificates.

Even on *generator* operands the visible switch bits cannot give an exact test across all admissible extensions. For example, adjoin to \(V\) the law making the bare cut-one square on two generating 3-cells an identity if its left input has a specified inverse. The positivity and Gray arguments above again preserve the unmarked free algebras and both switch bits. With the left generator marked this square becomes an identity. In \(V\) itself the same marked query fails by the [cyclic separating algebra for the left input](../answered/invertibility-in-directed-interchange-2026-11-21.md#input-positions-and-the-elementary-tests). The general obstruction therefore concerns precisely the permission to vary the theory on inverse-bearing assignments. The individual decision problems for the four specified \(V+S\) and for the Gray endpoint remain separate. The fixed-grid counterexample resolves the all-theories question posed in §§3–4.

**Validation.** Run `python3 -B scripts/e6/check_free_model_invertibility.py`. The checker builds the two native subdivision classes, checks both middle exchanges in the full grid, and evaluates the two pasted moves with their distinct 4-pads. It checks 52,500 indexed queries over all composable right length tuples and left lengths from \(-2\) through \(2\). Map composition uses the exact maps on \(\mathbb N\). The arbitrary-input checks are the product formula for \(u,v\), the length bound in \([4]\), and the guard verification above. [Reduction checker](../../../scripts/e6/check_free_model_invertibility.py)
