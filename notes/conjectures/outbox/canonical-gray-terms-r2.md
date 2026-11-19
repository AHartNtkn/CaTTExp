# Canonical CaTT terms for the cells of Gray tensors of pasting diagrams: beyond suspensions

*A self-contained problem. It assumes familiarity with the type theory CaTT, strict ω-categories and Steiner's directed complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** The most general theorem: a construction for **all** pairs and all finite families of globular pasting diagrams, or a proof that none exists for some pair together with the equations such a counterexample forces. The question is purely syntactic: whether chosen terms can match their boundaries on the nose in a theory with no definitional equalities.

## 1. Setting

**CaTT** (Finster–Mimram, LICS 2017, arXiv 1706.02866). Types are `⋆` or `u →_A v`. Terms are variables or `coh_{P, u →_A v}[σ]`, where P is a context presenting a globular pasting diagram, σ is a substitution into P, and either (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`. The type of `coh_{P, u→_A v}[σ]` is `u[σ] →_{A[σ]} v[σ]`. **Definitional equality is syntactic identity.** A context is well formed when, for each variable `x : u →_A v`, the terms u and v have type A syntactically.

**Gray tensors.** For globular pasting diagrams Θ, Δ, let λΘ, λΔ be their Steiner complexes and ν(λΘ ⊗ λΔ) the strict ω-category of the tensor (Steiner, *Omega-categories and chain complexes*, HHA 2004). Its generators are the pairs y ⊗ x of cells, of dimension dim y + dim x, with boundary given by the Leibniz formula. Its cells are molecules (Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273) and are determined by their sets of generators.

**The family context.** Fam(Θ ⊗ Δ) has one variable v_g per generator g, typed `T(∂⁻g) → T(∂⁺g)`, where T(c) is a CaTT term over the earlier variables denoting the cell c.

## 2. Statement

> **Conjecture CT.** For all finite globular pasting diagrams Θ, Δ there is an assignment T from cells c of ν(λΘ ⊗ λΔ) of dimension ≥ 1 to CaTT terms over Fam(Θ ⊗ Δ) such that
> - (a) T(g) = v_g for every generator g;
> - (b) T(c) is built from the variables by coh terms, and its strict interpretation (v_g ↦ g) is c;
> - (c) `T(c) : T(∂⁻c) → T(∂⁺c)` holds **syntactically** for every cell c. In particular Fam(Θ ⊗ Δ) is well formed.

The same question for iterated tensors λΘ₁ ⊗ ⋯ ⊗ λΘ_k.

## 3. What is known

1. **Low dimensions.** For Θ, Δ of dimension ≤ 1, binary composites can be chosen consistently by hand. CT holds for D² ⊗ D¹.
2. **Layered terms fail for D¹ ⊗ D¹ ⊗ D¹.** "Layered" means T(c) is the vertical composite, along a layering of the molecule c, of whiskered generators. The source hexagon of the top cell has a unique layering whose first two layers are a square whiskered on the right and a square whiskered on the left, meeting at a 3-edge path. The first layer's target contains a subterm denoting the 2-edge path bc, and no subterm of the second layer's source denotes bc (in CaTT every term uses exactly the variables of its strict image). So the two sides bracket the 3-edge path differently and (c) fails. Non-layered terms are not ruled out.
3. **The weak form holds through dimension 4.** With (c′) — T(c) has a type u → v with u, v connected to T(∂⁻c), T(∂⁺c) by invertible coherence cells, inserted into the variables' types — CT holds for generators of dimension ≤ 4.
4. **Single coherence heads do not avoid the problem directly.** Taking T(c) to be one composition coherence coh_{P, u→v}[σ] requires T(∂^±c) to be literally u[σ], v[σ]; this fails when the boundary is a composite of lower cells that are not among σ's arguments.
5. **Semantics is settled.** The (∞,ω) Gray tensor of pasting diagrams is the free (∞,ω)-category on the Steiner tensor (Campion, arXiv 2311.00205, Cor. 3.5; Chanavat, arXiv 2603.22242, Thm 3.29). CT is only about syntax.
6. **Suspension closure (all dimensions).** With I = D¹ and P a finite globular pasting diagram, CT(I ⊗ P) ⇒ CT(I ⊗ ΣP). Proof: the hom (I ⊗ ΣP)(A, D) between the two extreme vertices is strictly isomorphic to I ⊗ P (checked on chains, f_r bijective on bases for r > 0, degree 0 giving the two kinds of A → D paths); every other hom is globular. Whiskerings R_r, L_r over D^r ∨₀ D¹ and D¹ ∨₀ D^r with recursively chosen types satisfy the composition-case support condition. In a globular pasting diagram every positive-dimensional generator has generators as source and target, so the endpoint declarations of Fam(I ⊗ P) have variable boundaries; a context Γ′ with a substitution σ : Γ′ → Σ_{A,D} Fam(I ⊗ P) then declares the mixed variables by σ-substituted suspended types, and T′(c) = (ΣT(c̄))[σ] satisfies (c) by stability of typing under suspension and substitution. Consequences: CT holds for I ⊗ Dⁿ, Dⁿ ⊗ I (via the odd-dimensional opposite) and I ⊗ Σ^r[m], for every n, r, m.
7. **Where wedges fail.** Closure under P, Q ↦ P ∨ Q is not established. A cell of I ⊗ (P ∨ Q) uses generators from both pieces. When three independent n-generators are reordered, the selected (n+1)-cells compare adjacent orders, and a generic (n+2)-coherence in a common arity has as faces **derived** pair-comparison terms, which are not syntactically the selected ones and cannot be substituted for them. In the cylinder-extension formulation, changing a seed gives a transported filler ℓ_u⁻¹ ; F⁰(u) ; r_u with exactly the boundary of the prescribed F¹(u), and what is missing is a term κ_u from it to F¹(u), with higher compatibilities when several changes are composed. D¹ ⊗ D¹ ⊗ D¹ = I ⊗ (I ⊗ I) is the smallest case not covered, since I ⊗ I is not a suspension.

## 4. Questions

**Q1 (main).** Decide CT for **all** pairs Θ, Δ and for all iterated tensors Θ₁ ⊗ ⋯ ⊗ Θ_k, compatibly with associativity (the assignments for (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) agree up to renaming). Item 6 suggests an induction on the globular structure; the missing operations are wedge (item 7) and tensoring with a non-suspension. A positive answer may use any terms (non-layered composites, single coherence heads over chosen pasting diagrams, globally chosen bracketings, simultaneous inductive choices).

**Q2 (wedge closure).** As a step, prove CT(I ⊗ P) ∧ CT(I ⊗ Q) ⇒ CT(I ⊗ (P ∨ Q)), which with item 6 gives CT(I ⊗ P) for every globular P, and then CT(I ⊗ (I ⊗ I)) by a variant for the non-globular second factor. Equivalently, construct the terms κ_u of item 7 with their higher compatibilities, or show they cannot exist.

**Q3 (if CT fails).** If CT fails for some pair (D¹ ⊗ D¹ ⊗ D¹ is the natural candidate), prove that no assignment satisfies (a)–(c) and identify the minimal extra rule that makes the family contexts well formed, for example a typing rule for generators whose boundaries are molecules, or a definitional equation between bracketings. A precise description of the forced equations is the useful answer.

## 5. What counts as a solution

An explicit construction of T for all pairs and iterated tensors; wedge closure with proof; an impossibility proof with the forced equations; or a published reference.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Steiner, HHA 2004; Hadzihasanovic, arXiv 2404.07273 (molecules, layerings, Prop. 8.3.17 on supports).
- Campion, arXiv 2311.00205; Chanavat, arXiv 2603.22242.
- Finster–Mimram, arXiv 1706.02866; Benjamin–Markakis, arXiv 2406.12127 (invertibility of coherences).
- No paper on syntactically matched terms for non-globular molecules in a type theory without definitional equalities was found.

# Researcher Response 2

**Q2 holds, including the three-interval cube.** For finite globular pasting diagrams
$P,Q$, sections on $I⊗P$ and $I⊗Q$ give a section on $I⊗(P∨Q)$.
Consequently every globular cylinder admits a section. The cube
$I⊗(I⊗I)$ also admits one. In both constructions a generator is its
declared variable, every term has the required strict image, and its two
immediate boundaries are literally the chosen terms. Both tensor parenthesizations give the same cube terms under renaming.

### Why the wedge construction works in all dimensions

Write $z$ for the wedge point, $u:z_0→z_1$ for its interval, and
$A=I⊗P, B=I⊗Q$. Consider the hom from $a_0$ to $b_1$, where
$a$ is strictly on the $P$ side and $b$ strictly on the $Q$ side.
Set $L=A(a_0,z_1)$, $R=B(z_0,b_1)$. Embed $U=P(a,z)$ in $L$ by
$p↦p_0;u$, and $V=Q(z,b)$ in $R$ by $q↦u;q_1$, with strict
whiskering understood in higher dimensions.

The two projections obtained by collapsing one side at a time to $z$ identify the crossing hom with the full
sub-ω-category of $L×R$ on vertices $(l,r)$ for which $l∈U$
or $r∈V$. Indeed, the inverse on Steiner tableaux is $l+r-E_u$, with
$E_u$ the tableau of $u$. The degree-zero entries are $a_0,b_1$.
In degree one one subtracts a single $u$ from each row. A path in either
factor crosses the interval exactly once, and uses $u$ precisely when
it is in the indicated embedded hom. This gives exactly the stated
positivity test on both path endpoints. In higher degrees the rows add.
The boundary equations follow by linearity, and either projection of the
formula recovers its input. Conversely each non-seam basis coefficient
is retained by its own projection, and the single interval crossing
determines the seam coefficient. [Steiner, Definitions 2.6 and 2.8](https://arxiv.org/pdf/math/0403237)

Here $U$ is a full sieve and $V$ is a full cosieve. For details of the
sign test, a nonzero positive chain of positive degree in a unital strongly
loop-free basis has a differential of both signs. A negative face of its
least supported basis element cannot cancel, and a positive face of its
greatest cannot cancel. Write a degree-$k$ row as
$0⊗p_k+1⊗q_k+e⊗r_{k-1}$. For a 2-cell ending in $U$ the equation in
the endpoint-1 copy is $dq_2+r_1=-q_1^-$. The sign test gives
$q_2=r_1=q_1^-=0$, so the source also ends by crossing at $u$.
If both endpoint paths are in $U$, the same equation in each higher row
gives $q_k^±=r_{k-1}^±=0$ for $k≥2$. What remains is exactly a cell of
$U$ whiskered by $u$. At endpoint 0 the differential is $dp_k-r_{k-1}$.
Starting in $V$ gives $dp_2-r_1=p_1^+$, and the identical sign test
gives the cosieve and fullness on that side.

Put $X=L×V, Y=U×R, D=U×V$, identifying these with their embedded
images. Define preliminary terms $S_X,S_Y$ on $X,Y$ by
horizontally composing the two given terms, using the endpoint-1 copy of
the right factor on $X$ and the endpoint-0 copy of the left factor on $Y$.
Choose $S_X$ at vertices in $X$, and $S_Y$ at all remaining vertices.
At each $d∈D$ the two terms represent the same directed edge path. They
use exactly its edges and vertices, since a one-dimensional CaTT composite
concatenates the paths of its arguments. The path is acyclic, so the terms
rename to full-support terms on its generic path context. That context
supplies a coherence $g_d:S_Y(d)→S_X(d)$ with strict image the identity.

For a positive-dimensional cell in the crossing hom, choose the following
term according to its endpoints there. Here $*_1$ is composition at
dimension one in the cylinder, allowing a 2-term to whisker a higher term.

| Endpoints in the crossing hom | Chosen term |
|---|---|
| Both in $X$ | $S_X(h)$ |
| Both in $Y∖D$ | $S_Y(h)$ |
| From $Y∖D$ to $d∈D$ | $S_Y(h)*_1g_d$ |
| From $(ip,r)∈Y∖D$ to $(l,jq)∈X∖D$ | $(S_Y(1_p,β)*_1g_d)*_1S_X(α,1_q)$, where $h=(α,β), d=(p,q)$ |

Here $i,j$ are the embeddings above, and the identities are in the
dimension of $h$. The sieve and cosieve exclude all other directions.
In the last row the strict product factors through $d$, first by
$(1_p,β)$ then by $(α,1_q)$. This proves the claimed strict image.
In ambient dimension two the displayed endpoints agree literally by the
type of $g_d$. Above dimension two both faces of $h$ have the same
path endpoints, hence the same $d$. For the horizontal composites and both uses of $*_1$, choose operations
over two globes glued along the composition dimension, specifying their
source and target recursively by the same operations on the faces.
Keep the 2-term fixed when taking a higher face of its whiskering. Each
prescribed face uses the entire corresponding boundary of the glued
arity, so CaTT's composition rule applies. Taking a face of a table entry
now gives precisely the table entry for that face. This proves literal
boundary agreement in every dimension.

The two original contexts glue along the variables of $u$ and its
endpoints. Use one section for all common identity towers. Both sections already agree on the seam generators. An exterior
cell cannot have a positive-dimensional face in the common interval, since
such a cell would have both object endpoints in that interval, where
the only paths are seam paths and the sign test excludes additional
higher rows. Cells with endpoints in one piece stay there, since
projection to the other piece retains all its non-seam coefficients and
must land in the interval. Same-level crossing homs are $U×V$, by
splitting at $z$, so ordinary horizontal composition applies. Reverse
crossings are empty and wedging with a point is the unit case. All
generators lie in the pieces. This completes the wedge proof in
Researcher Response 1. The point, suspension closure (§3 item 6), and
the wedge decomposition of a Batanin tree give the claim for every
globular cylinder. [Benjamin–Markakis, §2](https://arxiv.org/pdf/2402.01611)

### A section on every cell of the three-interval cube

Label a vertex by the subset of coordinates already set to one. A path
from that vertex is a word of distinct available coordinates, in the
order in which they change. Choose the right-associated composite $T(w)$
of its edges, the variable for a singleton and the identity for the
empty word. The six square generators act by $ji→ij$ for $j>i$, at
the initial vertex of the square. Declare each square variable with the
two corresponding path terms as its type boundaries. These orientations
follow from $d(e⊗e)=(1-0)⊗e-e⊗(1-0)$.

Every nonidentity strict 2-cell is a nonempty sequence of adjacent swaps.
Indeed the atoms freely present the strict category with their globular
boundaries. Horizontal composition of two swap sequences can be serialized
by interchange. The only possible change of order is an exchange of
disjoint swaps, which would require four distinct moves in one word.
Equivalently, on a two-coordinate interval there is just one directed
swap, and on the full interval the six permutations form the following
two directed chains with common endpoints.

$$321→231→213→123,\qquad 321→312→132→123.$$

Their full routes use different square generators, so even those two
parallel composites are distinct. This accounts for six bare squares
and twelve nonempty subroutes on three-letter words.
[Steiner, Theorem 6.1](https://arxiv.org/pdf/math/0403237)

For a swap $w→w'$, take the square variable, whiskered by the untouched
prefix or suffix if present, and call the result $s$. Precompose it
vertically with the path coherence $T(w)→∂^-s$ and postcompose with the
path coherence $∂^+s→T(w')$, omitting a correction when its endpoints
already agree syntactically. Both coherences have strict identity image
by the generic path argument above. A bare square therefore retains its
variable. For a longer route take the left-associated vertical composite
of the corrected steps. Each junction now uses the same $T(w)$ on
both sides. This applies the path correction of
§4 of the project’s invertibility notes to the whole strict 2-skeleton. [Path corrections](../../invertibility-markings.md)

Write $H^-,H^+$ for the terms for the two full routes in the order
displayed. The tensor differential gives source squares $0ee,e1e,ee0$
in route order and target squares $ee1,e0e,1ee$. Thus $H^-,H^+$
represent the correct strict faces, and both have the literal type
$T(321)→T(123)$. Declare the top variable at $H^-→H^+$ and select it.

To see that this exhausts the nonidentity 3-cells, consider any strict
composite involving the top atom. Composition at dimension zero adds only
units at the initial or terminal cube vertex. At dimension one a factor
would have to end at $321$ or begin at $123$. Every swap strictly
decreases inversion number, so the only such 2-cells are identities.
At dimension two an identity on the matching hemisphere is a unit, and
two top atoms cannot compose because their hemispheres differ. Induction
on a strict composition expression therefore gives just the top atom.
All strict cells above dimension three are identities. At any dimension
select the CaTT identity on the already chosen lower term for an identity
cell. Its two boundaries are that term literally and its strict image
is the required identity. This proves (a)–(c) for all cells. Flattening
either tensor parenthesization to the same three ordered coordinates
also makes these cube choices agree under renaming.

The generator constructs the 27-variable context, enumerates the cells and
checks the square coefficients of each route. Agda 2.8.0 verified the inferred
types against the selected boundaries for all 30 nonidentity paths, all 18
nonidentity 2-cells and the top cell. As a negative control, Agda rejected
the uncorrected first whisker on $321→231$ at the selected type, although
its two strict path boundaries agree with those of the corrected term.
[Generator](../../../tools/canonical_gray_cube.py) · [Agda certificate](../../../src/CaTTExp/Generated/CanonicalGrayCube.agda)

Q1 for arbitrary pairs and iterated tensors remains open.
