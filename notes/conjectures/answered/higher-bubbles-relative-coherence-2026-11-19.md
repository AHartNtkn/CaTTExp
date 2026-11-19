# Higher bubbles obstruct relative coherence in CaTT

A nonidentity cell on an iterated identity obstructs relative coherence in every dimension. The obstruction exchanges two copies of the cell. A CaTT model that remembers the individual positions in a list distinguishes this exchange from the identity, including when each copy has even length.

**Theorem.** Let Γ be a finite CaTT context, let π be strict interpretation, and suppose that its free strict ω-category contains an n-cell
\[
q:1_b\longrightarrow 1_b,\qquad q\ne 1_{1_b},\quad n\ge2,
\]
where b is an (n−2)-cell, possibly itself an iterated identity. Then π is not a globular trivial fibration. Hence Γ fails RC_id(∞) by item 7 of the [relative-coherence problem](relative-coherence-all-dimensions-r3-2026-11-19.md).

The literal boundary in the hypothesis matters. We first construct a model in which the suspended Eckmann–Hilton operation on a nonempty list acts nontrivially. We then use the assumed lifting property to obtain the precise weak boundary required by that operation.

## A CaTT model of lists and bijections

Fix n and a set C of colours. Below dimension n take one cell in each dimension. An n-cell is a finite list in C. An (n+1)-cell between lists is a bijection of their position sets preserving colours. Above dimension n+1 take only iterated identities. We will interpret CaTT in these globular sets, naturally in recolourings C → C′. In particular forgetting colours keeps the underlying bijection. This last point lets us use different colours for the two inputs of a term even if their uncoloured values agree.

Here are two facts about a globular pasting context P. They concern the **generic** P, before substitution can identify any variables. Truncate its Batanin tree at height n, writing P′ for the resulting globular shape. The projection of P into the free strict category on P′ identifies n-variables joined by (n+1)-variables and sends all higher variables to identities. Call each n-variable of P′ a slot.

1. For any strict n-cell of P, its list of n-generator occurrences projects injectively to the slots, and the two n-faces of a higher cell use exactly the same slots. For injectivity, write a tree as a string of suspended subtrees. A strict positive-dimensional cell runs over a subinterval of that string and is a tuple of cells, one in each traversed factor. In the iterated hom description this lowers the dimension by one. The factors have disjoint slots. At dimension zero a cell selects a single vertex, which projects to the sole vertex of the height-zero truncation. Identities contribute no top occurrences in positive dimension. This also proves the assertion for subintervals of length zero. Equality of the two projected n-faces follows because the projected higher cell is an identity.
2. Given a labelling of P in the displayed globular set, one can give **distinct auxiliary colours** to all positions at one chosen n-variable per slot and propagate them to all n-variables of that slot. Each generating bijection then preserves auxiliary colours. To see this, use the same string-of-suspensions decomposition while n is positive. Its factors meet only at vertices and impose independent conditions on the positions. At n = 0 the vertices to be labelled form a string. Between two consecutive vertices each arrow label is a bijection. These bijections agree: the arrows are the vertices of the intervening subtree, whose 1-skeleton is connected, and each edge of that subtree is labelled by a 2-cell forcing equality of the parallel bijections. Thus one transports along an ordinary string of bijections, backwards using inverses when necessary. A one-vertex string entails no transport. Using disjoint sets of auxiliary colours for different slots proves the claim. Pairing each auxiliary colour with the original colour gives a labelling which recolours to the original one.

We define the interpretation by recursion on the CaTT coherence heads. Variables are projections. A head applied to a substitution acts on its evaluated arguments, so the ordinary substitution equation holds by construction. Strict interpretation in the generic globular arity tells us which strict cell the head denotes. These are the usual CaTT syntax and strict soundness used in the problem. [Finster–Mimram](https://arxiv.org/abs/1706.02866)

- Below dimension n the value is forced. For a head of dimension n, order the n-generator occurrences of its generic strict cell and concatenate the corresponding input lists in that order. The empty collection gives the empty list. For the binary vertical composite use first-input-then-second-input order. All choices are made on the syntax of the head, independently of the labels. In any term, substitution consequently concatenates one input block per occurrence in its strict expression: occurrence counts add under strict composition and are zero on identities.
- For an (n+1)-head evaluate its two boundary terms on the labelling with auxiliary colours from fact 2. By fact 1 and the concatenation rule, each output list contains exactly once each position from the common occupied slots. Match equal auxiliary colours. This is a bijection between the original lists and preserves their original colours. Renaming the auxiliary colours or changing the chosen representative of a slot leaves every match the same, since propagation along bijections identifies the same pairs of positions. The result commutes with every recolouring, including passage to one colour.
- For an (n+2)-head the two parallel (n+1)-terms in its type evaluate to bijections with the same endpoints. Evaluate them first on the labelling with auxiliary colours. Both preserve colours, and the common source and target have no repeated auxiliary colours by fact 1. There is at most one such bijection. Forgetting the auxiliary colours therefore gives equal boundary bijections in the original labelling, so the identity on that bijection has the required type. In still higher dimensions parallel identities coincide. This supplies every head, including heads applied to substitutions that repeat an argument.

In particular the interpretation of the identity on a list is the identity bijection: in its generic disc both boundary lists are the same ordered list of distinct auxiliary colours. This constructs a set-valued CaTT model for every palette.

As a finite check on the two tree arguments, quotient the (n+1)-arrows of a shape by the parallel pairs identified by its (n+2)-generators. Each connected component on n-variables must be a directed path. Independently close the atomic Steiner tableaux under composition, retaining generator multiplicities, and check injectivity into those components for every top row. The checker covers 60,671 strict cells in all 626 trees with at most seven edges. The dimension-independent arguments are facts 1 and 2 above. [Reproduce the check](../../../tools/relative_coherence_slots.py)

## The suspended Eckmann–Hilton operation

Benjamin and Markakis construct a term on two n-cells a, b with literal source and target the same identity on an (n−2)-cell. Its type is
\[
\mathrm{eh}_{n-2}(a,b): a*_{n-1}b\longrightarrow b*_{n-1}a.
\]
The generic term and its suspensions are given in [Benjamin–Markakis, §§6.1 and 6.3](https://arxiv.org/pdf/2402.01611#page=41).

Give a and b lists of lengths r and s with r+s pairwise distinct colours. Their lower-dimensional boundaries have the unique values required. The source list consists of the first block followed by the second and the target consists of the second followed by the first. The only colour-preserving bijection is the block exchange. Recolour to a singleton. By naturality the same operation on lengths r and s has exactly that underlying permutation. In particular on two copies of length m > 0 the first position moves to position m+1. This detects even m as well as odd m.

## Applying the obstruction to a composite strict cell

Work first in the n-skeleton Λ of Γ. If π for Γ is a trivial fibration then RC_id holds in every dimension in Λ by heredity (item 18 of the problem). Hence π for Λ is also a trivial fibration by item 7. The n-cell q and its boundary already belong to this skeleton.

Lift b to a weak term d by globular boundary lifting, lifting its faces first. Form the weak identity i on d. Since π(i) = 1_b, another boundary lift gives a term a **of literal type** i → i with π(a) = q. This use of the trivial-fibration hypothesis avoids any assumption that a particular expression for q lifts with the desired endpoints.

Interpret Λ in the one-colour model, sending each n-generator to a list of length one. All lower generators have forced values, so these assignments respect their types. The length of any n-term is the number of n-generator occurrences in its strict image. This holds on variables and follows on heads from concatenation and substitution. A strict n-cell expressed without n-generators is an identity, by induction on strict composition. Thus a has length m > 0, also when q is composite.

Set p = a *_{n−1} a. The weak (n+1)-terms eh_{n−2}(a,a) and 1_p are parallel and have the same strict image, because the strict category on Λ has only identities above n. A globular trivial fibration must lift the identity on that common image between these specified terms. In the list model the first term exchanges two length-m blocks and the second fixes all 2m positions. There is no (n+2)-cell between different bijections. This contradicts the required lift and proves the theorem.

**Scope.** This settles the higher-endo-cell obstruction in Question 1 for every dimension, base cell and positive generator count. RC_id(∞) and homotopicality therefore both imply bubble-freeness. The question whether those two properties coincide on bubble-free contexts remains open.
