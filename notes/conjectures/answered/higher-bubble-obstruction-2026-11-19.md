# Higher bubbles obstruct homotopicality

**Theorem.** Let Γ be a finite polygraph and let F(Γ) be its free strict ω-category. Suppose that for some n ≥ 2, some 0 ≤ k ≤ n − 2, and some k-cell c, there is a nonidentity n-cell

$$
q:1^{n-1-k}_c \longrightarrow 1^{n-1-k}_c.
$$

Then Γ is not a homotopy polygraph. This proves necessity in every dimension, including composite c and composite q. [Outbox Question 1](../outbox/homotopy-polygraphs-r2.md#4-questions)

Write $|C|$ for groupoidification and put $C=F(Γ_{≤n})$. Free attachment of generators above degree n leaves the n-cells unchanged, so q belongs to C. We prove the stronger conclusion that $|C|$ has nonzero cohomology in arbitrarily high degrees over a finite field. Working with this skeleton matters because a higher generator could have faces involving different numbers of n-generators.

## Two strict functors

For an abelian monoid M, write BⁱM for the strict i-category with one cell in each degree below i and with i-cells M under addition for every composition. Let d = n − 2 and let b be the d-cell obtained from c by taking d − k identities. Thus q is an endomorphism of the identity on b.

There are strict functors

$$
\Sigma^d B^2\mathbb N \xrightarrow{i} C \xrightarrow{r} B^n\mathbb Z .
$$

Here Σ is categorical suspension, with two objects and the indicated category as the hom from the first to the second. To construct i, use the d iterated homs of C specified by the globular faces of b. In the resulting strict 2-category, b is an object and q is a 2-cell on its identity arrow. Horizontal and vertical composition on these endomorphisms have the same unit and satisfy interchange. Hence they coincide and commute by Eckmann–Hilton. Sending j to the j-fold composite of q defines a strict functor from B²ℕ to this hom. The defining property of suspension gives i, also when some of the specified faces coincide. For d = 0 this is the functor selecting the ordinary bubble at an object.

Define r by sending every generator of degree below n to the unique cell of its degree and every n-generator to 1. Each n-generator has the required boundary and freeness extends the assignment. On any n-cell, r counts occurrences of n-generators in any strict expression. An expression containing none is an identity, by induction using the strict laws for composing identities. Consequently m = r(q) is a positive integer.

## The bottom cohomology class

For these strict categories, groupoidification can be computed by geometric realization of the multisimplicial nerve, which gives the same space as the Street nerve. [Ara and Maltsiniotis, *Comparison of the n-categorical nerves*](https://arxiv.org/abs/2010.00266)

There are natural identifications

$$
|B^2\mathbb N|\simeq K(\mathbb Z,2)\simeq\mathbb{CP}^{\infty},
\qquad |B^n\mathbb Z|\simeq K(\mathbb Z,n).
$$

In the first identification the inclusion ℕ → ℤ induces an equivalence. The top cell labelled 1 in Bⁱℤ represents 1 in πᵢ. One can see the normalization by iterating the based loop identification with Bⁱ⁻¹ℤ down to the usual loop in Bℤ. [Ara, Theorems 4.4, 4.7 and 4.9 and Example 4.10](https://www.normalesup.org/~ara/files/thmB.pdf)

Groupoidification takes categorical suspension to unreduced suspension of spaces. Indeed, a map from ΣD to a space with fixed endpoint images x, y is a map from D to the path space from x to y. This is also the mapping property of the topological suspension of |D|. Strict suspension agrees with categorical suspension on strict categories. For the connected based spaces here one can collapse the suspended basepoint interval to use reduced suspension. [Campion, Corollary 2.26 and Observation 2.27](https://arxiv.org/html/2311.00200v1#S2.SS1)

Let x generate H²(ℂP∞; ℤ), let u be the fundamental cohomology class of K(ℤ,n), and write σ for the reduced cohomology suspension. With consistent orientations,

$$
|i|^* |r|^* u = m\,\sigma^d x.
$$

To check the coefficient, restrict to the bottom sphere Sⁿ = ΣᵈℂP¹. Before suspension its fundamental 2-sphere is represented by the cell 1 of B²ℕ with identity boundary. After d suspensions, r i sends its top globe to the cell m of Bⁿℤ and every lower face to an identity. The resulting sphere represents m in πₙK(ℤ,n). Restriction to the bottom sphere is an isomorphism in degree n, giving the formula.

## Detection above dimension n

Fix any odd prime p that does not divide m. From now on take coefficients in ℱₚ and write x and u for the reductions. Put $a_0=|r|^*u$ in $H^n(|C|;\mathbb F_p)$ and set $a_{j+1}=P^{p^j}a_j$, using the Steenrod reduced powers. Then for every j ≥ 0,

$$
|i|^*a_j = (m\bmod p)\,\sigma^d(x^{p^j}) \ne 0
\quad\text{in degree }d+2p^j .
$$

Indeed, reduced powers are natural, additive and commute with cohomology suspension. On a class z of degree 2s their top-power formula gives Pˢz = zᵖ. Apply this to z = x^{pʲ} *before* suspending and use $H^*(\mathbb{CP}^{\infty};\mathbb F_p)=\mathbb F_p[x]$. This proves the formula by induction. Already j = 1 detects a class above degree n for either parity of n or m. [Steenrod and Epstein, *Cohomology Operations*, Chapter VI, §1](https://www.jstor.org/stable/j.ctt1b7x52h.9)

Groupoidification preserves the pushouts constructing Free(Γ_{≤n}). The boundary of an i-globe groupoidifies to Sⁱ⁻¹ and the globe to a contractible space, so these pushouts give a CW model with one i-cell per i-generator. Its cohomology vanishes above n. The comparison Free(Γ_{≤n}) → C therefore cannot be an equivalence.

Finally, homotopicality passes to skeleta. The strict skeletal inclusion is discrete Conduché because every factor of a skeletal cell again uses only skeletal generators. Pullback along it preserves the cellular pushouts and pulls the full comparison back to the skeletal one. Thus the failure at Γ_{≤n} implies the failure at Γ. ∎ [Skeletal comparison theorem and proof](fibration-presentations-all-dimensions-2026-11-19.md#1-homotopicality-passes-to-skeleta)

## A composite bubble over a path

Take two composable arrows whose composite is f, a 2-generator α from f to f, and two 3-generators u from 1_f to α and v from α to 1_f. Neither 3-generator is a bubble. Their composite q is one, with m = 2. For n = 3 and p = 3 the first reduced power pulls back to twice the suspension of x³, a nonzero class in degree 7. This checks the obstruction in a case where the base is composite and reduction of the counting class modulo 2 would give zero on the detecting sphere.

## Comparison with the researcher response

The researcher also detects the counting class, using $\Sigma^k K(\mathbb Z,n-k)$ at the original base cell. The proof above takes the $(n-2-k)$-fold identity on that base first, so it only needs $K(\mathbb Z,2)$. Both calculations give the same degrees, since $(n-2)+2p^j=n+2(p^j-1)$. [Researcher response, §1](../outbox/homotopy-polygraphs-r2.md)

The skeleton matters even for a finite 3-polygraph. At one vertex take a 2-bubble $a$ and one 3-generator $a\to 1$. In the weak realization this attaches a 3-disk to $S^2$ by degree one. In the strict realization the innermost hom-category is the poset $(\mathbb N,\geq)$. Strict interchange makes tensor strictly commutative and a map from $m$ to $l$ applies the generator to exactly $m-l$ copies. This poset contracts to zero, and its two monoidal deloopings are contractible by levelwise realization of the bar construction. Both total spaces are contractible. The 2-skeleton still has the bubble $a$, so the comparison of higher categories fails. [Researcher response, §2](../outbox/homotopy-polygraphs-r2.md)

For the converse problem the response gives a sufficient test. In each dimension at least two, choose source or target uniformly for that dimension. If every generator has a generator as its chosen face and a nonidentity opposite face, the polygraph is homotopical. Dimensionwise duality reduces this to the positive-to-one case. Zawadowski's opetope presentation identifies the generating faces and their attachments. Positive opetopes are acyclic, their face closures are positive opetopes, and Chanavat's pasting theorem applies to the resulting directed complex. The hypothesis on a chosen face is genuinely stronger than positivity since a 2-generator can have paths of length two on both sides. [Researcher response, §3](../outbox/homotopy-polygraphs-r2.md) · [Zawadowski, Proposition 12.2 and Corollary 13.5](https://arxiv.org/pdf/0708.2658) · [Hadzihasanovic, Lemma 9.4.4 and Corollary 9.4.11](https://arxiv.org/html/2404.07273v2#S9.SS4) · [Chanavat, Corollary 3.27](https://arxiv.org/html/2603.22242v2#S3)
