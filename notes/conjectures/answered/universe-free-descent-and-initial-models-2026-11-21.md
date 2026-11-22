# Descent for cocartesian fibrations and initial models of positive signatures in (∞,ω)-categories

## Setting and notation

Let `Cat_ω` denote the (∞,1)-category of (∞,ω)-categories (for definiteness, complete Segal Θ-spaces in the inductive sense, as in Loubaton, *Categorical theory of (∞,ω)-categories*, arXiv:2406.05425). Answers for the coinductive variant or for (∞,∞)-categories in the sense of Gepner–Heine are equally welcome; please say which one you use. `Cat_ω` is cartesian closed and also has the (lax) Gray tensor product `⊗`, closed on both sides.

For an (∞,ω)-category X:
- `Cocart(X)` is the (∞,1)-category of cocartesian fibrations over X (in the sense whose straightening is Loubaton's Thm 4.1.4.2 / Gepner–Heine's Thm 1.8.2, `Cocart(X) ≃ Fun(X, Cat_ω)`) and functors over X preserving cocartesian arrows.
- `Cat_ω/X` is the slice. Base change along `g : Y → X` is `g* : Cat_ω/X → Cat_ω/Y`.
- A colimit `X = colim_{k∈K} D_k` is **van Kampen for a class 𝓕 of maps** if (universality) for every `p : E → X` in 𝓕 the canonical map `colim_k (D_k ×_X E) → E` is an equivalence, and (effectiveness) restriction induces an equivalence from the full subcategory of `Cat_ω/X` on maps in 𝓕 to the limit over K of the corresponding full subcategories of `Cat_ω/D_k`, the limit taken along base change.
- An (∞,ω)-category is a **groupoid** if all its cells are invertible, and **n-truncated** if it is an n-truncated object of the (∞,1)-category `Cat_ω` whose cells above dimension n are invertible (so 0-truncated = discrete set).

Known facts, for orientation:
- Colimits in `Cat_ω` are not van Kampen for all maps: the pushout `[2] ≃ {0<1} ⊔_{1} {1<2}` is not preserved by base change along `{0<2} → [2]` (Ayala–Francis, *Fibrations of ∞-categories*, Higher Structures 4 (2020), Ex. 1.6).
- In the (∞,1) case, cocartesian fibrations descend along cocommas, sequential colimits and localisations, and straightening follows from descent (Sattler–Wärn, arXiv:2603.28688, Thm 5.7, Lemmas 6.1–6.2, Thm 8.1).
- A functor is a cocartesian fibration iff it is exponentiable and locally cocartesian (Gepner–Heine, arXiv:2608.02592, Thm 1.8.11). Loubaton proves that base change along classified left cartesian fibrations preserves colimits (Thm 3.2.3.15).
- Impredicative encodings of inductive types are correct only with a naturality condition (Awodey–Frey–Speight, arXiv:1802.02820); dinatural transformations `X^X → X^X` on Set form a proper class while Barr dinatural ones are exactly the iterates (Paré–Román, JPAA 128 (1998), §2.2 and Prop. 1).

## Questions

**1 (main).** Determine, for `Cat_ω`, the most general descent statement of the following form, and prove it.

(a) For every small diagram `D : K → Cat_ω` with colimit X, every colimit is van Kampen for the class of cocartesian fibrations: `Cocart(X) → lim_k Cocart(D_k)` is an equivalence, and base change along any cocartesian fibration `E → X` preserves all colimits.

(b) For every small diagram indexed by an ∞-groupoid K, the colimit is van Kampen for the class of **all** maps.

(c) For every ∞-groupoid Y in `Cat_ω` and every n ≥ −1, maps `E → Y` whose fibres are n-truncated descend uniquely along the unit `Y → τ_{≤n+1} Y`: base change along it is an equivalence between maps into `τ_{≤n+1} Y` with n-truncated fibres and maps into Y with n-truncated fibres.

(d) The oriented version: replacing `Cat_ω` by the oriented category of (∞,ω)-categories with lax transformations (Gepner–Heine, *Fibrations in oriented category theory*, arXiv:2607.18418), state and prove the analogue of (a) in which the gluing data are lax (oriented) rather than invertible, or show that only the invertible version holds.

Then characterise exactly which pairs (class of maps 𝓕 closed under base change, class of colimit diagrams) are van Kampen in `Cat_ω`. If a full characterisation is out of reach, prove (a)–(c) and give the boundary by counterexamples, in particular: is every colimit van Kampen for the class of exponentiable maps? (Ayala–Francis show exponentiable fibrations are classified by a flagged ∞-category; does that classification imply descent along all colimits, or only along those colimits that also compute colimits of maximal subgroupoids?)

**2.** Call a finite signature Δ over one sort X **strictly positive** if it is a finite list of operations and cells of the following kinds, where `S(X)` ranges over *source expressions* and `T(X)` over *target expressions*:
- source expressions are built from X and fixed (∞,ω)-categories by finite limits (including pullbacks over fixed objects), small colimits, `⊗` and `×` with fixed objects, and cotensors `[A, X]` with A fixed;
- target expressions are built from X and fixed objects by small colimits and by `⊗`, `×` with fixed objects (so they preserve colimits in X, or at least sifted colimits);
- an **operation** is a map `S(X) → T(X)`;
- a **cell** is a k-cell between two composites of operations, required invertible or not;
- a **mark** restricts X to a class closed under limits and filtered colimits and reflective in `Cat_ω`, e.g. "X is n-truncated".

A model is an object X with the operations and cells; model morphisms are maps commuting with the operations up to (coherent) cells, invertible where the signature's cells are, and the (∞,1)-category of models is `Mod(Δ)`.

Prove that `Mod(Δ)` has an initial object for every strictly positive Δ, and that the forgetful functor `Mod(Δ) → Cat_ω` preserves the initial object's universal property at every level (maps from the initial model to any model form a contractible space). Give the maximal syntactic class for which this holds, and an explicit signature just outside it with no initial model. Equivalently, in end notation: show that the strong-dinatural end `∫_{(A, σ) ∈ Mod(Δ)} A` (the limit of the forgetful functor) exists and is the carrier of an initial model.

Important instances, to check the class is right: free (∞,ω)-categories on graphs whose edges are labelled by objects (`ΣB_e → X` under two points); the n-truncation `(X n-truncated, A → X)`; the family `U → Θ₀` over the set of rose trees with fibre over `node(t₁…t_k)` the wedge `ΣU_{t₁} ∨ … ∨ ΣU_{t_k}` (so that the fibre over a tree T is the free (∞,ω)-category on the pasting diagram T), presented as a signature over a fixed base: `(X, p : X → Θ₀, a : Φ_p(X) → X over Θ₀)` with Φ_p built from pullbacks over Θ₀, wedges and suspensions.

**3 (fallback).** If Question 2 fails in the generality stated, give the largest subclass for which it holds, and show that initial models of strictly positive signatures are not derivable from finite limits, finite colimits and the descent statements of Question 1: a model of those (an (∞,1)-category with the corresponding structure) in which some strictly positive signature has no initial model.

## Why it matters

A type theory for (∞,ω)-categories without a universe (no object of all objects) has to state the consequences of a universe as rules. Question 1 would make one descent rule replace effective quotients, disjoint coproducts and the Grothendieck construction; Question 2 would make one initial-model rule replace truncations, free objects on labelled graphs, inductive objects and object-valued recursion along trees.

## What would count as a solution

For Question 1: proofs of (a)–(c), with (d) proved or refuted, and either a characterisation of the van Kampen pairs or counterexamples marking the boundary. For Question 2: a proof for the stated class, or a precise maximal class with a counterexample just outside it. A reference to the literature for any part counts, with the exact statement.

## Researcher Response 1

Cocartesian fibrations descend along every small colimit. All maps descend along space-indexed colimits. Families of $n$-truncated fibres over a space descend uniquely to its $(n+1)$-truncation. The proposed initial-model rule fails even for one nullary operation. With strong homomorphisms and independently chosen sources, the largest uniform class of operation targets consists of right adjoints.

### 1. Cocartesian fibrations and full slices

Write $C$ for the $(\infty,1)$-category of Loubaton's inductive, univalent $(\infty,\omega)$-categories, presented by complete Segal $\Theta$-spaces. Take a larger external universe for classifiers of small objects. This size convention supplies no universe object to the type theory.

**(a)** Let $X=\operatorname{colim}_K D$. Natural straightening identifies the category of cocartesian fibrations and cocartesian-preserving maps with the underlying $(\infty,1)$-category of the cartesian internal hom into the classifier $\boldsymbol\omega$. In the external universe of the classifier, for every test object $Z$,

$$
 \operatorname{Map}(Z,[X,\boldsymbol\omega])
 \simeq \operatorname{Map}(Z\times X,\boldsymbol\omega)
 \simeq \lim_{k\in K^{op}}\operatorname{Map}(Z\times D_k,\boldsymbol\omega).
$$

Here $Z\times-$ is a left adjoint. Yoneda gives the claimed equivalence of internal homs, and passage to the underlying $(\infty,1)$-category preserves limits. Loubaton's term for the classified fibrations, with the variance giving this covariant internal hom, is *left cartesian*. The fully marked-base specialization is the one used here. [Loubaton, Theorem 4.1.4.2 and Corollary 4.1.4.3](https://arxiv.org/pdf/2406.05425#page=203)

For the universality assertion let $p:E\to X$ be such a fibration. For a diagram $B_k\to X$ in the slice set $B=\operatorname{colim}_k B_k$ and pull back $p$ to $B$. This is again classified. Loubaton's reconstruction for this fibration over $B$ gives

$$
 \operatorname{colim}_k (B_k\times_X E)\simeq B\times_X E.
$$

The underlying-object functor from marked categories preserves limits and colimits by its two adjoints. Colimits in a slice are computed on total objects. Thus the equivalence proves preservation of **all slice colimits** by $p^*$. [Loubaton, Construction 3.1.1.16, Theorem 3.2.3.15 and Corollary 3.2.3.16](https://arxiv.org/pdf/2406.05425#page=156)

The full subcategory of $C_{/X}$ on these same fibrations admits additional arrows. Its descent follows as well. Restriction on objects up to equivalence is already essentially surjective by straightening, since an equivalence over a base preserves the cocartesian universal properties. For fibrations $E,F\to X$, write $E_k,F_k$ for their restrictions. Reconstruction of $E$ gives

$$
 \operatorname{Map}_{/X}(E,F)\simeq
 \lim_{k\in K^{op}}\operatorname{Map}_{/X}(E_k,F)\simeq
 \lim_{k\in K^{op}}\operatorname{Map}_{/D_k}(E_k,F_k).
$$

This proves full faithfulness for arbitrary maps over the base.

**(b)** In the presentation $C\subset\mathcal P(\Theta)$, spaces embed as constant presheaves. Loubaton calls a colimit *special* when the inclusion computes it as a presheaf colimit. If $K$ is a space, the constant diagram at the point has special colimit the constant presheaf $K$. For any $D:K\to C$ the map $D\to *$ is cartesian, since every transition is an equivalence. Proposition 2.2.1.27 now implies that $D$ has special colimit. This includes the empty index space. [Loubaton, Proposition 2.2.1.27 and Constructions 2.2.1.40–44](https://arxiv.org/pdf/2406.05425#page=81)

Presheaves of spaces have descent for all maps, objectwise by descent in spaces. Given compatible $E_k\to D_k$, their presheaf colimit is a local object by the preceding argument applied to $E:K\to C$. Presheaf descent says that its pullback to $D_k$ is $E_k$. Conversely, pulling back a map of local objects stays in $C$, since a reflective full subcategory is closed under limits. Presheaf descent reconstructs the total object and all maps over it. This proves both van Kampen clauses in $C$. More generally, every special colimit, of any indexing shape, has both properties for all maps. For such a diagram apply the same proposition directly to the cartesian family $E_\bullet\to D_\bullet$ to see that its presheaf colimit belongs to $C$. [Kerodon, Theorem 7.7.6.1](https://kerodon.net/tag/05VZ)

**(c)** Apply (b) to the diagram at the point indexed by a space $Y$. It gives $C_{/Y}\simeq\operatorname{Fun}(Y,C)$, using inversion to identify $Y^{op}\simeq Y$. Restrict to the full subcategory $B\subset C$ of allowed fibres. Each mapping space of $B$ is $n$-truncated because its target is $n$-truncated as an object of $C$. The proof needs no further property of the extra condition on cells.

For each $m\ge0$ put $N_m B=\operatorname{Fun}([m],B)^\simeq$. Mapping spaces of diagrams are limits of the mapping spaces between their entries, hence $n$-truncated. The loop space of $N_m B$ at a diagram consists of the equivalences in its endomorphism space and is $n$-truncated as well. For $n=-1$ the endomorphism space is contractible and contains the identity. Thus $N_mB$ is $(n+1)$-truncated. Degree $m$ of the complete Segal nerve of $\operatorname{Fun}(Y,B)$ is $\operatorname{Map}(Y,N_mB)$ because $Y$ is a space. The mapping property of $\tau_{\le n+1}Y$ proves the equivalence degreewise, including its assertion about noninvertible maps of families. [Lurie, Higher Topos Theory, §5.5.6](https://www.math.ias.edu/~lurie/papers/HTT.pdf)

The shift by one is optimal. For $n\ge0$ take the based map $*\to K(\mathbb Z/2,n+1)$. Its fibre is $K(\mathbb Z/2,n)$ and the $n$-truncation of the base is a point. Any constant family with this nonempty fibre admits a section. A section of the displayed map would contract the base. For $n=-1$ a singleton over a two-point set has one inhabited and one empty fibre, so it cannot descend to the propositional truncation of the base.

**(d)** Lax gluing at an ordinary colimit fails already for the constant point diagram indexed by the walking arrow. Its ordinary colimit is a point. Ordinary restriction identifies the two copies of a fibre by an equivalence. Lax gluing allows a non-equivalence between different fibres, such as the functor $\varnothing\to *$ (exchange the endpoints for the opposite orientation). Such data cannot belong to the essential image. The corresponding **oriented colimit** of this diagram is the walking arrow itself, and a classified fibration over it does record a functor between its fibres. This is the change of colimit that permits directed gluing.

There is a positive statement for a *specified oriented colimit*. Work in Gepner–Heine's oriented category $\mathcal A=\infty\mathfrak{Cat}$, which allows non-univalent categories, and let $U=\infty\mathcal{C}\mathit{at}$ be the classifier in a larger size. Equip the classified families over $S$ with the transformations between their classifying diagrams given by the Gray mapping object $H(S)=\operatorname{Mor}_{\mathcal A}(S,U)$. Its points are ordinary functors $S\to U$, hence classify cocartesian fibrations by straightening. If $S$ is the $\mathcal E$-oriented colimit of $D$, then

$$
 H(S)\simeq \mathcal E\text{-}\overrightarrow{\lim}\, H(D).
$$

Indeed Definition 3.3.6 gives this equivalence with *every* target in place of $U$. Evaluating at $U$ gives the assertion including all its transformations. The separate oriented straightening theorem identifies the oriented category with cocartesian-preserving morphisms as a fully faithful subcategory of an antioriented functor object. Its objects are those functors factoring through $U\subset\infty\mathfrak{Cat}$, and Corollary 1.8.4 identifies its morphism objects. These specifications distinguish directed structure on classifying diagrams from the invertible overlap identifications at an ordinary colimit. [Gepner–Heine, Theorems 1.8.1–2 and Corollary 1.8.4](https://arxiv.org/html/2608.02592v1#S1.SS8) [Definitions 3.3.5–6](https://arxiv.org/html/2608.02592v1#S3.SS3)

Even changing the colimit does not give preservation of all oriented colimits by ordinary pullback. Take $p:E=[1]\to *$, a cocartesian fibration, and use the slice whose Gray mapping objects are the fibres over the prescribed maps to $E$ (transformations over the identity). The oriented colimit of the constant point over $[1]$ pulls back to $E\times[1]\to E$. The oriented colimit of the pulled-back constant diagram at $\mathrm{id}_E$ is $E\boxtimes[1]\to E$, with projection induced by $[1]\to *$. To see its slice universal property, apply the ambient constant-diagram formula of Theorem 1.8.1 and take the fibre over the constant cone of structure maps to $E$. The weighted limit of mapping objects preserves this pullback. For $E=[1]$ the Gray square has two paths from the initial corner to the final corner joined by a noninvertible interchanger. In the cartesian square those paths are equal and the corresponding hom is terminal. The comparison is therefore not an equivalence.

### The boundary of descent

**An exact test for arbitrary pairs.** Fix a pullback-stable, equivalence-closed class $\mathcal F$ and a colimit $D\to X$. For any cartesian family $E_k\to D_k$ of local $\mathcal F$-maps, form the actual map

$$
 L(E_\bullet)=(\operatorname{colim}_k E_k\longrightarrow X).
$$

There are precisely two tests. First, for each such family this map must lie in $\mathcal F$, and each canonical square with corners $E_k,D_k,\operatorname{colim}E_k,X$ must be a pullback. Second, for every global $E\to X$ in $\mathcal F$, the canonical map $\operatorname{colim}_k(D_k\times_XE)\to E$ must be an equivalence. These tests involve just colimits, pullbacks and membership in the given class.

Indeed, on unrestricted slices $L$ is left adjoint to restriction $R$ by the colimit mapping property and the pullback adjunction at each $k$. The two tests assert that this adjunction restricts and its unit and counit are equivalences, respectively. Conversely, full-slice effectiveness gives an extension of each local family and the stated universality reconstructs that extension by $L$. Hence both tests are necessary. A class of diagrams works exactly when each of its diagrams passes these tests.

For instance, pull the spine pushout $[1]\amalg_{[0]}[1]\simeq[2]$ back along the long edge $\{0<2\}\hookrightarrow[2]$. The two edge terms become singletons and the middle term becomes empty. Their pushout is the discrete two-point set, whereas the total space of the long edge contains an arrow. This fails the second test for the class of all maps.

**Exponentiable maps.** By definition their base-change functors have right adjoints, so universality is automatic. Effectiveness can fail. In dimension one Ayala–Francis represent the *space* of exponentiable fibrations by the flagged category of correspondences. A flagged category is an essentially surjective map from a space into a category. An ordinary category enters with its maximal subgroupoid as the flag. Consequently the classifier takes a colimit to a limit whenever that diagram is also a colimit of flags. In particular it suffices that the canonical map $\operatorname{colim}_k D_k^\simeq\to X^\simeq$ be an equivalence. This gives effectiveness on objects. Universality then gives full faithfulness on arbitrary maps by the mapping-space argument in (a). [Ayala–Francis, Theorems 0.4 and 1.26, Example 1.29 and Remark 1.30](https://arxiv.org/html/1702.02681v4#S1.SS3)

Here is their obstruction, including the change of ambient category needed for this question. Consider the diagram

$$
 *\longleftarrow \{0<2\}\longrightarrow [3]\longleftarrow \{1<3\}\longrightarrow *.
$$

Its colimit in $(\infty,1)$-categories is $*$. Mapping into a test category describes strings of three arrows for which the two length-two composites are equivalences. By two-out-of-six all three arrows are equivalences. The choices of identifying each composite with a constant arrow form contractible spaces. Such strings therefore give the space of objects of the test category. The inclusion of $(\infty,1)$-categories in $C$ preserves colimits because it admits a right adjoint, so the colimit is also $*$ in $C$. Its flags have colimit the two-point set, given by the even and odd vertices. [Loubaton, Construction 2.2.1.44](https://arxiv.org/pdf/2406.05425#page=84)

Let $R$ be the walking retraction with objects $x,y$ and maps $i:y\to x$, $r:x\to y$ satisfying $ri=1_y$. Let $A\subset R$ be full on $x$, whose two endomorphisms are $1_x$ and $ir$. Inside $[3]\times R$ take the full subcategory $E$ with fibre $A$ at the even vertices and $R$ at the odd ones. Its projection $p:E\to[3]$ restricts on the two long edges to the products with $A$ and $R$, respectively. These are the required identifications with the pullbacks of the two point legs. No map to the colimit point can realize these data, since all its vertex fibres would be equivalent and $A,R$ have respectively one and two isomorphism classes of objects.

To check ordinary exponentiability directly, fix a base factorization $a\le b\le c$ and a lift of its composite, represented by $h:u\to v$ in $R$. The category of factorizations through the layer at $b$ has objects $u\xrightarrow{f}w\xrightarrow{g}v$ with $gf=h$. Its morphisms are the commuting maps of middle objects. Allowing all $w\in R$ gives an initial factorization $(1_u,h)$. If the middle layer is $A$, the allowed factorizations form a full subcategory, and any factorization through $y$ is a retract of the one through $x$ with legs $if,gr$. Thus the inclusion induces an equivalence on idempotent completions and hence on groupoidifications, since every space is idempotent complete. In either case the factorization category has contractible classifying space. This also applies when base vertices repeat. The factorization criterion proves $p$ exponentiable among $(\infty,1)$-categories. [Ayala–Francis, Lemma 1.11(6)](https://arxiv.org/html/1702.02681v4#S1.SS2)

**Change of ambient category for the exponentiable example.** Call an ordinary category gaunt if its only isomorphisms are identities. Suppose $p:E\to B$ is a functor of gaunt ordinary categories, with $B=[j]$, which is exponentiable in $\mathrm{Cat}_{(\infty,1)}$. Then $p$ is exponentiable in the complete $C=\mathrm{Cat}_{\omega}$ used here.

Use the presentation $C\simeq\mathrm{CSS}_{\mathcal S}(C)$. Its objects are simplicial objects $Z_\bullet$ of $C$ satisfying the Segal condition, with $Z_0$ a space and with the simplicial space of cores $Z_\bullet^\simeq$ complete. In the complete Θ-space presentation the core of $Z_l$ is its value at the point. Ordinary gaunt $E,B$ have horizontal nerves $NE,NB$ whose levels are discrete spaces, viewed as constant Θ-spaces. [Goldthorpe, Theorem A and Remarks 3.1.10–3.1.14](https://arxiv.org/html/2403.06926v1#S3.SS1)

Given $Z$ over $E$, form $W$ by applying the dependent product along $NE\to NB$ in simplicial spaces at each Θ-shape. At horizontal degree $m$, the fibre over $\sigma:[m]\to B$ is the space of maps of simplicial spaces over $NE$ from $NE\times_{NB}\Delta[m]$ to $Z$, evaluated at each Θ-shape. By the simplex decomposition this fibre is a limit, over simplices of the indicated pullback, of the Θ-spaces of lifts in $Z_l$ of their projections to $E_l$. These are pullbacks of local Θ-spaces. The limit and the disjoint union over $\sigma\in B_m$ are again local (disjoint unions are pointwise by the groupoid-indexed argument above). Thus $W_m\in C$.

To check the horizontal Segal condition, pull the spine decomposition of $[m]$ over $\sigma$ back along $E\to B$. This is a colimit in $\mathrm{Cat}_{(\infty,1)}$ by exponentiability. It is also a colimit of flagged categories. Indeed, the core of the total category over $[m]$ is the disjoint union of the cores at its vertices, exactly the colimit of the flags of the edge and vertex terms. Colimits of such pairs are computed on both entries whenever the resulting flag is essentially surjective, as it is here. Flagged categories present all Segal spaces. Hence the pulled-back spine maps test as equivalences into each Segal space $Z(\theta)$ over $NE$. Adjunction gives the Segal condition for $W(\theta)$. At the point $\theta=*$, the input $Z(*)$ is complete. For horizontal completeness use the walking isomorphism $J\to *$. Every test of it over the ordinal $B$ lands at one vertex $b$. Its pullback along $p$ is $J\times NE_b\to NE_b$, an equivalence after complete Segal localization, since that localization is cartesian. Adjunction against the complete input gives completeness of $W(*)$. [Ayala–Francis, Theorem 0.4 and proof of Lemma 1.11](https://arxiv.org/html/1702.02681v4#S1.SS2)

Finally take the full internal subcategory on the core of the object category. In degree $m$ this replaces $W_m$ by $W_m\times_{W_0^{m+1}}(W_0^\simeq)^{m+1}$. The Segal pullbacks persist, degree zero is now a space, and evaluation at the point is unchanged because the inclusion of the core induces an equivalence on object spaces. This yields an object over $B$ of $\mathrm{CSS}_{\mathcal S}(C)$. Every map to $W$ from such an object factors through this full internal subcategory with contractible choice, by the core adjunction on objects and the displayed pullbacks. The pointwise dependent-product adjunction therefore restricts to the required right adjoint to $p^*$ in $C$.

Both $R$ and the full subcategory $E$ of $[3]\times R$ are gaunt. The result applies to the projection $E\to[3]$. The two point legs are exponentiable by cartesian closure, and their restrictions on the overlaps are products. This is therefore a family of exponentiable maps in $C$ for which the required extension does not exist.

Preservation by the maximal-subgroupoid functor is not necessary for exponentiable descent. For example the pushout $*\leftarrow[1]\to *$ is $*$. Mapping the diagram into any target identifies its limit of mapping spaces with the self-pullback of the inclusion of the equivalence-arrow components into the space of all arrows. A point maps to its identity, and every equivalence arrow is equivalent to such an identity. This self-pullback is the space of objects. The pushout of the three cores, however, is the suspension of a two-point set, hence $S^1$. Every cartesian family on the span restricts on the middle to a product fibration, because it is pulled back from either endpoint. Therefore all its local maps are cocartesian. Part (a) gives effectiveness on objects. Every global map to $*$ is cocartesian, so (a) also gives universality and full faithfulness on arbitrary maps. This pushout has descent even for all maps.

### 2. Initiality requires a condition on operation targets

**The obstruction occurs within the grammar.** Take the one operation $1\to 2$, where $2=1\amalg1$ is fixed and discrete. A model is an arbitrary carrier equipped with a tag. Both tags occur, and a comparison between different tags would require a cell in $2$ between distinct points. Thus the model category is $C\amalg C$, which has no initial object. Even requiring the target to depend on $X$ and preserve all colimits fails. The operation $1\to X\amalg X$ chooses both a point of $X$ and a summand. Again no morphism can change summands.

**The choice of homomorphisms also matters.** Suppose that a map of pointed objects $(I,i)\to (Y,y)$ is a functor $f$ with a possibly noninvertible comparison $f(i)\to y$. Every proposed initial pointed object has two inequivalent maps to $([1],1)$. Take the constant maps at $0$ and at $1$ with their respective comparisons to $1$. Evaluation at $i$ distinguishes them. For the reverse comparison use $([1],0)$. The positive statements below use *strong homomorphisms*. Such a homomorphism preserves each chosen operation and each chosen cell by a coherent equivalence. The cells chosen *in* a model can still be directed.

**Maximal uniform target class.** Fix a presentable category $B$ of allowed carriers, such as $C$, a slice, or the intersection of the specified marks. Permit all the stated source expressions, including arbitrary fixed sources, independently of the targets. For this grammar with strong homomorphisms, precisely the accessible targets $T:B\to C$ that preserve small limits can be admitted uniformly. Equivalently, each such $T$ has a left adjoint $L:C\to B$. For the original target language one takes the intersection with this class. The argument also allows any small family of operations and successive well-typed cell declarations as below. [Kerodon, Theorem 9.5.2.1](https://kerodon.net/tag/06Q4)

For necessity take just one constant source $A$. Its model category is the comma category $(A\downarrow T)$. An initial model $(L A,u_A)$ means exactly that composition with $u_A$ gives natural equivalences

$$
 \operatorname{Map}_B(LA,X)\simeq\operatorname{Map}_C(A,TX).
$$

Existence for every $A$ therefore gives a left adjoint by the universal-arrow characterization. This step uses the contractible *space* of factorizations, including its higher coherences.

For sufficiency the source functors are accessible. In presentable categories a small colimit functor is a left adjoint and a small limit functor is a right adjoint. Tensoring or multiplying by a fixed object is a left adjoint, and a fixed cotensor is a right adjoint. These functors are accessible, and small diagrams of them admit a common accessibility rank. For a reflective mark closed under filtered colimits the composite of reflector and inclusion preserves filtered colimits. It therefore defines an accessible localization. A small intersection of such full subcategories is accessibly embedded and closed under limits, hence presentable. Over the resulting $B$, an operation $S(X)\to T(X)$ is adjoint to an algebra operation $LS(X)\to X$.

Here is the existence proof including cells. Suppose the category $M$ of preceding models is presentable and its carrier functor creates limits (with values in $B$). The category $\mathcal O(S,T)$ obtained by adding one operation is the pullback of $\operatorname{Fun}([1],C)\to C\times C$ along $(S,T):M\to C\times C$, with the carrier functor implicit. Hence it is accessible. Its projection to $M$ creates limits. Indeed for a limit $X=\lim X_i$, the prescribed cone of operations gives the composite

$$
 S(X)\longrightarrow\lim_i S(X_i)\longrightarrow
 \lim_i T(X_i)\simeq T(X).
$$

The mapping-space universal property of $T(X)$ identifies the spaces of compatible squares for test cones, including their homotopies. Thus this operation on $X$ is the limit in $\mathcal O(S,T)$, even when $S$ fails to preserve that limit. Accessibility and completeness imply presentability. This starts with $M=B$ and proves the result inductively for operations. [Kerodon, Corollaries 9.4.9.13 and 9.4.9.15](https://kerodon.net/tag/06LD) [Kerodon, Theorem 9.5.1.1](https://kerodon.net/tag/06PU)

For a cell declaration, specify its two parallel terms and their boundary in the preceding models. Impose the same limit-preservation condition on the actual target of the filler. With $G$ the walking globe and $H=\partial G$, a filler is an operation from the domain tensored with $G$ that restricts to that prescribed boundary on the tensor with $H$. Use the tensor on the side representing the given transformation, or cartesian product for cartesian transformations. Use the walking globe with its top cell inverted for an invertible filler. Form the pullback of the restriction $\mathcal O(S\otimes G,T)\to\mathcal O(S\otimes H,T)$ along the functor of prescribed boundaries from $M$. All functors here are accessible because terms are built by evaluation and composition from the specified small expressions. Both categories of operations create limits over $M$, so restriction and the boundary section preserve those limits. Their pullback is therefore accessible and complete and still creates limits over $M$. This proves existence of an initial model with contractible mapping spaces of strong homomorphisms. The forgetful functor supplies its carrier. Unrestricted maps between carriers can have many components, as the initial pointed object mapping into a pointed two-element set illustrates.

Uniform maximality concerns the formation rule that each admitted target is available with *every* source. Individual signatures outside this rule can have an initial model, for example $0\to T(X)$ for any $T$. There is also an exact small test for **individual signatures** whenever the model category $M$ is accessible. This includes the preceding strong, small cell presentations with arbitrary accessible targets because the pullback construction still proves accessibility without any preservation of limits by the target. Choose an accessibility rank $\kappa$ and a small skeleton of the $\kappa$-compact models. The signature has an initial model exactly when some representative $a$ has contractible $\operatorname{Map}_M(a,b)$ for every representative $b$. Initial objects are $\kappa$-compact because $\kappa$-filtered index categories have contractible groupoid completion. Conversely every model is a $\kappa$-filtered colimit of these $b$, and compactness of $a$ gives the required contractibility for that model. The question specifies no further syntax for side conditions selecting individual source–target pairs or for lax comparisons. Uniform maximality and this semantic test state distinct conclusions.

If fixed objects are given effectively, even recognition of the individual signatures can be undecidable. Allow the constant $BG$ specified by a finite presentation of the group $G$. For the single operation $1\to BG$ the category of strong models is $C\times BG$ because the comparison at the chosen point is exactly a path in $BG$. An initial object exists precisely when $G$ is trivial. Indeed the endomorphism space at any candidate has $G$ as a retract, by using the identity on its carrier. When $G$ is trivial the model category is $C$. Triviality of a finitely presented group is undecidable by the Adian–Rabin theorem. Thus no decidable syntax recognizes all successful instances in this effective family. Nor can a decidable sound subclass be largest among all decidable sound subclasses when individual exceptions may be adjoined, since adding any one missing successful instance preserves decidability. [Adian's papers in English translation](https://arxiv.org/abs/2208.08560)

**The proposed end.** Given an initial model $I$, the inclusion $\{I\}\to M$ is coinitial. Consequently the limit of the carrier functor $U$ is $U(I)$, even for the large diagram interpreted externally. Natural cones are determined by their component at $I$. The converse fails. For the operation $1\to2$ the limit of $U$ on either component of $C\amalg C$ is the initial carrier $0$ by the same argument. The limit on both components is $0\times0\simeq0$. This limit exists although the model category has no initial object. A bare limit of the forgetful functor cannot serve as the proposed equivalent axiom.

### 3. The three constructions and the independence claim

For a graph with discrete vertex set $V$, directed edges $e$, and labels $B_e$, take the pushout

$$
 P=V\amalg_{\coprod_e(1\amalg1)}\coprod_e\Sigma B_e .
$$

The two maps from the common domain select the incident vertices and the suspension endpoints, respectively. A map out of $P$ picks the vertices and the maps from the labelled suspensions with precisely these endpoints. This is an equivalence of mapping spaces by the pushout property. The corresponding strong model category is the coslice $C_{P/}$, with initial object $\mathrm{id}_P$.

For a reflective truncation mark with inclusion $j:B\hookrightarrow C$ and reflector $L$, a model is a map $A\to jX$. The unit $A\to jLA$ is initial by adjunction. For the stated mark the two conditions are accessible localization conditions. Ambient $n$-truncation is tested on the small generating shapes by requiring their mapping spaces into $X$ to be $n$-types. Invertibility above dimension $n$ is localization to $(\infty,n)$-categories (for $n=-1$ the objects are subterminal). Their intersection is again an accessible localization. This identifies the particular reflector required by the mark. [Loubaton, Constructions 2.2.1.40–44](https://arxiv.org/pdf/2406.05425#page=83)

For the set $\Theta_0$ of finite rose trees, (b) identifies $C_{/\Theta_0}$ with $\prod_T C$. Write $W(X_1,\ldots,X_k)$ for the chain of suspensions joined end to start, with $W()=1$, a single vertex. Define $P_{\mathrm{node}(t_1,\ldots,t_k)}=W(P_{t_1},\ldots,P_{t_k})$ by tree height and use these identifications as the structure maps. Fix any other algebra $a_T:W(X_{t_1},\ldots,X_{t_k})\to X_T$. Given a map on smaller heights, extension to $T$ chooses $f_T:P_T\to X_T$ together with a path from $f_T$ to $a_T W(f_{t_1},\ldots,f_{t_k})$. The space of a point with a path to this fixed value is contractible. Products over each height and the inverse limit over heights therefore give a contractible space of algebra homomorphisms. Suspension represents the choice of two endpoints and a map into their hom-category. Gluing the suspensions identifies their shared endpoints by the pushout property. Induction on height then gives exactly the mapping property of the free category on the pasting diagram at each $T$. The resulting family is $\coprod_T P_T\to\Theta_0$.

Finally take the category of spaces for Question 3. It has all small limits and colimits. All its colimits are van Kampen for all maps, every map classifies a space-valued family, and the proof of (c) applies inside spaces. Its directed comparisons between cells of spaces are invertible. Nevertheless $1\to 2$ produces two disjoint copies of the category of spaces as models. This witnesses the requested nonderivability even with all small colimits. It separates descent from the initial-model rule in the question. The positive theorem for accessible sources and right-adjoint targets uses the additional presentability argument above. [Kerodon, Theorem 7.7.6.1](https://kerodon.net/tag/05VZ)

# Verification (2026-11-21, F10 thread)

Checked against `notes/universe-free-principles.md` and the cited sources. Every answer below is accepted unless marked otherwise.

1. **Q1(a) holds for every small colimit, not only finite ones.** Straightening is natural in the base, so `Cocart(X)` is the underlying category of `[X, ω]`, and `[–, ω]` sends colimits to limits. Base change along a classified fibration preserves all slice colimits by Loubaton Thm 3.2.3.15. Full faithfulness also holds for *arbitrary* maps over the base between cocartesian fibrations, by the mapping-space limit. Checked at argument level; the citations are the ones the note already used. No gap.
2. **Q1(b) holds, and more generally every "special" colimit is van Kampen for all maps.** For a space-indexed diagram the map to the constant point diagram is cartesian, so the presheaf colimit is already local, and presheaf descent transfers. This confirms the note's sketch of DESC-grpd. No gap.
3. **Q1(c) holds, and the shift by one is optimal.** For n ≥ 0, `* → K(ℤ/2, n+1)` has fibre `K(ℤ/2, n)` but the base has trivial n-truncation; for n = −1, a singleton over a two-point set. This is exactly the note's DESC-tr. No gap.
4. **Q1(d): lax gluing at an ordinary colimit is false; it holds at an oriented colimit.** The constant point over the walking arrow has ordinary colimit a point, so lax gluing data (a non-invertible functor between fibres, e.g. `∅ → *`) cannot descend. At the *oriented* colimit (which is the walking arrow) the Gray mapping object into the classifier is the oriented limit of the pieces' mapping objects: this is the definition of oriented colimit (Gepner–Heine Def. 3.3.6) evaluated at the classifier, plus oriented straightening (Gepner–Heine Thm 1.8.1–1.8.2, Cor. 1.8.4). One size point is implicit: the classifier lives one size up, so the oriented colimit must remain one after enlarging the universe. That is standard for colimit-preserving inclusions of size-κ into size-λ categories and is accepted. Universality fails for oriented colimits (`E = [1]`: the Gray square versus the cartesian square), so the oriented clause has gluing and uniqueness but **no universality clause**. Verified at argument level.
5. **The exact test for van Kampen pairs** (left adjoint L to restriction; unit and counit tests) is the standard adjunction argument and is correct. It is a test, not a syntactic characterisation, which is what the prompt allowed.
6. **Exponentiable maps are not van Kampen in general.** The diagram `* ← {0<2} → [3] ← {1<3} → *` has colimit `*` (two-out-of-six), and the family with fibre A (walking retraction restricted to x) at even vertices and R at odd vertices is exponentiable but cannot descend (A has one isomorphism class of objects, R has two). Checked directly that the projection is not cocartesian: over 1 → 3, the map `i : y → x` has two factorisations through x (`1_x ∘ i = ir ∘ i`), so (a) does not apply, as it must not. The transfer of exponentiability from (∞,1) to Cat_ω for gaunt categories over an ordinal uses Goldthorpe's presentation and was checked at argument level only. Sufficient condition: cores preserve the colimit (Ayala–Francis); not necessary (`* ← [1] → *`). Accepted.
7. **Q2 as stated is false, and the counterexample is inside the grammar.** One operation `1 → 2` (target a constant, which preserves sifted colimits, so the prompt's target grammar admitted it): the models form `C ⊔ C`, with no initial object. Also `1 → X ⊔ X`. **The prompt's target condition (colimit-preserving) was the wrong one**: positivity of targets means limit-preserving, i.e. right adjoints. Checked: a model of one operation with constant source A is an object of the comma `(A ↓ T)`, and initial objects of these for all A are exactly a left adjoint (universal arrows). Sufficiency (accessible sources, accessible limit-preserving targets, cell declarations as operations out of the tensor with the globe restricted on the boundary) is the standard presentability argument (Kerodon 9.4.9.13, 9.4.9.15, 9.5.1.1, 9.5.2.1). No gap.
8. **Lax model morphisms break initiality.** For pointed objects with a non-invertible comparison `f(i) → y`, any candidate has two inequivalent maps to `([1], 1)` (constants at 0 and at 1). Checked. So INIT must use **strong** homomorphisms; the cells declared *inside* a model may still be non-invertible. This refutes the note's "lax by default" paragraph for model morphisms.
9. **The end reading is not equivalent to initiality.** If an initial model exists, the limit of the forgetful functor is its carrier (the initial object is coinitial). But for `1 → 2` the limit exists (it is `0`) while no initial model does. So the rule must be stated as initiality (INIT-J1/J2); the end is a consequence. Checked.
10. **Individual signatures**: exact semantic test via κ-compact models; undecidability with effectively given constants `BG` (Adian–Rabin). Correct, and it shows that the right syntactic statement is a *uniform* class of targets, not a per-signature test.
11. **Instances.** Labelled graphs (coslice `C_{P/}`), truncation marks (accessible localisations), and the rose-tree family `∐_T P_T → Θ₀` all have initial models. Checked; consistent with the note's §4.3.
12. **Q3 is answered only for the prompt's (wrong) grammar.** In spaces, descent holds and `1 → 2` has no initial model. For the corrected class (right-adjoint targets) spaces is presentable, so every such signature *does* have an initial model there. Non-derivability of the corrected rule from finite limits, finite colimits and descent remains **open**; it goes to the follow-up prompt `outbox/universe-free-initial-models-r2.md`.

**Corrections this forces in the repository** (made in this round, see `universe-free-principles.md` §3–§4, §6a, §7):
- INIT's target condition is changed from colimit-preserving to limit-preserving (X, `Hom_X(x, y)`, cotensors `[A, X]` and lax cotensors by fixed A, ⊤, finite limits of these), with arbitrary accessible sources.
- INIT uses strong model morphisms. "Lax by default" is withdrawn for model morphisms (standard 4 answered negatively for this rule).
- The impredicative reading `∀Δ. X` is a consequence of INIT, not its definition.
- R-A⁺'s original form `B_e → Hom_X(x_v, x_w)` is admissible as it stands (the note had called it non-positive).
- A new clause **DESC-or** (oriented descent: lax gluing along oriented colimits, no universality clause) is added. Over the walking arrow, seen as the oriented colimit of the point, it gives the classification half of G₁.
- Found while correcting §6a (not from the response): the "object with an automorphism" context written with one quasi-inverse s⁻¹ and two invertible cells has a non-set initial model (Basold–Geuvers–van der Weide 2017, cited by Altenkirch–Scoccola, arXiv:2007.00167 §1.2). It is replaced by bi-invertible data or an `inv` mark on s, and T-init is restricted accordingly.
