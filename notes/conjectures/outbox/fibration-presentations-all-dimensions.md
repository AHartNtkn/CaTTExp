# Finite presentations of Grothendieck constructions over free bases of any dimension

*A self-contained problem. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, polygraphs (computads) and Grothendieck constructions, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** One theorem for bases and fibres of **every** finite dimension, with its finite check. The cases of base dimension ≤ 3 and of suspension bases are done (§3), each by a construction tailored to its dimension. A further case such as "base dimension 4" is not what we want; the point is a construction whose correctness does not depend on the dimension.

## 1. Setting

### 1.1 Marked (∞,ω)-categories and left cartesian fibrations

Work in Loubaton's model (*Categorical theory of (∞,ω)-categories*, arXiv 2406.05425).
- A **marked** (∞,ω)-category has a chosen class of positive-dimensional cells containing the equivalences and closed under composition. A^♯ marks every cell. D_n^t is the n-globe with its top cell marked. ⊗ is the marked Gray tensor.
- A map p : E → B is a **left cartesian fibration** (Def. 3.2.2.1) when it has the unique right lifting property against `K ⊗ {0} → K ⊗ [1]^♯` for `K ∈ {D_n^♭ : n ≥ 0} ∪ {D_n^t : n ≥ 1}`. Straightening (Thm 4.1.4.2) identifies left cartesian fibrations over B^♯ with functors B → ω (the (∞,ω)-category of (∞,ω)-categories). The fibration classifying T is written ∫T.

### 1.2 Polygraphs and localisation

- For a finite polygraph Ψ, `Free(Ψ)` is the free (∞,ω)-category on Ψ and `F(Ψ)` the free strict ω-category. Ψ is **homotopical** when the comparison Free(Ψ) → F(Ψ) is an equivalence. `F_m(Π)` is the free strict m-category on an m-polygraph Π.
- A marking is a set of generators. `J[S⁻¹]` is the localisation of J at a set S of cells.
- A **presentation** of a fibration p : E → B over a polygraph base Γ is a finite marked polygraph Ψ with a map to Γ and a set S of marked generators such that `Free(Ψ)[S⁻¹] → Free(Γ)` is equivalent to p.

### 1.3 Why it matters

A W-weighted limit of a diagram F is the marked lax limit of F ∘ p over the total space of the fibration p classifying W (Loubaton, Cor. 4.2.2.6, Cor. 4.2.3.18). If p has a finite presentation with a finite correctness certificate, a proof checker can accept the weighted limit as a marked lax limit over a finite index. So a theorem for all dimensions gives checkable weighted limits for every finite weight with free values over every homotopical finite base.

## 2. The expected answer

For a base n-polygraph Γ and a strict weight T : F(Γ) → strict ω-categories with each value T(b) = F_m(Π_b), Π_b finite and homotopical, the expected presentation is the **relative Gray-generator presentation**:
- the generators of every fibre Π_b over the base vertices b;
- for each base k-generator q (k ≥ 1) with source vertex b and each j-generator g of Π_b, one marked generator `q ⊗ g` of dimension k + j, with boundary given by the Leibniz formula `∂(q ⊗ g) = ∂q ⊗ g ± q ⊗ ∂g`, read through T;
- localisation at the generators q ⊗ g with j > 0.

So the presentation has dimension ≤ n + m.

## 3. What is known

1. **Localisation lemma.** If S is a set of marked cells of J and q : J → J[S⁻¹], restriction is an equivalence of (∞,ω)-categories of marked cones, natural in the apex.
2. **Tensor-localisation and mixed localisation.** For any set S of positive-dimensional cells, `X[S⁻¹] ⊗ I ≃ (X ⊗ I)[{s ⊗ 0, s ⊗ 1, s ⊗ i}⁻¹]`. For finite homotopical X and Y there is a finite cellular model 𝓡_Y(X), natural in X, with one generator x ⊗ y per pair of generators, and `𝓡_Y(X)[(x ⊗ y)⁻¹ : dim x, dim y > 0] ≃ X × Y`.
3. **Bases of dimension ≤ 2.** For every finite homotopical 2-polygraph base and fibres F_m(Π_b) with Π_b finite homotopical, the expected presentation is correct. Proof: for a base path p = e₁; …; e_r the map δ_r : I → [r] (0 ↦ 0, 1 ↦ r) and A ⊗ [r] ≃ (A ⊗ I) ∐_A ⋯ ∐_A (A ⊗ I) give a map from the cylinder of T(p) into the **unlocalised** graph presentation; attach a double Gray cylinder block for each base 2-generator along these maps; conclude with Loubaton's theorem that pullback preserves colimits (Thm 3.2.3.15, Cor. 3.2.3.16).
4. **Bases of dimension 3.** For a finite 3-polygraph base Γ such that Γ and its 2-skeleton are homotopical (more precisely: the 2-skeleton is homotopical and attaching the 3-generators is a homotopy pushout), the expected presentation is correct for every fibre dimension m, with generators of dimension ≤ m + 3. The 3-generators of the base are handled by left and right whiskering subdivisions of the outer interval, which reduce each 3-generator to a cylinder over its 2-dimensional boundary data, where item 3 applies.
5. **Suspension bases.** For Q = F_d(Λ) with Λ finite homotopical and base ΣQ, the expected presentation is correct for every fibre dimension, via K = 1^co ⋆ Q and the suspension-base classification (Loubaton, Cor. 4.1.2.19).
6. **The obstacle in base dimension ≥ 4.** Gluing the local totals over the base generators gives the right generators. But the attaching maps are first obtained in the **localised** category Free(Ψ)[S⁻¹], while adjoining generators to Ψ needs attaching maps in Free(Ψ) itself, and such lifts need not exist (in Free(s)[s⁻¹] the inverse of s exists; in Free(s) no arrow goes back). For bases of dimension ≤ 3 the lifts were constructed by hand, by subdividing cylinders along composites in the boundary of each generator. For base dimension ≥ 4 what is missing is a **compatible** choice of such lifts for all higher-dimensional boundary expressions at once.
7. **A finite certificate exists for the proved cases:** homotopicality certificates for the fibres and base attachments, the weight data, the attaching expressions, the generator list indexed by base–fibre pairs, the marking and localisation lists, and face-compatibility checks on the intersections of the cylinders.
8. **Homotopicality of the base is needed.** For the base (x; σ : 1_x ⇒ 1_x), F(Γ) = B²ℕ groupoidifies to K(ℤ,2), while every Free(Ψ)[S⁻¹] with Ψ finite groupoidifies to a finite CW complex. So even the terminal weight has no finite presentation.

## 4. Questions

**Question 1 (main).** Let Γ be a finite n-polygraph all of whose skeleta are homotopical, and T : F(Γ) → strict ω-categories a strict functor with values F_m(Π_b), Π_b finite and homotopical. Prove that the relative Gray-generator presentation of §2 presents ∫T, for all n and m. State the finite certificate.

A uniform proof will probably need attaching maps that are functorial in the base cell, so that compatibility along common boundaries is automatic rather than checked shape by shape. Two possible routes, offered only as suggestions:
- **(a) A strict model.** Build the unlocalised presentation as a strict construction on F(Γ) itself, for example a strict lax Grothendieck construction of T (or of a cofibrant replacement of T) computed in strict ω-categories with the Gray tensor, natural in maps of bases. Then show once, by cellular induction on Γ, that localising it gives ∫T. Naturality would replace the hand-made lifts of item 6.
- **(b) Cylinder functors on pasting shapes.** Define, for every globular pasting shape P and every strict functor P → strict ω-categories, an unlocalised cylinder presentation that is natural in maps of pasting shapes (including degeneracies and composites). Every base generator's boundary is a composite of pasting shapes, so the attaching maps are images of this natural construction.

**Question 2 (weights with non-free values).** Extend Question 1 to weights whose values are themselves given by finite homotopical polygraphs Π_b but whose functors T(q) are only given up to equivalence (an (∞,ω)-functor F(Γ) → ω rather than a strict one). Is there a finite presentation, and what extra data must the certificate contain?

**Question 3 (sharpness).** Is homotopicality of all skeleta of the base necessary, or is homotopicality of Γ itself enough? Give a base Γ that is homotopical with a non-homotopical skeleton, and decide whether the terminal weight on it has a finite presentation.

## 5. What counts as a solution

A proof of Question 1 (with the certificate); a counterexample, i.e. a base and weight in the class of Question 1 for which the expected presentation is wrong (for example by an Euler-characteristic or homology count after groupoidification); answers to Questions 2–3; or a published reference.

## 6. Literature (searched 2026-11-18)

- Loubaton, arXiv 2406.05425 (left cartesian fibrations, straightening, weighted limits as marked lax limits, pullback preserves colimits).
- Campion, *The Gray tensor product of (∞,n)-categories*, arXiv 2311.00205; Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (homotopy polygraphs).
- Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*, Mém. SMF (joins and Gray tensor of strict ω-categories).
- No published recognition theorem for Grothendieck constructions over free strict n-categories presented by polygraphs was found.

# Researcher Response

**Question 3 has a negative answer to the requested example: under the cellular meaning of \(\mathrm{Free}(\Gamma)\), a finite homotopical polygraph necessarily has homotopical skeleta.** Thus the two proposed hypotheses on the base are equivalent.

The literal formulation of Question 2 also reduces to Question 1: if each value is equivalent to \(F(\Pi_b)\), without further localisation, the weight can be made strict on those chosen values.

I do not have a proof or counterexample for Question 1. Below are proofs of these two reductions, including the certificate data they require.

## 1. Homotopicality passes to skeleta

Write \(\mathcal C=(\infty,\omega)\text{-}\mathrm{Cat}\).

### Lemma: pullback along a subpolygraph inclusion preserves colimits

Let \(\Delta\subseteq\Gamma\) be a subset of generators closed under their boundaries. Then
\[
j:F(\Delta)\hookrightarrow F(\Gamma)
\]
is a discrete Conduché functor in \(\mathcal C\). Consequently,
\[
j^*:\mathcal C_{/F(\Gamma)}
\longrightarrow
\mathcal C_{/F(\Delta)}
\]
preserves colimits.

Here the external result being used is Loubaton’s **Theorem 2.2.2.10**: pullback along a discrete Conduché functor preserves colimits. His **Definition 2.2.2.2** characterises these functors by unique lifting against units and composition maps. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

**Proof that \(j\) satisfies those lifting conditions.** For a strict cell \(u\), let \(\operatorname{supp}(u)\) be the set of generators used in a composite expression for \(u\), together with the generators used in their iterated boundaries. This set is independent of the expression: associativity and interchange preserve the union of the supports, and the unit laws preserve it because the support of a boundary is a subset of the support of the cell.

In particular,
\[
\operatorname{supp}(1_u)=\operatorname{supp}(u),
\qquad
\operatorname{supp}(u*_k v)
=
\operatorname{supp}(u)\cup\operatorname{supp}(v).
\]
Moreover,
\[
u\in F(\Delta)
\quad\Longleftrightarrow\quad
\operatorname{supp}(u)\subseteq\Delta.
\]

Therefore:

- If \(1_u\) belongs to \(F(\Delta)\), then \(u\) belongs to \(F(\Delta)\).
- If \(u*_k v\) belongs to \(F(\Delta)\), then both \(u\) and \(v\) belong to \(F(\Delta)\).
- These lifts are unique because \(j\) is an inclusion.

These strict lifting statements are also the required lifting statements in \(\mathcal C\). Indeed, free strict categories are gaunt: the number of generating \(d\)-cells in a \(d\)-cell is nonnegative, additive under composition, and zero precisely on identities, so a strictly invertible \(d\)-cell must be an identity. Loubaton’s inclusion of gaunt strict categories into \(\mathcal C\) is fully faithful, with discrete mapping spaces between them. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

This proves the lemma.

### Theorem: the skeletal comparison is a pullback of the whole comparison

Let \(\Gamma\) be a finite \(N\)-polygraph. Then, for every \(r\leq N\), the square
\[
\begin{array}{ccc}
\mathrm{Free}(\Gamma_{\leq r})
&\longrightarrow&
\mathrm{Free}(\Gamma)
\\[2mm]
\downarrow c_r&&\downarrow c_\Gamma
\\[2mm]
F(\Gamma_{\leq r})
&\longrightarrow&
F(\Gamma)
\end{array}
\tag{1}
\]
is a pullback in \(\mathcal C\).

**Proof.** Make the cellular construction explicit. Put
\[
X_{-1}=\varnothing,
\]
and, for \(0\leq d\leq N\), form the pushout
\[
X_d
=
X_{d-1}
\mathop{\coprod}\limits_{\displaystyle\coprod_{q\in\Gamma_d}\partial D_d}
\displaystyle\coprod_{q\in\Gamma_d}D_d.
\tag{2}
\]
The attaching maps are those defining the free cellular realisation, and the comparison maps
\[
c_d:X_d\longrightarrow F(\Gamma_{\leq d})
\]
send each generator to its corresponding strict generator. Thus
\[
X_d=\mathrm{Free}(\Gamma_{\leq d}).
\]

Fix \(r\), and abbreviate
\[
A=F(\Gamma_{\leq r}),\qquad B=F(\Gamma),\qquad j:A\hookrightarrow B.
\]
Regard every stage of (2) as lying over \(B\), and apply
\[
j^*(-)=(-)\times_B A.
\]
The lemma shows that this functor preserves the pushouts in (2).

For \(d\leq r\), the map \(X_d\to B\) factors through \(A\). Since \(j\) is a monomorphism,
\[
j^*X_d\simeq X_d.
\tag{3}
\]

Now let \(d>r\), and consider the globe \(D_d\to B\) labelled by \(q\in\Gamma_d\). Every cell of \(D_d\) absent from \(\partial D_d\) is its top cell or an iterated identity of that top cell. Its image has \(q\) in its support, and therefore does not belong to \(A\). Consequently,
\[
(\partial D_d)\times_B A
\;\cong\;
D_d\times_B A.
\tag{4}
\]
These strict pullbacks compute the pullbacks in \(\mathcal C\): the inclusion of gaunt strict categories is a right adjoint and hence preserves limits.

Equation (4) means that each attachment above dimension \(r\), after applying \(j^*\), is a pushout along an equivalence. It changes nothing. Combining this with (3) gives
\[
\boxed{
\mathrm{Free}(\Gamma)\times_{F(\Gamma)}
F(\Gamma_{\leq r})
\simeq
\mathrm{Free}(\Gamma_{\leq r}).
}
\tag{5}
\]
The map from (5) to \(F(\Gamma_{\leq r})\) is \(c_r\), proving (1). \(\square\)

Notice that (4) does **not** assert that the pullback is \(\operatorname{sk}_rD_d\). A higher-dimensional boundary cell can map to an identity on a lower-dimensional cell and survive the pullback. Equality of the two pullbacks in (4) is all that is needed.

### Consequences for Question 3

Pullback preserves equivalences. Applying this to (1) yields
\[
c_\Gamma\text{ is an equivalence}
\quad\Longrightarrow\quad
c_r\text{ is an equivalence for every }r.
\]
The converse includes the case \(r=N\). Hence
\[
\boxed{
\Gamma\text{ is homotopical}
\quad\Longleftrightarrow\quad
\text{every skeleton of }\Gamma\text{ is homotopical}.
}
\tag{6}
\]

Thus there is **no finite base of the requested kind**: a homotopical \(\Gamma\) with a non-homotopical skeleton.

This argument uses the cellular meaning of \(\mathrm{Free}(\Gamma)\) explicitly displayed in (2). It works for any compatible choice of weak attaching maps defining that realisation; it does not assert that arbitrary strict boundary expressions have a canonical weak lift.

For the terminal weight,
\[
\int_{F(\Gamma)}\mathbf 1
\simeq
F(\Gamma)
\xrightarrow{\mathrm{id}}
F(\Gamma).
\]
Its finite presentation is
\[
\Psi=\Gamma,\qquad
S=\varnothing,
\]
with every positive-dimensional generator marked. Under the equivalence \(c_\Gamma\), the projection is the identity of \(\mathrm{Free}(\Gamma)\).

The certificate consists of the finite polygraph data, the marking list, and the supplied proof that \(c_\Gamma\) is an equivalence. Separate proofs for the skeleta can be derived from that proof by (1).

## 2. The stated weak weights can be made strict

Here I use the literal assumption
\[
T(b)\simeq F(\Pi_b),
\tag{7}
\]
with no additional localisation of \(F(\Pi_b)\).

Let
\[
\mathcal G=(0,\omega)\text{-}\mathrm{Cat}
\]
be the category of gaunt strict categories, and let
\[
N:\mathcal G\hookrightarrow\mathcal C
\]
be Loubaton’s fully faithful right adjoint.

### The whole transformation category is strict

For \(A,B\in\mathcal G\), there is an equivalence of cartesian internal homs
\[
\underline{\operatorname{Hom}}_{\mathcal C}(NA,NB)
\simeq
N\underline{\operatorname{Hom}}_{\mathcal G}(A,B).
\tag{8}
\]

To verify this, evaluate on \(\theta\in\Theta\):
\[
\begin{aligned}
\operatorname{Map}_{\mathcal C}
\left(
\theta,
\underline{\operatorname{Hom}}_{\mathcal C}(NA,NB)
\right)
&\simeq
\operatorname{Map}_{\mathcal C}(\theta\times NA,NB)
\\
&\simeq
\operatorname{Hom}_{\mathcal G}(\theta\times A,B).
\end{aligned}
\tag{9}
\]
The second line uses full faithfulness and preservation of products by \(N\). The result is a discrete set, and these sets are precisely the nerve of the strict cartesian internal hom. Its \(s\)-cells are strict functors
\[
D_s\times A\longrightarrow B.
\]

Loubaton’s equation **(4.1.1.24)** identifies the hom-category in the classifier \(\omega\) with this cartesian internal hom:
\[
\operatorname{hom}_{\omega}(NA,NB)
\simeq
\underline{\operatorname{Hom}}_{\mathcal C}(NA,NB).
\tag{10}
\]
Thus (8) concerns the full higher transformation category, rather than only its maximal subgroupoid. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### Rectification of the weight

Choose
\[
C_b=F(\Pi_b)
\quad\text{and}\quad
e_b:NC_b\xrightarrow{\simeq}T(b).
\]
Transporting \(T\) along the \(e_b\) gives hom maps
\[
F(\Gamma)(b,c)
\longrightarrow
N\underline{\operatorname{Hom}}_{\mathcal G}(C_b,C_c).
\tag{11}
\]
Both the source and target in (11) are gaunt strict categories, so full faithfulness makes each map a strict functor.

The transported maps preserve composition and units up to equivalence. But the relevant mapping spaces between these gaunt strict categories are discrete. Those equivalences therefore assert **equality of the corresponding strict functors**. The transported maps consequently define a strict weight
\[
T_{\mathrm{str}}:F(\Gamma)\longrightarrow
\omega\mathrm{Cat}_{\mathrm{strict}},
\qquad
T_{\mathrm{str}}(b)=C_b,
\]
with strict higher transformations, together with an equivalence
\[
T_{\mathrm{str}}\simeq T.
\tag{12}
\]

Straightening then gives
\[
\int T_{\mathrm{str}}\simeq\int T
\]
over the base.

Therefore, under (7), **a positive answer to Question 1 gives a positive answer to Question 2 with the same dimension bound and generator prescription after rectification**. Conversely, Question 1 is a special case of Question 2. Their existence assertions are equivalent under the stated fibre hypothesis.

### Extra finite certificate data for this reduction

In addition to a certificate for Question 1, the reduction uses:

1. **Fibre identifications:** the finitely many equivalences \(e_b\).
2. **Images of base generators:** the transported image of each \(q\in\Gamma\), with its globular source and target.
3. **Strict functor data:** for each base \(1\)-generator, images of the finitely many generators of its source fibre.
4. **Strict transformation data:** for each base \(k\)-generator with \(k\geq2\), the components of its strict \((k-1)\)-transformation at the source fibre’s vertices, together with naturality equations against its positive-dimensional generators.
5. **Finite derivations of the required equalities:** boundary equations, naturality equations, and comparisons identifying the assignments with the transported \(T(q)\).

Naturality on composites follows from strict composition. The cell expressions and equality derivations are finite; checking a supplied derivation does not require assuming a decision procedure for arbitrary equality of strict higher composites.

There is no additional independent tower of associativity and unit coherence choices after this rectification: the relevant equivalences have become equalities.

If “non-free values” instead means values of the form
\[
\mathrm{Free}(\Pi_b)[W_b^{-1}],
\]
then (7) is a different hypothesis. The internal homs need not be gaunt, and the argument above does not settle that version of Question 2.

## 3. What remains of Question 1

The relevant additional published reference is Ara–Guetta, *Lax functorialities of the comma construction for \(\omega\)-categories*, §7. It constructs a strict Grothendieck construction and proves Gray functoriality. It does not provide the relative finite polygraphic resolution required here. [arxiv.org](https://arxiv.org/html/2503.08832v3?utm_source=chatgpt.com)

For example, for the constant diagram over \(D_1\) with value \(D_1\), the strict Grothendieck total is
\[
D_1\times D_1,
\]
whereas the proposed unlocalised presentation is
\[
D_1\otimes D_1.
\]
The former imposes commutativity of the square; the latter has a generating \(2\)-cell between its two boundary paths. Thus the strict construction’s functoriality does not itself furnish the required unlocalised attaching maps.

The reductions proved above eliminate two distinctions in the statement—whole-base versus skeletal homotopicality, and strict versus weak weights with the stated unlocalised values. **The uniform construction of the compatible unlocalised attaching maps in Question 1 remains unproved here.**

# Followup

**Question 1 is false for the prescribed globular Gray boundaries.** There is a counterexample with base dimension \(4\) and fibre dimension \(3\). The required generator \(P\otimes x\) has no attaching map in the unlocalised presentation: one side of its boundary requires the inverse of a mixed \(3\)-generator.

There is nevertheless a uniform positive result: **finite presentations exist in every dimension, including for weak weights with finitely presented fibres, if auxiliary generators are allowed.** This gives a positive answer to Question 2, without the prescribed generator count or the \(n+m\) bound.

For Question 3, homotopicality passes to skeleta under the stated definition. Thus the requested example of a homotopical polygraph with a non-homotopical skeleton does not exist.

## 1. Counterexample to the relative Gray-generator presentation

I use the fibre-first convention \(A\otimes I\) appearing in your proved cylinder constructions. All boundaries below are explicit, so the argument does not depend on interpreting the shorthand “\(\pm\)” in the Leibniz formula.

### 1.1 Base, fibre, and homotopicality certificates

Words are written in categorical right-to-left order. A sequence of rewriting steps separated by semicolons is executed from left to right. A subscript \(i\) means “apply this generator to the substring starting at position \(i\), counting from zero in the current word.”

Let \(\Gamma\) have one generator in each dimension \(0,\ldots,4\):
\[
b,\qquad a:b\to b,\qquad \mu:aa\Rightarrow a,
\]
\[
\alpha:(\mu_1;\mu_0)\Rrightarrow(\mu_0;\mu_0),
\]
and a pentagon \(4\)-generator \(P\).

To specify \(P\), write the five parenthesisations of four letters as
\[
\begin{aligned}
R&=1(2(34)),&
B&=1((23)4),&
C&=(1(23))4,\\
E&=(12)(34),&
L&=((12)3)4.
\end{aligned}
\]
Each denotes the corresponding \(2\)-cell \(a^4\Rightarrow a\) built from \(\mu\). Each arrow below is the indicated associativity rotation, using a whiskered copy of \(\alpha\):
\[
s_3P=(R\longrightarrow B\longrightarrow C\longrightarrow L),
\]
\[
t_3P=(R\longrightarrow E\longrightarrow L).
\]
The two expressions for the intermediate multiplication \(E\) agree by strict interchange.

Let the fibre polygraph \(\Pi\) have
\[
x,\qquad g:x\to x,\qquad \delta:g\Rightarrow gg,
\]
and
\[
\kappa:(\delta_0;\delta_1)\Rrightarrow(\delta_0;\delta_0).
\]
Put \(\mathcal C=F_3(\Pi)\).

These satisfy the required homotopicality hypotheses. Let \(X_{\le r}\) be the finite semisimplicial set with one simplex in each dimension \(0,\ldots,r\), every face being the unique simplex of the preceding dimension. Then:

- \(\Pi\) is the standard oriental polygraph of \(X_{\le3}\);
- \(\Gamma\) is the **even-dimensional dual** of the oriental polygraph of \(X_{\le4}\), reversing dimensions \(2\) and \(4\).

Reversing dimension \(2\) changes the comultiplication into \(\mu\) and gives the displayed associator. Reversing dimension \(4\) makes the pentagon point from the three-associator side to the two-associator side. Each skeleton has the same description with a lower truncation.

Chanavat’s Theorem 3.35 states that the polygraph generated by a semisimplicial set is a homotopy polygraph. Applying it to these truncations, and then applying duality, certifies every base skeleton and the fibre. Duality preserves the relevant globes, pushouts, and equivalences. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

### 1.2 The strict weight

Let \(Z:\mathcal C\to\mathcal C\) be the constant strict functor at \(x\). It sends every positive-dimensional cell to an identity, and \(Z^2=Z\) literally.

Define
\[
T(b)=\mathcal C,\qquad T(a)=Z,
\]
and give the higher transformations by their components at \(x\):
\[
T(\mu)_x=g,\qquad T(\alpha)_x=\delta,\qquad T(P)_x=\kappa.
\]

Here is the boundary check.

The two multiplication composites defining the source and target of \(\alpha\) evaluate respectively to
\[
g,\qquad g^2.
\]
One contribution to the first composite is killed by postcomposition with \(Z\). Thus \(T(\alpha)_x=\delta:g\Rightarrow g^2\) is correctly typed.

The long pentagon evaluates to
\[
\delta_0;\delta_1,
\]
whereas the short pentagon evaluates to
\[
\delta_0;\delta_0.
\]
Thus \(T(P)_x=\kappa\) is correctly typed. All strict naturality equations hold because \(Z\) sends the positive-dimensional cells of its argument to identities. Freeness of \(F(\Gamma)\) now gives the strict functor \(T\).

### 1.3 The prescribed relative \(3\)-skeleton

Write
\[
t=a\otimes x.
\]
The \(1\)-generators are \(g,t\). The \(2\)-generators are
\[
\delta:g\Rightarrow gg,\qquad
c=a\otimes g:t\Rightarrow tg,\qquad
u=\mu\otimes x:gtt\Rightarrow t.
\]

The \(3\)-generators are exactly the following:
\[
\begin{array}{c|c|c}
\text{generator}&\text{source }2\text{-cell}&\text{target }2\text{-cell}\\ \hline
D=a\otimes\delta&
c_0;\delta_1&
c_0;c_0\\
M=\mu\otimes g&
u_0;c_0&
c_2;u_0\\
V=\alpha\otimes x&
c_1;u_2;u_0&
\delta_0;u_1;u_0\\
\kappa&
\delta_0;\delta_1&
\delta_0;\delta_0
\end{array}
\tag{1}
\]

Their respective \(1\)-boundaries are
\[
t\Rightarrow tgg,\quad
gtt\Rightarrow tg,\quad
gt^3\Rightarrow t,\quad
g\Rightarrow ggg.
\]

In particular, the direction of \(M\) is fixed by the fibre-first Gray prism. Before identifying the two endpoints of \(g\), its Leibniz boundary is
\[
\partial(g\otimes\mu)
=
(x_1\otimes\mu)-(x_0\otimes\mu)
-(g\otimes a)+(g\otimes a^2).
\]
Its source uses \(u\) followed by the naturality cell for \(a\); its target uses the naturality cell for \(a^2\) followed by \(u\). Since \(Z(g)\) is an identity, this gives precisely
\[
M:(u_0;c_0)\Rrightarrow(c_2;u_0).
\]

There is no choice of a larger positive \(2\)-cell with any of the four displayed \(1\)-boundaries: in each case there are exactly the two \(2\)-cells listed in (1). This can be checked by counting \(g\)’s and \(t\)’s, as in the exhaustive calculation below.

### 1.4 The required pentagon boundary does not exist

The prescribed \(P\otimes x\) has \(1\)-source and \(1\)-target
\[
gt^4,\qquad t.
\tag{2}
\]
Indeed, the right-comb \(2\)-source of \(P\) evaluates under \(T\) to \(g\), while transport along \(a^4\) is \(t^4\).

Consider all \(2\)-cells
\[
gt^4\Rightarrow t
\]
in the free strict \(2\)-category on \(c,\delta,u\).

Every such \(2\)-cell uses exactly three \(u\)’s: only \(u\) changes the number of \(t\)’s, decreasing it by one. Those three applications consume three \(g\)’s. There is initially one \(g\), and each \(c\) or \(\delta\) creates one. Consequently every such \(2\)-cell uses exactly two generators from \(\{c,\delta\}\).

Thus every rewriting path has **exactly five generating steps**. This is an exhaustive bound, not a search cutoff.

There are 18 paths, giving the following eight \(2\)-cells after quotienting by strict interchange:

| \(2\)-cell | Representative path |
|---|---|
| \(R\) | \(c_1;c_3;u_4;u_2;u_0\) |
| \(B_\delta\) | \(c_1;\delta_2;u_3;u_2;u_0\) |
| \(B_c\) | \(c_1;c_1;u_3;u_2;u_0\) |
| \(C\) | \(c_1;\delta_0;u_3;u_1;u_0\) |
| \(L_r\) | \(\delta_0;\delta_1;u_2;u_1;u_0\) |
| \(L_l\) | \(\delta_0;\delta_0;u_2;u_1;u_0\) |
| \(E_{\mathrm{early}}\) | \(c_2;\delta_0;u_1;u_2;u_0\) |
| \(E_{\mathrm{late}}\) | \(\delta_0;u_1;c_1;u_2;u_0\) |

Insert every \(3\)-generator from (1) in every possible \(2\)-cell context. The complete directed graph is
\[
R\xrightarrow{V}B_\delta
 \xrightarrow{D}B_c
 \xrightarrow{V}C
 \xrightarrow{V}L_r
 \xrightarrow{\kappa}L_l,
\tag{3}
\]
together with
\[
R\xrightarrow{V}E_{\mathrm{early}}
 \xleftarrow{M}E_{\mathrm{late}}
 \xrightarrow{V}L_l.
\tag{4}
\]
There are no other edges.

The projection to the base sends the two \(B\)-vertices to \(B\), the two \(E\)-vertices to \(E\), and the two \(L\)-vertices to \(L\). It sends \(V\) to a whiskered \(\alpha\), and sends \(D,M,\kappa\) to identities.

The long side of the pentagon therefore has a positive lift, with its fibre correction, along (3). The short side has **no positive lift at all**: its first \(\alpha\)-step necessarily lands at \(E_{\mathrm{early}}\), which has no outgoing edge.

Every \(3\)-cell is a composite of contextual applications of the generating \(3\)-cells. Horizontal and vertical whiskering can be sequentialised into such applications, using strict \(2\)-interchange. Hence the graph exhausts all positive \(3\)-cells with (2) as their \(1\)-boundaries.

It follows that the required target \(3\)-cell of \(P\otimes x\) does not exist. Higher generators cannot change the strict \(3\)-skeleton. Nor can weak structural coherence repair this: any proposed attaching map into the unlocalised weak free category would compose with
\[
\operatorname{Free}(\Psi)\longrightarrow F(\Psi)
\]
to give the missing strict \(3\)-cell.

After localisation, the missing path exists:
\[
R\xrightarrow{V}E_{\mathrm{early}}
 \xrightarrow{M^{-1}}E_{\mathrm{late}}
 \xrightarrow{V}L_l.
\]
This is exactly the inverse that is unavailable at the required unlocalised attachment stage.

### 1.5 Finite verification and scope

The complete checker is q1_pentagon_certificate.py[q1_pentagon_certificate.py](sandbox:/workspace/scratch/14127eabc9f1/q1_pentagon_certificate.py). It uses only Python’s standard library. Running it gives:
```text
2-paths 18 2-diagrams 8 3-edges 8
positive pentagon boundary pairs 0
verified: no distinct parallel positive 3-paths anywhere in this hom
```

It enumerates all paths allowed by the forced generator counts, quotients by every adjacent disjoint interchange, and inserts every generating \(3\)-cell in every context.

This refutes the **actual globular Gray boundary prescription**. It does not refute an assertion allowing arbitrary different boundaries with the same generator counts. For example, reversing \(M\) repairs this particular pentagon, but changes its Gray boundary. The abelianised Leibniz equation alone cannot distinguish that reversal, since both boundaries of \(M\) have generator sum \(u+c\). Thus interpreting §2 solely as an equation of cellular chains would leave the attaching prescription underdetermined.

## 2. A uniform finite-existence theorem, including weak weights

The following survives the counterexample.

> **Finite Grothendieck presentation theorem.**  
> Let \(\Gamma\) be a finite polygraph whose skeleta are homotopical. Let
> \[
> T:F(\Gamma)\longrightarrow\omega
> \]
> be an arbitrary \((\infty,\omega)\)-functor. Suppose each value has a finite weak polygraphic presentation, allowing a finite localisation set.
>
> Then the classified left cartesian fibration has a presentation
> \[
> \bigl(\operatorname{Free}(\Psi),\langle Q\cup S\rangle\bigr)[S^{-1}]
> \simeq \int T
> \]
> over \(F(\Gamma)\), where \(\Psi\) is finite and homotopical and \(Q,S\) are finite sets of positive-dimensional generators. The equivalence preserves the cartesian marking.
>
> The construction supplies no bound \(\dim\Psi\le n+m\) and no prescribed base–fibre generator count.

Here \(\langle-\rangle\) denotes the generated marking. The set \(S\) is inverted; \(Q\) records the additional cartesian marking. Including \(S\) in the marked list ensures the convention in §1.2.

This answers Question 2 both for its literal fibre hypothesis and for the stronger interpretation where the values are finite localisations.

### 2.1 Finite models are closed under finite homotopy pushouts

Use saturated complicial sets as a model of \((\infty,\omega)\)-categories. The comparison with Loubaton’s model is proved in his *The complicial model of \((\infty,\omega)\)-categories*, Theorem 3.3.1.7. [arxiv.org](https://arxiv.org/pdf/2207.08504?utm_source=chatgpt.com)

The model structure has monomorphisms as cofibrations, finite elementary anodyne domains and codomains, and the marked interval \(\Delta[1]^t\) as a homotopy interval. It is cartesian and left proper. The \(n=\infty\) case is explicitly included in Ozornova–Rovelli’s discussion. [arxiv.org](https://arxiv.org/pdf/1809.10621?utm_source=chatgpt.com)

“Finite” below means finitely many nondegenerate simplices.

Let \(A,B\) be finite models and let
\[
f:[A]\longrightarrow[B]
\]
be a morphism in the presented higher-category theory. Form an elementary-anodyne fibrant replacement \(B\hookrightarrow RB\), using an \(\omega\)-sequence of attachment stages. Represent \(f\) by an actual map
\[
A\longrightarrow RB.
\]

Because \(A\) is finite, its image uses finitely many attached simplices and marking extensions. Each has a finite attaching domain. Include the earlier attachments needed to define those attaching maps. This process terminates: the stages decrease, and each selected attachment has finitely many dependencies.

Consequently the map factors through
\[
A\longrightarrow B',
\qquad B\hookrightarrow B',
\]
where \(B'\) is finite and \(B\to B'\) is a **finite sequence of elementary anodyne attachments**.

Apply this to both arrows of a homotopy span. Its homotopy pushout has the finite double mapping-cylinder model
\[
B'
\amalg_{A\times\{0\}}
\bigl(A\times\Delta[1]^t\bigr)
\amalg_{A\times\{1\}}
C'.
\tag{5}
\]
This proves closure under finite iterated homotopy pushouts; finite coproducts are immediate.

Finite weak polygraphic presentations have finite complicial models: globes and their boundaries have finite models, cell attachments are finite homotopy pushouts, and localisation of a specified \(r\)-cell is the homotopy pushout imposing
\[
D_r\longrightarrow D_{r-1}.
\]

This argument does not identify compact objects with finite cell objects and does not use closure under arbitrary colimits indexed by a category with finitely many morphisms.

### 2.2 Converting a finite simplicial model into a homotopical polygraph

There is an explicit finite conversion which avoids degeneracy problems.

Let \(K\) be a finite stratified simplicial set of dimension at most \(d\). Define a semisimplicial set by
\[
X_r=K_r\times\operatorname{Inj}_\Delta([r],[d])
\quad(0\le r\le d),
\]
with
\[
d_i(\sigma,j)=(d_i\sigma,j\delta_i).
\]
There are no simplices above dimension \(d\).

Freely adjoin degeneracies and call the resulting simplicial set \(L_dK\). Its projection is
\[
\pi:L_dK\longrightarrow K,\qquad(\sigma,j)\longmapsto\sigma.
\]
Mark a positive-dimensional generating pair precisely when \(\sigma\) is marked in \(K\). **This includes degenerate simplices of \(K\)**, which become new nondegenerate simplices in \(L_dK\).

There are exactly
\[
|K_r|\binom{d+1}{r+1}
\]
nondegenerate \(r\)-simplices, so the construction is finite.

Here is a proof that \(\pi\) is an equivalence.

For \(K=\Delta[p]\), \(p\le d\), the underlying \(L_dK\) is the nerve of the finite poset
\[
P_{p,d}=\{(x,i):0\le x\le p,\ 0\le i\le d\},
\]
whose nonidentity comparisons are
\[
(x,i)<(y,j)\iff x\le y\ \text{and}\ i<j.
\]
The projection to \([p]\) has section
\[
s(x)=(x,x).
\]
The monotone map
\[
F(x,i)=(x,\max(i,x))
\]
admits transformations
\[
\operatorname{id}\Longrightarrow F\Longleftarrow s\pi.
\]
Both are over \([p]\).

Their simplicial homotopies preserve the actual complicial markings. Indeed,
\[
\pi H=\pi\operatorname{pr}_1,
\]
and the marking on \(L_d\Delta[p]\) is the pullback marking. Thus these are \(\Delta[1]^t\)-homotopies, proving that \(\pi\) is an equivalence. The same argument works for the top-marked simplex.

The functor \(L_d\) preserves colimits and monomorphisms. Cellular induction through the simplex attachments and marking attachments of \(K\), using left properness, now gives
\[
L_dK\simeq K.
\tag{6}
\]

Let \(\Psi_X\) be the oriental polygraph of \(X\). It is finite and homotopical by Chanavat’s semisimplicial pasting theorem. Let \(S\) consist of its generators corresponding to marked simplices of \(L_dK\). The comparison of complicial simplices with orientals identifies marking a top simplex with weakly inverting its top oriental cell. Therefore
\[
K\simeq L_dK
\simeq\operatorname{Free}(\Psi_X)[S^{-1}].
\tag{7}
\]
The marking-to-localisation identification is explicit in Loubaton’s Construction 3.3.2.4 and Remark 3.3.2.5, with comparison theorem 3.3.2.9. [arxiv.org](https://arxiv.org/pdf/2207.08504?utm_source=chatgpt.com)

### 2.3 Retaining the cartesian marking

The complicial marking in (7) records equivalences. The cartesian marking is separate and must also be retained.

The necessary lemma is:

> If a higher category has a finite complicial model and its external marking is generated by finitely many cells, it has a finite marked polygraphic presentation with a separate finite localisation set.

To prove it, first observe that the top-cell inclusion
\[
D_r\longrightarrow O_r
\]
has a strict retraction \(O_r\to D_r\). Hence any specified \(r\)-cell can be represented as the top cell of an \(r\)-simplex.

For completeness, a retraction can be constructed on augmented directed chain complexes. Write the globe’s basis below dimension \(r\) as \(s_k,t_k\), and put
\[
a_k=
\begin{cases}s_k&k\text{ even},\\t_k&k\text{ odd},\end{cases}
\qquad
b_k=
\begin{cases}t_k&k\text{ even},\\s_k&k\text{ odd}.\end{cases}
\]
Send vertex \(0\) to \(s_0\), the other vertices to \(t_0\), and, for \(0<k<r\), send
\[
[0,\ldots,k-1,j]
\]
to \(a_k\) when \(j=k\), and to \(b_k\) when \(j>k\). Send other positive-dimensional proper faces to zero and the top simplex to the globe’s top generator. The two surviving boundary terms give \(t_{k-1}-s_{k-1}\); unsupported faces have cancelling images. This is a positive augmentation-preserving chain map. Steiner’s realisation theorem gives the required strict retraction. [arxiv.org](https://arxiv.org/pdf/math/0403237?utm_source=chatgpt.com)

Now choose simplex representatives for the finitely many externally marked cells in a fibrant replacement \(RK\). The finite-factorisation argument enlarges \(K\) by finitely many anodyne attachments so that all these representatives belong to a finite \(K'\). Apply \(L_d\) with \(d\) at least their dimensions.

For each chosen representative \(\sigma_j\), externally mark one generator
\[
(\sigma_j,[r_j]\hookrightarrow[d]).
\]
Keep this finite list \(Q\) separate from the thin-simplex localisation list \(S\). The equivalence (7) carries the marking generated by \(Q\) to exactly the prescribed external marking.

In a marked homotopy pushout, the marking is generated by the images of the markings of the input categories. This follows directly from its mapping-space universal property. Thus finite marked presentations are closed under finite homotopy pushouts and finite coproducts.

They are also closed under finite products. Such presentations are assembled by finite colimits from unmarked and top-marked globes. Marked cartesian product preserves colimits in each variable, so it suffices to handle products of marked globes. Their underlying categories have finite complicial models obtained by multiplying finite globe models; their strict globe products have finitely many nonidentity cells, so their external markings are finitely generated. The preceding lemma applies. The colimit-preservation input is Loubaton’s Proposition 3.1.1.19. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 2.4 Applying the lemma to weak weights

For arbitrary higher categories \(A,B,C\), a weight on the suspension \(\Sigma C\) is specified by
\[
\varphi:A\times C\longrightarrow B.
\]
Loubaton’s suspension classification gives its marked total as
\[
A^\flat\times K_C
\amalg_{A^\flat\times C^\flat}
B^\flat,
\qquad
K_C\simeq 1^{\mathrm{co}}\star C^\flat.
\tag{8}
\]
This is Corollary 4.1.2.19 together with Theorem 3.2.4.9, and it applies to arbitrary weak \(\varphi\). [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

For \(C\) a globe or a globe boundary, the finite cone models in the suspension-base construction give finite presentations of \(C^\flat\) and \(K_C\). If \(A,B\) have finite presentations, product closure and marked pushout closure applied to (8) give finite presentations of the local totals over globes and their boundaries.

Now use the finite cellular construction of the base. The pullback-colimit theorem in your hypotheses gives, at every attachment, a marked homotopy pushout
\[
E_{\mathrm{old}}
\amalg^h_{E_{\partial D_k}}
E_{D_k}
\simeq E_{\mathrm{new}}.
\]
All three inputs have finite marked presentations. Induction gives one for the full total, **including its cartesian marking**.

The map to the base can also be retained. Choose a fibrant model
\[
\widetilde E\longrightarrow N(F\Gamma).
\]
Represent the equivalence from the finite model by a map \(K\to\widetilde E\). Its extension to an elementary-anodyne fibrant replacement supplies maps from every finite expansion used above. Consequently
\[
L_dK'\longrightarrow N(F\Gamma)
\]
induces a strict functor
\[
F(\Psi)\longrightarrow F(\Gamma).
\]
The generators in \(S\) map to identities: \(F(\Gamma)\) has no nonidentity equivalences, by descending induction on dimension and freeness. The selected external generators map to cartesian cells. This produces the required equivalence in the marked slice. Transport across
\[
\operatorname{Free}(\Gamma)\simeq F(\Gamma)
\]
gives the presentation over the base in §1.2.

### 2.5 The finite certificate

For a weak weight, the certificate must supply more than equivalence classes of the transport functors. It consists of:

1. **Input certificates:** finite fibre presentations and the base homotopicality certificates.
2. **Weak weight representatives:** finite representatives of the transport data on base generators, their boundary coherences, and comparisons with the specified weight.
3. **Finite expansions:** the finite sequences of elementary anodyne attachments used to represent each gluing map, with their attaching maps.
4. **Colimit data:** the finite mapping-cylinder and pushout diagrams, with compatibility maps.
5. **Polygraphic conversion:** the finite semisimplicial set \(X\), its oriental attaching expressions, and the projection \(L_dK'\to K'\).
6. **Two marking lists:** the external cartesian generators \(Q\) and the localisation generators \(S\), together with the map to \(\Gamma\).

The universal proof of (6), the elementary-anodyne rules, and the semisimplicial pasting theorem are reusable proof-checker rules. Once those rules and the input certificates are accepted, the remaining checks concern finite maps, finite face identities, and explicitly listed elementary attachments.

The possible increase beyond \(n+m\) occurs in the finite anodyne expansions. The subsequent \(L_d\)-conversion introduces no cells above its chosen finite dimension \(d\).

## 3. Homotopicality of the whole base implies homotopicality of its skeleta

Under the stipulated cellular comparison,
\[
\boxed{\Gamma\text{ homotopical}\quad\Longrightarrow\quad
\Gamma_{\le r}\text{ homotopical for every }r.}
\]

Here is the proof.

### 3.1 Skeletal inclusions are discrete Conduché

Consider
\[
j_r:F(\Gamma_{\le r})\hookrightarrow F(\Gamma).
\]

For a strict cell \(u\), let \(\operatorname{gen}(u)\) be the set of generator labels used in a term for \(u\), together with the labels in their iterated boundaries. Strict unit, associativity, and interchange equations preserve this set. Moreover,
\[
\operatorname{gen}(1_u)=\operatorname{gen}(u),
\qquad
\operatorname{gen}(u*_k v)
=\operatorname{gen}(u)\cup\operatorname{gen}(v).
\]

A cell belongs to the skeletal subcategory precisely when this set uses no generators above dimension \(r\). Therefore:

- a factorisation of a skeletal cell as a composite has skeletal factors;
- an identity on a cell is skeletal only if that cell is skeletal;
- these lifted factorisations are unique, since \(j_r\) is an inclusion.

These are the discrete Conduché lifting conditions. Loubaton’s Theorem 2.2.2.10 therefore says that pullback along \(j_r\) preserves colimits. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 3.2 Pulling back the cellular comparison removes the higher attachments

Let \(X_d\) be the weak cellular construction through dimension \(d\), equipped with its comparison to \(F(\Gamma)\). Thus
\[
X_n=\operatorname{Free}(\Gamma).
\]

For \(d\le r\), the comparison factors through \(F(\Gamma_{\le r})\), so pulling back does not change \(X_d\).

For a generator \(q\) of dimension \(d>r\), the pullbacks satisfy
\[
D_d\times_{F(\Gamma)}F(\Gamma_{\le r})
=
\partial D_d\times_{F(\Gamma)}F(\Gamma_{\le r}).
\tag{9}
\]
The top cell of the globe maps to \(q\), which is not skeletal; all remaining globe cells lie in its boundary. This remains valid when some higher-dimensional boundary faces map to identities.

These are pullbacks of gaunt strict categories, so their strict pullbacks compute the corresponding higher-categorical pullbacks. Since \(j_r^*\) preserves colimits, (9) shows that each attachment above dimension \(r\) becomes an attachment along an identity and contributes nothing.

Consequently
\[
\operatorname{Free}(\Gamma)
\times_{F(\Gamma)}F(\Gamma_{\le r})
\simeq
\operatorname{Free}(\Gamma_{\le r}),
\]
and under this equivalence the pulled-back comparison is exactly
\[
\operatorname{Free}(\Gamma_{\le r})
\longrightarrow F(\Gamma_{\le r}).
\]

If the comparison for \(\Gamma\) is an equivalence, its pullback is an equivalence. This proves the assertion.

Thus “all skeleta are homotopical” and “\(\Gamma\) is homotopical” are equivalent hypotheses here. The finite-existence theorem in §2 can therefore be stated using only homotopicality of \(\Gamma\).

For the terminal weight, the presentation is simply
\[
\Psi=\Gamma,\qquad S=\varnothing,
\]
with all positive-dimensional generators marked. Its total is the identity fibration, and the comparison equivalence is its correctness certificate.
