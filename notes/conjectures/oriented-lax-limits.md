# Lax limits in oriented categories: is the unrestricted universal property consistent?

*Self-contained problem statement. No project context needed.*

## Background

**Oriented categories.** Gepner and Heine (*Oriented category theory*, arXiv:2510.10504) define an *oriented category* to be a category enriched in ∞Cat, the ∞-category of (∞,∞)-categories, with respect to the lax Gray tensor product (Campion, arXiv:2311.00205; Loubaton, arXiv:2406.05425).
- The main example is ∞Cat itself, whose hom-objects are Fun^lax(S, T).
- In an oriented category, the two ways of composing 2-cells β : u ⇒ u′ : c → L and φ : v ⇒ v′ : L → y are related by a *directed* interchange cell, not an invertible one. In execution order, its direction is

  ```
  (u◁φ) ; (β▷v′)  ⇛  (β▷v) ; (u′◁φ).
  ```

- Gepner–Heine's companion paper *Colimits in oriented category theory* (arXiv:2608.02592) studies oriented (co)limits.

**Lax cones.** For a finite diagram given by a computad Γ (e.g. a single arrow f : x → y), a lax cone with apex c consists of:
- projections p_x : c → x for each object x;
- for each arrow f : x → y, a cell p_f : p_y ⇒ p_x ; f;
- for each higher cell, the corresponding higher cells.

None of these is required to be invertible.

**Morphisms of lax cones (lax transfors).** A morphism m : P → Q of lax cones consists of:
- cells m_x : p_x ⇒ q_x;
- for each arrow f, a comparison cell m_f : p_f ; (m_x ▷ f) ⇛ m_y ; q_f;
- and so on, with Gray-tensor shapes.

In the *unrestricted* version, m_f is arbitrary. In the *pseudo* version, m_f must be invertible for every positive-dimensional diagram variable.

**What is known.** In an ordinary (cartesian-enriched) (∞,ω)-category, the unrestricted version cannot be the universal property of any limit object. A universal cone λ forces every m_f to be invertible, because ucone_*(β) has the invertible interchanger as its comparison cell. With the universal property imposed in all dimensions, every cell of dimension ≥ 3 is forced to be invertible as well. The pseudo version is the correct property there. (This is a verified result in the companion file `catt-lim-pseudo-vs-gray.md` of this folder.)

## The problems

Let 𝒦 be an oriented category, e.g. ∞Cat with lax transformations, and Γ a finite computad, starting with the single arrow x → y.

**Problem 1 (no collapse).** Show that the forced-invertibility argument does not go through in 𝒦. Concretely:
- define the lax limit L of a Γ-diagram in 𝒦 by the unrestricted universal property: an equivalence, natural in c, between 𝒦(c, L) and the (∞,ω)-category of lax cones with apex c and unrestricted lax transfors;
- show that this does *not* force the m_f, or any higher cells, to be invertible;
- ideally, exhibit an oriented category, such as ∞Cat, together with a diagram whose lax limit has a cone morphism with non-invertible m_f.

**Problem 2 (existence).** Does every finite diagram in ∞Cat, viewed as an oriented category, have a lax limit in the unrestricted sense? Is it Gepner–Heine's oriented limit? For the arrow diagram, is it the oriented comma/arrow construction, e.g. built from Fun^lax([1], –)?

**Problem 3 (comma and hom objects).** For the partially lax limit of ⊤ →a C ←b ⊤, with the b-comparison invertible and m unrestricted, is the result the full hom-object Hom_C(b, a), with non-invertible arrows? Compare the cartesian case, where the analogous construction gives only the maximal sub-∞-groupoid (Gagna–Harpaz–Lanari, arXiv:2012.04537).

## Why it matters

A type theory for higher categories needs limits whose universal property is stated by generic filler rules. The verified negative result shows that in an ordinary (cartesian) setting, lax cone morphisms must be restricted to pseudo ones, and that hom-objects then cannot be built as limits. This problem asks whether moving to oriented categories, where the relevant interchange is directed, restores the unrestricted lax universal property. If it does, comma and hom objects become limits again.

## What would count as a solution

Any of the following:
- a proof of Problem 1, or a counterexample showing that some other mechanism still forces invertibility in oriented categories;
- references settling Problems 2–3, e.g. from Gepner–Heine's oriented (co)limits;
- partial answers in the (∞,2) case, using Gray-enriched 2-categories and lax limits in the sense of Street and Lack.

## Status (updated 2026-11-18 after a verified researcher response)

**Answered.**
- *Problem 1: yes.* The unrestricted universal property does not collapse in ∞Cat. The forced-invertibility argument stops exactly where it needs the interchanger to be invertible.
- *Problem 2: yes, for every small diagram.* The construction is a weighted limit in the Gray self-enrichment of ∞Cat. For the arrow F : X → Y it is `Fun^oplax([1], Y) ×_{ev₁, Y, F} X`. This is Gepner–Heine's framework, but with the cone direction reversed relative to their named "oriented limit".
- *Problem 3: false as literally stated, true once corrected.* If m_b (the cone-morphism cell on the marked leg) is arbitrary, a finite strict 2-category shows that no limit exists. If transfors respect the marked leg coherently (m_b invertible, in every dimension), the limit is the full `Hom_C(b, a)`, with non-invertible higher cells. In the cartesian case the same construction gives only the core `Hom_C(b, a)^≃`.

**Correction to the problem statement:** in Problem 3, "m unrestricted" must exclude the marked leg; the marking has to be respected by cone morphisms and all higher transfors. See the verification at the end.

# Researcher Response

**The unmarked unrestricted universal property is consistent, and the arrow case has an explicit construction in \(\infty\mathrm{Cat}\).** There are two qualifications:

1. Your cone direction is opposite to the direction selected by Gepner–Heine’s particular weight called the *oriented-limit weight*. The construction below uses your stated boundaries.
2. **Problem 3 is false if “\(m\) unrestricted” includes an arbitrary \(m_b\).** Invertibility on the marked leg must be respected by cone morphisms and higher transfors. With that correction, the result is the full \(\operatorname{Hom}_C(b,a)\).

I give the constructions and proofs below.

## 1. Exactly where the forced-invertibility argument stops

Let \(F:X\to Y\), and suppose a cone
\[
\lambda_X:L\to X,\qquad
\lambda_Y:L\to Y,\qquad
\lambda_F:\lambda_Y\Rightarrow\lambda_X;F
\]
represents the unrestricted cone category.

For \(u,u':c\to L\) and \(\beta:u\Rightarrow u'\), the induced cone morphism has
\[
m_X=\beta\triangleright\lambda_X,
\qquad
m_Y=\beta\triangleright\lambda_Y.
\]
Its comparison is the interchanger
\[
\begin{aligned}
&(u\triangleleft\lambda_F);
   \bigl(\beta\triangleright(\lambda_X;F)\bigr)\\
&\hspace{2em}\Longrightarrow
   (\beta\triangleright\lambda_Y);
   (u'\triangleleft\lambda_F).
\end{aligned}
\tag{1}
\]
These are exactly your boundaries
\[
p_F;(m_X\triangleright F)\Longrightarrow m_Y;q_F.
\]

Consequently, representability implies that every cone morphism is equivalent to one whose comparison arises from an interchanger. **It does not imply that this comparison is invertible unless the relevant interchangers are invertible.**

This identifies the precise failed step in the cartesian argument. It does not, by itself, prove existence: an arbitrary oriented category can still lack the required limits. The following construction proves existence and noncollapse in the main example.

## 2. The arrow limit in \(\infty\mathrm{Cat}\)

Write
\[
\mathcal K(A,B)=\operatorname{Fun}^{\mathrm{lax}}(A,B)
\]
and define
\[
\operatorname{Arr}_{\mathrm{oplax}}(Y)
=
\operatorname{Fun}^{\mathrm{oplax}}([1],Y).
\]

For your cone direction, set
\[
\boxed{
L_F
=
\operatorname{Arr}_{\mathrm{oplax}}(Y)
\times_{\operatorname{ev}_1,Y,F}X.
}
\tag{2}
\]

Thus the arrow represented by a point of \(L_F\) ends at \(F(x)\). In strict low-dimensional notation, its data are
\[
(x,y,h),\qquad h:y\to F(x).
\]

A morphism
\[
(x,y,h)\longrightarrow(x',y',h')
\]
has data
\[
a:x\to x',\qquad b:y\to y',\qquad
\theta:h;F(a)\Longrightarrow b;h'.
\tag{3}
\]
There is no invertibility condition on \(\theta\).

The projections give \(\lambda_X,\lambda_Y\). The universal transformation \(\lambda_F\) has value \(h\) at \((x,y,h)\), and its naturality comparison at (3) is \(\theta\).

### Proof of the universal property in all dimensions

The relevant closure identity is **mixed lax–oplax**:
\[
\boxed{
\operatorname{Fun}^{\mathrm{lax}}
\bigl(c,\operatorname{Fun}^{\mathrm{oplax}}(A,Y)\bigr)
\simeq
\operatorname{Fun}^{\mathrm{oplax}}
\bigl(A,\operatorname{Fun}^{\mathrm{lax}}(c,Y)\bigr).
}
\tag{4}
\]

Here is a derivation that fixes the variance. Use Gepner–Heine’s tensor convention \(\boxtimes\), in which
\[
c\boxtimes(-)\dashv\operatorname{Fun}^{\mathrm{lax}}(c,-),
\qquad
(-)\boxtimes A\dashv\operatorname{Fun}^{\mathrm{oplax}}(A,-).
\]
These are their Notation 3.1.3. [arxiv.org](https://arxiv.org/html/2510.10504v2?utm_source=chatgpt.com)

For any test \(T\), maps from \(T\) into the left side of (4) correspond to maps
\[
(c\boxtimes T)\boxtimes A\longrightarrow Y.
\]
Maps into its right side correspond to maps
\[
c\boxtimes(T\boxtimes A)\longrightarrow Y.
\]
Associativity identifies these mapping spaces. No interchange cell is inverted.

Since \(\operatorname{Fun}^{\mathrm{lax}}(c,-)\) is a right adjoint, applying it to (2) gives
\[
\begin{aligned}
\mathcal K(c,L_F)
&\simeq
\operatorname{Fun}^{\mathrm{lax}}
 \bigl(c,\operatorname{Arr}_{\mathrm{oplax}}(Y)\bigr)
\times_{\mathcal K(c,Y)}\mathcal K(c,X)\\
&\simeq
\operatorname{Fun}^{\mathrm{oplax}}
 \bigl([1],\mathcal K(c,Y)\bigr)
\times_{\mathcal K(c,Y)}\mathcal K(c,X).
\end{aligned}
\tag{5}
\]

The last expression is a precise definition of your unrestricted cone category:

- A \(0\)-cell specifies \(p_X,p_Y\) and \(p_F:p_Y\Rightarrow p_X;F\).
- A \(1\)-cell specifies \(m_X,m_Y\) and
  \[
  m_F:p_F;(m_X\triangleright F)\Longrightarrow m_Y;q_F.
  \]
- Higher cells have the corresponding Gray shapes supplied by the oplax internal hom.

Equation (5) is an equivalence of \((\infty,\infty)\)-categories, natural in \(c\). It therefore establishes the universal property in every dimension.

There is also a published strict \(2\)-categorical version of precisely this argument: Mesiti’s Definition 4.4 and Proposition 4.5 give the full lax comma universal property in \(2\text{-}\mathrm{Cat}_{\mathrm{lax}}\), including arbitrary comparison modifications, and explicitly identify the comparison with the lax interchanger. [tac.mta.ca](https://tac.mta.ca/tac/volumes/41/30/41-30.pdf?utm_source=chatgpt.com)

### An explicit non-invertible \(m_F\)

Let \(Y=D^2\) be the walking non-invertible \(2\)-cell:
\[
r,s:b\to a,\qquad \alpha:r\Rightarrow s.
\]
Concretely,
\[
Y(b,a)=[1],\qquad
Y(a,a)=Y(b,b)=1,\qquad
Y(a,b)=\varnothing.
\]
Let \(F:1\to Y\) select \(a\).

At test apex \(c=1\), take the cones
\[
P=(b,r:b\to a),\qquad Q=(b,s:b\to a).
\]
There is a cone morphism
\[
m_X=\mathrm{id},\qquad
m_Y=\mathrm{id}_b,\qquad
m_F=\alpha.
\tag{6}
\]

Under (5), it corresponds to the morphism
\[
(\mathrm{id},\mathrm{id}_b,\alpha):
(*,b,r)\longrightarrow(*,b,s)
\]
of \(L_F\). Formula (1) evaluates to \(\alpha\). Because \([1]\) has no arrow from its terminal vertex back to its initial vertex, \(\alpha\) is not invertible.

Thus **a universal cone can induce a cone morphism whose comparison is non-invertible**.

There is no collapse in higher dimensions either. For each \(r\geq1\), take \(Y=D^{r+1}\) and let \(F:1\to Y\) select its target \(0\)-cell \(a\). The fiber of \(L_F\to Y\) over its source \(0\)-cell \(b\) is
\[
\operatorname{Hom}_{D^{r+1}}(b,a)\simeq D^r.
\tag{7}
\]
The fixed-endpoint fiber identification is Gepner–Heine, Proposition 3.6.4. [arxiv.org](https://arxiv.org/pdf/2510.10504v2?utm_source=chatgpt.com)

Its generating \(r\)-cell remains non-invertible in \(L_F\): an inverse would restrict to an inverse in the same fixed-endpoint fiber. Hence these arrow limits retain non-invertible cells in arbitrarily high dimensions.

## 3. General existence, and the precise relation to Gepner–Heine

### Existence

The general existence statement is:

> The Gray self-enrichment of \(\infty\mathrm{Cat}\) admits all small weighted limits, on either side.

The Gray tensor gives a presentably monoidal structure. Heine’s *The higher algebra of weighted colimits*, Lemma 3.69, says that a presentable category with left and right tensor actions preserving small colimits admits all small weighted limits. Apply that lemma to the regular Gray actions on \(\infty\mathrm{Cat}\). [arxiv.org](https://arxiv.org/html/2608.02592v1?utm_source=chatgpt.com)

Therefore **finiteness is unnecessary once the coherent Gray cone weight has been specified**. This proves existence for the standard weighted interpretation of your unrestricted cones.

For a higher computad, the phrase “and so on, with Gray-tensor shapes” must specify that coherent cone weight. The weighted construction supplies a precise interpretation; identifying a separately proposed collection of type-theoretic filler rules with it would still require a comparison proof.

### Your convention is a different cone weight

Gepner–Heine define their oriented limit as a **right \(W_{\mathrm{oplax}}^I\)-weighted limit** in Definitions 3.2.3–3.2.4 of *Colimits in Oriented Category Theory*. [arxiv.org](https://arxiv.org/html/2608.02592v1?utm_source=chatgpt.com)

Already for \(I=[1]\), this weight distinguishes their cone direction from yours. For an ordinary indexing category,
\[
W_{\mathrm{oplax}}^I(i)=I_{/i}.
\]
At the target of \([1]\), the structure map selects the initial vertex of the interval \(I_{/1}\). Consequently:

| Weight for \(F:X\to Y\) | Cone comparison | Representing pullback |
|---|---|---|
| Gepner–Heine’s \(W_{\mathrm{oplax}}^{[1]}\) | \(p_X;F\Rightarrow p_Y\) | \(\operatorname{Arr}_{\mathrm{oplax}}(Y)\times_{\operatorname{ev}_0,Y,F}X\) |
| Reverse cone weight | \(p_Y\Rightarrow p_X;F\) | \(\operatorname{Arr}_{\mathrm{oplax}}(Y)\times_{\operatorname{ev}_1,Y,F}X\) |

This table follows by evaluating their weight definition; the slice identification is also recorded in Proposition 3.3.8. [arxiv.org](https://arxiv.org/html/2608.02592v1?utm_source=chatgpt.com)

For an ordinary \(I\), the reverse weight can be written
\[
W^-(i)=(I_{/i})^{\mathrm{op}}.
\]
In their higher-dimensional weight notation, the corresponding choice is \(W_{\mathrm{lax}}^{I^\circ}\), used with the **right** weighted-limit convention appropriate to your ambient enrichment.

Thus the answer to “is it Gepner–Heine’s oriented limit?” is:

**It belongs to their Gray-enriched weighted-limit framework, but it is not literally their named oriented-limit convention with the displayed cone direction unchanged.** The arrow formula (2) removes that naming ambiguity.

## 4. Problem 3 as literally stated has an obstruction

Suppose “the \(b\)-comparison is invertible and \(m\) unrestricted” means:

- \(p_b\) is an equivalence;
- \(m_b\) may be arbitrary.

Then the proposed construction need not be representable.

### The extra morphisms

At apex \(1\), a cone over
\[
1\xrightarrow{a}C\xleftarrow{b}1
\]
has data
\[
z\in C,\qquad u:z\to a,\qquad e:z\xrightarrow{\simeq}b.
\]

Consider the normalized cones
\[
z=b,\qquad e=\mathrm{id}_b,
\]
so their remaining data are arrows \(u:b\to a\).

For two such cones \(u,v\), your cone-morphism formula gives
\[
h:b\to b,\qquad
\eta:\mathrm{id}_b\Rightarrow h,\qquad
\theta:u\Rightarrow h;v.
\tag{8}
\]

The cell \(\eta\) is \(m_b\). If it is arbitrary, (8) does not reduce to a \(2\)-cell \(u\Rightarrow v\).

### A finite strict \(2\)-category counterexample

Define \(C\) to have one \(0\)-cell \(*\), with
\[
C(*,*)=[1]=\{0<1\},
\qquad
r;s=\max(r,s),
\qquad
\mathrm{id}_*=0.
\tag{9}
\]
The operation \(\max\) is associative, unital with unit \(0\), and monotone, so this defines a strict \(2\)-category. Its only equivalence \(1\)-cell is \(0\).

Set \(a=b=*\). There are two normalized cones, indexed by \(u=0,1\). A morphism \(u\to v\) is an \(h\in\{0,1\}\) satisfying
\[
0\leq h,\qquad u\leq\max(h,v).
\tag{10}
\]

Taking
\[
u=1,\qquad v=0,\qquad h=1
\]
satisfies (10). Thus the literal cone category has a morphism from cone \(1\) to cone \(0\), whereas
\[
\operatorname{Hom}_C(*,*)=[1]
\]
has no morphism \(1\to0\).

### In fact, no universal cone represents this assignment

Suppose \(L\) represented it. Its universal cone would include an equivalence
\[
\lambda_b:p_C\Rightarrow\underline * 
\quad\text{in}\quad
\operatorname{Fun}^{\mathrm{lax}}(L,C).
\tag{11}
\]
Choose an inverse lax transformation.

Every value of both transformations at a \(0\)-cell of \(L\) must be \(0\), since \(0\) is the only equivalence \(1\)-cell of \(C\). For any arrow \(\beta:\ell\to\ell'\) of \(L\), their two naturality comparisons give
\[
0\leq p_C(\beta),
\qquad
p_C(\beta)\leq0.
\]
Hence
\[
p_C(\beta)=0.
\tag{12}
\]

Every cone morphism induced by the universal cone therefore has \(h=0\). But the morphism \(1\to0\) above requires \(h=1\). No invertible \(2\)-cell can identify those values: the hom-category in (9) is a poset.

The comparison at apex \(1\) cannot be an equivalence. This contradicts representability.

The mechanism is narrower than the original cartesian obstruction: **interchange with the invertible marked comparison must respect its inverse**. Allowing arbitrary \(m_b\) violates that requirement, even though interchange with an arbitrary unmarked comparison can remain non-invertible.

## 5. The coherently marked construction gives the full hom-object

The correction is to require transfors to respect the marked leg coherently. At the first morphism level this requires \(m_b\) in (8) to be invertible. Then
\[
\eta:\mathrm{id}_b\xRightarrow{\simeq}h
\]
allows transport of \(\theta:u\Rightarrow h;v\) to an arbitrary
\[
u\Rightarrow v.
\]
There is no invertibility requirement on this remaining cell.

In all dimensions, the precise construction is
\[
\boxed{
H=
\{(b,a)\}
\times_{C\times C}
\operatorname{Fun}^{\mathrm{oplax}}([1],C)
\simeq
\operatorname{Hom}_C(b,a).
}
\tag{13}
\]
The equivalence is exactly Gepner–Heine, *Oriented Category Theory*, Proposition 3.6.4; there is no opposite on the hom-object. [arxiv.org](https://arxiv.org/pdf/2510.10504v2?utm_source=chatgpt.com)

For every test \(c\), write \(D_c=\operatorname{Fun}^{\mathrm{lax}}(c,C)\). Applying preservation of pullbacks and mixed currying gives
\[
\begin{aligned}
\operatorname{Fun}^{\mathrm{lax}}(c,H)
&\simeq
\{(\underline b,\underline a)\}
\times_{D_c\times D_c}
\operatorname{Fun}^{\mathrm{oplax}}([1],D_c)\\
&\simeq
\operatorname{Hom}_{D_c}(\underline b,\underline a).
\end{aligned}
\tag{14}
\]
This proves the full enriched universal property.

It also explains the marking through the weight. At the central index of the cospan, your reverse cone weight is the walking span
\[
A\leftarrow R\to B.
\]
Inverting \(R\to B\) makes that weight equivalent to the interval \(B\to A\). Its endpoint values are fixed at \(b,a\), producing (13).

Gepner–Heine implement partial laxness by **localizing the weight**, not merely by selecting cone \(0\)-cells and retaining all morphisms between them. Definitions 3.3.3–3.3.6 and the enriched section construction in Notation 4.3.5 make this distinction precise. [arxiv.org](https://arxiv.org/html/2608.02592v1?utm_source=chatgpt.com)

### Cartesian comparison

Replacing the oplax internal hom in (13) by the cartesian internal hom gives
\[
\{(b,a)\}
\times_{C\times C}
\operatorname{Fun}([1],C)
\simeq
\operatorname{Hom}_C(b,a)^{\simeq}.
\tag{15}
\]
Gepner–Heine discuss this directly in §1.3: endpoint evaluation for the ordinary functor category is conservative, so its fixed-endpoint fibers are spaces. [arxiv.org](https://arxiv.org/html/2510.10504v2?utm_source=chatgpt.com)

Equations (13) and (15) give the requested distinction. The oriented construction retains arbitrary higher cells of \(\operatorname{Hom}_C(b,a)\). For generic filler rules, this requires unrestricted comparisons on unmarked legs and coherent compatibility with localization on marked legs.


---

## Verification of the researcher response (2026-11-18)

**Verdict: correct.** I checked every step against Gepner–Heine, *Oriented category theory* (arXiv 2510.10504v2), Gepner–Heine, *Colimits in oriented category theory* (arXiv 2608.02592v1), Mesiti (TAC 41(30), 2024) and Mikhail's conventions as used in `catt-lim-pseudo-vs-gray.md`.

**§1, where the argument stops.** The cone morphism induced by β : u ⇒ u′ has m_X = β▷λ_X and m_Y = β▷λ_Y. Its comparison (1) is the interchanger of β with λ_F. With φ = λ_F : λ_Y ⇒ λ_X;F, this is the background's interchanger `(u◁φ);(β▷v′) ⇛ (β▷v);(u′◁φ)`, and its boundaries are `p_F;(m_X▷F) ⇛ m_Y;q_F`. Correct. Representability gives "every cone morphism is induced", not "every cone morphism is invertible". This is also the internal re-derivation of R11 that open-issues B8 asked for, so that part is done.

**§2, the arrow limit.**
- GH Notation 3.1.3 confirms the conventions: `C ⊠ (−) ⊣ Fun^lax(C, −)` and `(−) ⊠ C ⊣ Fun^oplax(C, −)`.
- From these, `Fun^lax(c, Fun^oplax(A, Y))` and `Fun^oplax(A, Fun^lax(c, Y))` both classify maps out of `c ⊠ T ⊠ A`, which proves the mixed currying (4) by associativity alone. Correct.
- (5) follows because `Fun^lax(c, −)` is a right adjoint and so preserves the pullback. Correct.
- The cone category is *defined* as the right side of (5). This is the right definition: (5) is natural in c, so the morphisms it contains are exactly those induced by interchangers in 𝒦. The labels "lax" and "oplax" therefore cannot be mismatched.
- Mesiti's Definition 4.4 and Proposition 4.5 (lax comma objects in 2-Cat_lax, with the full universal property) exist as cited.
- *Non-invertible m_F.* Take Y = D² and F picking out a. The fiber of L_F over b is `Mor_Y(b, a) = [1]` (GH Prop. 3.6.4), and (id, id_b, α) lies in it, so it is not invertible. The D^{r+1} version gives non-invertible r-cells for every r. Correct.

**§3, existence and convention.**
- GH-colimits cites Heine's *The higher algebra of weighted colimits* (arXiv 2406.08925) as [18], and uses its Lemma 3.69 in the way the response describes. I did not open Heine's paper itself.
- GH-colimits Definition 3.2.3 defines the oriented limit as the right `W^C_oplax`-weighted limit, as stated.
- I did not re-derive the response's orientation table, i.e. that GH's named convention gives the opposite cone direction. Nothing depends on it, because formula (2) states the cone direction explicitly.

**§4, the Problem 3 obstruction.**
- *The example 2-category.* C has one object, hom-poset [1], composition max, and unit 0. This is a strict 2-category whose only equivalence 1-cell is 0. For normalized cones over `1 → C ← 1`, a morphism is h with `0 ≤ h` (this inequality is m_b) and `u ≤ max(h, v)`. Then (u, v, h) = (1, 0, 1) is a cone morphism from cone 1 to cone 0. Correct.
- *Non-representability.* A universal cone's λ_b is an equivalence of lax transformations. Its components are equivalences, hence 0. Its naturality cells give `p_C(β) ≤ 0` for every arrow β of L, so `p_C(β) = 0`. Every induced morphism therefore has h = 0. The hom-categories are posets, so no 2-cell can identify a morphism with h = 1 with one with h = 0, and full faithfulness fails. Correct.

**§5, the corrected construction.** `H = {(b, a)} ×_{C×C} Fun^oplax([1], C) ≃ Hom_C(b, a)` is GH Prop. 3.6.4. (14) follows from pullback preservation and (4) as in §2, so H has the stated enriched universal property. This part is fully checked.
- The identification of `Hom_{D_c}(b, a)` with the coherently marked cone category is checked at the first morphism level: transport along the invertible η. In higher dimensions it is argued through localizing the weight (GH-colimits Defs 3.3.3–3.3.6). I checked that this mechanism is the one Gepner–Heine use, but not the identification line by line.
- (15), the cartesian case, is standard and is discussed in GH §1.3.

**What this settles, and what it opens.**
- Settled: Problems 1 and 2, and Problem 3 as corrected. In an oriented ambient, cone-morphism comparison cells may be unrestricted on unmarked legs and must be coherently invertible on marked legs. Contrast the cartesian (CaTT) ambient of `limits-representables.md`, where every comparison cell over a positive-dimensional diagram variable has to be certified invertible.
- Open (internal, design): restate the limit rules over the L core so that their cone and transfor shapes match the right side of (5). This is open-issues B7. Generic filler rules still need a comparison proof against the weighted limit (response §3, last paragraph).
- Nothing in this file needs to go back to a researcher.

## Internal strict proof for general diagrams (2026-11-18)

`limits-metatheory.md` §1 (Theorem A) proves the strict analogue for **every finite computad**, not only the arrow. In strict ω-categories, self-enriched by the Ara–Maltsiniotis Gray tensor, build the lax limit by attaching generators: one pullback of a Gray cotensor per generator. Then `𝒦(c, lim) ≅ Cone(c)` is an isomorphism of strict ω-categories, by the same two facts used in §2 above (mixed currying and pullback preservation).

Its marked case agrees with the corrected Problem 3. Making the marked cone cell an identity also makes every transfor comparison on that leg an identity, so the marking is respected coherently.
