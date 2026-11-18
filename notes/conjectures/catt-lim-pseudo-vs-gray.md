# Does CaTT_lim force cone morphisms to be pseudo?

## Background

**CaTT** (Finster–Mimram, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory whose models are Grothendieck–Maltsiniotis weak ω-categories (Benjamin–Finster–Mimram, [2106.04475](https://arxiv.org/abs/2106.04475)).
- Its types are `⋆` and `t →_A u`.
- Its only term former is `coh_{Γ, t→u}[σ]` over a pasting-scheme context Γ, with a free-variable side condition.
- Because that side condition is symmetric in t and u, every coherence has an inverse coherence. Benjamin–Markakis ([2406.12127](https://arxiv.org/abs/2406.12127)) show coherences are coinductively invertible, and that coinductive equivalences are closed under composition.

**CaTT_lim** (T. J. Mikhail, *A type-theoretic definition of lax (∞,∞)-limits*, [arXiv 2412.13310](https://arxiv.org/abs/2412.13310), Def. 4.15) extends CaTT with:
- a judgment `K cone(Γ; c)` that generates the context of lax cones with apex c over a diagram context Γ;
- a universal cone `ucone_{Γ,x}`;
- judgments `ctrf` generating "conical (n+1)-transfors", which are morphisms of cones, morphisms between those, and so on. Their shapes follow a Gray tensor `M ⊗ Dⁿ`: each cone variable is duplicated and joined to its copy by a connecting cell. **These connecting cells are not required to be invertible.**
- a filler schema `uni`, which states that `ucone_* : Hom(c, lim_Γ) → Cones(Γ; c)` is essentially surjective on cells of every dimension. "Essentially" is witnessed by invertible cells in a judgment `⊨`.

## Statement

Let Γ = `(x:⋆, y:⋆, f : x → y)` and let `L = lim_Γ`. Take two 1-cells `u, u' : c → L` and a 2-cell `β : u → u'`.

1. The cone morphism `ucone_*(β)` has a connecting cell at f. It relates the two composites of `ucone_f` (a 2-cell along `L → ·`) and β (a 2-cell along `c → L`). **Show that this cell is an interchange coherence, and hence invertible in every model of CaTT_lim.**
2. Deduce from the 2-dimensional instance of `uni` that for *every* cone morphism `m` (a `ctrf` context with n = 1), the connecting cell `m_f` is invertible. That is, an inverse for the variable `m_f` is derivable in CaTT_lim.
3. Conclude, or refute: in the (∞,ω)-category of (∞,ω)-categories with *cartesian* hom-objects, where 2-cells are pseudo-natural transformations and non-invertible modifications exist, the lax limit of a non-trivial arrow does **not** satisfy CaTT_lim's universal property as written.
4. Determine the corrected universal property in that setting. The conjecture is: the same rules with every `ctrf` connecting cell over a positive-dimensional cone variable placed in `⊨`. Also determine what the original rules *do* model. The conjecture is: (∞,ω)-categories enriched over the **Gray** tensor, i.e. "oriented" categories in the sense of Gepner–Heine ([2608.02592](https://arxiv.org/abs/2608.02592)).

## A consequence to check

If (1)–(3) hold, take the cartesian setting and the partially lax limit of `⊤ →a C ←b ⊤` with the b-leg invertible. Its points are arrows `b → a` of C, but its arrows are only the **invertible** 2-cells of C. The genuine hom-object `Hom_C(b, a)` is instead the fibre of the *oplax arrow object*, which is characterised through the Gray tensor. This matches the (∞,2) fact that mapping categories are fibres of `Ar^oplax(C) → C × C`, not of `Fun([1], C)` (Gagna–Harpaz–Lanari, [2012.04537](https://arxiv.org/abs/2012.04537)) **[recalled, please verify]**.

## What is known

- Step 1 seems to need only that `ucone_*` is computed by whiskering, which is how Mikhail defines it (§4.3–4.4).
- Step 2 uses invertibility of `⊨` cells and closure of coinductive equivalences under composition (Benjamin–Markakis).
- The worry is whether the paper's `ctrf` connecting cells are oriented so that the cell in step 1 is literally the one in the `ctrf` context. Rules KE and pctrf of Def. 4.15 fix this through σCond/τCond.

### Literature search (2026-11-18)
- **No answer found.** Mikhail's thesis (*Type Theory for (∞,∞)-Categories, and Decomposition Spaces*, UAB; [record](https://ddd.uab.cat/record/321550)) restates the arXiv results. It does not discuss whether cone morphisms are invertible, or pseudo vs lax limits.
- No follow-up paper on CaTT_lim was found.

## Why it matters

A type theory for higher categories with limits has to decide whether its ambient's 2-cells are pseudo or lax transformations. If CaTT_lim's universal property already forces one choice, that decides which semantics the rules can have and which constructions (hom objects, lax functor objects) they can produce.

## What would count as a solution

One of:
- a derivation of (2) in CaTT_lim;
- an identification of where the argument fails, with the correct orientation of `ctrf` cells;
- a precise statement of which enriched setting CaTT_lim's rules are sound for.

# Researcher Response

**Your interchange obstruction is correct for the universal property described in §§4.3–4.4.** Under that interpretation, an inverse for \(m_f\) can be constructed explicitly. Requiring the same property in every dimension has a stronger consequence: it forces ambient cells of every dimension \(\geq 3\) to be invertible.

There is, however, a distinction between that intended universal property and **Definition 4.15 literally as printed**. I found a concrete problem in the `ctrf` side conditions that prevents the expected boundary of \(m_f\) from passing the recognition rule. Thus the calculation below proves the implication for the intended cone calculus, and identifies the syntactic repair needed before calling it a derivation in the published theory.

The proposed Gray interpretation also needs correction: **general oriented categories cannot model unchanged CaTT**, because changing the enrichment does not remove CaTT’s existing invertible interchange terms.

## 1. The orientation and the interchange calculation

Write composition in execution order: \(a;b\) means first \(a\), then \(b\). Write \(\triangleleft,\triangleright\) for left and right whiskering.

A cone \(P\) over \(f:x\to y\) has

\[
p_x:c\to x,\qquad p_y:c\to y,\qquad
p_f:p_y\Rightarrow p_xf.
\]

For two cones \(P,Q\), the intended conical 2-transfor \(m:P\to Q\) has

\[
m_x:p_x\Rightarrow q_x,\qquad
m_y:p_y\Rightarrow q_y,
\]

and

\[
\boxed{
m_f:
p_f;(m_x\triangleright f)
\;\Longrightarrow\;
m_y;q_f.
}
\tag{1}
\]

Both boundaries are 2-cells \(p_y\Rightarrow q_xf\). This is the conical version of the modification boundary displayed in Mikhail’s Example 4.2, using his orientation of cones. [arxiv.org](https://arxiv.org/html/2412.13310v2?utm_source=chatgpt.com)

Let the universal cone be

\[
\lambda_x:L\to x,\qquad
\lambda_y:L\to y,\qquad
\lambda_f:\lambda_y\Rightarrow\lambda_xf,
\]

and put \(F=\mathrm{ucone}_*\). For \(\beta:u\Rightarrow u'\),

\[
(F\beta)_x=\beta\triangleright\lambda_x,\qquad
(F\beta)_y=\beta\triangleright\lambda_y.
\]

Suppressing associators temporarily, its \(f\)-comparison is

\[
\boxed{
(u\triangleleft\lambda_f);
\bigl(\beta\triangleright(\lambda_xf)\bigr)
\;\Longrightarrow\;
(\beta\triangleright\lambda_y);
(u'\triangleleft\lambda_f).
}
\tag{2}
\]

This has exactly the orientation in (1).

### Why (2) is an invertible CaTT coherence

Take a pasting-scheme context consisting of two horizontally composable 2-cells

\[
\beta:u\Rightarrow u',
\qquad
\phi:v\Rightarrow v'.
\]

The parallel 2-cells

\[
S=(u\triangleleft\phi);(\beta\triangleright v'),
\qquad
T=(\beta\triangleright v);(u'\triangleleft\phi)
\]

use every variable of that context. The symmetric fullness premises of `(COH)` therefore give

\[
I_{\beta,\phi}=\operatorname{coh}_{\mathcal P,S\to T}.
\]

Substituting

\[
v=\lambda_y,\qquad v'=\lambda_xf,\qquad \phi=\lambda_f
\]

gives (2). Reversing \(S,T\) gives its inverse, and higher coherences give the cancellation witnesses. Benjamin–Markakis’s Proposition 16 proves coinductive invertibility of such coherences; their Theorem 33 proves closure under composition. [arxiv.org](https://arxiv.org/html/2412.13310v2?utm_source=chatgpt.com)

With actual binary parenthesizations, there is a small qualification. The cone comparison for \(F(u)\) must end at

\[
(u\lambda_x)f,
\]

whereas \(u\triangleleft\lambda_f\) ends at

\[
u(\lambda_xf).
\]

Consequently, the complete term also uses associators and their naturality coherences. It is therefore **an interchanger with invertible coherence adjustments**, not necessarily one term whose outermost constructor is `coh`.

That establishes the invertibility needed in step 1. Neither \(\beta\) nor \(\lambda_f\) needs to be invertible.

## 2. An explicit inverse for \(m_f\)

First suppose that

\[
P=F(u),\qquad Q=F(u').
\]

The intended dimension-two `uni` instance supplies a 2-cell \(\beta:u\Rightarrow u'\) and an invertible higher transfor

\[
E:m\Rightarrow F(\beta).
\]

The comparison context here is a **conical 3-transfor**, so its parameter is \(n_M=2\), although \(m\) itself is a conical 2-transfor. Write \(n=F(\beta)\). The relevant entries are

\[
E_x:m_x\Longrightarrow n_x,\qquad
E_y:m_y\Longrightarrow n_y,
\]

together with a 4-cell

\[
E_f:
m_f;B
\;\Longrightarrow\;
A;n_f,
\tag{3}
\]

where the 3-cells \(A,B\) are

\[
A=1_{p_f}*_1(E_x\triangleright f),
\qquad
B=E_y*_1 1_{q_f}.
\]

Here \(*_1\) denotes composition along a 1-dimensional boundary. Explicitly,

\[
\begin{aligned}
A:\;&p_f;(m_x\triangleright f)
 \Longrightarrow p_f;(n_x\triangleright f),\\
B:\;&m_y;q_f
 \Longrightarrow n_y;q_f.
\end{aligned}
\]

Thus (3) has matching boundaries. The `uni` rule’s \(J_2\) conclusion certifies \(E_x,E_y,E_f\) as invertible; these are the entries introduced after the lifted \(\beta\) in equations (11)–(13). [arxiv.org](https://arxiv.org/html/2412.13310v2?utm_source=chatgpt.com)

Set

\[
R=m_f,\qquad N=n_f.
\]

Then:

- \(A,B\) are invertible because they are whiskerings of \(E_x,E_y\);
- \(N\) is invertible by the interchange calculation;
- \(E_f\) is an invertible 4-cell \(R;B\Rightarrow A;N\).

An inverse candidate for \(R\) is therefore

\[
\boxed{
R^{-1}=B;N^{-1};A^{-1}.
}
\tag{4}
\]

The two cancellation calculations are

\[
\begin{aligned}
R;R^{-1}
&\simeq R;B;N^{-1};A^{-1}\\
&\simeq A;N;N^{-1};A^{-1}\\
&\simeq 1,
\end{aligned}
\]

and

\[
\begin{aligned}
R^{-1};R
&\simeq B;N^{-1};A^{-1};R\\
&\simeq B;N^{-1};A^{-1};R;B;B^{-1}\\
&\simeq B;N^{-1};A^{-1};A;N;B^{-1}\\
&\simeq 1.
\end{aligned}
\]

The middle step in each calculation uses \(E_f\); the other steps use associativity and cancellation data for \(A,B,N\). All these witnesses are invertible, so the construction supplies coinductive inverse data.

This proves the desired implication without assuming that \(m_x\) or \(m_y\) is invertible.

### Arbitrary cone endpoints

The dimension-two instance directly treats morphisms between image cones. For arbitrary \(m:P\to Q\), one also needs the dimension-one instance.

It supplies invertible cone morphisms

\[
e:P\to F(u),\qquad d:Q\to F(u').
\]

Form

\[
\widetilde m=e^{-1};m;d:F(u)\to F(u').
\]

The preceding calculation makes \(\widetilde m_f\) invertible. In the formula for \(\widetilde m_f\), the \(f\)-comparisons contributed by \(e^{-1},d\) are invertible, and the whiskerings applied to \(m_f\) use invertible lower cells. Such whiskering reflects invertibility: whisker back using the chosen inverse and cancel.

Hence \(m_f\) is invertible.

So step 2 is valid for the intended calculus, with this qualification:

> For image endpoints, use dimension-two `uni`. For arbitrary endpoints, also use dimension-one `uni` and composition of cone transfors.

### An inverse term is different from the judgment \(\models\)

The construction above gives inverse and cancellation terms. It does **not** derive the literal judgment

\[
\Omega\models m_f:A.
\]

The printed rules have no rule recognizing an arbitrary term as marked from supplied inverse data. The outermost constructors of marked terms are `uni`, `inv`, `eta`, and `eps`; substitution preserves those constructors. Consequently, a marked judgment whose term is a variable \(m_f\) cannot be derived from those rules alone. [arxiv.org](https://arxiv.org/pdf/2412.13310v2?utm_source=chatgpt.com)

Thus “\(m_f\) has derivable coinductive inverse data” and “\(m_f\) is derivably marked by \(\models\)” must be kept distinct.

## 3. The obstruction in the printed `ctrf` rule

Here is the concrete reason I cannot label the preceding argument a literal derivation from Definition 4.15.

The definition of \(\delta\mathrm{Cond}\), for both \(\delta=\sigma\) and \(\delta=\tau\), selects earlier joining cells \(p\) using

\[
y\propto\tau(p),
\qquad
y\in\operatorname{FV}\bigl(\delta(x):\partial X\bigr).
\tag{5}
\]

The `pctrf` rule reuses this condition for the source of a new joining cell. [arxiv.org](https://arxiv.org/html/2412.13310v2?utm_source=chatgpt.com)

Apply it to the proposed source of \(m_f\):

\[
s=p_f;(m_x\triangleright f).
\]

The required condition is

\[
\tau\mathrm{Cond}\bigl(s,p_f,\{m_x,m_y\}\bigr).
\]

But

\[
\tau(p_f)=p_xf,\qquad
\tau(m_x)=q_x,\qquad
\tau(m_y)=q_y.
\]

Neither \(q_x\) nor \(q_y\) belongs to \(\operatorname{FV}(p_xf)\). Therefore the selector in (5) selects neither \(m_x\) nor \(m_y\). Its prescribed free-variable set omits \(m_x\), although \(s\) uses \(m_x\).

**The intended source of \(m_f\) fails the printed side condition.**

This is not a choice between two opposite orientations of the same valid cell. The displayed recognition rule does not recognize the expected cell. Locally, its source test needs to select joining cells through their sources, while its target test selects them through their targets.

There is also a dependency-renaming issue: copying \(x:X\) as \(x':X\) literally copies \(p_f:p_y\Rightarrow p_xf\) as another cell with those same boundaries, whereas the second cone needs

\[
q_f:q_y\Rightarrow q_xf.
\]

These observations explain the status of the proof:

- The equations and examples describe a cone calculus for which the invertibility argument works.
- The printed recognition rules require repair before that argument becomes a derivation in the formal system.

## 4. A stronger consequence and a concrete cartesian counterexample

### The intended property forces every ambient 3-cell invertible

This is a deduction from the preceding argument.

Take an arbitrary ambient 3-cell

\[
z:a\Longrightarrow b,
\qquad
a,b:r\Rightarrow s,
\qquad
r,s:c\to Y.
\]

Specialize the diagram arrow to

\[
1_Y:Y\to Y.
\]

Choose cones with repeated legs

\[
P_x=P_y=r,\qquad Q_x=Q_y=s,
\]

and choose their comparisons

\[
P_f:r\Rightarrow r1_Y,\qquad
Q_f:s\Rightarrow s1_Y
\]

to be inverse right unitors. Set

\[
m_x=a,\qquad m_y=b.
\]

The required \(f\)-comparison has type

\[
m_f:
P_f;(a\triangleright1_Y)
\Longrightarrow
b;Q_f.
\]

Invertible unit coherences identify its source with \(a\) and its target with \(b\). Pasting those coherences with \(z\) produces such an \(m_f\), and

\[
m_f\text{ invertible}
\quad\Longleftrightarrow\quad
z\text{ invertible}.
\]

Step 2 therefore forces \(z\) invertible.

The same argument extends dimension by dimension. For an ambient \(d\)-cell \(\alpha\), \(d\ge2\), the generic categorical data used to construct \(F(\alpha)_f\) have dimension at most \(d\), while \(F(\alpha)_f\) has dimension \(d+1\). It is therefore invertible by the empty-support criterion of Benjamin–Markakis, Proposition 35. Higher `uni` compares arbitrary transfors with these images; the identity-arrow specialization places any ambient \((d+1)\)-cell in that comparison position. [arxiv.org](https://arxiv.org/pdf/2406.12127?utm_source=chatgpt.com)

Under the intended full cone calculus, the unrestricted universal property thus forces the invertibility profile of an \((\infty,2)\)-category. **Higher `uni` is used at every dimension**; invertibility of all 3-cells alone would not imply invertibility of all 4-cells.

This is a necessary restriction on the intended models, not a proof that the theory’s models are exactly \((\infty,2)\)-categories with finite lax limits.

### A finite counterexample to the proposed cartesian semantics

A concrete cartesian ambient is the self-enrichment of bicategories. Its hom bicategories are biequivalent to those of pseudofunctors, pseudonatural transformations, and arbitrary modifications; Campbell describes this in §§9.1–9.2. [acmbl.github.io](https://acmbl.github.io/coherentnerve.pdf?utm_source=chatgpt.com)

Define a strict 2-category \(C\) by

\[
C(b,b)=C(a,a)=1,\qquad
C(a,b)=\varnothing,\qquad
C(b,a)=[1].
\]

Write the nonidentity arrow of \(C(b,a)\) as

\[
\alpha:f\Rightarrow g,
\qquad f,g:b\to a.
\]

Thus \(\alpha\) is noninvertible, and \(C\) has no nonidentity equivalences or invertible 2-cells.

Consider the single-arrow diagram

\[
a:1\to C.
\]

There are two cones with apex \(1\), whose \(C\)-leg selects \(b\), with respective comparisons \(f\) and \(g\). There is an unrestricted cone morphism between them whose vertex entries are identities and whose arrow comparison is \(\alpha\).

Suppose a universal cone were given by

\[
L,\qquad P:L\to C,\qquad
\tau:P\Rightarrow a!,
\]

with \(\tau\) pseudonatural.

Essential surjectivity on cones supplies points \(x_f,x_g\in L\) satisfying

\[
P(x_f)=P(x_g)=b,\qquad
\tau_{x_f}=f,\qquad\tau_{x_g}=g.
\]

The equalities follow because all equivalences and invertible 2-cells available in \(C\) are identities.

Lifting the displayed cone morphism would supply an arrow

\[
h:x_f\to x_g.
\]

Necessarily \(P(h)=1_b\). Pseudonaturality of \(\tau\) at \(h\) would then require an invertible 2-cell between \(f\) and \(g\), which does not exist.

Therefore **no universal cone with a pseudonatural connector satisfies the unrestricted property in this example**.

This establishes failure of general soundness in the proposed cartesian setting. It does not establish failure for every nonidentity diagram arrow; nonidentity alone is not the relevant condition.

## 5. The corrected universal property

For the stated cartesian setting, the appropriate property is

\[
\boxed{
\operatorname{Hom}_{\mathcal A}(c,L)
\simeq
\operatorname{Cone}^{\mathrm{lax},\mathrm{ps}}_\Gamma(c),
}
\tag{6}
\]

naturally in \(c\).

The right-hand side has lax cones as its 0-cells. Its higher transfors have arbitrary entries at diagram vertices and invertible compatibility cells indexed by positive-dimensional diagram cells.

For the first few dimensions:

| Diagram generator | Cone datum | Cone morphism datum | Next transfor datum |
|---|---|---|---|
| \(x\), dimension \(0\) | \(p_x\), arbitrary 1-cell | \(m_x\), arbitrary 2-cell | \(E_x\), arbitrary 3-cell |
| \(f\), dimension \(1\) | \(p_f\), arbitrary 2-cell | \(m_f\), invertible 3-cell | \(E_f\), invertible 4-cell |
| \(\alpha\), dimension \(2\) | \(p_\alpha\), arbitrary 3-cell | \(m_\alpha\), invertible 4-cell | \(E_\alpha\), invertible 5-cell |

This is the marking prescription your conjecture needs, with two qualifications.

**First, the index is a positive-dimensional diagram variable.** Every cone projection \(p_x\) already has positive dimension. Marking every joining cell over a positive-dimensional *projection* would also mark the vertex entries \(m_x\), excluding the noninvertible pointwise cells that should remain available.

**Second, the marking must restrict admissible inputs to `uni`.** It must not be a rule asserting that an arbitrary previously declared variable \(m_f\) is invertible. A syntactic implementation needs marked declarations, with substitutions required to supply equivalence certificates for those declarations. Otherwise the alleged repair repeats the original collapse.

For the arrow diagram, (6) gives the exact repair of the demonstrated obstruction: retain arbitrary \(p_f,m_x,m_y\), and quantify only over invertible \(m_f\), with the analogous condition at higher transfor levels.

For arbitrary computads, this describes the required semantic universal property. Turning it into a complete corrected CaTT presentation still requires repairing the recognition rules and proving the associated substitution, composition, and soundness results.

## 6. Why the unchanged rules do not instead model oriented categories

Gepner–Heine define oriented categories through enrichment in the directed Gray tensor product. Their Remark 3.2.3 explicitly explains that a general oriented category does not have an underlying ordinary higher category with the same higher cells: ordinary interchange fails. Theorem 4.2.7 characterizes the ordinary higher categories among oriented categories by an interchange condition factoring through the cartesian product. [arxiv.org](https://arxiv.org/html/2510.10504v2?utm_source=chatgpt.com)

That distinction is exactly relevant here.

CaTT already supplies an invertible 3-cell between the two composites in (2). A general directed Gray enrichment supplies a directed interchanger that need not be invertible. Interpreting the existing CaTT interchanger as that noninvertible cell would fail to interpret its existing inverse and cancellation terms.

Thus:

- **Keeping CaTT and restricting cone transfors** gives the cartesian repair in (6).
- **Keeping unrestricted lax transfors and allowing noninvertible mixed interchangers** requires changing the underlying categorical theory.

The second direction is compatible with the motivation of oriented category theory. It is not a semantics for unchanged \(\mathrm{CaTT}_{\mathrm{lim}}\).

What can be said about the original intended property is more restrictive: with ordinary CaTT interchange and all the asserted `uni` levels, the argument above forces cells of dimension \(\ge3\) invertible. I do not have a model-classification theorem beyond that necessary condition.

## 7. The partially lax limit and the arrow-object fibre

Your recalled \((\infty,2)\) distinction is correct, including the **oplax** orientation.

Using Gagna–Harpaz–Lanari’s notation,

\[
\operatorname{Ar}^{\mathrm{oplax}}(C)
=
\operatorname{Fun}^{\mathrm{opgr}}([1],C).
\]

Their mapping-category definition and Gray internal-hom definitions give

\[
\boxed{
\operatorname{fib}_{(b,a)}
\left(
\operatorname{Ar}^{\mathrm{oplax}}(C)\to C\times C
\right)
\simeq
\operatorname{Hom}_C(b,a).
}
\tag{7}
\]

For the cartesian internal hom,

\[
\boxed{
\operatorname{fib}_{(b,a)}
\left(
\operatorname{Fun}([1],C)\to C\times C
\right)
\simeq
\operatorname{Hom}_C(b,a)^{\simeq}.
}
\tag{8}
\]

These formulas follow from Notation 1.2.13 and §1.3; Remark 4.2.6 independently identifies the corresponding slice fibres with the mapping \(\infty\)-category. [arxiv.org](https://arxiv.org/html/2012.04537v2?utm_source=chatgpt.com)

The distinction can be checked directly. An arrow between \(f,g:b\to a\) in either fibre has identity endpoint arrows. Its remaining comparison is

\[
1_a\circ f\Longrightarrow g\circ1_b.
\]

In the oplax fibre, this is an arbitrary 2-cell \(f\Rightarrow g\). In the cartesian fibre, pseudonaturality requires it to be invertible. In the \((\infty,2)\) case, this gives precisely the maximal \(\infty\)-groupoid of the mapping category.

For the partially lax limit

\[
1\xrightarrow{a}C\xleftarrow{b}1
\]

with the \(b\)-comparison invertible, normalize that comparison to the identity. The remaining cone datum is an arrow \(b\to a\). With the pseudo cone-transfor convention of (6), its arrows are invertible 2-cells between those arrows.

The full core identification (8) is verified here for \((\infty,2)\)-categories; the same boundary calculation establishes the claimed distinction between points and arrows in your higher setting.

For the finite \(C\) used above, the difference is

\[
\operatorname{Hom}_C(b,a)
=
\bigl(f\xrightarrow{\alpha}g\bigr),
\qquad
\operatorname{Hom}_C(b,a)^{\simeq}
=
\{f,g\}_{\mathrm{disc}}.
\]

The oplax arrow fibre retains \(\alpha\); the cartesian arrow fibre does not.
