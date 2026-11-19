# Canonical CaTT terms for the cells of Gray tensors of pasting diagrams

*A self-contained problem. It assumes familiarity with the type theory CaTT, strict ω-categories and Steiner's directed complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** A construction for **all** pairs (and finite families) of pasting diagrams, or a proof that none exists. The question is purely syntactic: whether chosen terms can be made to match their boundaries on the nose, in a theory with no definitional equalities.

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

1. **Low dimensions.** For Θ, Δ of dimension ≤ 1, binary composites can be chosen consistently by hand.
2. **D² ⊗ D¹: CT holds.** With binary composites for two-edge paths and whiskering coherences typed `f ∗ h ⇒ g ∗ h`, all boundaries of the layers agree syntactically.
3. **D¹ ⊗ D¹ ⊗ D¹: CT fails for every T built from layerings.** Here "layered" means T(c) is the vertical composite, along a layering of the molecule c, of whiskered generators. The source hexagon of the top cell has a unique layering whose first two layers are a square whiskered on the right and a square whiskered on the left, meeting at a 3-edge path. The first layer's target contains a subterm denoting the 2-edge path bc, and no subterm of the second layer's source denotes bc (in CaTT every term uses exactly the variables of its strict image). So the two sides bracket the 3-edge path differently, and (c) fails.
4. **The weak form holds through dimension 4.** Replace (c) by (c′): T(c) has a type `u → v` with u, v connected to T(∂⁻c), T(∂⁺c) by invertible coherence cells, and the context is made well formed by inserting these coherences into the variables' types. (c′) holds for every generator of dimension ≤ 4: conjugate each layer by associators to a fixed bracketing of paths (dimension ≤ 3), and use that any two parallel 2-terms of any context with equal strict image are connected by a 3-term (dimension 4). In higher dimensions (c′) follows from the analogous statement for parallel (n−2)-terms in loop-free contexts.
5. **Single coherence heads do not avoid the problem directly.** Taking T(c) to be one composition coherence `coh_{P, u→v}[σ]` per cell requires T(∂^±c) to be literally of the form u[σ], v[σ] for terms u, v over P. This fails when the boundary is a composite of lower cells that are not among σ's arguments.
6. **Semantics is settled.** The (∞,ω) Gray tensor of pasting diagrams is the free (∞,ω)-category on the Steiner tensor (Campion, arXiv 2311.00205, Cor. 3.5; Chanavat, arXiv 2603.22242, Thm 3.29). CT is only about syntax.

## 4. Questions

**Q1 (main).** Decide CT for all Θ, Δ. Item 3 rules out layered terms only. A positive answer may use any terms: non-layered composites, single coherence heads over chosen pasting diagrams, terms whose bracketing of each boundary path is chosen globally (for example by a fixed total order on the generators of every molecule that is respected by every boundary), or assignments defined by induction on dimension with all lower choices made simultaneously.

**Q2 (if CT fails).** Prove that no assignment satisfies (a)–(c) for D¹ ⊗ D¹ ⊗ D¹ (or for some other pair), and identify the minimal extra rule that makes the family contexts well formed, for example a typing rule for generators whose boundaries are molecules, or a definitional equation between bracketings. A precise description of which equations are forced is the useful answer.

**Q3 (iterated tensors).** If CT holds for pairs, does it hold for λΘ₁ ⊗ ⋯ ⊗ λΘ_k, compatibly with the associativity of the tensor (the two assignments for (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) agree up to renaming)?

## 5. What counts as a solution

An explicit construction of T for all Θ, Δ; an impossibility proof with the forced equations; or a published reference.

## 6. Literature (searched 2026-11-18)

- Steiner, HHA 2004; Hadzihasanovic, arXiv 2404.07273 (molecules, layerings, Prop. 8.3.17 on supports).
- Campion, arXiv 2311.00205; Chanavat, arXiv 2603.22242.
- Finster–Mimram, arXiv 1706.02866; Benjamin–Markakis, arXiv 2406.12127 (invertibility of coherences).
- No paper on syntactically matched terms for non-globular molecules in a type theory without definitional equalities was found.

# Researcher Response

**I have not obtained a full resolution of CT for arbitrary pairs or finite families.** I did obtain an unconditional construction in all dimensions, together with a closure property:

> **Suspension closure.** Let \(I=D^1\), and let \(P\) be a finite globular pasting diagram. Then
> \[
> \mathrm{CT}(I\otimes P)\Longrightarrow
> \mathrm{CT}(I\otimes\Sigma P).
> \]
> Consequently, CT holds for
> \[
> I\otimes D^n\qquad\text{and}\qquad D^n\otimes I
> \]
> for every \(n\geq 0\).
>
> Using your known case of two one-dimensional diagrams, it also holds for
> \[
> I\otimes\Sigma^r[m]
> \]
> for every \(r,m\geq 0\), where \([m]\) is the path of \(m\) composable arrows.

This construction assigns terms to **all cells**, including identity towers, and fixes every generator literally. Here is the construction and its typing proof.

## 1. Whiskering operations with literal boundaries

Choose right and left whiskering operations
\[
R_r(a,h),\qquad L_r(h,a),
\]
where \(a\) is an \(r\)-cell and \(h\) is a composable \(1\)-cell.

For \(r=1\), use fixed binary composition coherences. For \(r>1\), define the operations by composition coherences over
\[
D^r\vee_0D^1
\qquad\text{and}\qquad
D^1\vee_0D^r,
\]
with types chosen recursively so that
\[
\begin{aligned}
sR_r(a,h)&=R_{r-1}(sa,h),&
tR_r(a,h)&=R_{r-1}(ta,h),\\
sL_r(h,a)&=L_{r-1}(h,sa),&
tL_r(h,a)&=L_{r-1}(h,ta).
\end{aligned}
\tag{1}
\]

These are syntactic equalities: the terms on the right are the boundary terms used in the coherence declarations on the left.

The composition support condition holds. For example, the source term defining \(R_r\) uses exactly the variables of
\[
D^{r-1}\vee_0D^1=\partial^-(D^r\vee_0D^1),
\]
and its target uses exactly the corresponding positive boundary. Their types agree by induction and globularity.

We will also use syntactic suspension. Given fresh endpoints \(A,D\), it replaces \(\star\) by \(A\to_\star D\), shifts every declaration up one dimension, and sends
\[
\operatorname{coh}_{Q,B}[\tau]
\quad\longmapsto\quad
\operatorname{coh}_{\Sigma Q,\Sigma B}[\Sigma\tau].
\]
Suspension preserves the support conditions and commutes literally with substitution and typing. This construction is also given explicitly in Benjamin–Markakis, §4.1. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

## 2. The strict hom decomposition

Write \(s,t\) for the vertices of \(\Sigma P\), and set
\[
A=(0,s),\quad B=(0,t),\quad
C=(1,s),\quad D=(1,t).
\]

The nonempty homs between distinct vertices of \(I\otimes\Sigma P\) are
\[
\begin{aligned}
(I\otimes\Sigma P)(A,B)&\cong P,\\
(I\otimes\Sigma P)(C,D)&\cong P,\\
(I\otimes\Sigma P)(A,C)&\cong D^0,\\
(I\otimes\Sigma P)(B,D)&\cong D^0,\\
(I\otimes\Sigma P)(A,D)&\cong I\otimes P.
\end{aligned}
\tag{2}
\]
Here \(P\) denotes the free strict category presented by the pasting diagram. Each endomorphism hom is terminal.

This is the hom description underlying Loubaton’s **strict** suspension–tensor formula, Theorem 0.0.1. [arxiv.org](https://arxiv.org/pdf/2203.11845?utm_source=chatgpt.com)

For the construction below, the precise identification of the diagonal hom matters. It can be checked directly on Steiner tableaux.

Let \(e\) be the degree-one interval basis element. For a degree-\(r\) basis element \(a\) of \(\lambda P\), define a degree-shifting map \(f\) by
\[
\begin{aligned}
f_r(\epsilon\otimes a)
  &=\epsilon\otimes\Sigma a
  &&(r>0),\\
f_r(e\otimes b)
  &=e\otimes\Sigma b
  &&(\dim b=r-1,\ r>0),\\
f_0(0\otimes a)
  &=0\otimes\Sigma a+e\otimes t
  &&(\dim a=0),\\
f_0(1\otimes a)
  &=e\otimes s+1\otimes\Sigma a
  &&(\dim a=0).
\end{aligned}
\tag{3}
\]

The tensor differential gives
\[
\partial f_r=f_{r-1}\partial
\qquad(r>0).
\tag{4}
\]
For example,
\[
\partial(e\otimes\Sigma a)
=
\bigl(e\otimes s+1\otimes\Sigma a\bigr)
-
\bigl(0\otimes\Sigma a+e\otimes t\bigr)
\]
when \(\dim a=0\), which is exactly the required degree-zero identity.

For \(r>0\), \(f_r\) bijects the relevant positive bases. At degree zero, its images are precisely the \(A\)-to-\(D\) paths: either an arrow in the \(0\)-copy of \(\Sigma P\) followed by \(e\otimes t\), or \(e\otimes s\) followed by an arrow in the \(1\)-copy.

Applying \(f_r\) to tableau row \(r\), shifting it to row \(r+1\), and adding the fixed row \((A,D)\), therefore gives
\[
\Phi:I\otimes P
\xrightarrow{\;\cong\;}
(I\otimes\Sigma P)(A,D).
\tag{5}
\]
The inverse is positive: above row zero it is the inverse basis bijection, and at row zero it selects the unique path of one of the two displayed forms. Equation (4) verifies the tableau equations in both directions. The tableau formulas for identities and composition verify that \(\Phi\) is a strict isomorphism.

In particular,
\[
\begin{aligned}
\Phi(0\otimes a)
  &=(0\otimes\Sigma a)\mathbin{\#_0}(e\otimes t),\\
\Phi(1\otimes a)
  &=(e\otimes s)\mathbin{\#_0}(1\otimes\Sigma a),\\
\Phi(e\otimes a)
  &=e\otimes\Sigma a.
\end{aligned}
\tag{6}
\]

In the first two lines, the displayed expressions include the required lower-dimensional whiskering data.

## 3. Constructing the new family context

Assume that \(\Gamma\) and \(T\) establish CT for \(I\otimes P\).

Construct a context \(\Gamma'\) for \(I\otimes\Sigma P\). Begin with:

- the four vertices \(A,B,C,D\);
- the ordinary globular variables for the two copies of \(\Sigma P\);
- the interval variables
  \[
  u_s:A\to C,\qquad u_t:B\to D.
  \]

We construct a substitution
\[
\sigma:\Gamma'\longrightarrow\Sigma_{A,D}\Gamma.
\]
Thus \(\sigma\) assigns a term of \(\Gamma'\) to each variable of the suspended context.

For an endpoint generator \(a\) of \(P\), prescribe
\[
\begin{aligned}
(\Sigma v_{0\otimes a})[\sigma]
&=
R_{\dim a+1}(v_{0\otimes\Sigma a},u_t),\\
(\Sigma v_{1\otimes a})[\sigma]
&=
L_{\dim a+1}(u_s,v_{1\otimes\Sigma a}).
\end{aligned}
\tag{7}
\]

These assignments are literally well typed. The reason is specific: **the immediate boundaries of a positive-dimensional generator of \(P\) are generators of \(P\)**. By CT(a), the endpoint declarations in \(\Gamma\) therefore have ordinary variable boundaries. Substituting (7) into those declarations gives exactly the recursively specified whiskering types in (1).

For a zero-dimensional \(a\), the suspended type is \(A\to D\), which is also exactly the type of the binary composite in (7).

Now process the mixed variables of \(\Gamma\) in increasing dimension. If the old declaration is
\[
x:p\to_Xq,
\]
declare the corresponding new mixed variable by
\[
v_x:
(\Sigma p)[\sigma]
\longrightarrow_{(\Sigma X)[\sigma]}
(\Sigma q)[\sigma],
\tag{8}
\]
and extend the substitution by
\[
(\Sigma x)[\sigma]=v_x.
\tag{9}
\]

Every term needed in (8) uses variables of lower dimension than \(x\), so its substitution has already been defined. Since \(\Sigma p\) and \(\Sigma q\) have the same type syntactically, their substituted terms do too.

There is exactly one new mixed variable for each generator
\[
e\otimes\Sigma a
\]
of \(I\otimes\Sigma P\). The suspended endpoint variables are assigned the whiskering terms in (7); they are **not additional declarations** in \(\Gamma'\).

Equations (6)–(9) also verify the strict interpretations of the declarations. An old mixed generator \(e\otimes a\) becomes the new generator \(e\otimes\Sigma a\), with its actual strict source and target.

## 4. Assigning terms to all cells

For a positive-dimensional cell \(c\) with \(0\)-source \(A\) and \(0\)-target \(D\), let \(\bar c\) be its preimage under (5). Define
\[
\boxed{\quad
T'(c)=(\Sigma T(\bar c))[\sigma].
\quad}
\tag{10}
\]
As usual, extend \(T\) to zero-dimensional cells by their vertex variables.

If \(\dim c\geq2\), the old typing judgment is
\[
T(\bar c):
T(s\bar c)\longrightarrow T(t\bar c).
\]
Suspension and substitution give
\[
T'(c):
(\Sigma T(s\bar c))[\sigma]
\longrightarrow
(\Sigma T(t\bar c))[\sigma].
\]
By (5) and the definition (10), this is literally
\[
T'(c):T'(sc)\longrightarrow T'(tc).
\tag{11}
\]

If \(\dim c=1\), then \(\bar c\) is a vertex and its suspended type is \(A\to D\), so (11) holds in that case as well.

The other homs in (2) are handled as follows.

### The two copies of \(P\)

Choose ordinary CaTT representatives \(S_P(a)\) for the cells of the free strict category on the globular set \(P\), with literal boundaries and with generators represented by variables. Use their suspensions in the two copies of \(\Sigma P\).

For completeness, this ordinary globular construction can be made dimensionwise. Write a free strict cell as a globular pasting arity labelled by generators. Over that arity, choose a composition coherence whose boundary terms are the already chosen composites of its two boundary arities. Globularity makes those terms parallel literally, and the composition support condition is exactly the requirement that they use their respective boundary arities. For a single generating globe use its top variable; for an identity use an identity coherence. Substitution of the generator labels gives \(S_P\).

Equivalently, the free weak-to-strict comparison on a globular set has the globular boundary-lifting property supplied by the operadic contraction. This is the free-globular situation covered by the identification with Leinster’s operad; it makes no assertion about arbitrary computad contexts. [arxiv.org](https://arxiv.org/pdf/2208.08719?utm_source=chatgpt.com)

### The interval and endomorphism homs

Use \(u_s,u_t\) and their identity towers for the two interval homs. Use identity towers on vertex variables for endomorphism homs.

These cases exhaust all cells by (2).

### Verification of CT

For a mixed generator \(g=e\otimes\Sigma a\), its preimage \(\bar g=e\otimes a\) is a generator. Hence
\[
T'(g)
=(\Sigma v_{\bar g})[\sigma]
=v_g
\]
literally by (9). Endpoint generators and interval generators were also assigned their variables.

Strict interpretation of (10) is \(c\), since the interpretation of \(\sigma\) is the map (3), hence the isomorphism (5). The other assignments have their stated strict interpretations by construction.

Equation (11), together with the ordinary globular and identity constructions on the remaining homs, proves exact boundary matching everywhere.

This proves the suspension-closure theorem.

## 5. Consequences and the opposite tensor order

Taking \(P=D^{n-1}\) and starting with
\[
I\otimes D^0=I
\]
gives CT for \(I\otimes D^n\) for every \(n\).

The other order follows by odd-dimensional opposite. On directed complexes this replaces
\[
\partial_r\quad\text{by}\quad
\partial_r^{\mathrm{op}}=(-1)^r\partial_r.
\]
The unsigned basis flip
\[
a_p\otimes b_q\longmapsto b_q\otimes a_p
\]
then gives a positive chain isomorphism
\[
(A\otimes B)^{\mathrm{op}}
\cong B^{\mathrm{op}}\otimes A^{\mathrm{op}}.
\tag{12}
\]
Indeed, both differentials after the flip give
\[
(-1)^{p+q}b_q\otimes\partial a_p
+
(-1)^q\partial b_q\otimes a_p.
\]

Each globe \((D^n)^{\mathrm{op}}\) is isomorphic to \(D^n\): swap the parallel pair of basis elements in every even degree below the top.

CaTT has the corresponding recursive opposite operation, including transformation of coherence arities and their declaration order. It preserves generators, fullness, and literal equality. Benjamin–Markakis establish these properties in §5, particularly Lemma 16 and properties (op4)–(op5). [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

Applying this operation to the constructed terms and then renaming through (12) proves CT for \(D^n\otimes I\).

Finally, your known case gives CT for \(I\otimes[m]\). Repeated suspension closure therefore gives
\[
\mathrm{CT}\bigl(I\otimes\Sigma^r[m]\bigr)
\qquad(r,m\geq0).
\]

## 6. The general step that is still missing

The suspension argument does not establish closure under
\[
P,Q\longmapsto P\vee Q.
\]
A cell of \(I\otimes(P\vee Q)\) can use generators from both tensor pieces. Gluing the two family contexts does not assign a representative to that cell with the already chosen boundary terms.

The attempted general resolution has a precise failure at higher faces. Suppose three independent \(n\)-generators are being reordered.

1. The construction supplies selected \((n+1)\)-cells comparing adjacent orders.
2. A common globular arity for the three generators supplies a generic \((n+2)\)-coherence.
3. Its faces are particular **derived pair-comparison terms** in that arity.
4. Those derived terms have not been shown equal, syntactically, to the independently selected pair comparisons.

They are not substitution variables, so substituting the selected pair comparisons for them is not an available operation. Padding can make the relevant terms parallel, but it does not supply the next comparison merely from equality of their strict images.

The cylinder-extension construction reaches the same point. Changing a seed gives a transported filler
\[
\widetilde F^1(u)
=
\ell_u^{-1}\,;\,F^0(u)\,;\,r_u
\]
with exactly the boundary of the prescribed \(F^1(u)\). What remains is a term
\[
\kappa_u:\widetilde F^1(u)\longrightarrow F^1(u).
\]
The checked construction does not produce this term in general, nor the higher compatibility needed when several such changes are composed.

Thus the results above establish an all-dimensional family of cases and an exact suspension closure theorem. They do **not** decide CT for arbitrary pairs, prove a counterexample, or identify equations forced by such a counterexample. The general construction and Q3 remain unresolved in this analysis.

## Verification of the researcher response (2026-11-19)

**Verdict: partial answer, verified.** CT is proved for an infinite family in every dimension, by a suspension-closure theorem; CT for all pairs, a counterexample, and Q3 remain open. The follow-up prompt is `canonical-gray-terms-r2-2026-11-19.md`.

**Suspension closure CT(I ⊗ P) ⇒ CT(I ⊗ ΣP), checked.**
- The whiskerings R_r, L_r over D^r ∨₀ D¹ and D¹ ∨₀ D^r with recursively chosen types satisfy (1) literally, and the composition-case support condition holds (the source uses exactly ∂⁻(D^r ∨₀ D¹)).
- The hom decomposition (2) and the strict isomorphism Φ : I ⊗ P ≅ (I ⊗ ΣP)(A, D) of (3)–(6) were checked on the chain level: ∂ f_r = f_{r−1} ∂ including the degree-0 case written out, f_r is a bijection of bases for r > 0, and at degree 0 the image is exactly the two kinds of A → D paths. Example: P = D⁰ gives the square, whose (A, D) hom is [1] = I ⊗ D⁰.
- The context Γ′ and substitution σ : Γ′ → Σ_{A,D} Γ: the key point is that in a globular pasting diagram every positive-dimensional generator has generators as its source and target, so by CT(a) the endpoint declarations of Γ have variable boundaries, and substituting (7) gives exactly the types (1). Mixed variables are declared by σ-substituted suspended types, so they are literally well formed. T′(c) = (ΣT(c̄))[σ] then satisfies (c) by stability of typing under suspension and substitution; the other homs use ordinary globular composites and identity towers.
- Consequences: CT for I ⊗ Dⁿ and Dⁿ ⊗ I (the latter by the odd-dimensional opposite, with the chain isomorphism (12) checked), and for I ⊗ Σ^r[m]. This includes the known D² ⊗ D¹ case and goes beyond dimension 4 without any relative-coherence input.
- Consistency with the known failure: D¹ ⊗ D¹ ⊗ D¹ = I ⊗ (I ⊗ I) is not covered, because I ⊗ I is not a suspension. The response does not contradict item 3 (which only rules out layered terms).

**Not established.** Closure under wedges P ∨ Q (the response identifies the precise failure: derived pair-comparison terms in a common arity are not syntactically the selected ones), CT for general pairs, and iterated tensors (Q3).

**In-house follow-up (standard 9).** Generate Fam(I ⊗ Dⁿ) and the terms T′ by the suspension construction for n ≤ 4 and run them through the certified checker (owner: E8 line, MARK; see `../../open-issues.md`).
