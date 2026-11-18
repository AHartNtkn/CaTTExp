# Problem: naturality of CaTT coherences at depth ≥ 2

*Standalone problem statement. It assumes familiarity with globular weak ω-categories and dependent type theory, and nothing else. Questions are in §4, smallest first.*

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory whose models are weak ω-categories. We use the syntax of Benjamin–Markakis–Offord–Sarti–Vicary (BMOSV, [arXiv 2501.11620](https://arxiv.org/abs/2501.11620), §2).

```
Types          A ::= ⋆ | u →_A v
Terms          t ::= x | coh_{P, A}[γ]
Contexts       Γ ::= ∅ | Γ, x : A
Substitutions  γ ::= ⟨⟩ | ⟨γ, x ↦ t⟩
```

- `dim ⋆ = −1`, `dim(u →_A v) = dim A + 1`; a term of type A has dimension `dim A + 1`. For `t : u → v` write `σt = u`, `τt = v`, and `σᵏ, τᵏ` for iterates.
- `Var(t : A)` is the set of free variables of t and A.
- A **pasting context** `P ⊢ps` is a context presenting a globular pasting diagram (Finster–Mimram's rules). It has source and target boundaries `∂⁻P`, `∂⁺P`, again pasting contexts.
- **Coherence rule.** If `P ⊢ps`, `P ⊢ u →_A v` and `Δ ⊢ γ : P`, then `Δ ⊢ coh_{P, u→_A v}[γ] : (u →_A v)[γ]`, provided either
  - (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or
  - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality. There is nothing else.
- Binary composites `u ∗_k v` (including whiskerings, when the dimensions differ) are coherences over the pasting context of two discs glued along a k-disc. Their boundaries are computed componentwise, syntactically.

### 1.2 Strict interpretation

Every CaTT context Γ is a finite computad (polygraph); write `F(Γ)` for the free *strict* ω-category on it. Strict ω-categories are models of CaTT, so every term t of Γ has a strict image `π(t)` in `F(Γ)`: a coherence is sent to the unique strict composite of its arity. (In a strict ω-category, any two full parallel terms over a pasting context are equal.)

### 1.3 The cylinder context Q↑Y

Let P be a pasting context and `Y ⊆ Var(P)` **up-closed**: if `y ∈ Y` occurs in the type of x, then `x ∈ Y`. The **depth** of Y in a term `t : A` is `max { dim t − dim y : y ∈ Var(t : A) ∩ Y }`.

Suppose that every term w of dimension `< n` with `Var(w) ∩ Y ≠ ∅` already has a "cylinder" `w↑`, and two copies `w⁻`, `w⁺`. If `Var(w) ∩ Y = ∅`, put `w⁻ = w⁺ = w`, and **omit** every factor `w↑` below (literal deletion of that binary composite). For a term t of dimension `n ≥ 1` define

```
a_t := ( … ((t⁻ ∗₀ (τⁿt)↑) ∗₁ (τⁿ⁻¹t)↑) … ) ∗_{n−1} (τt)↑
b_t := (σt)↑ ∗_{n−1} ( … ((σⁿ⁻¹t)↑ ∗₁ ((σⁿt)↑ ∗₀ t⁺)) … )
```

and `a_t := t⁻`, `b_t := t⁺` for n = 0. For n = 1 this is the lax square `t⁻ ∗₀ (τt)↑ → (σt)↑ ∗₀ t⁺`.

**Lemma 1.** If each lower `w↑` has type `a_w → b_w`, then `a_t, b_t : a_{σt} → b_{τt}` are well typed. (Uses that terms disjoint from Y have boundaries disjoint from Y.)

The context `P↑Y` keeps each `x ∉ Y` and replaces each `x ∈ Y` by `x⁻, x⁺` (copies, with Y-variables in their types renamed to the same sign) and `x↑ : a_x → b_x`. By Lemma 1 it is well formed. It is not a pasting context in general. For `Y = Var(P)` it presents the strict Gray cylinder: with Steiner's sign convention the formulas give `I ⊗ P`.

**Example (the lax square).** `P = (x, y, f : x → y)`, `Y = Var(P)`:

```
x⁻, x⁺, x↑ : x⁻ → x⁺,   y⁻, y⁺, y↑ : y⁻ → y⁺,
f⁻ : x⁻ → y⁻,   f⁺ : x⁺ → y⁺,   f↑ : f⁻ ∗₀ y↑ → x↑ ∗₀ f⁺.
```

### 1.4 Naturality terms and Conjecture N

Naturality terms are defined by recursion: `x↑` is the variable for `x ∈ Y`, and

```
(coh_{Q,B}[γ])↑ := K(Q, B, γ⁻¹Y)[γ↑]
```

where `γ⁻¹Y = { q : Var(q[γ]) ∩ Y ≠ ∅ }` (up-closed in Q) and `γ↑` sends `q^± ↦ (q[γ])^±`, `q↑ ↦ (q[γ])↑`, and `q ↦ q[γ]` for q outside `γ⁻¹Y`. The recursion runs by dimension, and within a dimension by structural induction on the term (a composite's top arity variables are sent to terms of the same dimension, which are proper subterms). Its only non-syntactic ingredient is the family K:

> **Conjecture N.** For every pasting context Q, every type B full in Q, and every non-empty up-closed `Y ⊆ Var(Q)`, the type `a_c → b_c`, where `c = coh_{Q,B}[id]`, is inhabited in `Q↑Y`.

Given N, every CaTT context Γ (not only pasting ones) gets cylinder contexts `Γ↑X` and naturality terms `t↑ : a_t → b_t` for every term t, by substitution. For `X = Var(Γ)` this is the context `Γ ⊗ D¹` (lax transformations out of Γ), and iterating on the top layer gives `Γ ⊗ Dⁿ`.

## 2. What is known

1. **Depth ≤ 1** (depth of Y at most 1 in both Q and c): BMOSV, Theorem 3.1.
2. **Relative coherence in dimension 2 (proved).** Write RC(n) for the property:

   > **RC(n) for a context Γ.** Any two parallel n-terms `T, T'` of Γ with `π(T) = π(T')` are connected by an (n+1)-term `T → T'`.

   **Theorem A.** RC(2) holds for every CaTT context Γ.

   *Proof sketch* (this generalises an unpublished "relative ladder theorem" of an external referee, which is the case of the cylinder of a chain):
   - *Paths.* A 1-term has a flattened path (word in 1-variables). Two 1-terms with the same endpoints and the same path w are full parallel terms over the chain context `C(w)`, pulled back along `C(w) → Γ`, so the coherence rule gives `κ_w(a, b) : a → b`. Likewise any 2-term with no 2-variables pulls back to `C(w)` and is connected to the κ with the same boundary.
   - *Sequentialization.* Every 2-term is connected, in both directions, to a vertical composite of factors that are either (G) a 2-variable x whiskered by 1-terms, or (I) 2-terms with no 2-variable. (Replace each composite over a 2-dimensional arity by a column-by-column composite, by the coherence rule over that arity; flatten binary composites by interchange, distributivity and associativity coherences over small pasting contexts.)
   - *Normal form of a whiskered generator.* For a whiskered generator with whisker paths λ, ρ, let `P_g` be the pasting context "chain of length |λ|, a 2-disc `z⁻ ⇒ z⁺`, chain of length |ρ|", and `H_g` the composition coherence over it. Substitute `z^± ↦ σx, τx`, the disc ↦ x. Fixing one bracketing `B_w` per path w gives `e_g : B_{λ·σx·ρ} → B_{λ·τx·ρ}`. Every factor of kind (G) with the same (λ, x, ρ) is connected to `κ ∗₁ e_g ∗₁ κ` by a coherence over `P_g`, where all comparisons happen over the *expanded* paths. So T is connected to `κ ∗₁ e_{g₁} ∗₁ … ∗₁ e_{g_k} ∗₁ κ`, where `g₁ … g_k` is the 2-path of whiskered generators that T traces in `F(Γ)`.
   - *Exchange.* In the free strict 2-category on a 2-polygraph, two 2-paths represent the same 2-cell iff they are related by exchange moves of two whiskered generators in disjoint horizontal positions. Each exchange move is realised by a coherence over the pasting context "chain, 2-disc, chain, 2-disc, chain", substituted, then normalised as above.
   - No loop-freeness is used. ∎
3. **Reduction of N to RC (proved).** Fix Q, B, Y and let `n = dim c`. Under the strict collapse `F(I ⊗ Q) → F(Q↑Y)` (which sends `e ⊗ x` to an identity for `x ∉ Y`), the strict cell `e ⊗ π(c)` goes `π(a_c) → π(b_c)`.
   - If c is a **coherence**, `π(c)` is an identity, so `π(a_c) = π(b_c)`, and RC(n) for `Q↑Y` gives K.
   - If c is a **composition**, write the strict cell as a sequence of whiskered top generators `q↑`. Realise each layer by an (n+1)-term `U₁ ∗ (a ∗₀ q↑ ∗₀ b) ∗ U₂` (whiskers chosen with the right strict images, boundaries adjusted by κ), and connect consecutive layers, and the two ends to `a_c`, `b_c`, by RC(n).
   
   So **RC(n) on the cylinder contexts implies N for coherences of dimension n.**
4. **Consequence: N holds for every term of dimension ≤ 2**, every pasting context Q and every up-closed Y, by Theorem A and item 3. This includes the associator and every 2-dimensional coherence over a chain with any up-closed Y. It gives `Γ ⊗ D¹` for every context Γ of dimension ≤ 3, and `Γ ⊗ Dⁿ` for every n when `dim Γ ≤ 2`.

## 3. Why dimension 3 is different

RC(3) is false for arbitrary contexts. In `Γ = (x : ⋆, a : id_x → id_x)`, the Eckmann–Hilton 3-cell `a ∗₀ a → a ∗₀ a` and the identity are parallel, with equal strict images, but are expected not to be connected: in the fundamental weak ω-groupoid of S², with a sent to a generator of π₂, the Eckmann–Hilton cell represents a non-zero element of π₃(S²). *(Sketch; not checked in detail.)* So any proof of RC(3) must use **loop-freeness** of the context. The cylinder contexts `Q↑Y` are loop-free: they present Steiner complexes with loop-free bases, whose free strict ω-categories are also their free (∞,ω)-categories (Campion, [arXiv 2311.00205](https://arxiv.org/abs/2311.00205), Cor. 3.5; Chanavat, [arXiv 2603.22242](https://arxiv.org/abs/2603.22242), Thm 3.29). So RC holds for them semantically in (∞,ω)-categories; the question is whether CaTT proves it.

**Where the dimension-2 proof stops.** Sequentialization and generator normal forms extend to dimension 3. What does not extend is the comparison of runs of 3-cells of kind (I) (no 3-variables) between 2-terms with equal strict image. In dimension 2 these runs live over one path and are settled by the coherence rule over a chain. In dimension 3 they live over a 2-dimensional context that is not a pasting context, such as the lax square. A natural attack is a Squier-style argument: show that critical branchings between elementary 3-cells close up to 4-cells. The hard branchings are those where one elementary 3-cell moves a 2-generator, say `f↑`, and the other reassociates a composite that splits its boundary `f⁻ ∗₀ y↑`. No pasting context contains both.

## 4. Questions

Each question asks for an explicit CaTT term, built only with the coherence rule over pasting contexts and substitution.

1. **Smallest open case.** Let S be the lax square (§1.3 example). Are any two parallel 3-terms of S connected by a 4-term? (This is RC(3) above the top dimension of S. It gives N for every 3-dimensional coherence over the single arrow `Q = (x, y, f)`.) Even one non-trivial instance is useful: for a 3-dimensional coherence c over `(x, y, f)` with `Y = Var(Q)`, construct `K : a_c → b_c` explicitly.
2. **The 3-dimensional unitor over the 2-disc.** `Q = (x, y, f, g, α : f → g)`, `Y = Var(Q)`, and `c : α ∗₁ id_g → α` the unitor. Construct `K : a_c → b_c` in `Q↑Y`. (By §2.3 this follows from RC(3) for the 3-dimensional context `Q↑Y`.)
3. **RC(3) in general.** Prove RC(3) for every finite context whose computad is loop-free in Steiner's sense (or at least for every cylinder `Q↑Y`), or give a loop-free counterexample.
4. **All dimensions.** Prove RC(n) for all n on loop-free contexts (or on all cylinders `Q↑Y`). By §2.3 this proves Conjecture N at every depth.

## 5. What counts as a solution

A construction of the terms in question 1 or 2, a proof of RC(3) or RC(n) for loop-free contexts, or a counterexample: a loop-free context (preferably a cylinder `Q↑Y`) with two parallel n-terms of equal strict image and no term between them. A reference to a published proof also counts.

## 6. Literature (searched 2026-11-18)

- BMOSV, *Naturality for higher-dimensional path types*, [arXiv 2501.11620](https://arxiv.org/abs/2501.11620): depth ≤ 1. Its v3 says higher-depth cases are beyond the paper.
- Benjamin–Markakis–Sarti, *Invertible cells in ω-categories*, [arXiv 2406.12127](https://arxiv.org/abs/2406.12127), and Benjamin–Champin–Markakis, ICaTT, [arXiv 2602.16602](https://arxiv.org/abs/2602.16602): every cell built here is a composite of coherences, hence invertible.
- Mikhail, *A type-theoretic definition of lax (∞,∞)-limits*, [arXiv 2412.13310](https://arxiv.org/abs/2412.13310), Thm 4.4: the contexts `Γ ⊗ D¹` for globular Γ, without the terms K.
- Campion and Chanavat (above): the (∞,ω) analogue holds. Chanavat also proves that frame-acyclic molecules have essentially unique composites in (∞,n)-categories.
- Steiner, *Omega-categories and chain complexes*, HHA 6 (2004): loop-free bases and Gray tensors.
- Ara, Burroni, Guiraud, Lafont, Métayer, *Polygraphs: from rewriting to higher categories* ([arXiv 2312.00429](https://arxiv.org/abs/2312.00429)): free 2-categories on 2-polygraphs as 2-paths modulo exchange; Squier-style coherence.

# Researcher Response

**Question 2 has a construction, provided the identity and vertical-composition lifts are chosen by the universal formulas below.** Specializing that construction gives a non-endomorphism example for question 1, including an example whose outer constructor is literally \(\operatorname{coh}_{Q,B}[\mathrm{id}_Q]\) for the one-arrow context \(Q\).

The qualification about lower lifts is substantive. These formulas are fixed in their universal contexts before any specialization, so they respect the recursive substitution rule. The argument does not establish independence from an arbitrary previously fixed family of \(K_2\)’s.

The construction uses only coherences over globular pasting contexts, substitution, and binary composition. It does not require RC(3).

## 1. Notation and how the displayed comparisons expand into CaTT terms

During the calculation, write
\[
uv:=u*_1v
\]
for composition of 2-cells and for the corresponding whiskering of a 3-cell by a 2-cell. Write
\[
r;s:=r*_2s
\]
for composition of 3-cells. Composition of 4-cells remains \(*_3\).

Let
\[
\mathfrak a_{u,v,w}:(uv)w\longrightarrow u(vw),
\qquad
\lambda_u:\mathbf1u\longrightarrow u,
\qquad
\rho_u:u\mathbf1\longrightarrow u
\]
be the usual 3-dimensional associators and unitors. They are direct coherences over a chain of three 2-discs or a single 2-disc, followed by substitution.

For a primitive coherence \(r\), write \(r^{\mathrm{rev}}\) for the coherence over the same pasting context with its endpoints exchanged. This notation specifies another term; it does not impose inverse equations.

### A convention for constructing 4-cells

When \(P\) is a stated pasting context and \(r,s\) are the stated parallel full 3-terms over \(P\), use
\[
[r\Rightarrow s]_P[\theta]
:=
\operatorname{coh}_{P,r\to s}[\theta].
\tag{1}
\]
Assignments to the maximal variables of \(P\) determine the assignments to their globular boundaries.

Every semicolon word below has fixed left-associated brackets. Rebracketing is implemented by (1) over a chain of 3-discs. More explicitly, to replace a consecutive block of a semicolon word by a parallel term:

1. use a 4-coherence on the corresponding 3-cell chain to put parentheses around the block;
2. whisker the proposed 4-cell by the prefix and suffix;
3. use another such 4-coherence to restore left association.

Empty prefixes or suffixes are omitted. Thus the replacement sequences below specify finite CaTT terms, including their necessary reassociations.

The underlying coherence rule is exactly the full-support rule in BMOSV §2; no coherence rule on the cylinder context is being added. [arxiv.org](https://arxiv.org/pdf/2501.11620?utm_source=chatgpt.com)

## 2. Fix two universal lower-dimensional lifts

These choices are part of the construction.

Write
\[
L(\xi)=\xi^-*_0Y,
\qquad
R(\xi)=X*_0\xi^+,
\]
where \(X=x^\uparrow\) and \(Y=y^\uparrow\). The same notation applies to the relevant cells in each dimension.

### 2.1. The lift of vertical composition

Start with the universal vertical chain
\[
\alpha:f\Rightarrow g,
\qquad
\beta:g\Rightarrow h.
\]
Its fully selected cylinder has
\[
F:Lf\Rightarrow Rf,\quad
G:Lg\Rightarrow Rg,\quad
H:Lh\Rightarrow Rh
\]
and
\[
A:(L\alpha)G\Rightarrow F(R\alpha),
\qquad
B:(L\beta)H\Rightarrow G(R\beta).
\]

Choose the distributivity coherences
\[
\phi_L:
L(\alpha\beta)\Rightarrow (L\alpha)(L\beta),
\]
\[
\phi_R:
(R\alpha)(R\beta)\Rightarrow R(\alpha\beta).
\]
The arity of \(\phi_L\) is
\[
(D^2*_1D^2)*_0D^1,
\]
and that of \(\phi_R\) is
\[
D^1*_0(D^2*_1D^2).
\]
They are therefore ordinary CaTT coherences.

Define the universal vertical-composition lift by
\[
\boxed{
\begin{aligned}
C(A,B)={}&
(\phi_LH);
\mathfrak a_{L\alpha,L\beta,H};
((L\alpha)B);
\mathfrak a^{\mathrm{rev}}_{L\alpha,G,R\beta};\\
& (A(R\beta));
\mathfrak a_{F,R\alpha,R\beta};
(F\phi_R).
\end{aligned}}
\tag{2}
\]
Its successive 2-boundaries are
\[
\begin{aligned}
L(\alpha\beta)H
&\longrightarrow ((L\alpha)(L\beta))H\\
&\longrightarrow (L\alpha)((L\beta)H)\\
&\longrightarrow (L\alpha)(G(R\beta))\\
&\longrightarrow ((L\alpha)G)(R\beta)\\
&\longrightarrow (F(R\alpha))(R\beta)\\
&\longrightarrow F((R\alpha)(R\beta))\\
&\longrightarrow F(R(\alpha\beta)).
\end{aligned}
\]
Thus (2) has exactly the required cylinder type.

### 2.2. The lift of an identity 2-cell

For a 1-variable \(g\), put
\[
e=L(\mathbf1_g),\qquad
h=R(\mathbf1_g),\qquad b=G.
\]
Choose
\[
\kappa:e\Rightarrow\mathbf1_{Lg},
\qquad
\ell:h\Rightarrow\mathbf1_{Rg}.
\tag{3}
\]
Here:

- \(\kappa\) is a direct 3-coherence on the path \(g^-,Y\);
- \(\ell\) is a direct 3-coherence on the path \(X,g^+\).

Their sources and targets are parallel full 2-terms on those paths. Choose the reversed coherences on the same paths.

Define
\[
\boxed{
J=(\kappa b);\lambda_b;\rho_b^{\mathrm{rev}};(b\ell^{\mathrm{rev}})
:
eb\Rightarrow bh.
}
\tag{4}
\]
Its boundaries are verified by
\[
eb
\longrightarrow \mathbf1_{Lg}b
\longrightarrow b
\longrightarrow b\mathbf1_{Rg}
\longrightarrow bh.
\]

Equations (2) and (4) are universal definitions of the corresponding \(K_2\)’s. Consequently, under the substitution
\[
\beta\mapsto\mathbf1_g,
\]
the recursively defined lift of
\[
s=\alpha*_1\mathbf1_g
\]
is literally
\[
s^\uparrow=C(A,J).
\tag{5}
\]
This is the required substitution compatibility. We have not selected a new lift of \(s\) specifically to force the unitor equation.

## 3. The calculation in dimension 4

Now work in the cylinder of the 2-disc
\[
Q=(x,y,f,g,\alpha:f\Rightarrow g).
\]
Abbreviate
\[
a=L\alpha,\qquad b=G,\qquad c=F,\qquad d=R\alpha.
\]
Their types are
\[
\begin{array}{ll}
a:Lf\Rightarrow Lg,&b:Lg\Rightarrow Rg,\\
c:Lf\Rightarrow Rf,&d:Rf\Rightarrow Rg,
\end{array}
\]
and the cylinder generator is
\[
A:ab\Rightarrow cd.
\]

Retain \(e,h,\kappa,\ell,J\) from (3)–(4), and write
\[
i=\mathbf1_{Rg}.
\]
Thus
\[
\kappa:e\Rightarrow\mathbf1_{Lg},
\qquad
\ell:h\Rightarrow i.
\]

Define
\[
r_a=(a\kappa);\rho_a:ae\Rightarrow a,
\qquad
r_d=(d\ell);\rho_d:dh\Rightarrow d.
\tag{6}
\]

The central comparison is between the following 3-terms:
\[
\mathcal L=(r_a b);A,
\tag{7}
\]
\[
\mathcal R=
\mathfrak a_{a,e,b};
(aJ);
\mathfrak a^{\mathrm{rev}}_{a,b,h};
(Ah);
\mathfrak a_{c,d,h};
(cr_d).
\tag{8}
\]
Both have type
\[
(ae)b\Rightarrow cd.
\]

We will construct
\[
K_{\mathrm{mid}}:\mathcal L\Rightarrow\mathcal R
\]
by connecting both terms to one specified 3-term.

### 3.1. Normalize the left side

Put
\[
T=
\mathfrak a_{a,e,b};
a(\kappa b);
(a\lambda_b)
:
(ae)b\Rightarrow ab.
\tag{9}
\]

There is a 4-term
\[
L_4:\mathcal L\Rightarrow T;A.
\tag{10}
\]
Its construction is:

1. Distribute the right whisker \(b\) over the composite
   \[
   r_a=(a\kappa);\rho_a.
   \]
2. Replace
   \[
   \rho_a b
   \quad\text{by}\quad
   \mathfrak a_{a,\mathbf1_{Lg},b};(a\lambda_b).
   \tag{11}
   \]
   This is a direct 4-coherence on the vertical 2-cell chain \(a,b\). Both endpoints of (11) have type
   \[
   (a\mathbf1_{Lg})b\Rightarrow ab.
   \]
3. Replace
   \[
   ((a\kappa)b);
   \mathfrak a_{a,\mathbf1_{Lg},b}
   \quad\text{by}\quad
   \mathfrak a_{a,e,b};a(\kappa b).
   \tag{12}
   \]
   Form this coherence over
   \[
   D^2*_1D^3*_1D^2,
   \]
   with the middle 3-variable having generic 2-source \(e\) and generic 2-target \(e'\). Then substitute
   \[
   e'\mapsto\mathbf1_{Lg},
   \qquad
   \text{middle 3-variable}\mapsto\kappa.
   \]
4. Reassociate the semicolon word and postcompose by \(A\).

This gives (10). The potentially troublesome identity 2-cell in (12) is introduced only by substitution into a genuine globular pasting context.

### 3.2. Expand the right side

Expand \(J\) using (4), distribute whiskering, and reassociate. This gives a 4-term
\[
\mathcal R\Rightarrow T;\tau,
\tag{13}
\]
where
\[
\begin{aligned}
\tau={}&
(a\rho_b^{\mathrm{rev}});
a(b\ell^{\mathrm{rev}});
\mathfrak a^{\mathrm{rev}}_{a,b,h};
(Ah);\\
&\mathfrak a_{c,d,h};
c(d\ell);
(c\rho_d).
\end{aligned}
\tag{14}
\]
Here \(\tau:ab\Rightarrow cd\).

It remains to construct a 4-term
\[
\tau\Rightarrow A.
\tag{15}
\]

### 3.3. Move the two copies of \(\ell\) next to the whiskering of \(A\)

Associator naturality gives the two replacements
\[
a(b\ell^{\mathrm{rev}});
\mathfrak a^{\mathrm{rev}}_{a,b,h}
\quad\Longrightarrow\quad
\mathfrak a^{\mathrm{rev}}_{a,b,i};
((ab)\ell^{\mathrm{rev}}),
\tag{16}
\]
\[
\mathfrak a_{c,d,h};c(d\ell)
\quad\Longrightarrow\quad
((cd)\ell);\mathfrak a_{c,d,i}.
\tag{17}
\]

Each is a direct 4-coherence over two 2-discs followed by a 3-disc, glued along their 1-faces:
\[
D^2*_1D^2*_1D^3.
\]
The last 3-variable is substituted by \(\ell^{\mathrm{rev}}\) or \(\ell\), respectively.

Therefore \(\tau\) is connected to
\[
\begin{aligned}
&(a\rho_b^{\mathrm{rev}});
\mathfrak a^{\mathrm{rev}}_{a,b,i};
((ab)\ell^{\mathrm{rev}});
(Ah);\\
&\hspace{30mm}
((cd)\ell);
\mathfrak a_{c,d,i};
(c\rho_d).
\end{aligned}
\tag{18}
\]

Every adjacent pair in (16)–(18) has literally equal intermediate 2-boundaries.

### 3.4. Interchange \(A\) and \(\ell^{\mathrm{rev}}\)

Use the 4-coherence
\[
((ab)\ell^{\mathrm{rev}});(Ah)
\quad\Longrightarrow\quad
(Ai);((cd)\ell^{\mathrm{rev}}).
\tag{19}
\]

Its arity is
\[
D^3*_1D^3.
\]
More explicitly, form the comparison using generic 3-variables
\[
Z:u\Rightarrow v,
\qquad
k:w\Rightarrow z,
\]
then substitute
\[
u\mapsto ab,\quad v\mapsto cd,\quad Z\mapsto A,
\]
\[
w\mapsto i,\quad z\mapsto h,\quad
k\mapsto\ell^{\mathrm{rev}}.
\]

Both sides of (19) have 2-source \((ab)i\) and 2-target \((cd)h\).

This is the point at which a comparison involving \(A\) and a boundary adjustment is needed. The arity is two globular 3-discs; the square presenting \(A\) is used only through substitution.

### 3.5. Cancel the two structural 3-cells

After (19), the relevant part of the word is
\[
(Ai);((cd)\ell^{\mathrm{rev}});((cd)\ell).
\]
Combine the last two factors by the reversed whiskering-distribution coherence, obtaining
\[
(Ai);(cd)(\ell^{\mathrm{rev}};\ell).
\]

There is a direct 4-coherence
\[
\epsilon:
\ell^{\mathrm{rev}};\ell
\Longrightarrow
\mathbf1_i
\tag{20}
\]
over the original 1-dimensional path
\[
X,\ g^+.
\]
Both endpoints of (20) are 3-terms on that path, have type \(i\to i\), and have full typed support there.

Whisker (20) by \(cd\). Then use the identity-preservation coherence
\[
(cd)\mathbf1_i\Longrightarrow\mathbf1_{(cd)i}
\]
over a vertical chain of two 2-discs, and remove the resulting identity 3-cell using a 4-unitor.

Expression (18) has now been connected to
\[
(a\rho_b^{\mathrm{rev}});
\mathfrak a^{\mathrm{rev}}_{a,b,i};
(Ai);
\mathfrak a_{c,d,i};
(c\rho_d).
\tag{21}
\]

The cancellation used here is fully specified by (20). It requires no inverse for the cylinder generator \(A\).

### 3.6. Remove the remaining unitors

Direct 4-coherences on the respective vertical 2-cell chains \(a,b\) and \(c,d\) give
\[
(a\rho_b^{\mathrm{rev}});
\mathfrak a^{\mathrm{rev}}_{a,b,i}
\Longrightarrow
\rho_{ab}^{\mathrm{rev}},
\tag{22}
\]
\[
\mathfrak a_{c,d,i};(c\rho_d)
\Longrightarrow
\rho_{cd}.
\tag{23}
\]

Thus (21) is connected to
\[
\rho_{ab}^{\mathrm{rev}};(Ai);\rho_{cd}.
\]

Finally, over a single generic 3-disc \(Z:u\Rightarrow v\), take the direct coherence
\[
\rho_u^{\mathrm{rev}};(Z\mathbf1);\rho_v
\Longrightarrow Z.
\]
Substitute \(u=ab,v=cd,Z=A\). This completes (15).

Combining (13) with the \(T\)-whiskering of (15) gives
\[
R_4:\mathcal R\Rightarrow T;A.
\]
Define
\[
\boxed{
K_{\mathrm{mid}}=L_4*_3R_4^{\mathrm{rev}}.
}
\tag{24}
\]
Here \(R_4^{\mathrm{rev}}\) is obtained by reversing the sequence of constructed 4-coherences and reversing each primitive coherence’s endpoints.

### Arity summary

For reference, every comparison used in this calculation has one of the following arities:

| Comparison | Pasting arity before substitution |
|---|---|
| Reassociation of semicolon words | A chain of 3-discs |
| Preservation of 3-composition by a 2-whisker | A chain of 3-discs whiskered by a 2-disc |
| Equation (12) | \(D^2*_1D^3*_1D^2\) |
| Equations (16)–(17) | \(D^2*_1D^2*_1D^3\) |
| Interchange (19) | \(D^3*_1D^3\) |
| Equations (11), (22), (23) | \(D^2*_1D^2\) |
| Cancellation (20) | The path \(X,g^+\) |
| Identity preservation after (20) | \(D^2*_1D^2\) |
| Final unitor conjugation | \(D^3\) |

In each row, the terms being compared use every maximal generator of the stated arity, and their common type supplies the remaining boundary variables. This verifies the full-support side condition.

## 4. Assemble the requested unitor naturality term

Let
\[
\varrho_\alpha:
\alpha*_1\mathbf1_g\Longrightarrow\alpha
\]
be the right unitor in question 2. Put
\[
W_L=L(\varrho_\alpha):
L(\alpha\mathbf1_g)\Rightarrow a,
\]
\[
W_R=R(\varrho_\alpha):
R(\alpha\mathbf1_g)\Rightarrow d.
\]

The required cylinder endpoints are
\[
a_{\varrho_\alpha}=(W_Lb);A,
\tag{25}
\]
\[
b_{\varrho_\alpha}=C(A,J);(cW_R).
\tag{26}
\]

### 4.1. The two outside comparisons

There are direct 4-coherences
\[
H_L:
W_L\Longrightarrow\phi_L;r_a,
\tag{27}
\]
\[
H_R:
\phi_R;W_R\Longrightarrow r_d.
\tag{28}
\]

For (27), use the pasting arity
\[
D^2(\alpha^-)*_0D^1(Y).
\]
Both endpoints are 3-terms from \(L(\alpha\mathbf1_g)\) to \(a\), and both have full support in that arity.

For (28), use
\[
D^1(X)*_0D^2(\alpha^+).
\]
Both endpoints are 3-terms from \(dh\) to \(d\), with full support there.

In particular, \(\phi_L,\phi_R,\kappa,\ell\) in these formulas are their already specified substitution instances. Equations (27)–(28) do not require new naturality terms for them.

Set
\[
P=\phi_Lb.
\tag{29}
\]

Applying (27), distributing the whisker \(b\), and reassociating gives
\[
E_L:
a_{\varrho_\alpha}\Longrightarrow P;\mathcal L.
\tag{30}
\]

Starting from (26), expand \(C(A,J)\) using (2). Its last two factors are
\[
(c\phi_R);(cW_R).
\]
Combine these into \(c(\phi_R;W_R)\), apply \(cH_R\), and reassociate. This gives
\[
E_R:
b_{\varrho_\alpha}\Longrightarrow P;\mathcal R.
\tag{31}
\]

### 4.2. The final term

The requested 4-term is
\[
\boxed{
K_{\varrho_\alpha}
=
\bigl(
E_L*_3(P*_2K_{\mathrm{mid}})
\bigr)
*_3E_R^{\mathrm{rev}}.
}
\tag{32}
\]

Its sequence of 3-boundaries is
\[
a_{\varrho_\alpha}
\longrightarrow
P;\mathcal L
\longrightarrow
P;\mathcal R
\longrightarrow
b_{\varrho_\alpha}.
\]

Every primitive coherence in (32) has been specified above by its endpoints, pasting arity, and substitution. Hence
\[
\boxed{
Q\uparrow\operatorname{Var}(Q)
\vdash
K_{\varrho_\alpha}:
a_{\varrho_\alpha}\longrightarrow b_{\varrho_\alpha}.
}
\]

This answers **question 2 for the universal lower lifts (2) and (4)**.

## 5. A non-endomorphism example for question 1

Now let
\[
Q_1=(x,y,f:x\to y)
\]
and let \(S=Q_1\uparrow\operatorname{Var}(Q_1)\) be its lax square.

Put
\[
u=\mathbf1_f,\qquad v=u*_1u.
\]
Substitute in (32)
\[
f\mapsto f,\qquad
g\mapsto f,\qquad
\alpha\mapsto\mathbf1_f.
\]
The lifted substitution sends
\[
F,G\mapsto F,
\qquad
A\mapsto u^\uparrow,
\]
where \(u^\uparrow\) is precisely the universal identity lift (4).

The result is a 4-term \(K_0\) witnessing naturality of
\[
c_0=\rho_u:v\Longrightarrow u.
\tag{33}
\]
This is a non-endomorphism: \(v=u*_1u\) and \(u\) are different CaTT terms.

### Requiring literal outer arity \(Q_1\)

If the example must have the exact form in Conjecture N, take
\[
c=
\operatorname{coh}_{Q_1,v\to u}[\mathrm{id}_{Q_1}].
\tag{34}
\]
Its outer arity is \(Q_1\), whereas the outer arity of the term \(c_0\) in (33) is the 2-disc.

Both have the same type \(v\to u\), with full support in \(Q_1\). Therefore define
\[
\delta=
\operatorname{coh}_{Q_1,c\to c_0}[\mathrm{id}_{Q_1}],
\qquad
\delta^{\mathrm{rev}}=
\operatorname{coh}_{Q_1,c_0\to c}[\mathrm{id}_{Q_1}].
\tag{35}
\]
These are 4-terms.

Let
\[
U=u^\uparrow,\qquad V=v^\uparrow
\]
be the lower lifts already determined by (2) and (4). Define
\[
\boxed{
\begin{aligned}
K_c={}&
\left(
 \left(
   \bigl((\delta^-*_0Y)*_1F\bigr)*_2U
 \right)
 *_3K_0
\right)\\
&\quad *_3
\left(
 V*_2\bigl(F*_1(X*_0(\delta^{\mathrm{rev}})^+)\bigr)
\right).
\end{aligned}}
\tag{36}
\]

The first factor changes \(a_c\) to \(a_{c_0}\); the last changes \(b_{c_0}\) to \(b_c\). Thus
\[
\boxed{S\vdash K_c:a_c\longrightarrow b_c.}
\]

Equation (36) supplies the requested nontrivial instance in question 1, with syntactically unequal 2-source and 2-target and the required literal coherence arity. It uses the copies of \(\delta\), not a naturality term for \(\delta\).

## 6. An additional family that does not depend on the choice of lower lifts

There is also a general endomorphism result.

> **Endomorphism naturality.** Let \(Q\) be a pasting context, let \(u\) have full typed support in \(Q\), and let
> \[
> c:u\longrightarrow u.
> \]
> For every fixed valid lower lift \(U=u^\uparrow\), the type \(a_c\to b_c\) is inhabited. This holds in arbitrary dimension and with omitted staircase factors.

Here is the construction.

The coherence rule on \(Q\) gives
\[
\delta:c\longrightarrow\mathbf1_u,
\qquad
\delta^{\mathrm{rev}}:\mathbf1_u\longrightarrow c.
\]
Remove the final \(U\)-factor from the target staircase and the initial \(U\)-factor from the source staircase. Denote the resulting operations on \(c^\pm\) by \(T\) and \(S\). If \(\dim u=n\), then
\[
a_c=T(c^-)*_nU,
\qquad
b_c=U*_nS(c^+).
\]

For every staircase step, the comparison
\[
\mathbf1_a*_k b\longrightarrow\mathbf1_{a*_k b}
\]
or its left-handed version is a direct coherence on the pasting arity of the corresponding two discs. Apply these comparisons only to the factors actually present. Together with the whiskered copies of \(\delta\), they construct
\[
\ell:T(c^-)\longrightarrow\mathbf1_{a_u},
\qquad
r:\mathbf1_{b_u}\longrightarrow S(c^+).
\]

Now compose
\[
\boxed{
(\ell*_nU)
*_{n+1}\lambda_U
*_{n+1}\rho_U^{\mathrm{rev}}
*_{n+1}(U*_nr),
}
\tag{37}
\]
with fixed brackets. Its endpoints are exactly \(a_c,b_c\).

Unlike the non-endomorphism unitor construction, (37) works with the existing lower lift \(U\) without prescribing its formula.

## 7. Scope of the result

The construction establishes:

| Question | Result |
|---|---|
| Question 1: all parallel 3-terms of the lax square | Not established |
| Question 1: one non-endomorphism 3-coherence with explicit naturality 4-term | Established by (34)–(36), for the lower choices (2) and (4) |
| Question 2: vertical right unitor over the fully selected 2-disc | Established by (32), for those same universal choices |
| Question 3: RC(3) on all loop-free contexts or cylinders | Not established |
| Question 4: RC in all dimensions | Not established |
| Naturality of full endomorphism coherences, conditional on their fixed lower lift | Established by (37), in arbitrary dimension |

One refinement to §2.3 is needed for the broader induction: **strict compatibility and lower-dimensional boundary adjustment should be explicit induction invariants.** RC(\(n\)) applies only after the compared \(n\)-terms are literally parallel. It does not itself turn strict equality of their lower boundaries into syntactic equality. In dimension 2, path coherences supply that adjustment, so this does not obstruct your stated \(N_{\leq2}\) consequence.

The new unitor calculation avoids that general lifting issue. Its only nontrivial cancellation occurs on the 1-path \(X,g^+\); the comparison that moves \(A\) past that cancellation is formed on \(D^3*_1D^3\). Those two facts allow the required 4-term to be constructed without first proving RC(3) for the lax square.
