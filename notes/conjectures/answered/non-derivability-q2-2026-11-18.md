# Is ℕ provably a set in a coherence-style theory of ω-categories with limits and exponentials by shapes?

*A self-contained problem. No knowledge of the project that posed it is assumed. It is the one question left open by an earlier answer; §"What is known" says exactly what that answer proved.*

## Background

**The base theory.** Fix a dependent type theory 𝕋 for weak ω-categories in the style of CaTT (Finster–Mimram, LICS 2017): contexts of typed variables (objects, and cells between cells), and one term former `coh` producing cells between parallel composites over pasting contexts. Add to it, as rules stated by universal properties witnessed by cells (never by definitional equalities, and with no universe):
- **finite limits** in the ambient (∞,ω)-category of ω-categories: a terminal object ⊤, pullbacks, and *cotensors* `[⟦D⟧, C]` by finite shapes D;
- **finite colimits**: pushouts, coequalisers, coproducts, and lax colimits of finite diagrams;
- **R-A (free objects on finite computads):** for each finite context Γ, an object ⟦Γ⟧ such that maps `⟦Γ⟧ → C` correspond to substitutions Γ → C (up to cells at every level). In particular, for the loop `L = (x : ⋆, s : x → x)`, maps `⟦L⟧ → C` correspond to an object of C with an endo-1-cell.

Write `Hom_C(a, b)` for the pullback of `[⟦D¹⟧, C] → C × C` along `(a, b)`. Put `N := Hom_{⟦L⟧}(x, x)`, with `zero := 1_x` and `succ := – ; s`. Semantically (in the (∞,ω)-category of (∞,ω)-categories), ⟦L⟧ is the free category on one loop and N is the discrete set ℕ (the free weak ω-category on a graph is the free category on it).

**Truncation levels.** An object C is *n-truncated* (C trunc n) when parallel cells into C of level ≥ n + 1 are connected and cells of level n + 1 are invertible. Sets are the 0-truncated objects. A *truncation rule* `Trunc_n` gives for each X a reflection `|–| : X → ‖X‖_n` onto n-truncated objects (existence of extensions, and of cells between extensions agreeing on X).

**Derivability.** A rule is *derivable* if every instance of its conclusion is a term of 𝕋 (with the stated additional rules). Non-derivability can be shown by a model of the rules in which the conclusion fails, or by a normal-form argument on the syntax.

**The strengthened rules (the reading intended here).**
- **(E) Cotensors are cartesian exponentials by the realized shapes:** maps `A → [⟦D⟧, C]` correspond to maps `A × ⟦D⟧ → C`, for every object A, naturally and at every level.
- **Parameterised R-A:** for every object A, maps `A × ⟦Γ⟧ → C` correspond to substitutions of Γ into the hom ω-category of maps A → C.
- **Universal disjoint coproducts of sets:** Bool := ⊤ ⊔ ⊤ is a set, coproduct injections of sets are disjoint monos, and coproducts of sets are stable under pullback along any map.

## Statement

In 𝕋 + (E) + parameterised R-A + universal disjoint coproducts of sets (optionally + Trunc₀), is `N trunc 0` derivable? More generally, is "⟦Γ⟧ is 1-truncated for every finite graph Γ" derivable?

The expected answer is **no**. A "no" should come with a model in which (E), parameterised R-A and universal coproducts hold and N is not a set; a "yes" with a derivation.

## What is known

- **Semantically** the conclusion holds: in (∞,ω)-categories the free category on a graph is a 1-category and N is the discrete set ℕ.
- **Without (E) the answer is no (proved).** Let 𝒦 = (F ↓ id) for F : Spaces → D(ℤ), F(X) = H₁(X; ℤ)[1], regarded as locally groupoidal. Objects are (X, A, α : F(X) → A). It has all limits and colimits, enriched cotensors `Map(T, C^D) ≃ Map(|D|, Map(T, C))`, and R-A with ⟦Γ⟧ = (|Γ|, F|Γ|, id). There N ≃ (ℤ, ℤ[0], 0), and for E = (∅, ℤ[−1], 0), Map(E, N) ≃ K(ℤ,1), so N is not a set; Map(E, ⟦L⟧) ≃ K(ℤ,2). Sets are the (S, 0, 0) with S discrete; Bool is a set with disjoint injections. But (E) fails: with E₂ = (∅, ℤ/2[0], 0) and the two-point shape T(2) = (2, 0, 0), E₂ × T(2) ≃ E₂, so Map(E₂ × T(2), E₂) has 2 points while Sub(2, Map(E₂, E₂)) has 4.
- **Recursion and effectiveness are independent even with (E) (proved).** Recursion on N fails in categories with an auxiliary equivalence relation on objects (N is discrete ℕ with the total relation, so every map N → Bool is constant). Effectiveness of quotients fails in Pos with discrete homs. Both models satisfy (E). In both, N is a set, so neither bears on this question.
- **Where the obvious derivation stops.** A Hedberg-style proof (decidable equality N × N → Bool, then "eq(m,n) = true gives an invertible m → n") needs induction on m for all n at once, i.e. exponentials over N or induction with a varying parameter. The theory has exponentials only by shapes ⟦D⟧, and recursion on N is itself not derivable.
- **Observation.** In the comma model, R-A cannot detect the failure: maps from realized shapes into ⟦L⟧ form 1-types; the failure is seen only by the "phantom" objects E with empty underlying space. (E) and universal coproducts force products with shapes to behave like copowers, which kills that particular model.

## Candidate approaches

- Modify the comma construction so that products with realized shapes are copowers: e.g. glue along a functor F that is product-preserving in a suitable sense, or replace D(ℤ) by a cartesian closed target with a non-truncated "phantom" part.
- A syntactic normal-form argument: in context `c : ⋆`, `u, u' : c → ⟦L⟧`, `α, β : u → u'`, show no term `α → β` exists. Under (E), maps c × ⟦D¹⟧ → ⟦L⟧ are available, which is exactly what the earlier normal-form attempt did not account for.

## What would count as a solution

A model of the stated rules in which N (or some ⟦Γ⟧ for a finite graph Γ) is not appropriately truncated; or a derivation; or references.'

# Researcher Response

**No. There is a countermodel satisfying (E), parameterized R-A, universal disjoint coproducts, and \(\operatorname{Trunc}_0\).** In fact, it is cartesian closed. In this model,
\[
\operatorname{Map}(1,\llbracket L\rrbracket)
\simeq S^1\times K(\mathbb Z,2),
\qquad
\operatorname{Map}(1,N)
\simeq \mathbb Z_{\mathrm{disc}}\times K(\mathbb Z,1).
\]
Thus \(\llbracket L\rrbracket\) is not \(1\)-truncated and \(N\) is not \(0\)-truncated.

The construction uses an accessible monad on spaces. The main verification is that products with its free algebras are space-indexed copowers; this supplies exactly the strengthened parameterization.

## 1. The monad

Let \(\mathcal S\) denote the \(\infty\)-category of spaces. For \(c\in\pi_0X\), let \(X_c\) be the fiber of \(X\to\pi_0X\) at \(c\). Define
\[
M(X)=
\coprod_{c\in\pi_0X}
X_c\times K\!\left(H_1(X_c;\mathbb Z),2\right).
\tag{1}
\]
Here \(K(B,2)\) is the functorial simplicial abelian-group model of the Eilenberg–Mac Lane space, obtained by applying Dold–Kan to \(B[2]\). Its addition will define the monad multiplication. For the Dold–Kan construction, see *Higher Algebra*, Theorem 1.2.3.7. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HA.pdf?utm_source=chatgpt.com)

For \(f:X\to Y\), the restriction of \(M(f)\) to the summand indexed by \(c\) is
\[
(x,u)\longmapsto
\left(f(x),K(H_1(f|_{X_c}),2)(u)\right).
\]

Write \(p_X:MX\to X\) for projection. Since \(K(B,2)\) is connected and simply connected, \(p_X\) induces isomorphisms on \(\pi_0\) and on the first homology of each connected component. Consequently, there are natural identifications
\[
M^nX\simeq
\coprod_{c\in\pi_0X}
X_c\times K(H_1(X_c;\mathbb Z),2)^n.
\tag{2}
\]
Under these identifications, the unit inserts zero and multiplication adds the two new coordinates:
\[
\eta_X(x)=(x,0),
\qquad
\mu_X(x,u,v)=(x,u+v).
\tag{3}
\]

### Coherence of the monad

These formulas can be made into a strict monad before localization. Perform construction (1) on Kan complexes, with the simplicial abelian-group model of \(K(-,2)\). Write
\[
q_X=(p_X)_*:H_1(MX)\xrightarrow{\cong}H_1(X)
\]
componentwise. Without suppressing this identification, multiplication is
\[
\mu_X((x,u),v)
=
\left(x,u+K(q_X,2)(v)\right).
\tag{4}
\]

The unit identities follow from
\[
q_XH_1(\eta_X)=\mathrm{id}.
\]
For associativity, the identity
\[
p_X\mu_X=p_Xp_{MX}
\]
and invertibility of \(q_X\) imply
\[
H_1(\mu_X)=H_1(p_{MX})=q_{MX}.
\]
Both composites \(M^3X\to MX\) therefore send
\[
(x,u,v,w)
\longmapsto
\left(
x,\,
u+K(q_X,2)v+K(q_Xq_{MX},2)w
\right).
\]
Thus the monad identities hold strictly in this presentation. All the functors preserve weak equivalences, so localization gives a coherent monad on \(\mathcal S\).

### Preservation properties

The monad has three properties needed below.

First, **\(M\) preserves finite products**. For connected spaces,
\[
H_1(X_c\times Y_d;\mathbb Z)
\cong
H_1(X_c;\mathbb Z)\oplus H_1(Y_d;\mathbb Z).
\]
This follows from the product formula for \(\pi_1\) and the identification of \(H_1\) with the abelianization of \(\pi_1\); the latter is Hatcher’s Theorem 2A.1. [pi.math.cornell.edu](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf?utm_source=chatgpt.com)
Since
\[
K(B\oplus B',2)\simeq K(B,2)\times K(B',2),
\]
the canonical comparison
\[
M(X\times Y)\longrightarrow MX\times MY
\]
is an equivalence. Also \(M(*)=*\).

Second, **\(M\) preserves arbitrary coproducts**, directly from (1).

Third, **\(M\) is accessible**. Indeed, the construction commutes with filtered colimits: connected components and componentwise first homology are determined by finite paths, cycles, and relations, while \(K(-,2)\) commutes with filtered colimits degreewise. The products in (1) also commute with filtered colimits. The corresponding general fact for finite limits of spaces is *Higher Topos Theory*, Proposition 5.3.3.3. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HTT.pdf?utm_source=chatgpt.com)

In particular,
\[
M(S)=S
\tag{5}
\]
for every discrete set \(S\), including \(\varnothing\).

## 2. The ambient category

Set
\[
\mathcal C=\operatorname{Alg}_M(\mathcal S),
\qquad
F:\mathcal S\rightleftarrows\mathcal C:U.
\]
These are homotopy-coherent \(M\)-algebras.

Because \(M\) is accessible, \(\mathcal C\) is presentable. The applicable result is Henry–Meadows, *Higher Theories and Monads*, **Corollary 6.8**: an accessible monad on a presentable \(\infty\)-category has a presentable algebra \(\infty\)-category. Thus \(\mathcal C\) has all small limits and colimits. [dml.cz](https://www.dml.cz/bitstream/handle/10338.dmlcz/153486/HigherStructures_009-2025-1_5.pdf?utm_source=chatgpt.com)

We use the following monadic facts:

- \(U\) creates limits and reflects equivalences.
- Every algebra has a simplicial resolution by free algebras whose augmentation becomes split after applying \(U\).
- \(U\) detects the colimit property for these \(U\)-split augmented simplicial diagrams.

These follow from *Higher Algebra*, Corollary 4.2.3.3, Theorem 4.7.3.5, Remark 4.7.3.7, and Proposition 4.7.3.14. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HA.pdf?utm_source=chatgpt.com)

Since \(M\) preserves finite products and \(U\) creates them, the free functor preserves finite products:
\[
F(X\times Y)\simeq FX\times FY,
\qquad
F(*)\simeq1_{\mathcal C}.
\tag{6}
\]
The adjunction consequently gives
\[
\operatorname{Map}_{\mathcal C}(1,A)\simeq UA.
\tag{7}
\]
This identification will make the failure of truncation visible at the terminal probe.

## 3. Products with free algebras are copowers

For a space \(X\) and \(A\in\mathcal C\), write
\[
X\otimes A:=\operatorname*{colim}_{X}A
\]
for the space-indexed copower.

The crucial equivalence is
\[
\boxed{FX\times A\simeq X\otimes A}
\tag{8}
\]
naturally in both variables.

Here is a proof, including the passage from free algebras to arbitrary algebras.

### Products preserve the free bar resolutions

Let
\[
A_\bullet\longrightarrow A
\]
be the monadic bar resolution, with
\[
A_n=F(M^nUA).
\]
Its augmentation becomes split after applying \(U\).

For any \(B\in\mathcal C\), apply \(B\times-\). Since \(U\) creates products, the resulting underlying augmented diagram is
\[
UB\times UA_\bullet\longrightarrow UB\times UA.
\]
The extra degeneracy giving the original splitting remains an extra degeneracy after taking this product. Hence the new augmented diagram is also split after applying \(U\). By the monadic facts above,
\[
\left|B\times A_\bullet\right|\simeq B\times A.
\tag{9}
\]

This argument requires preservation only of these split resolutions.

### Establishing the comparison

Since \(F\) preserves colimits and \(F(*)=1\),
\[
FX\simeq X\otimes1.
\]
The universal \(X\)-indexed family of points of \(FX\) therefore induces a natural comparison
\[
c_{X,A}:X\otimes A\longrightarrow FX\times A.
\]

For a free algebra \(A=FY\), it is an equivalence:
\[
X\otimes FY
\simeq F(X\times Y)
\simeq FX\times FY.
\tag{10}
\]
For arbitrary \(A\), resolve \(A\) by the free algebras \(A_n\). The functor \(X\otimes-\) preserves colimits, and (9) shows that \(FX\times-\) preserves this resolution. Realizing the equivalences \(c_{X,A_n}\) proves (8).

There is also a stronger consequence. Resolving any \(B\) by free algebras \(B_n=FX_n\), equation (9) gives
\[
B\times-
\simeq
\operatorname*{colim}_{[n]\in\Delta^{op}}
(FX_n\times-).
\]
Each functor on the right is \(X_n\otimes-\), so preserves colimits. Therefore \(B\times-\) preserves colimits and, by presentability, has a right adjoint. **Thus \(\mathcal C\) is cartesian closed.**

## 4. Realizations, parameterized R-A, and (E)

Regard \(\mathcal C\) as a locally groupoidal higher category. Its homs are spaces.

For a finite computad \(\Gamma\), let \(|\Gamma|\) denote its groupoidal realization: the space representing \(\Gamma\)-shaped diagrams in \(\infty\)-groupoids. Define
\[
\llbracket\Gamma\rrbracket:=F(|\Gamma|).
\tag{11}
\]
For the one-loop computad,
\[
|L|\simeq S^1.
\tag{12}
\]

For arbitrary \(A,C\in\mathcal C\), equation (8) gives
\[
\begin{aligned}
\operatorname{Map}_{\mathcal C}
 \bigl(A\times\llbracket\Gamma\rrbracket,C\bigr)
&\simeq
\operatorname{Map}_{\mathcal C}(|\Gamma|\otimes A,C)\\
&\simeq
\operatorname{Map}_{\mathcal S}
 \bigl(|\Gamma|,\operatorname{Map}_{\mathcal C}(A,C)\bigr).
\end{aligned}
\tag{13}
\]
The last space is precisely the space of substitutions of \(\Gamma\) into the hom \(\infty\)-groupoid \(\operatorname{Map}_{\mathcal C}(A,C)\).

Equation (13) is natural and is an equivalence of whole spaces. It therefore verifies **parameterized R-A at every cell level**.

For (E), define the shape cotensor by
\[
[\llbracket D\rrbracket,C]
:=
\lim_{|D|}C.
\tag{14}
\]
Then
\[
\begin{aligned}
\operatorname{Map}_{\mathcal C}
 \bigl(A,[\llbracket D\rrbracket,C]\bigr)
&\simeq
\operatorname{Map}_{\mathcal S}
 \bigl(|D|,\operatorname{Map}_{\mathcal C}(A,C)\bigr)\\
&\simeq
\operatorname{Map}_{\mathcal C}
 \bigl(A\times\llbracket D\rrbracket,C\bigr).
\end{aligned}
\tag{15}
\]
Thus these cotensors are actual cartesian exponentials by the realized shapes.

The required limits and colimits exist by presentability. In this locally groupoidal interpretation, the comparison cells of a lax cone are invertible, so the required lax colimits are the corresponding homotopy-coherent colimits. The groupoidal interpretation also supplies the coherence operations of the base theory.

## 5. Universal disjoint coproducts and the sets

Because \(M\) preserves coproducts, \(U\) creates coproducts. Explicitly, the algebra structure on \(\coprod_i UA_i\) is
\[
M\!\left(\coprod_i UA_i\right)
\simeq
\coprod_i MUA_i
\longrightarrow
\coprod_i UA_i.
\tag{16}
\]
The general colimit-creation statement is *Higher Algebra*, Corollary 4.2.3.5, applied to coproducts and the powers of \(M\). [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HA.pdf?utm_source=chatgpt.com)

Since \(U\) also creates pullbacks and reflects equivalences, coproducts in \(\mathcal C\) are disjoint and stable under arbitrary pullback. More explicitly, for
\[
f:B\longrightarrow A_0\amalg A_1,
\qquad
B_i:=B\times_{A_0\amalg A_1}A_i,
\]
the canonical map
\[
B_0\amalg B_1\longrightarrow B
\tag{17}
\]
becomes an equivalence of spaces under \(U\), and hence is an equivalence in \(\mathcal C\). The pullback of the two distinct injections has underlying space \(\varnothing\), so it is initial. Their diagonals are equivalences, so the injections are monos.

These properties hold for all algebras, which is stronger than the stipulated condition for sets.

### Identifying the \(0\)-truncated algebras

Every discrete space \(S\) has a unique \(M\)-algebra structure, since \(MS=S\). For every algebra \(A\),
\[
\operatorname{Map}_{\mathcal C}(A,S)
\simeq
\operatorname{Hom}_{\mathbf{Set}}(\pi_0UA,S).
\tag{18}
\]

To verify this, let \(a:MUA\to UA\) be the algebra action. The unit identity implies that \(\pi_0a\) is the inverse of the canonical identification
\[
\pi_0UA\xrightarrow{\cong}\pi_0MUA.
\]
Every map \(UA\to S\) therefore respects the action on connected components. Since its target is discrete, the required compatibility homotopies and their higher coherences are unique. Equivalently, mapping the free bar resolution into \(S\) gives the constant cosimplicial set
\[
\operatorname{Hom}_{\mathbf{Set}}(\pi_0UA,S).
\]

Equation (18) proves that every discrete algebra is intrinsically \(0\)-truncated. Conversely, if \(A\) is intrinsically \(0\)-truncated, equation (7) implies that
\[
UA\simeq\operatorname{Map}_{\mathcal C}(1,A)
\]
is discrete. Consequently,
\[
\mathcal C_{\le0}\simeq\mathbf{Set}.
\tag{19}
\]
In particular,
\[
\mathrm{Bool}=1\amalg1\simeq F(\{0,1\})
\]
is the usual discrete two-element set.

### The optional truncation rule

Equation (18) supplies the reflector:
\[
\|A\|_0:=\pi_0UA,
\tag{20}
\]
equipped with its unique discrete algebra structure. The canonical map \(A\to\pi_0UA\) induces the required equivalence of mapping spaces into every set. Thus **\(\operatorname{Trunc}_0\) holds in this model**.

## 6. Computing the free loop and its endohom

By (11) and (12),
\[
\llbracket L\rrbracket=F(S^1).
\]
Hence
\[
U\llbracket L\rrbracket
=M(S^1)
\simeq
S^1\times K(\mathbb Z,2).
\tag{21}
\]
The designated vertex \(x\) is the basepoint with zero second coordinate.

In a locally groupoidal model, the hom defined from the arrow cotensor and its endpoint map is the based loop object. Therefore the \(N\) specified in the question is
\[
N\simeq1\times_{\llbracket L\rrbracket}1.
\tag{22}
\]
Since \(U\) creates pullbacks,
\[
\begin{aligned}
UN
&\simeq\Omega_x U\llbracket L\rrbracket\\
&\simeq\Omega\bigl(S^1\times K(\mathbb Z,2)\bigr)\\
&\simeq\mathbb Z_{\mathrm{disc}}\times K(\mathbb Z,1).
\end{aligned}
\tag{23}
\]

Using (7),
\[
\pi_1\operatorname{Map}_{\mathcal C}(1,N)
\cong\mathbb Z
\]
at the point designated by zero. Thus \(N\) is not a set. Similarly,
\[
\pi_2\operatorname{Map}_{\mathcal C}(1,\llbracket L\rrbracket)
\cong\mathbb Z,
\]
so \(\llbracket L\rrbracket\) is not \(1\)-truncated.

The \(\mathbb Z\) indexing in (23) reflects the locally groupoidal interpretation: the loop generator is invertible. This is permitted by the stated rules. The failure of discreteness is the additional \(K(\mathbb Z,1)\) factor, detected already by maps from the terminal algebra.

Therefore both proposed truncation rules are **non-derivable under the strengthened assumptions**, including after adjoining \(\operatorname{Trunc}_0\). The same countermodel satisfies full cartesian closure.

---

## Verification of the researcher response (2026-11-18)

**Verdict: correct. Question 2 is settled negatively even under the strengthened rules:** there is a model with (E), parameterised R-A, universal disjoint coproducts, Trunc₀, and in fact full cartesian closure, in which N is not a set and ⟦L⟧ is not 1-truncated. Checked step by step:

- **V1. The monad (1)–(4).** M(X) = ∐_c X_c × K(H₁(X_c), 2). Each component of MX is X_c × K(B,2) with H₁ = H₁(X_c) (K(B,2) is simply connected), giving (2); unit inserts 0, multiplication adds. The strict model on Kan complexes with simplicial abelian K(−,2) satisfies the monad laws (the composite M³X → MX computed both ways agrees), and all functors preserve weak equivalences, so it descends to a monad on 𝒮. **Confirmed** (the descent of a homotopical strict monad to a coherent one is standard; not re-derived).
- **V2. Preservation.** H₁(X_c × Y_d) = H₁(X_c) ⊕ H₁(Y_d) for connected spaces, so M preserves finite products; M(*) = *; M preserves coproducts by construction; H₁ and K(−,2) commute with filtered colimits, so M is accessible; M(S) = S for discrete S. **Confirmed.**
- **V3. Algebras (§2).** 𝒞 = Alg_M(𝒮) is presentable (Henry–Meadows Cor. 6.8, not re-read); U creates limits, U-split simplicial resolutions (HA 4.7.3.5). F preserves finite products because U creates them and M preserves them; Map(1, A) ≃ UA (7). **Confirmed.**
- **V4. Products with free algebras are copowers (8).** For A = FY: X ⊗ FY ≃ F(X × Y) ≃ FX × FY. For general A, B × − preserves the U-split bar resolution (extra degeneracy survives the product), so (9) holds and the comparison realises. Hence B × − ≃ colim_n (X_n ⊗ −) preserves colimits, so 𝒞 is cartesian closed. **Confirmed.**
- **V5. R-A and (E) (§4).** ⟦Γ⟧ = F|Γ|; Map(A × ⟦Γ⟧, C) ≃ Map(|Γ| ⊗ A, C) ≃ Map(|Γ|, Map(A, C)) is parameterised R-A at every level; [⟦D⟧, C] := lim_{|D|} C satisfies (E) by (15). **Confirmed.**
- **V6. Coproducts and sets (§5).** U creates coproducts and pullbacks and reflects equivalences, so coproducts are disjoint and universal for all algebras. Map(A, S) ≃ Set(π₀UA, S) for discrete S (the action is the inverse of π₀UA ≅ π₀MUA; coherences into a discrete target are unique), so 𝒞_{≤0} ≃ Set, Bool = F(2) = 2, and π₀U is the Trunc₀ reflector. **Confirmed.**
- **V7. The failure (§6).** U⟦L⟧ = M(S¹) = S¹ × K(ℤ,2). In the locally groupoidal model [⟦D¹⟧, C] ≃ C (|D¹| contractible), so N = 1 ×_{⟦L⟧} 1 and UN ≃ Ω(S¹ × K(ℤ,2)) ≃ ℤ × K(ℤ,1). By (7), π₁ Map(1, N) = ℤ and π₂ Map(1, ⟦L⟧) = ℤ. **Confirmed.**

**Consequences for F3b.** `N trunc 0` and "⟦Γ⟧ is 1-truncated for finite graphs Γ" are **not derivable** from 𝕋 + (E) + parameterised R-A + universal disjoint coproducts + Trunc₀, nor with full cartesian closure (so F8, exponentials of sets, does not by itself give them). `ordinary-math.md` Prop. 2.5 (T-graph not derivable from R-A) is now proved for the project's reading, and T-graph must stay a rule. The Hedberg route (§2.3) can only succeed with rules beyond these (recursion and DJ; recursion is itself not derivable, `non-derivability-2026-11-18.md` Q1). No follow-up prompt.
