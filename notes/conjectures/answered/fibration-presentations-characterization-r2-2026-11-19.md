# Grothendieck constructions over free bases: which bases admit Gray-generator presentations, and a uniform localised presentation

*A self-contained problem. It assumes familiarity with (∞,ω)-categories, the Gray tensor product, polygraphs (computads) and Grothendieck constructions, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** Two exact answers valid in **every** dimension:
- a characterization of the bases (and weights) for which the relative Gray-generator presentation of §2, or any presentation of bounded dimension, presents the fibration;
- one uniform, explicitly described localised presentation that works for every homotopical base.

The expected presentation is now known to fail from base dimension 4 (§3 item 9), and existence of *some* finite presentation is known (item 10). Neither is the answer: the counterexample is one shape, and the existence proof goes through complicial models with no control on generators or dimension. A further counterexample, or a further special class, is not what we want.

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
9. **The expected presentation fails from base dimension 4.** Base Γ: one vertex b, a : b → b, μ : aa ⇒ a, an associator α : (μ₁;μ₀) ⇛ (μ₀;μ₀) (words in right-to-left order; a subscript is the position of the rewrite), and a pentagon 4-generator P. Fibre Π: x, g : x → x, δ : g ⇒ gg, κ : (δ₀;δ₁) ⇛ (δ₀;δ₀). Weight: T(b) = F₃(Π), T(a) = Z the constant functor at x, T(μ)_x = g, T(α)_x = δ, T(P)_x = κ.
   - Both polygraphs and all their skeleta are homotopical: Π is the oriental polygraph of the semisimplicial set with one simplex in each dimension ≤ 3, and Γ is the even dual of the one for dimension ≤ 4 (Chanavat, arXiv 2603.22242, Thm 3.35).
   - With the fibre-first Leibniz convention ∂(g ⊗ q) = ∂g ⊗ q + (−1)^{|g|} g ⊗ ∂q, the mixed generators are t = a ⊗ x, c : t ⇒ tg, u : gtt ⇒ t, and the 3-generators D = a ⊗ δ, M = μ ⊗ g : (u₀;c₀) ⇛ (c₂;u₀), V = α ⊗ x : (c₁;u₂;u₀) ⇛ (δ₀;u₁;u₀), together with κ.
   - The 2-cells gt⁴ ⇒ t are 8 (18 rewriting paths up to interchange). Every contextual instance of a 3-generator gives exactly 8 edges. Over the short side R → E → L of the pentagon, the only V-step out of the lift of R lands at a vertex with no outgoing edge. So the target face of P ⊗ x does not exist in the unlocalised category: it would need M⁻¹, which exists only after localisation. No weak attaching map can repair this, since it would project to the missing strict 3-cell.
   - Reversing M repairs this pentagon but changes M's Gray boundary.
10. **Finite presentations exist, with auxiliary generators.** For every finite polygraph Γ with homotopical skeleta, and every (∞,ω)-functor T : F(Γ) → ω whose values have finite weak polygraphic presentations (localisations allowed), ∫T has a presentation (Free(Ψ), ⟨Q ∪ S⟩)[S⁻¹] with Ψ finite and homotopical and Q, S finite sets of positive-dimensional generators, keeping the cartesian marking. The proof gives no dimension bound and no control of the generators. It goes through finite complicial models: closure under finite homotopy pushouts and products, and a conversion L_d of a finite stratified simplicial set into a finite semisimplicial set whose oriental polygraph is homotopical. It then inducts over the base cells with Loubaton's pullback–colimit theorem and the suspension classification for globes. For weights whose values are ≃ F(Π_b), the weight can moreover be made strict, since the homs of ω between gaunt strict categories are gaunt.
11. **Homotopicality of the base passes to skeleta.** The inclusion F(Γ_{≤r}) ↪ F(Γ) is discrete Conduché (the generator support of a strict cell is well defined and additive), so pulling back along it preserves colimits (Loubaton Thm 2.2.2.10), and the comparison for Γ_{≤r} is a pullback of the comparison for Γ. Hence Γ is homotopical iff all its skeleta are.

## 4. Questions

**Question 1 (main: characterization).** For which finite homotopical polygraphs Γ (and strict weights T with values F_m(Π_b), Π_b finite and homotopical) is the relative Gray-generator presentation of §2 well defined, meaning that every generator q ⊗ g has an attaching map in the unlocalised Free(Ψ), and correct? Give an exact criterion that can be checked on finite data in every dimension. Two natural forms:
- (a) a condition on Γ alone that makes the presentation work for every such weight (for example a positivity or orientation condition on how the generators' boundaries compose, ruling out item 9's mismatch between the base associator's direction and the fibre correction);
- (b) a condition on the pair (Γ, T).

Prove necessity and sufficiency. If no condition on Γ alone suffices, show it, and give the criterion on pairs.

**Question 2 (bounded dimension).** Characterize the pairs (Γ, T) admitting *some* finite presentation of dimension ≤ n + m, or of dimension bounded by a function of n and m. In particular, does item 9's base and weight have a presentation of dimension ≤ 7? Is there a uniform bound for all pairs?

**Question 3 (a uniform localised presentation).** Give one explicit presentation, defined for every finite homotopical Γ and every weight with finite homotopical fibres, built from the Gray generators q ⊗ g plus **explicitly described** auxiliary generators, with an explicit localisation set and a dimension bound, and prove it presents ∫T. Natural candidates:
- adjoin inverse data (a reverse cell and two cancellation cells) for the mixed generators that are inverted anyway, before attaching higher generators;
- use a resolution of the base (for example a homotopically equivalent polygraph with better orientation properties) and transport the fibration;
- construct the unlocalised presentation as a strict, functorial lax Grothendieck construction on F(Γ) and prove once, by cellular induction, that localisation gives ∫T.

State the finite certificate: the data a proof checker must check.

**Question 4 (weights with non-free values).** Extend Question 3 to weights whose values are finite localisations Free(Π_b)[W_b⁻¹] and whose transport functors are given only up to equivalence.

## 5. What counts as a solution

A characterization with proof for Question 1 or 2; an explicit uniform presentation with proof and certificate for Question 3; or a published reference.

## 6. Literature (searched 2026-11-19)

- Loubaton, arXiv 2406.05425 (left cartesian fibrations, straightening, pullback preserves colimits, discrete Conduché functors); Loubaton, arXiv 2207.08504 (complicial model).
- Campion, arXiv 2311.00205 and 2311.00200; Chanavat, arXiv 2603.22242 (homotopy polygraphs, semisimplicial pasting theorem).
- Ara–Guetta, arXiv 2503.08832, §7 (strict Grothendieck construction with Gray functoriality; its total is the strict, not the Gray, construction).
- No published recognition theorem for Gray-generator presentations of Grothendieck constructions over polygraphs was found.

# Researcher Response

**Every pair in Question 2 admits a finite presentation of dimension at most \(n+m\). This bound is optimal uniformly in \(n,m\).** In particular, the pentagon example admits some presentation of dimension at most \(7\).

The point missing from the finite-existence argument is a dimension-controlled realization lemma. Its proof separates the cells of a presentation from the cells used to certify that a marking is harmless.

I give the lemma, the resulting construction, and its finite certificate below. The construction produces an explicit oriental refinement of the local Gray generators. Their boundaries pass through auxiliary generators; it does not preserve the original fibre computads as literal subcomputads. The recognition problem for the unaugmented prescription in Question 1 remains separate.

## 1. The dimension theorem

Write \(\dim\Pi_b\le m\).

**Theorem.** Let \(\Gamma\) be a finite homotopical \(n\)-polygraph. Let
\[
T:F(\Gamma)\longrightarrow\omega
\]
be a coherent functor whose values admit presentations
\[
T(b)\simeq \mathrm{Free}(\Pi_b)[W_b^{-1}]
\]
with \(\Pi_b\) finite of dimension at most \(m\), and \(W_b\) sets of generators. Then there are a finite homotopical polygraph \(\Psi\), finite sets \(Q,S\) of positive-dimensional generators, and a map to the base, such that
\[
\dim\Psi\le n+m
\]
and
\[
\bigl(\mathrm{Free}(\Psi),\langle Q\cup S\rangle\bigr)[S^{-1}]
\simeq
\bigl(\textstyle\int T,\operatorname{Cart}_p\bigr)
\]
over \(\mathrm{Free}(\Gamma)\simeq F(\Gamma)\).

Here \(S\) specifies intrinsic equivalences, while \(Q\) specifies the additional cartesian marking.

Consequently:

- **The characterization requested in Question 2 is: every pair in the stated class.**
- The optimal uniform dimension bound is
  \[
  \boxed{f(n,m)=n+m.}
  \]
- The dimension bound also holds for the weak weights and localized fibre values in Question 4.

The proof does not require strictifying \(T\).

## 2. A dimension-controlled realization lemma

Work in the saturated \(\omega\)-complicial model category of stratified simplicial sets. Throughout this section, “thin” concerns intrinsic equivalences, not the external cartesian marking.

We use two model facts. Cofibrations are monomorphisms; and a map with fibrant codomain is a fibration precisely when it lifts against complicial horns, complicial marking extensions, and saturation extensions. The last two kinds of extensions change only markings. These statements are recorded in Doherty–Kapulkin–Maehara, Theorem 1.12(2). [arxiv.org](https://arxiv.org/pdf/2106.09428?utm_source=chatgpt.com)

### Lemma 2.1: bounded relative realization

Suppose:

- \(K\) is a finite stratified simplicial set;
- \(E\) is fibrant;
- \(e:K\to E\) is a weak equivalence;
- \(A_0\hookrightarrow A\) is a finite simplicial inclusion, with \(\dim A=d\);
- maps \(A_0\to K\) and \(A\to E\) agree over \(E\).

Then there is a finite extension
\[
K\hookrightarrow K'
\]
and a commuting relative lift
\[
A\longrightarrow K'\longrightarrow E
\]
such that \(K\hookrightarrow K'\) is a weak equivalence and
\[
\boxed{\dim K'\le \max\{\dim K,d+1\}.}
\]

The lift agrees with the prescribed map on \(A_0\).

### Proof

#### Step 1: reflect thin markings from \(E\)

For a map \(u:X\to E\), define \(X_E\) to have the same underlying simplicial set as \(X\), with
\[
\sigma\text{ thin in }X_E
\quad\Longleftrightarrow\quad
u(\sigma)\text{ thin in }E.
\]

If \(u\) is a weak equivalence, then
\[
X\longrightarrow X_E
\]
is a trivial cofibration.

Indeed, marking a simplex localizes at the top cell of its oriental. Every newly marked cell is already an equivalence in the category presented by \(X\): its image is an equivalence under the equivalence presented by \(u\). Thus this additional localization changes nothing. The interpretation of simplex marking as localization is explicit in Loubaton, Construction 3.3.2.4 and Remark 3.3.2.5. [arxiv.org](https://arxiv.org/pdf/2207.08504?utm_source=chatgpt.com)

#### Step 2: complete using relative horns

Start with \(K_E\). At each stage, attach a simplex for **every** commutative square
\[
\begin{array}{ccc}
\Lambda^i[r]&\longrightarrow&X\\
\downarrow&&\downarrow\\
\Delta^i[r]&\longrightarrow&E,
\end{array}
\]
and then reflect thin markings from \(E\).

Thus a simplex is attached for each pair consisting of a horn map and a specified extending simplex in \(E\). No choice of fillers is needed to define this completion. Repeat for \(\omega\) stages and denote the result by \(R_EK\).

Every horn attachment is a trivial cofibration. After each attachment stage, reflection of markings is a trivial cofibration by Step 1. Therefore
\[
K\longrightarrow R_EK
\]
is a trivial cofibration, and \(R_EK\to E\) is a weak equivalence.

The map \(R_EK\to E\) has the right lifting property against relative complicial horns by construction. It also lifts against thinness and saturation extensions: their underlying simplicial maps are identities, and every required marking is already present by reflection from \(E\).

The fibration characterization therefore makes
\[
R_EK\longrightarrow E
\]
a trivial fibration. It supplies an **exact** lift \(A\to R_EK\), relative to \(A_0\).

#### Step 3: retain finite ancestry

A horn attachment of dimension \(r\) introduces only:

- its missing \((r-1)\)-face;
- its top \(r\)-simplex.

Consider the finitely many simplices used by \(A\to R_EK\). Every such simplex has dimension at most \(d\). If it was newly introduced, its birth horn has dimension at most \(d+1\).

Retain that horn and recursively retain the birth horns of the simplices used by its attaching map. The attaching domain of a horn of dimension at most \(d+1\) has dimension at most \(d\). Hence this recursion never requires a horn of dimension greater than \(d+1\).

Each attaching domain is finite, and ancestor stages strictly decrease in \(\mathbb N\). The resulting dependency set is finite.

Replay these finitely many horn attachments starting from \(K\), reflecting markings after each step. Call the result \(K'\). Each replayed step remains a weak equivalence over \(E\), and
\[
\dim K'\le\max\{\dim K,d+1\}.
\]
The selected lift factors through \(K'\). ∎

**The reflection step is essential.** Without it, a marking required on a \(d\)-simplex can depend on a thinness or saturation derivation using higher-dimensional simplices. After reflection, its marking depends directly on its image in \(E\), so those higher-dimensional derivations need not be included in \(K'\).

### Lemma 2.2: finite certificates for reflected markings

Reflection does not require a semantic oracle in the certificate.

Suppose \(K^+\) is obtained from a finite \(K\) by adding finitely many thin markings. A sufficient finite certificate that \(K\to K^+\) is a weak equivalence consists of a finite elementary-anodyne extension
\[
K\longrightarrow H
\]
in which every newly marked simplex is already thin.

Then
\[
H\amalg_K K^+=H.
\]
Consequently \(K^+\to H\) is a pushout of the trivial cofibration \(K\to H\), and two-out-of-three proves that \(K\to K^+\) is a weak equivalence.

Such a certificate exists for every reflected-marking step above. To see this, take an ordinary saturated fibrant replacement
\[
K\hookrightarrow R(K)
\]
built from elementary horn, thinness, and saturation extensions. Since \(K\to K^+\) is a trivial cofibration, it extends over \(R(K)\). Because \(K\) and \(K^+\) have the same underlying simplicial set, the additional markings already hold on their corresponding simplices in \(R(K)\). Their finite ancestry gives the required finite \(H\).

There is **no dimension bound on \(H\)**. It belongs to the proof certificate, not to the output presentation.

## 3. The resulting dimension calculus

For a category \(X\), say that \(X\) has a finite complicial model of dimension \(a\) when a finite stratified simplicial set of dimension at most \(a\) presents \(X\).

### Controlled homotopy pushouts

Suppose \(A,B,C\) have finite models of dimensions \(a,b,c\), respectively. For an arbitrary span
\[
B\longleftarrow A\longrightarrow C,
\]
Lemma 2.1 realizes both maps through finite equivalent extensions \(B',C'\) with
\[
\dim B'\le\max\{b,a+1\},
\qquad
\dim C'\le\max\{c,a+1\}.
\]

The double mapping cylinder
\[
B'
\amalg_{A\times\{0\}}
\bigl(A\times\Delta[1]^t\bigr)
\amalg_{A\times\{1\}}
C'
\tag{3.1}
\]
presents the homotopy pushout. The complicial model structure is cartesian and left proper, with all simplicial sets cofibrant; the marked interval supplies the cylinder used here. [arxiv.org](https://arxiv.org/pdf/1809.10621?utm_source=chatgpt.com)

Its dimension is bounded by
\[
\boxed{
\dim\operatorname{hpo}(B\leftarrow A\to C)
\le \max\{b,c,a+1\}.
}
\tag{3.2}
\]

The inclusions of \(B'\) and \(C'\) into (3.1) are monomorphisms. Indeed, their coproduct inclusion is the pushout of
\[
A\times\partial\Delta[1]\hookrightarrow A\times\Delta[1].
\]
This will preserve distinguished generator representatives.

### Products

If \(K,L\) are finite of dimensions \(a,b\), then \(K\times L\) is finite of dimension at most \(a+b\).

For completeness, an \(r\)-simplex of the product comes from simplices of nondegenerate dimensions \(p\le a\) and \(q\le b\). If the pair is nondegenerate, their sets of degeneracy positions are disjoint. Thus
\[
(r-p)+(r-q)\le r,
\]
so \(r\le p+q\le a+b\).

Since the complicial model structure is cartesian,
\[
\boxed{\dim(X\times Y)\le a+b}
\tag{3.3}
\]
in this finite-model sense.

### Finite localized polygraphs

Every finite polygraph \(\Pi\) of dimension \(m\), with generator-localization set \(W\), has a finite complicial model of dimension at most \(m\).

Build \(\mathrm{Free}(\Pi)\) by its globe attachments. Finite complicial globe models are
\[
G_r=\Sigma^r\Delta[0],
\qquad
\partial G_r=\Sigma^r\varnothing.
\]
Their dimensions are at most \(r\) and \(r-1\). Loubaton constructs suspension from the Gray interval product by endpoint pushouts, so each suspension increases dimension by at most one. [arxiv.org](https://arxiv.org/pdf/2207.08504?utm_source=chatgpt.com)

Apply (3.2) at each generator attachment. Attaching an \(r\)-generator requires no simplex dimension greater than \(r\). Keep its actual globe copy in the mapping-cylinder pushout.

Finally, make the representatives of the generators in \(W\) thin. This implements the desired localization without adding simplices.

This argument concerns \(\mathrm{Free}(\Pi)\); it does not require comparing it with \(F(\Pi)\).

## 4. Applying the calculus to the total

Let
\[
E_X:=X\times_{F(\Gamma)}\int T
\]
for a map \(X\to F(\Gamma)\).

### Totals over globes

For \(k\ge1\), write
\[
D_k=\Sigma D_{k-1}.
\]
Let \(A,B\) be the fibres over its two vertices and put \(C=D_{k-1}\).

The suspension classification gives
\[
E_{D_k}\simeq
(A\times K_C)
\amalg^h_{A\times C}
B,
\qquad
K_C=1^{co}\star C.
\tag{4.1}
\]
This is Loubaton’s Corollary 4.1.2.19, with the representable total identified with the cojoin cone as in the supplied suspension result. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The finite cone construction has dimension at most \(\dim C+1\): it is built from an interval tensor product by endpoint pushouts. [arxiv.org](https://arxiv.org/pdf/2207.08504?utm_source=chatgpt.com)

Therefore the three terms in (4.1) have models with dimensions bounded by
\[
m+k,\qquad m+k-1,\qquad m,
\]
respectively. Equation (3.2) gives
\[
\boxed{\dim E_{D_k}\le m+k.}
\tag{4.2}
\]

### Totals over globe boundaries

For \(k\ge2\),
\[
\partial D_k=\Sigma\partial D_{k-1}.
\]
Use (4.1) with \(C=\partial D_{k-1}\), of dimension \(k-2\). The same calculation gives
\[
\boxed{\dim E_{\partial D_k}\le m+k-1.}
\tag{4.3}
\]

For \(k=1\), the boundary total is the coproduct of the two fibres, so its bound is \(m\), again agreeing with (4.3).

### Cellular induction on the base

By the supplied skeleton result, all skeleta of \(\Gamma\) are homotopical. Its \(k\)-generator attachment square is therefore a homotopy pushout. Pullback along the classified fibration preserves that pushout, by the supplied pullback–colimit theorem.

Thus
\[
E_{\Gamma_{\le k}}
\simeq
E_{\Gamma_{\le k-1}}
\amalg^h_{\coprod_q E_{\partial D_k}}
\coprod_q E_{D_k}.
\tag{4.4}
\]

Assume the previous stage has a finite model of dimension at most \(m+k-1\). Equations (4.2), (4.3), and (3.2) give
\[
\dim E_{\Gamma_{\le k}}
\le
\max\{m+k-1,\ m+k,\ (m+k-1)+1\}
=m+k.
\]

Starting with the coproduct of the vertex fibres proves
\[
\boxed{
\int T\text{ has a finite complicial model of dimension at most }n+m.
}
\tag{4.5}
\]

All constructions can be performed over a fixed fibrant model of the base. Lemma 2.1 then supplies lifts over that base, so the result presents the map \(p\), not merely its total category.

### Retaining the cartesian marking

The local globe presentations generate their cartesian marking, apart from intrinsic equivalences, by lifts of base cells at fibre vertices. These have dimension at most \(k\). Positive-positive mixed generators are localized and consequently require no additional external marking.

Taking the finite union of these local marking generators gives generators for the global cartesian marking, all of dimension at most \(n\). This follows from the marked suspension construction and the marked colimits used in (4.4).

If \(m\ge1\), realize these finitely many marked cells in the model from (4.5), using Lemma 2.1. The required dimension is at most
\[
\max\{n+m,n+1\}=n+m.
\]
Record their simplex representatives in a separate external-marking list.

If \(m=0\), the fibres are discrete and every total cell is cartesian. Marking every positive-dimensional generator of the output presents the required marking.

Thus the cartesian marking does not increase the bound.

## 5. An explicit finite polygraph

Set \(D=n+m\), and let \(K\) be the finite stratified simplicial model just constructed, including its external-marking representatives.

Define a finite semisimplicial set \(X=L_D^{ss}K\) by
\[
X_r=
K_r\times\operatorname{Inj}([r],[D]),
\qquad 0\le r\le D,
\tag{5.1}
\]
and \(X_r=\varnothing\) for \(r>D\). Here \(K_r\) includes degenerate simplices.

Writing an injection as \(I=(i_0<\cdots<i_r)\), define
\[
d_a(\sigma,I)
=
\bigl(d_a\sigma,\,
i_0<\cdots<\widehat{i_a}<\cdots<i_r\bigr).
\tag{5.2}
\]

Freely adjoin simplicial degeneracies, and declare the generator \((\sigma,I)\) thin exactly when \(\sigma\) is thin in \(K\). Denote the resulting stratified simplicial set by \(L_DK\).

### Why \(L_DK\to K\) is an equivalence

The projection
\[
\pi:L_DK\longrightarrow K,\qquad (\sigma,I)\longmapsto\sigma
\tag{5.3}
\]
is a weak equivalence.

Here is a direct verification. For \(K=\Delta[p]\), \(p\le D\), its source is the nerve of the poset with elements
\[
(x,i),\qquad x\in[p],\ i\in[D],
\]
and order
\[
(x,i)\le(y,j)
\quad\Longleftrightarrow\quad
(x,i)=(y,j)
\ \text{or}\ 
(x\le y\text{ and }i<j).
\]

The projection has section
\[
s(x)=(x,x).
\]
Define
\[
F(x,i)=(x,\max\{i,x\}).
\]
There are natural transformations
\[
\operatorname{id}\Longrightarrow F
\Longleftarrow s\pi,
\]
both over \(\Delta[p]\). With the pullback stratification, these give marked-interval homotopies. Hence \(\pi\) is a weak equivalence on \(\Delta[p]\), including its top-marked version.

The construction preserves colimits and monomorphisms. Finite induction over simplex attachments and marking attachments therefore proves (5.3) for every finite \(K\) of dimension at most \(D\).

### Generators and boundaries

Let \(\Psi\) be the oriental polygraph of \(X\). Explicitly, it has one \(r\)-generator
\[
[\sigma;I]
\]
for every pair in (5.1). In particular,
\[
\boxed{
|\Psi_r|=|K_r|\binom{D+1}{r+1},
\qquad
\dim\Psi\le D.
}
\tag{5.4}
\]

Its boundary is defined by the **actual oriental attaching map**: take the top globular generator of \(O_r\), and map each of its proper simplex faces using (5.2). Thus the standard oriental source and target pastings determine the globular source and target.

This specifies more than an alternating chain boundary. All coface compatibility equations follow from the semisimplicial identities in (5.2). The resulting polygraph is homotopical by Chanavat’s semisimplicial pasting theorem, Theorem 3.35. [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

The localization set is
\[
\boxed{
S=
\{[\sigma;I]\mid \dim\sigma>0,\ \sigma\text{ is thin in }K\}.
}
\tag{5.5}
\]

For each chosen external cartesian marking representative
\(\sigma_\lambda\in K_{r_\lambda}\), put
\[
[\sigma_\lambda;0<1<\cdots<r_\lambda]
\]
in \(Q\). Then
\[
\bigl(\mathrm{Free}(\Psi),\langle Q\cup S\rangle\bigr)[S^{-1}]
\simeq
(\int T,\operatorname{Cart}_p).
\tag{5.6}
\]

The map to the base is induced by
\[
L_DK\longrightarrow K\longrightarrow N_{\!RS}F(\Gamma).
\]
Its values on the oriental generators give the finite generator assignments to \(F(\Gamma)\). Every generator in \(S\) maps to an identity, so the map descends through localization.

### The relation to the Gray generators

In the strict free-fibre case, begin the local construction with the valid Gray presentations over individual globes. When converting such a presentation to a finite complicial model, retain a distinguished principal simplex \(\sigma_h\) for every generator \(h\).

These simplices remain distinct and nondegenerate: horn extensions and the inclusions into the mapping cylinders (3.1) are monomorphisms.

Select:

- each fibre generator from its vertex-fibre model;
- each \(q\otimes g\) from the local model over the corresponding base generator \(q\).

In the final polygraph, designate
\[
[\sigma_h;0<1<\cdots<\dim h]
\tag{5.7}
\]
as the generator indexed by \(h\). Every remaining generator in (5.4) is an explicitly indexed auxiliary generator. The designated \(q\otimes g\) has dimension \(k+j\), and it belongs to \(S\) when \(j>0\).

The precise limitation is that these are **oriental refinements of the local Gray cells**. Their original endpoints and attaching words need not remain literal. For example, a fibre loop represented by a principal edge \(\sigma_g\) gives
\[
[\sigma_g;0<1]:(x,0)\longrightarrow(x,1);
\]
auxiliary localized arrows relate these vertex copies.

Thus this construction supplies a uniform presentation with distinguished base–fibre generators and explicit auxiliary boundaries. It does not assert that \(\Pi_b\) embeds unchanged as a subcomputad, or that the obstructed original Leibniz words become valid without refinement.

## 6. Construction by finite search and its certificate

The use of a fibrant semantic target in Lemma 2.1 can be replaced by finite data.

A derived map into the category presented by a finite \(K\) can be specified by a finite roof
\[
A\xrightarrow{\alpha}H\xleftarrow{\sim}K,
\tag{6.1}
\]
where \(K\to H\) is a finite elementary-anodyne extension. Such roofs exist: represent the map into an ordinary fibrant replacement of \(K\), and take the finite ancestry of its image.

For this finite input, enumerate tuples consisting of:

1. a finite extension \(K\hookrightarrow K'\) using horns of dimension at most \(\dim A+1\) and additional thin markings;
2. a finite marking certificate from Lemma 2.2 for every additional marking;
3. a map \(A\to K'\);
4. a finite elementary-anodyne extension \(H\to H^+\);
5. a map \(K'\to H^+\) making the two maps from \(A\), and the two maps from \(K\), literally equal.

All these conditions are checks on finite simplicial data. Fix an enumeration and take the first valid tuple.

This search terminates. Apply Lemma 2.1 with
\[
E=R(H).
\]
The resulting finite \(K'\to E\) factors through a finite elementary-anodyne extension \(H^+\) of \(H\), by finite ancestry. Since \(H^+\to E\) is a monomorphism, the required equalities hold already in \(H^+\).

The output dimension remains
\[
\dim K'\le\max\{\dim K,\dim A+1\}.
\]
The possibly higher-dimensional complexes \(H^+\) and the marking witnesses are certificate data.

A certificate for the complete construction consists of the following finite data.

| Data | What is checked |
|---|---|
| Base and fibre presentations | Generator dimensions, source and target expressions, and the supplied homotopicality certificates |
| Weight representatives | Transport maps and the coherences identifying their restrictions on generating boundaries |
| Bounded realizations | Horn histories, marking witnesses, finite roofs, and the commuting diagrams above |
| Local totals | The suspension spans and their actual finite gluing maps |
| Global assembly | The mapping-cylinder pushouts corresponding to base attachments |
| Marking representatives | The finite list generating the cartesian marking |
| Final polygraph | Equations (5.1)–(5.2), oriental boundaries, \(Q\), \(S\), and the map to \(\Gamma\) |

The checker verifies the finite incidence tables, simplicial identities, elementary-anodyne steps, pushout descriptions, and stated equalities. Correctness then follows from the fixed lemmas proved above, the suspension classification, and pullback preservation of the base’s cellular colimits.

There is no asserted bound on certificate size or certificate dimension. The theorem bounds the dimension of the **presentation**.

### Weak weights and localized fibres

For Question 4, start each fibre with its given finite localized presentation. Section 3 produces a finite complicial model of dimension at most \(m\). The suspension formula (4.1) applies to the coherent transport map
\[
A\times C\longrightarrow B
\]
without requiring strict representatives between the original polygraphs. The bounded realization procedure supplies the actual maps used in the finite construction.

The additional certificate data are finite representatives of:

- transport functors on the presented fibres;
- their compatibility with the fibre localization sets;
- the higher transformations assigned to base generators;
- the coherences identifying their restrictions along the base attaching maps.

These must specify the coherent functor \(T\), not merely unrelated equivalence classes of individual transport functors. Once supplied in finite model form, the construction and verification above apply unchanged.

## 7. Optimality of \(n+m\)

Assume first that \(n,m>0\). Take
\[
\Gamma=\partial D_{n+1},
\qquad
\Pi=\partial D_{m+1},
\]
and the constant weight with value \(F(\Pi)\).

These finite globular-boundary polygraphs are homotopical. Their groupoidifications are \(S^n\) and \(S^m\), and the total is their cartesian product.

One can compute its top homology directly from the mixed-product presentation in the supplied item 2. Its cellular differential is the tensor-product differential. If \(s_n,t_n\) are the two top base cells and \(s_m,t_m\) the two top fibre cells, then
\[
(s_n-t_n)\otimes(s_m-t_m)
\]
is a nonzero cycle in degree \(n+m\). There are no generators in degree \(n+m+1\), so this cycle is not a boundary. Localizing the mixed generators does not change groupoidification.

On the other hand, a localization of a finite \(d\)-polygraph groupoidifies to a finite CW complex of dimension at most \(d\): groupoidification takes its globe attachments to ordinary cell attachments, and subsequent localization has no effect.

Therefore this total has no presentation of dimension less than \(n+m\). If one of \(n,m\) is zero, use a point in that factor and the corresponding globular boundary in the other.

Hence
\[
\boxed{\text{the optimal uniform bound is exactly }n+m.}
\]

This proves the affirmative characterization in Question 2, including the dimension-\(7\) assertion for the pentagon example, and extends it to the weights in Question 4. It leaves open the necessary-and-sufficient recognition criterion for the **unaugmented, prescribed** Gray attaching words in Question 1.

# Followup

The construction can now be made explicit while retaining **the original fibre polygraphs and the original fibre vertices as the endpoints of every named Gray cell**, with dimension still bounded by \(n+m\).

The positive-dimensional faces of the named Gray cells are auxiliary copies. They are related to the required composites by explicitly localized comparison cylinders. Thus this construction supplies a uniform presentation with auxiliary generators; it does not assert that the unaugmented Leibniz attaching expressions exist.

I give the construction and its proof below. The remaining unresolved part is a terminating recognition criterion for the **unaugmented** presentation in Question 1.

## 1. Uniform presentation theorem

Put \(B=F(\Gamma)\), \(E=\int T\), and \(D=n+m\).

**Theorem.** Suppose \(\Gamma\) is finite and homotopical, and
\[
T:B\longrightarrow\omega
\]
has values
\[
T(b)\simeq \operatorname{Free}(\Pi_b)[W_b^{-1}],
\]
where each \(\Pi_b\) is a finite homotopical polygraph of dimension at most \(m\). The functor \(T\) may be coherent rather than strict.

There is a finite marked polygraph \(\Omega\), a finite localization set \(S_\Omega\), and an equivalence of marked categories over \(B^\sharp\),
\[
\operatorname{Free}(\Omega)[S_\Omega^{-1}]
   \simeq E,
\]
with the following properties.

1. \(\dim\Omega\le n+m\).
2. Each original fibre polygraph \(\Pi_b\) is a literal subpolygraph of \(\Omega\): its generators and boundary expressions are unchanged.
3. For every base generator \(q\) of dimension \(k\ge1\) and every generator \(g\) of its source fibre of dimension \(j\ge0\), \(\Omega\) has a designated generator
   \[
   z_{q,g},\qquad |z_{q,g}|=k+j.
   \]
   Under the displayed equivalence, it denotes the local Gray cell \(q\otimes g\).
4. The two \(0\)-endpoints of \(z_{q,g}\) are the corresponding vertices of the retained fibre polygraphs. Its positive-dimensional proper faces are explicitly specified auxiliary generators.
5. Every \(z_{q,g}\) is cartesian-marked, and every \(z_{q,g}\) with \(j>0\) belongs to \(S_\Omega\).
6. The remaining generators and the entire localization set are given by the construction below.

For a coherent weight, choosing representatives of its values and cells is part of the finite weight data. In particular, when a transported vertex is specified only up to equivalence, choose a presenting fibre vertex and record that equivalence.

The theorem does not require the final unlocalized polygraph \(\Omega\) to be homotopical. The definition of presentation in §1.2 does not impose that requirement.

## 2. The finite-model results used

I use the bounded-model and bounded-realization results established in the preceding argument, in the following precise forms.

### 2.1 Bounded model for the total

The total \(E\), with its cartesian marking, has a finite complicial model of dimension at most \(D=n+m\).

The dimension calculation is cellular. A finite homotopy pushout
\[
C\amalg_A^h C'
\]
can be represented in dimension
\[
\max\{\dim C,\dim C',\dim A+1\}.
\]
Products add dimensions. The suspension classification gives dimension at most \(m+k\) for the total over a \(k\)-globe, and at most \(m+k-1\) for its boundary total. Pulling the base’s cellular colimits back along the classified fibration therefore gives the bound \(n+m\). The categorical inputs are Loubaton’s suspension classification and preservation of colimits by pullback along a left cartesian fibration. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

### 2.2 Bounded realization of finite maps

Suppose \(K\to E\) is a finite complicial model, and \(A\to E\) is a map from a finite complicial set of dimension \(a\). There is a finite weak-equivalence extension
\[
K\hookrightarrow K'
\]
through which the map from \(A\) factors, with
\[
\dim K'\le \max\{\dim K,a+1\}.
\tag{2.1}
\]

This holds relatively, including in the slice over the strict base nerve.

The proof uses a relative complicial horn completion, with the marking at each stage reflected from \(E\). To obtain a simplex of dimension at most \(a\), only horn attachments of dimension at most \(a+1\) are needed: the new simplices of an \(r\)-horn attachment have dimensions \(r-1\) and \(r\). A finite map uses finitely many such attachments and finitely many attaching predecessors. Marking extensions do not add simplices.

A reflected marking is certified separately by a finite anodyne witness. Such a witness can have dimension greater than \(a+1\); its cells are proof data, not generators of \(K'\).

The relevant complicial horn, marking, and saturation maps are finite, and their lifting property characterizes fibrant objects and fibrations with fibrant codomain. This is the property required here; one need not assert that the elementary maps generate every trivial cofibration. [arxiv.org](https://arxiv.org/pdf/2005.07603?utm_source=chatgpt.com)

### 2.3 Explicit conversion to homotopical polygraphs

For a finite stratified simplicial set \(K\) of dimension at most \(d\), use the finite semisimplicial set
\[
(L_dK)_r
   =K_r\times\operatorname{Inj}([r],[d]),
   \qquad 0\le r\le d,
\tag{2.2}
\]
with faces
\[
d_\ell(\sigma,I)
   =(d_\ell\sigma,I\setminus\{i_\ell\}).
\]
Here \(K_r\) includes degenerate simplices. After freely adjoining degeneracies, mark \((\sigma,I)\) exactly when \(\sigma\) is thin.

The projection \(L_dK\to K\) is an equivalence. Its oriental polygraph is finite, has dimension at most \(d\), and has one generator for each pair \((\sigma,I)\). It is homotopical by the semisimplicial pasting theorem. Localizing the generators indexed by thin \(\sigma\) presents \(K\). [arxiv.org](https://arxiv.org/html/2603.22242v2?utm_source=chatgpt.com)

The conversion is compatible with changing the cutoff: if \(a\le d\) and \(A\to K\) is a simplicial map, the initial inclusion \([a]\hookrightarrow[d]\) gives
\[
L_aA\longrightarrow L_dK.
\tag{2.3}
\]

That last compatibility will produce the required **strict unlocalized maps**.

## 3. A closure lemma for keeping the original vertices

The following lemma permits all named Gray globes to be attached at the original fibre vertices.

**Lemma.** Let \(\Pi\) be homotopical. Adjoin finitely many fresh globes \(D_{r_i}\), identifying their two \(0\)-faces with prescribed vertices \(s_i,t_i\in\Pi_0\), and identifying no positive-dimensional generators. The resulting polygraph is homotopical.

The endpoints may coincide, and different globes may have the same endpoints.

### Proof

Write \(C=F(\Pi)\) and \(A_i=D_{r_i-1}\), so \(D_{r_i}=\Sigma A_i\). The strict extension \(C^+\) has the same vertices as \(C\). Its hom-categories are
\[
\begin{aligned}
C^+(x,y)
={}&C(x,y)\\
&\amalg
\coprod_{\ell\ge1}\ \coprod_{i_1,\ldots,i_\ell}
C(t_{i_\ell},y)\times A_{i_\ell}
\times C(t_{i_{\ell-1}},s_{i_\ell})
\times\cdots\\[-1mm]
&\hspace{42mm}\cdots\times A_{i_1}\times C(x,s_{i_1}).
\end{aligned}
\tag{3.1}
\]

The sequence \((i_1,\ldots,i_\ell)\) records the ordered new factors. It cannot change under a relation because no positive-dimensional face of a new globe was identified with a pre-existing cell or with a face of another globe. Composition concatenates these sequences and composes the adjacent old \(C\)-factors.

An empty old segment is the identity in its designated \(C(v,v)\)-factor; it is not another word. Consequently the same formula works for loops \(s_i=t_i\).

To check that this strict calculation is homotopical, work at a finite dimension \(N\) exceeding the dimensions involved, in a Cartesian model \(\mathcal V\) of \((\infty,N-1)\)-categories with all objects cofibrant. On the fixed vertex set \(O=C_0\), the extension is the coproduct of the enriched category for \(C\) with the free enriched category on the graph having \(A_i\) at \((s_i,t_i)\).

Replace the first enriched category cofibrantly. The free graph extension is cofibrant, so their coproduct computes the derived extension. Formula (3.1) calculates its homs as well. The comparison to the strict extension is a coproduct of finite products of homwise weak equivalences, hence is a weak equivalence. The fixed-vertex model and free enriched-category adjunction are described by Muro; Haugseng’s rectification and iterated-enrichment comparisons justify this calculation in the usual higher-categorical theory. [arxiv.org](https://arxiv.org/pdf/1201.1575?utm_source=chatgpt.com)

The strict nerve preserves the products in (3.1). It also preserves these coproducts: a connected test shape maps into one disjoint summand. Thus the calculated strict extension is precisely the image of \(F(\Pi^+)\).

On the weak side, the extension is \(\operatorname{Free}(\Pi^+)\). Since \(\Pi\) and the globes are homotopical, its comparison with the strict extension is an equivalence. ∎

The infinite coproduct in (3.1) describes the generated hom-categories. **The polygraph being constructed remains finite.**

## 4. Build the finite polygraphs \(H\subseteq P\)

Assume first that \(n,m\ge1\).

Start with the disjoint union of the original fibre polygraphs,
\[
\Pi_{\mathrm{fib}}=\coprod_b\Pi_b.
\]

For every pair \((q,g)\), choose the semantic local Gray globe
\[
\gamma_{q,g}:D_{k+j}\longrightarrow E.
\tag{4.1}
\]
This comes from the already proved presentation over the individual base globe. Its construction therefore does not assume that the global relative presentation exists.

Adjoin a fresh copy \(D_{k+j}^{q,g}\), identifying its two vertices with the corresponding vertices of \(\Pi_{\mathrm{fib}}\). Name its top generator \(z_{q,g}\). Make no positive-dimensional identifications.

Call the resulting polygraph \(P\). Explicitly, its generators are:

- every original fibre generator;
- one top \(z_{q,g}\) for every pair;
- the positive-dimensional proper faces of each newly adjoined globe.

The globe faces have their ordinary globular boundaries. They are distinct generators for different pairs. The preceding lemma proves that \(P\) is homotopical, and
\[
\dim P\le D.
\tag{4.2}
\]

The fibre maps and the maps (4.1) agree at the identified vertices, so they give a map
\[
F(P)\longrightarrow E.
\tag{4.3}
\]

Now define \(H\subseteq P\) by retaining:

- all original fibre polygraphs;
- the whole globe \(D_k^{q,g}\) when \(j=0\);
- only the source face \(D_{k+j-1}\subset D_{k+j}^{q,g}\) when \(j>0\).

The same closure lemma proves that \(H\) is homotopical. Moreover,
\[
\dim H
 \le \max\{m,n,n+m-1\}
 =D-1.
\tag{4.4}
\]

Put
\[
M=\{z_{q,g}:j>0\}.
\tag{4.5}
\]

For every \(r\ge1\), if \(z\) is the top cell of \(D_r\), the source-face inclusion induces an equivalence
\[
D_{r-1}\xrightarrow{\simeq}D_r[z^{-1}].
\tag{4.6}
\]
Indeed, mapping out of the right side consists of a source \((r-1)\)-cell, a parallel target, and an equivalence between them. Over a fixed source, the space of choices of the target and that equivalence is contractible.

Passing from \(H\) to \(P\) adjoins, for each mixed pair, exactly one fresh parallel target face and the top cell relating it to the retained source face. Applying (4.6) to these attachments gives
\[
\boxed{F(H)\xrightarrow{\simeq}F(P)[M^{-1}].}
\tag{4.7}
\]

This conclusion uses the weak cellular pushout followed by localization. It is not inferred merely from a strict pushout.

Every member of \(M\) maps to an equivalence in \(E\) and to an identity in \(B\). Thus (4.3) factors through \(F(P)[M^{-1}]\), over \(B\).

## 5. Produce strict maps from one common resolution

Let
\[
K\longrightarrow E
\]
be the finite model of dimension at most \(D\). Work with a fibrant model of \(E\) **in the slice over** \(N_{\mathrm{RS}}B\).

Set \(a=\dim H\le D-1\). Choose a finite model
\[
A\longrightarrow N_{\mathrm{RS}}F(H),
\qquad \dim A\le a.
\tag{5.1}
\]
Composing with (4.3) gives a semantic map \(A\to E\) over the base.

Bounded realization gives
\[
K\hookrightarrow K'\longrightarrow E,
\qquad A\longrightarrow K',
\qquad \dim K'\le D,
\tag{5.2}
\]
with the relevant triangles commuting literally over \(N_{\mathrm{RS}}B\).

Let:

- \(\Psi_0\) be the oriental polygraph of \(L_DK'\);
- \(R\) be the oriental polygraph of \(L_aA\);
- \(S_0,S_R\) be their generators indexed by thin simplices.

Then
\[
\operatorname{Free}(\Psi_0)[S_0^{-1}]\simeq E,
\qquad
\operatorname{Free}(R)[S_R^{-1}]\simeq F(H).
\tag{5.3}
\]

Equation (2.3) gives a strict map
\[
u:F(R)\longrightarrow F(\Psi_0).
\tag{5.4}
\]
The map (5.1), followed by \(H\hookrightarrow P\), gives a strict map
\[
v:F(R)\longrightarrow F(P).
\tag{5.5}
\]

These maps have the required literal properties:

\[
u(S_R)\subseteq S_0,\qquad
v(S_R)\text{ consists of identities}.
\tag{5.6}
\]

If \(\rho:F(\Psi_0)\to B\) and \(\pi:F(P)\to B\) are the strict base maps, then
\[
\boxed{\rho u=\pi v}
\tag{5.7}
\]
as strict functors.

Equation (5.7) follows from the literal simplicial equality over \(N_{\mathrm{RS}}B\), followed by oriental categorification. No lift \(F(P)\to F(\Psi_0)\) has been assumed.

Also,
\[
\dim R\le a\le D-1.
\tag{5.8}
\]

The use of \(L_aA\), rather than \(L_DA\), is essential: the latter can introduce generators through dimension \(D\) from degenerate simplices.

## 6. The complete generator and localization lists

Apply the already proved graph-base presentation to the strict diagram
\[
F(\Psi_0)\xleftarrow{u}F(R)\xrightarrow{v}F(P).
\tag{6.1}
\]

The graph has three vertices and two edges, both directed out of the vertex of value \(F(R)\).

The resulting polygraph \(\Omega\) has exactly the following generators:

| Family | Generators | Dimensions |
|---|---|---:|
| Retained polygraph | Every generator of \(P\) | At most \(D\) |
| Central model | Every generator of \(\Psi_0\) | At most \(D\) |
| Common resolution | Every generator of \(R\) | At most \(D-1\) |
| First comparison cylinder | \(c_h^0\), for every generator \(h\) of \(R\) | \(|h|+1\) |
| Second comparison cylinder | \(c_h^1\), for every generator \(h\) of \(R\) | \(|h|+1\) |

The boundaries of \(c_h^0,c_h^1\) are the ordinary graph Gray-cylinder boundaries determined by the strict maps \(u,v\). These are unlocalized attaching expressions. Their existence is exactly the established graph-base case.

Define
\[
\boxed{
S_\Omega=
S_0\cup S_R\cup M\cup\bigcup_bW_b
 \cup\{c_h^0,c_h^1:h\in\operatorname{Gen}(R)\}.
}
\tag{6.2}
\]

**Every comparison-cylinder generator is inverted, including those indexed by vertices \(h\).**

Let \(Q_0\) be the finite marking on the central presentation that presents the cartesian marking of \(E\). Use
\[
\boxed{
Q_\Omega=
Q_0\cup S_\Omega\cup\{z_{q,g}\}.
}
\tag{6.3}
\]

The map to \(B\) is given by \(\rho,\pi,\rho u=\pi v\) on the three vertex values. On each cylinder, use the constant transformation between the strictly equal base functors in (5.7). Hence every cylinder generator projects to an identity. The same is true of every generator in \(S_\Omega\).

### Why this presents \(E\)

Initially omit the redundant localizations \(\bigcup_bW_b\). Localizing all cylinder generators turns the diagram’s comparison transformations into equivalences. Its mapping-space universal property is therefore the homotopy-pushout formula
\[
\begin{aligned}
\operatorname{Free}(\Omega)[S_\Omega^{-1}]
\simeq\;&
\operatorname{Free}(\Psi_0)[S_0^{-1}]
\\
&\amalg^h_{\operatorname{Free}(R)[S_R^{-1}]}
F(P)[M^{-1}].
\end{aligned}
\tag{6.4}
\]

One can verify this directly: a map to a target \(Z\) consists of maps from the three vertex values and equivalences from the middle map to the restrictions of the other two. Eliminating the middle map gives the homotopy pullback of mapping spaces that characterizes (6.4). This is also the graph case of the description of a colimit by localization of its Grothendieck construction. [arxiv.org](https://arxiv.org/pdf/2406.05425?utm_source=chatgpt.com)

The right leg in (6.4) is an equivalence by (5.3) and (4.7). Consequently the central inclusion is an equivalence, and
\[
\operatorname{Free}(\Omega)[S_\Omega^{-1}]
 \simeq
\operatorname{Free}(\Psi_0)[S_0^{-1}]
 \simeq E.
\tag{6.5}
\]

The comparison restricts on \(P\) to the specified map (4.3). Thus the designated generators denote the chosen local Gray cells, rather than merely receiving their names.

Each original \(w\in W_b\) already maps to an equivalence in \(E\), so adding the remaining localizations in (6.2) changes nothing.

### Cartesian marking

All generators listed in (6.3) map to cartesian cells:

- the central generators do so by their existing certificate;
- each \(z_{q,g}\) does so by the local Gray construction;
- all localization generators map to equivalences.

This proves preservation of marking.

For reflection, use the central inclusion in (6.5). Its composite with the comparison to \(E\) is already a marked equivalence. Since markings are replete subspaces of the spaces of cells, every marked cell of \(E\) is represented by a marked cell from that central presentation. Hence the comparison in (6.5) is an equivalence of marked categories.

## 7. Dimension and the pentagon example

The construction has
\[
\begin{aligned}
\dim\Omega
&\le
\max\{\dim P,\dim\Psi_0,\dim R+1\}\\
&\le D.
\end{aligned}
\tag{7.1}
\]

The source-face substitution for mixed cells is what prevents an extra dimension. A mixed \(r\)-cell is retained using a resolution of its \((r-1)\)-dimensional source face, so its comparison cylinder has dimension at most \(r\).

The remaining cases are direct.

- **If \(n=0\):** take the disjoint union of the given fibre presentations.
- **If \(m=0\):** the values are finite discrete sets. The strict total has cells \((\beta,x)\), with \(x\) in the fibre over the \(0\)-source of \(\beta\). Boundaries and composites lift uniquely. It is free on the generators \((q,x)\), and its projection is discrete Conduché. Pulling back the base’s cellular presentation proves that this lifted polygraph is homotopical. Mark all its positive-dimensional generators and invert none.

For the pentagon example,
\[
D=4+3=7.
\]
Here \(P\) has dimension at most \(7\), \(H\) and \(R\) have dimension at most \(6\), and both comparison cylinders have dimension at most \(7\). Thus it has a presentation of dimension at most \(7\) that retains the original fibre and all designated base–fibre cells.

The missing original target face of \(P\otimes x\) is replaced by a fresh \(3\)-face. The comparison cylinders identify that face, after localization, with the required composite. No nonexistent positive expression involving \(M^{-1}\) is asserted in the original unlocalized generators.

## 8. What the finite certificate records

The certificate has the following finite data.

1. **Input presentations and weight data.**  
   The base and fibre polygraphs, their homotopicality certificates, fibre localization sets, and the transport and higher coherence data.

2. **Local Gray cells.**  
   For every \((q,g)\), the local globe presentation, its designated Gray generator, its two fibre vertices, and its finite comparison to the total’s cellular construction.

3. **The lists defining \(P,H,M\).**  
   Check that the original fibre boundaries are unchanged; only the prescribed vertices are identified; all positive-dimensional proper globe faces are fresh; and \(H\) omits exactly the mixed top cells and their fresh target faces.

4. **The central finite model.**  
   The finite cellular construction of \(K\), its dimension calculation, its base map, and its cartesian marking.

5. **Finite derived-map data.**  
   The map \(A\to E\) used in §5 must be supplied as a finite roof relative to the central finite model, together with the finite comparison data. An unspecified map into an infinite fibrant \(E\) is not a certificate.

6. **Bounded realization witnesses.**  
   The finite horn attachments and marking additions producing \(K'\), the map \(A\to K'\), and the finite anodyne witnesses for the marking additions.

7. **Oriental conversion and strict maps.**  
   The pairs \((\sigma,I)\), their faces, the cutoff inclusion \([a]\hookrightarrow[D]\), and the generator images defining \(u,v,\rho,\pi\). Include finite derivations of
   \[
   \rho u=\pi v.
   \]

8. **Final presentation data.**  
   The complete generator and boundary lists of §6, the sets \(S_\Omega,Q_\Omega\), and verification that every localization generator projects to an identity.

The checker invokes the vertex-attachment lemma and source-face equivalence as proved rules. It checks finite simplex tables, finite attachment lists, and finite typing and equality derivations. It does not decide equivalence of arbitrary presented higher categories.

The construction can be made deterministic by fixing an encoding of finite diagrams and selecting the first verified bounded-realization certificate. The bounded-realization theorem proves that this search terminates for the finite derived-map data supplied by the cellular construction. The dimension bound concerns the output presentation; it does not bound the size or dimension of separate proof witnesses.

## 9. Coherent weights and non-free values

For homotopical \(\Pi_b\), the argument already permits
\[
T(b)\simeq\operatorname{Free}(\Pi_b)[W_b^{-1}]
\]
and a coherent \(T\).

The additional certificate data are the finite roofs representing transport and higher coherence maps, together with their boundary compatibilities. Equivalence classes of the individual transport functors alone are insufficient: the higher coherence choices specifying the weight must also be given.

Strictness is not required for the semantic map \(F(H)\to E\). After choosing a fibrant model in the slice, bounded realization and the conversion \(L_aA\to L_DK'\) produce the strict maps \(u,v\) needed for the final unlocalized graph construction.

If the presenting \(\Pi_b\) are arbitrary finite weak polygraphs, rather than homotopical ones, first use their dimension-\(m\) finite complicial models and the \(L_m\) conversion. This gives finite homotopical localized fibre presentations of the same dimension bound. The theorem then applies with those replacement fibre presentations, still giving dimension at most \(n+m\). Literal retention of the original non-homotopical fibre computads is not asserted by this additional step.

## 10. Recognition: a finite certificate, but not a terminating test

There is a complete finite certificate for equivalence of two **specified finite complicial models**. This helps check a proposed unaugmented Gray presentation, but does not supply the missing bound on possible attaching expressions.

Let \(J\) be the elementary complicial horn, marking, and saturation extensions, and let \(I=\Delta[1]^t\). For finite models \(K,L\), a certificate consists of finite \(J\)-extensions
\[
L\hookrightarrow A,\qquad
K\overset{i}{\hookrightarrow}U,\qquad
A\overset{j}{\hookrightarrow}V,
\]
maps
\[
f:K\to A,\qquad g:A\to U,\qquad h:U\to V,
\]
and finite cylinder maps witnessing
\[
gf\simeq i,\qquad hg\simeq j.
\tag{10.1}
\]

Every condition is a finite combinatorial check.

**Sufficiency.** In the homotopy category, both \(gf\) and \(hg\) are invertible, because \(i,j\) are anodyne extensions. Therefore \(g\) has both a left and a right inverse; these coincide. It follows that \(f,g,h\) are invertible. Since \(L\to A\) is also an equivalence, \(K\simeq L\).

**Necessity.** Choose \(J\)-fibrant replacements \(RK,RL\) and homotopy inverse maps
\[
F:RK\rightleftarrows RL:G.
\]
Choose a finite subextension \(A\subset RL\) admitting the image of \(K\) under \(F\); then a finite \(U\subset RK\) admitting \(G(A)\) and the required unit homotopy on \(K\); then a finite \(V\subset RL\) admitting \(F(U)\) and the counit homotopy on \(A\). Such finite subextensions exist because the anodyne domains are finite and the selected cells have finite attaching ancestry. Restriction gives (10.1).

The same proof works over a fibrant base, requiring all maps and homotopies to commute with the base. Cartesian marking must additionally be preserved and reflected; for the uniform construction above this is established directly by the central marked presentation.

Applied to Question 1, this gives a finite correctness certificate **after actual ordered Gray attaching terms have been supplied**. Enumerating terms and certificates gives a positive search. Equality of alternating boundary chains is not a substitute for those attaching terms.

What remains unproved is a finite bound on the positive mixed-generator expressions that must be searched. Additivity of base-generator support bounds the top base lifts, but does not by itself bound the lower mixed steps. I have neither proved the required bound nor obtained a valid undecidability reduction. Thus the uniform presentation and dimension questions are handled by the construction above; the terminating recognition characterization for the unaugmented presentation remains unresolved.

## Verification of the researcher response (2026-11-19)

**Verdict: Questions 2, 3 and 4 answered, verified; Question 1 (a terminating recognition criterion for the unaugmented Gray-generator presentation) open, with a positive semi-decision procedure.** The follow-up prompt is `../outbox/fibration-presentations-characterization-r3.md`.

**Question 2: every pair has a presentation of dimension ≤ n + m, and n + m is optimal.**
- Lemma 2.1 (bounded relative realization: a finite extension K ↪ K′ of dimension ≤ max{dim K, d + 1} realizing a map from a d-dimensional A). The key step is reflecting thin markings from the fibrant target after each horn stage, so that markings do not depend on higher-dimensional saturation derivations; marking certificates (Lemma 2.2) may be of any dimension but are proof data, not generators. Checked.
- Dimension calculus: homotopy pushouts by the double mapping cylinder with A × Δ[1]^t give max{b, c, a + 1}; products add dimensions (the degeneracy-position count is right); globe attachments keep dimension ≤ r. The totals over globes (4.1)–(4.3) via Loubaton's Cor. 4.1.2.19 give m + k and m + k − 1, and cellular induction over the base gives n + m. Checked.
- The conversion L_D: X_r = K_r × Inj([r], [D]). For K = Δ[p] its nerve with degeneracies is the nerve of the poset {(x, i)} with (x, i) < (y, j) iff x ≤ y and i < j; the homotopies id ⇒ F ⇐ sπ with F(x, i) = (x, max{i, x}) were checked monotone (if x < y and i < j then max{i, x} < max{j, y}). So L_D K → K is an equivalence, and the oriental polygraph of L_D K is homotopical by Chanavat's semisimplicial pasting theorem (Thm 3.35), with |Ψ_r| = |K_r| · C(D+1, r+1).
- Optimality: Γ = ∂D_{n+1}, Π = ∂D_{m+1}, constant weight; the total groupoidifies to Sⁿ × S^m with H_{n+m} ≠ 0, while a localised finite d-polygraph groupoidifies to a CW complex of dimension ≤ d. Correct. In particular item 9's pentagon example has a presentation of dimension ≤ 7.

**Question 3 (Followup): a uniform presentation that keeps the original fibre polygraphs and the original fibre vertices as endpoints of every named Gray cell z_{q,g}.**
- The vertex-attachment lemma (adjoining fresh globes along two prescribed vertices, with no positive-dimensional identifications, preserves homotopicality; strict hom formula (3.1)) is correct and is the same mechanism as the graph-assembly theorem of `homotopy-polygraphs-2026-11-19.md` §1.
- D_{r−1} → D_r[z⁻¹] is an equivalence, giving F(H) ≃ F(P)[M⁻¹] (4.7).
- The strict maps u : F(R) → F(Ψ₀), v : F(R) → F(P) with ρu = πv, obtained from one common bounded realization and the cutoff inclusion L_a A → L_D K′ (using L_a rather than L_D keeps dim R ≤ D − 1), and the graph-base presentation of the span (6.1), give Ω with dim Ω ≤ D and the homotopy pushout (6.4), whose right leg is an equivalence. Checked. The cartesian marking is preserved and reflected through the central inclusion.
- The certificate list (§8) is finite; its size and the dimension of the proof witnesses are unbounded, as stated.

**Question 4.** Covered: coherent weights and localised fibre values, with finite roofs for the transport data.

**Question 1.** Section 10 gives a finite certificate for equivalence of two specified finite complicial models, hence a positive semi-decision procedure for the unaugmented Gray presentation once attaching terms are supplied. A bound on the positive mixed-generator expressions to search, or an undecidability reduction, is not given.

**Effect on the project.** B14's practical goal (checkable weighted limits over every finite homotopical base, with finite certificates) is met by the uniform presentation, with optimal dimension. The exact recognition question for the unaugmented presentation remains, and is posed in r3.
