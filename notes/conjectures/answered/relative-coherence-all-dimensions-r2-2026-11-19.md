# Relative coherence in CaTT in every dimension: free weak ω-categories on homotopical computads are strict

*A self-contained problem. It assumes familiarity with globular weak ω-categories, strict ω-categories, polygraphs (computads) and Steiner complexes, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** One theorem valid in every dimension and for a whole class of computads, or a counterexample. Individual new cases (one more context, one more dimension) are not useful to us. Several exact reductions are now known (§3, items 9–14); what is missing is the contraction itself.

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, arXiv 1706.02866) is a dependent type theory whose models are weak ω-categories (Benjamin–Finster–Mimram, arXiv 2106.04475: models are exactly Grothendieck–Maltsiniotis weak ω-categories).

```
Types          A ::= ⋆ | u →_A v
Terms          t ::= x | coh_{P, A}[γ]
Contexts       Γ ::= ∅ | Γ, x : A
Substitutions  γ ::= ⟨⟩ | ⟨γ, x ↦ t⟩
```

- `dim ⋆ = −1`, `dim(u →_A v) = dim A + 1`, and a term of type A has dimension `dim A + 1`.
- A **pasting context** `P ⊢ps` presents a globular pasting diagram. It has boundaries `∂⁻P`, `∂⁺P`.
- **The only term former.** If `P ⊢ps`, `P ⊢ u →_A v` and `Δ ⊢ γ : P`, then `Δ ⊢ coh_{P, u→_A v}[γ] : (u →_A v)[γ]`, provided either
  - (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or
  - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality. There are no other equations.
- Binary composites `u ∗_k v` and whiskerings are composition coherences over two discs glued along a k-disc.
- Contexts are exactly finite computads, and the terms of Γ are the cells of the free weak ω-category on Γ (Benjamin–Markakis–Sarti, arXiv 2405.00398). Coherence terms are invertible in the coinductive sense (Benjamin–Markakis, arXiv 2406.12127).

### 1.2 Strict image and relative coherence

Every context Γ is a polygraph. Write `F(Γ)` for the free strict ω-category on it. Strict ω-categories are CaTT models, so every term t has a **strict image** `π(t) ∈ F(Γ)`: a coherence is sent to the unique strict composite of its arity.

> **RC(n) for Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

Because coherence terms are invertible, RC(n) is symmetric. Write **RC(∞)(Γ)** for "RC(n) holds for Γ for every n ≥ 1".

> **RC_id(n) for Γ.** As RC(n), with the connecting term required to have identity image: `π(T → T′) = 1_{π T}`. Write RC_id(∞) as above.

RC_id implies RC. They agree when every endo-(n+1)-cell on an n-cell of F(Γ) is an identity, which holds in the loop-free class of Question 1. With loops, plain RC is too weak: in (x; f : x → x; α : f ⇒ f), the pair (f, f) is joined by α itself, whose image is not an identity. Wherever loops can occur, RC_id is the statement that matters.

*Equivalent form (proved for every finite context).* Every strict cell of F(Γ) is the image of some term. Given that, RC_id(∞)(Γ) is equivalent to: **π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models**, and also to π_Γ being a weak equivalence (F(Γ) is gaunt: its only invertible cells are identities, since the multiset of top generators is additive). The trivial-fibration form says: for every pair of parallel (n−1)-terms u, v and every strict n-cell c : π(u) → π(v) there is an n-term t : u → v with π(t) = c. (Lift c with some boundary, then conjugate by RC_id connections, which have identity image.) 

### 1.3 Contexts we need

All of the following are finite. The full cylinders (Y = Var(Q)), the joins, the Gray products of globes and the orientals present strongly loop-free Steiner complexes (Steiner, *Omega-categories and chain complexes*, HHA 2004; Ara–Maltsiniotis, *Joint et tranches pour les ∞-catégories strictes*), so F(Γ) = ν(K) has cells determined by their supports. The partial cylinders (Y ≠ Var(Q)) also present strongly loop-free unital Steiner complexes (§3 item 9), and they are positive in every dimension (the source of x↑ has x⁻ as a factor and its target has x⁺).

- **Cylinders.** For a pasting context Q and an up-closed set `Y ⊆ Var(Q)` (if y ∈ Y occurs in the type of x then x ∈ Y), the context `Q↑Y` keeps each `x ∉ Y` and replaces each `x ∈ Y` by two copies `x⁻, x⁺` and a cell `x↑ : a_x → b_x`, where for x of dimension n

  ```
  a_x := ( … ((x⁻ ∗₀ (τⁿx)↑) ∗₁ (τⁿ⁻¹x)↑) … ) ∗_{n−1} (τx)↑
  b_x := (σx)↑ ∗_{n−1} ( … ((σⁿ⁻¹x)↑ ∗₁ ((σⁿx)↑ ∗₀ x⁺)) … )
  ```

  with every factor `w↑` for `w ∉ Y` omitted. For Y = Var(Q) the strict ω-category F(Q↑Y) is the Gray cylinder `D¹ ⊗ Q`. The smallest example is the **lax square** (x⁻, x⁺, y⁻, y⁺; x↑, y↑, f⁻, f⁺; F : f⁻ ∗₀ y↑ ⇒ x↑ ∗₀ f⁺).
- **Joins.** For a pasting context Q, `Cone(Q; c)` adds an object c and, for each variable t of Q of dimension m, a variable `p_t : p_{τt} → p_{σt} ∗_{m−1} (p_{σ²t} ∗_{m−2} ( … (p_{σᵐt} ∗₀ t)))` (with `p_x : c → x` for objects). F(Cone(Q; c)) is the Ara–Maltsiniotis join `c ⋆ Q`.
- **Gray molecules.** Gray products `D^{n₁} ⊗ ⋯ ⊗ D^{n_k}` of globes, and more generally pasting diagrams in Steiner's or Hadzihasanovic's sense, presented in CaTT by giving each cell the type `⌈∂⁻x⌉ → ⌈∂⁺x⌉` with chosen composite terms for its boundary molecules.
- **Orientals.** For example the **triangle** (x, y, z; f : x → y, g : y → z, h : x → z; α : f ∗₀ g ⇒ h).


## 2. Why it matters

RC is the single missing ingredient in several constructions in CaTT: lax naturality of every coherence with respect to every up-closed set of its variables (equivalently a lax cylinder Γ ⊗ D¹ for every context Γ); composites, unique up to higher cells, for non-globular pasting diagrams (Gray products of globes, joins); cones over every coherence; and the comparison of the free CaTT model on a computad with its strict free ω-category, which is the unit condition in comparing CaTT models with (∞,ω)-categories.

## 3. What is known

1. **RC(1) and RC(2) hold in every context.** For 2-terms: normalise to vertical composites of whiskered 2-variables; two composites with the same strict image are related by exchange moves (Ara–Burroni–Guiraud–Lafont–Métayer, *Polygraphs*, arXiv 2312.00429, §4.1), and each move is one coherence.
2. **Support lemma.** supp(π t) = supp(t) in every context, and if t has no variable of dimension dim t in its support then supp(t) = supp(σt) = supp(τt). Parallel terms whose image is an identity on a cell w are joined by one coherence over supp(w) whenever supp(w) is a pasting context. For a pasting context P, π_P is a trivial fibration (this is the coherence and composition rule).
3. **RC(3) is known** for the lax square, the triangle, every cylinder Q↑Y, the 2 × 2 and 2 × 3 grids, the Gray cube D¹ ⊗ D¹ ⊗ D¹, and joins over vertical chains of 2-discs. Each proof is a hand-built normalisation for one context; in each, RC(n+1) needed a separately constructed coherence of the normalisation one dimension up.
4. **Adjoining top generators in dimension 3.** If Λ has dimension ≤ 2 and an acyclic generating 1-graph, and Γ adds 3-generators between parallel 2-terms of Λ, then RC(3)(Γ) ⟺ RC(3)(Λ) (using depth-1 naturality, Benjamin–Markakis–Offord–Sarti–Vicary, arXiv 2501.11620, Thm 3.1). In dimension 4 only a conditional version (assuming RC(3) and RC(4) for Λ) is known.
5. **Exchange combinatorics in dimension 2 are settled.** For a 2-dimensional context with an acyclic generating 1-graph and non-empty boundary paths, the 2-paths representing a strict 2-cell c are the linear extensions of an event poset, and the graph of exchange moves with squares and hexagons as 2-cells is simply connected; squares and hexagons are single coherences.
6. **Loops obstruct.** In Γ = (x; a : 1_x ⇒ 1_x) the Eckmann–Hilton 3-cell a ∗₀ a ⇛ a ∗₀ a and the identity are parallel with equal strict image, and no 4-term joins them (the weak free object groupoidifies to S², the strict one B²ℕ to K(ℤ, 2), and π₃(S²) ≠ 0).
7. **Gaunt targets.** F(Γ) is gaunt for every finite Γ (generator counts), so an FHM ω-weak equivalence into F(Γ) is a trivial fibration. RC_id(∞)(Γ) ⟺ π_Γ is a trivial fibration ⟺ π_Γ is a weak equivalence.
8. **Homotopical computads.** Γ is *homotopical* when the comparison from the free (∞,ω)-category on Γ (generators attached by homotopy pushouts) to F(Γ) is an equivalence. Strongly loop-free Steiner complexes with unital basis, and regular directed complexes with frame-acyclic molecules, are homotopical (Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242, Thm 3.17). **A finite 2-polygraph is homotopical if and only if F(Γ) has no bubble** (no non-identity 2-cell 1_x ⇒ 1_x); in particular every 2-polygraph whose 2-generators all have non-empty target (or all non-empty source) is homotopical, loops and cycles in the 1-graph allowed. Bubble-freeness is undecidable. For a homotopical context, RC_id(∞)(Γ) is equivalent to the unit of the realization adjunction between CaTT models and (∞,ω)-categories being a weak equivalence at the free CaTT model on Γ.
9. **Partial cylinders are strong Steiner.** For Y ⊆ Var(Q) up-closed, the complex K_Y obtained from the Steiner tensor I ⊗ λQ by identifying c⁻ = c⁺ and killing Ic for c ∉ Y is strongly loop-free and unital, with ∂⁻-iterates (∂⁻)^j Ix = (σ^{j−1}x)⁻ + I(τ^j x), (∂⁺)^j Ix = (τ^{j−1}x)⁺ + I(σ^j x) (omitted terms zero); so F(Q↑Y) ≅ ν(K_Y).
10. **Cartesian strictification.** Call Γ *positive* if every generator of dimension ≥ 2 of its polygraph has non-identity source and target. For every generator-preserving map f : Δ → Γ of positive CaTT contexts (variables to variables, attaching terms preserved), the square Free(Δ) → Free(Γ) over F(Δ) → F(Γ) is a pullback in every dimension: a term t of Γ and a strict cell d of F(Δ) over π(t) have exactly one lift. (Proof: Henry's theorem that composition is cartesian on positive polygraphs, *Non-unital polygraphs form a presheaf category*, Cor. 2.3.13, 2.4.9, plus induction on terms.)
11. **Reduction to polyplexes.** For a strict cell c of F(Γ), Γ positive, let P_c → Γ be its generic (Henry) polyplex, with the uniquely lifted weak attaching terms. Then π_Γ is a trivial fibration iff every π_{P_c} is; the same holds for RC(n) and RC_id(n) for each n. Positive 2-polyplexes are strong Steiner, so **RC(n) for every finite positive context of dimension ≤ 2 is equivalent to RC(n) for every finite strong-Steiner context of dimension ≤ 2** (no hypothesis on the 1-graph).
12. **The fibre over one generator.** If Γ = (Λ, z : a → b) is a strong Steiner atom polygraph with z of top dimension m, then Free(Γ) ×_{F(Γ)} 𝔻^m is the free extension, by one m-cell, of Free(Λ) ×_{F(Λ)} ∂𝔻^m (𝔻^m the strict m-globe mapped onto π(z)). So the trivial-fibration property over the cell π(z) would follow from: *adjoining an m-cell to a trivial fibration B → ∂𝔻^m, along an attaching sphere over the two faces, gives a trivial fibration B[ẑ] → 𝔻^m.* That statement is unproved, and it does not cover strict composites of z with other generators.
13. **Arity lemma.** If a coherence coh_{P,A}[γ] has a substituted strict boundary using a top generator z exactly once, the variables of P labelled by terms involving z form one suspended subtree Σ^m Q of P's Batanin tree.
14. **Maximal variables.** If Y ⊆ Var(P) consists of variables occurring in no other variable's boundary, P↑Y is a pasting context, and every term over P (any dimension) has a naturality term over P↑Y with its full cylinder boundary. This does not give compatibility under substitutions that change a selected variable's boundary.
15. **Not counterexamples.** Chanavat's 4-dimensional regular directed complex (arXiv 2509.26563, Comment 2.67) has a polygraph Q whose strict free category differs from the "stricter" one, but the extra equations appear only in Q → r^>Q, so they do not give equal strict images in F(Q). Benjamin–Markakis's hom-computads (hom weak ω-categories of free computads are free) do not transport π: for (x), the hom computad has distinct 0-cells id_x and id_x ∗₀ id_x, while Hom_{F(x)}(x, x) has one.
16. **A related open conjecture.** Dean (*Globular multicategories with homomorphism types*, thesis, Thm 5.4.0.1) proves an all-dimensional acyclic-fibration strictification for fibrational homomorphism types with a strict computation law; the weak analogue is his Conj. 5.4.0.9. No equivalence with RC is known.

## 4. Questions

**Question 1 (main).** Prove that π_Γ : Free(Γ) → F(Γ) is a trivial fibration of CaTT models (equivalently RC_id(∞)(Γ)) for **every finite CaTT context Γ whose polygraph is homotopical**. If that is false, prove it for every finite context that is positive in every dimension, or at least for every finite strong-Steiner context, and give the counterexample that separates the classes.

By item 11 the positive case reduces to generic positive polyplexes, and by item 12 the strong-Steiner case reduces to one attachment statement plus composites. Routes that would do:
- **(a)** prove the attachment statement of item 12 for arbitrary trivial fibrations B → ∂𝔻^m of CaTT models (a homotopy-pushout property of free cell extensions of CaTT models), and extend it from a single generator to strict composites;
- **(b)** describe the fibre of π_Γ over each strict cell as a CaTT-definable object and show it is contractible (e.g. a retract of something built from pasting contexts);
- **(c)** a relative Guiraud–Malbos construction: a normalisation strategy towards the strict cells of F(Γ), producing all higher comparisons at once;
- **(d)** a proof that RC_id(∞) is equivalent to Dean's Conj. 5.4.0.9, or to another named open statement.

**Question 2 (the exact class).** Does RC_id(∞)(Γ) imply that Γ is homotopical? A direct proof that RC_id(∞) fails for (x; a : 1_x ⇒ 1_x), and more generally for every finite 2-dimensional context with a bubble, is welcome. Combined with Question 1 this would give "RC_id(∞) ⟺ homotopical" for finite contexts.

**Question 3 (fallback, still every dimension).** Prove RC_id(n) for **every n** for every finite 2-dimensional context whose polygraph is bubble-free (equivalently homotopical, item 8). By item 11, for positive ones it suffices to treat finite strong-Steiner 2-dimensional contexts. Together with an extension theorem for adjoining generators of any dimension ≥ 3 (preserving RC_id(n) for all n), this answers Question 1 for every context whose higher generators sit over such a 2-skeleton.

## 5. What counts as a solution

A proof of Question 1 (or of Question 3 with the extension theorem) under a stated hypothesis; a counterexample in one of the named classes, with a proof that no connecting term exists (for example an invariant of a model); an equivalence with a named open problem; or a published reference. An existence proof of the connecting cells is enough, provided it is a proof about CaTT terms or CaTT models.

## 6. Literature (searched 2026-11-18 and 2026-11-19)

- Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (Thm 3.17, Cors. 3.38–3.39, Comment 3.40) and arXiv 2509.26563.
- Henry, *Non-unital polygraphs form a presheaf category*, Higher Structures 3(1) (2019); Henry, *Regular polygraphs and the Simpson conjecture*, arXiv 1807.02627.
- Guiraud–Malbos, *Higher-dimensional normalisation strategies for acyclicity*, Adv. Math. 231 (2012).
- Benjamin–Markakis–Offord–Sarti–Vicary, arXiv 2501.11620 (naturality at depth ≤ 1; Lemma B.6).
- Benjamin–Markakis, arXiv 2402.01611 and *Hom ω-categories of a computad are free*, J. London Math. Soc. (2025).
- Fujii–Hoshino–Maehara, arXiv 2511.09849 (ω-weak equivalences and trivial fibrations).
- Dean, thesis (globular multicategories with homomorphism types), Conj. 5.4.0.9.
- Delpeuch–Vicary, arXiv 1804.07832; Heidemann, arXiv 2411.04870 (used for the 2-dimensional homotopicality theorem of item 8).
- No published comparison of free weak ω-categories with free strict ones on non-globular computads was found.

# Researcher Response 1

The general bubble obstruction requested in Question 2 admits a direct proof. It also persists under arbitrary higher-dimensional extensions:

\[
\boxed{
F(\Gamma_{\le 2})\text{ has a nonidentity bubble}
\quad\Longrightarrow\quad
\neg\mathrm{RC}_{\mathrm{id}}(3)(\Gamma).
}
\]

For a 2-dimensional context, the proof rules out **every** connecting 4-term, regardless of its image. Thus, using your homotopicality criterion, it establishes
\[
\boxed{
\dim\Gamma\le2,\quad
\mathrm{RC}(3)(\Gamma)
\quad\Longrightarrow\quad
\Gamma\text{ is homotopical}.
}
\]

This proves the necessity direction of Question 2 for all finite 2-dimensional contexts, including contexts whose bubbles are composites. It does not provide the contraction required by Questions 1 and 3.

## 1. The obstruction theorem

**Theorem.** Let \(\Lambda\) be a finite CaTT context of dimension at most \(2\). Suppose that \(F(\Lambda)\) has a nonidentity 2-cell
\[
c:1_x\Rightarrow1_x.
\]
Then there are parallel 3-terms \(T,T'\) of \(\Lambda\) such that
\[
\pi(T)=\pi(T')
\]
and there is no 4-term \(T\to T'\).

The proof uses an explicit CaTT model in which the two 3-terms evaluate to distinct integers.

### 1.1. The detecting model

Define a strict braided monoidal groupoid \(\mathcal B\) by
\[
\operatorname{Ob}(\mathcal B)=\mathbb N,
\qquad
\mathcal B(p,q)=
\begin{cases}
\mathbb Z,&p=q,\\
\varnothing,&p\ne q.
\end{cases}
\]

Composition of morphisms is addition, with identity \(0\). Define the tensor product by addition on both objects and morphisms:
\[
p\otimes q=p+q,
\qquad
k\otimes\ell=k+\ell.
\]
Its unit is \(0\). Define the braiding by
\[
\beta_{p,q}=pq\in\operatorname{End}_{\mathcal B}(p+q).
\]

These data satisfy the braided monoidal axioms. Naturality follows from commutativity of integer addition. The two hexagon equations are
\[
p(q+r)=pq+pr,
\qquad
(p+q)r=pr+qr,
\]
and the unit equations are \(p0=0=0p\).

The double delooping of a braided strict monoidal category is a Gray category; this is stated explicitly in *Gray categories with duals and their diagrams*, Lemma 2.18. Thus \(\mathcal B\) determines a Gray 3-category \(\mathcal G\). [nottingham-repository.worktribe.com](https://nottingham-repository.worktribe.com/preview/36291483/1-s2.0-S000187082400255X-main.pdf?utm_source=chatgpt.com) Its cells are:

- One 0-cell \(*\).
- One 1-cell \(I\).
- A 2-cell \(n:I\Rightarrow I\) for each \(n\in\mathbb N\).
- A 3-cell \(k:n\Rightarrow n\) for each \(k\in\mathbb Z\), and no 3-cells between distinct natural numbers.

The 2-cell compositions are addition. The 3-cell compositions are induced by addition, and the Gray tensorator on \(p,q\) is \(pq\).

We use \(\mathcal G\) as a CaTT model, with only identity cells above dimension \(3\). Here is the justification for that step.

Batanin–Cisinski–Weber identify the globular operad for Gray categories in Example 3.6 of *Multitensor lifting and strictly unital higher category theory*. Example 5.7 states its contractibility and supplies choices of contractions compatible with strict units. Their finite-dimensional contractibility condition includes uniqueness in the top dimension, as explained in §4.6. [arxiv.org](https://arxiv.org/pdf/1209.2776?utm_source=chatgpt.com)

Fix their left-to-right column-order contraction. Top-dimensional uniqueness concerns **parallel 3-operations with the same arity**, not arbitrary parallel 3-cells of an algebra. It permits the identity extension above dimension \(3\): when the 4-dimensional inputs are identities, the two boundary operations evaluate equally, and the resulting 4-operation is interpreted by the identity on that value. Higher operations are then interpreted by iterated identities. Restriction along the initial contractible globular operad supplies the CaTT interpretation; the identification of the relevant free weak \(\omega\)-category monad with that initial operad is recorded in Benjamin–Markakis, Remark 26. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

Consequently, in this model,
\[
\text{a 4-cell }(k:n\Rightarrow n)\longrightarrow(k':n\Rightarrow n)
\text{ exists}
\quad\Longleftrightarrow\quad
k=k'.
\tag{1}
\]

### 1.2. Every nonidentity bubble has positive weight

Let \(B^2\mathbb N\) denote the strict 2-category with one object, one 1-cell, and 2-cells the commutative monoid \((\mathbb N,+)\).

Define a strict functor
\[
w:F(\Lambda)\longrightarrow B^2\mathbb N
\]
by sending every 2-generator to \(1\), and every 0- and 1-generator to the unique corresponding cell.

Set
\[
N=w(c).
\]
Then
\[
N>0.
\tag{2}
\]

Indeed, \(w\) counts the total number of 2-generator uses in a strict composite expression. Associativity, units and exchange preserve this count. An expression of weight \(0\) uses only identity 2-cells, and hence evaluates to an identity 2-cell. Since \(c\) is nonidentity, its weight is positive.

Interpret \(\Lambda\) in \(\mathcal G\) by assigning
\[
x\longmapsto *,
\qquad
f\longmapsto I,
\qquad
\alpha\longmapsto 1
\]
to its generators in dimensions \(0,1,2\), respectively. Every declared 2-generator has a valid interpretation because all 1-terms evaluate to \(I\).

The projection
\[
\mathcal G\longrightarrow B^2\mathbb N
\]
is the identity on 2-cells and sends every 3-cell to an identity. It preserves the chosen CaTT operations. The two maps from the free CaTT model of \(\Lambda\) to \(B^2\mathbb N\) agree on generators, so they agree everywhere. Thus every 2-term \(t\) satisfies
\[
\llbracket t\rrbracket=w(\pi t).
\tag{3}
\]

### 1.3. Give the bubble literal weak identity boundaries

By the given surjectivity of strictification, choose a 2-term
\[
U:u\Rightarrow v,
\qquad
\pi(U)=c.
\]
Its boundaries satisfy
\[
\pi(u)=\pi(v)=1_x.
\]

By the support lemma, \(u\) and \(v\) are terms of the one-object context \((x)\). The coherence rule there gives
\[
r:1_x\Rightarrow u,
\qquad
s:v\Rightarrow1_x,
\]
both with identity strict image.

Define
\[
a=(r*_1U)*_1s.
\]
Then
\[
a:1_x\Rightarrow1_x,
\qquad
\pi(a)=c,
\qquad
\llbracket a\rrbracket=N.
\tag{4}
\]

The first assertion is an assertion about the **literal type** of \(a\). This allows substitution into an Eckmann–Hilton term without any additional boundary-comparison theorem.

### 1.4. The two 3-terms

Benjamin–Markakis, §6.1, construct the clockwise Eckmann–Hilton term
\[
\operatorname{eh}(a,b):
a*_1b\longrightarrow b*_1a
\]
for \(a,b:1_x\Rightarrow1_x\), using unitors, associators and interchangers. Their construction has precisely these endpoints. [arxiv.org](https://arxiv.org/pdf/2402.01611?utm_source=chatgpt.com)

Set
\[
p=a*_1a,
\qquad
T=\operatorname{eh}(a,a):p\longrightarrow p,
\qquad
T'=1_p:p\longrightarrow p.
\tag{5}
\]

We now compute their interpretations.

Under the chosen Gray interpretation, the unit and associativity comparisons in the Eckmann–Hilton construction become identities. Its remaining contribution is a Gray tensorator.

More explicitly, write the interchange convention as
\[
\chi(a,b,c,d):
(a*_1b)*_0(c*_1d)
\longrightarrow
(a*_0c)*_1(b*_0d).
\]
For left-column-first composition, its integer value is \(bc\), up to reversing the tensorator orientation: it exchanges the middle two entries. In the Eckmann–Hilton construction, one interchange has middle entries \(0,0\), while the other has middle entries \(N,N\). Therefore
\[
\llbracket T\rrbracket=\pm N^2
\in\operatorname{End}_{\mathcal B}(2N),
\qquad
\llbracket T'\rrbracket=0.
\tag{6}
\]
The sign depends only on the orientation convention and does not affect the argument.

By (2), these integers differ. By (1), there is no 4-cell between them in \(\mathcal G\). Soundness of the interpretation therefore gives
\[
\text{there is no CaTT 4-term }T\longrightarrow T'.
\tag{7}
\]

Finally, \(\Lambda\) has no generators above dimension \(2\), so \(F(\Lambda)\) has only identity 3-cells. Consequently,
\[
\pi(T)=\pi(T')=1_{\,c*_1c}.
\tag{8}
\]
Equations (7) and (8) prove the theorem. \(\square\)

## 2. The obstruction persists under all higher attachments

The support lemma gives the following hereditary property.

**Lemma.** Let \(\Delta\subseteq\Gamma\) be a dependency-closed subcontext. If \(\mathrm{RC}_{\mathrm{id}}(n)(\Gamma)\) holds, then \(\mathrm{RC}_{\mathrm{id}}(n)(\Delta)\) holds.

**Proof.** Let \(T,T'\) be parallel \(n\)-terms of \(\Delta\) with equal strict image \(d\). An identity-image filler in \(\Gamma\) would be a term
\[
H:T\longrightarrow T',
\qquad
\pi(H)=1_d.
\]
The support lemma gives
\[
\operatorname{supp}(H)
=
\operatorname{supp}(\pi H)
=
\operatorname{supp}(1_d)
=
\operatorname{supp}(d)
\subseteq\operatorname{Var}(\Delta).
\]
Thus \(H\) is literally a term of \(\Delta\). \(\square\)

Now let \(\Gamma\) have arbitrary finite dimension and put
\[
\Lambda=\Gamma_{\le2}.
\]
If \(F(\Lambda)\) has a nonidentity bubble, the theorem supplies \(T,T'\) in \(\Lambda\) with no connecting 4-term there. The lemma prevents an identity-image connecting 4-term from appearing in \(\Gamma\). Hence
\[
\boxed{
F(\Gamma_{\le2})\text{ has a nonidentity bubble}
\Longrightarrow
\neg\mathrm{RC}_{\mathrm{id}}(3)(\Gamma).
}
\tag{9}
\]

This is where requiring identity image matters: the support argument excludes higher generators from an identity-image filler.

## 3. Consequence for the exact-class question

For finite \(\Lambda\) of dimension at most \(2\), your item 8 gives
\[
\Lambda\text{ is homotopical}
\quad\Longleftrightarrow\quad
F(\Lambda)\text{ is bubble-free}.
\]
Combining this with the theorem yields
\[
\boxed{
\mathrm{RC}_{\mathrm{id}}(\infty)(\Lambda)
\Longrightarrow
\mathrm{RC}_{\mathrm{id}}(3)(\Lambda)
\Longrightarrow
\Lambda\text{ is homotopical}.
}
\]

The argument applies to a bubble assembled from arbitrarily many differently typed 2-generators. No individual generator needs to have two identity boundaries: the positive weight \(N\) of the composite bubble gives the nonzero obstruction \(\pm N^2\).

The sufficient direction for bubble-free 2-contexts, the all-dimensional attachment theorem, and the converse in arbitrary finite dimension remain unresolved here. No equivalence with Dean’s conjecture has been established.

## Verification of the researcher response (2026-11-19)

*Checked by the thread "Process seven round-3 researcher responses". Verdict: **correct**. Question 2 is settled for finite contexts of dimension ≤ 2, and the obstruction is hereditary to every context whose 2-skeleton has a bubble. Questions 1 and 3 are not addressed.*

1. **The model.** I checked that 𝓑 (Ob ℕ, End(p) = ℤ, ⊗ = +, β_{p,q} = pq) is a strict braided monoidal groupoid. Naturality holds because ℤ is commutative. The hexagons are p(q+r) = pq + pr and (p+q)r = pr + qr. It is not symmetric, since β_{q,p}β_{p,q} = 2pq. Its double delooping is a Gray category (one object, one 1-cell). In it, ∗₀ and ∗₁ of 2-cells are both addition, and interchange is the braiding.
2. **Gray categories are CaTT models.** I checked Batanin–Cisinski–Weber (arXiv 1209.2776) in the paper. Ex. 3.6 is the T≤3-operad for Gray categories. §4.5 defines contractibility by lifting against {∂(k) → k : k ≤ n} ∪ {∂(n+1) → n}, which includes top-dimensional uniqueness. Ex. 5.7 states that this operad is contractible. Extending by identities above dimension 3 is contractible: two parallel 3-operations with the same arity are equal, so the identity lifts every higher sphere. So the initial contractible ω-operad maps to it, and 𝒢 is a CaTT model with only identity 4-cells. This gives (1). Every 3-coherence is interpreted by the unique 3-operation of its arity, so [[eh(a,a)]] is the braiding β_{N,N}^{±1} = ±N² whatever contraction is chosen.
3. **Weights.** The functor w : F(Λ) → B²ℕ (2-generators ↦ 1) is well defined, and w(c) = 0 iff c is an identity. All 2-operations of the Gray operad are strict composites at the level of 2-cells, so [[t]] = w(πt) for 2-terms.
4. **Literal identity boundaries.** By the support lemma u and v are terms of (x), so r : 1_x ⇒ u and s : v ⇒ 1_x are coherences over the pasting context (x). This gives a : 1_x ⇒ 1_x literally, with π(a) = c.
5. **No 4-term.** [[T]] = ±N² ≠ 0 = [[T′]], N > 0, and 𝒢 has only identity 4-cells. π(T) = π(T′) because F(Λ) has only identity 3-cells. So plain RC(3) fails for dim Λ ≤ 2.
6. **Heredity.** An identity-image filler H in Γ has supp(H) = supp(πH) = supp(d) ⊆ Var(Δ). F(Δ) → F(Γ) is injective for a dependency-closed subcontext, so H is an identity-image filler in Δ.

**Consequences.** For finite Λ with dim Λ ≤ 2: RC(3)(Λ) ⇒ bubble-free ⇔ homotopical. For any finite Γ: a bubble in Γ_{≤2} ⇒ ¬RC_id(3)(Γ). This gives a proof internal to CaTT models of the earlier π₃(S²) remark (Known item 6), and extends it to composite bubbles in every 2-dimensional context.

**Open after this response.**
- (Q1) The contraction: homotopical ⇒ RC_id(∞).
- (Q2, higher) An n-bubble with n ≥ 3 ⇒ ¬RC_id(∞)? The same argument needs an n-fold delooping. For n ≥ 3 that means an E₃ = symmetric structure, where β must satisfy β² = 1. A ℤ/2-valued version (β_{p,q} = pq mod 2) would only detect odd weight. It would also need an explicit weak (n+1)-categorical CaTT model of that shape, which the Gray-operad argument does not supply.
- (Q3) The bubble-free 2-dimensional case in every dimension.

The follow-up prompt is `outbox/relative-coherence-all-dimensions-r3.md` (answered 2026-11-19: `answered/relative-coherence-all-dimensions-r3-2026-11-19.md`).
