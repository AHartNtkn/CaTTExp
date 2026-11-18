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
