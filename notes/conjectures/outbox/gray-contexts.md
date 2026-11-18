# Problem: composites of molecules in CaTT (Gray contexts)

*Standalone problem statement. It assumes familiarity with globular weak ω-categories, strict ω-categories and Hadzihasanovic's molecules, and nothing else. Questions are in §4, smallest first.*

## 1. Setting

### 1.1 CaTT

CaTT (Finster–Mimram, LICS 2017, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory for weak ω-categories.

- Types are `⋆` and `u →_A v`. Contexts are lists of typed variables. By Benjamin–Markakis–Sarti ([arXiv 2405.00398](https://arxiv.org/abs/2405.00398)), contexts are exactly finite computads, and terms are the cells of the free weak ω-category on them.
- A variable's type may be a composite: `f : x → y, g : y → z, h : x → z, τ : g·f → h` is a context, though not a pasting diagram.
- The only term former is `coh_{P, u →_A v}[σ]`. It needs P to be a **pasting context** (a globular pasting diagram), σ a substitution into P, and one side condition:
  - (coherence) `Var(u : A) = Var(P) = Var(v : A)`, or
  - (composition) `Var(u : A) = Var(∂⁻P)` and `Var(v : A) = Var(∂⁺P)`.
- Definitional equality is syntactic equality.
- Every CaTT term t of a context Γ has a strict image `π(t)` in the free strict ω-category `F(Γ)` on the computad Γ, since strict ω-categories are models of CaTT.

### 1.2 Molecules and their presentations

- A **molecule** is a pasting diagram in Hadzihasanovic's regular directed complexes (*Combinatorics of higher-categorical diagrams*, [arXiv 2404.07273](https://arxiv.org/abs/2404.07273)). Globes are molecules, and so are Gray products `U ⊗ V` of molecules. Their cells satisfy Steiner's boundary formula `∂^α(x⊗y) = (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^{dim x} α} y)`.
- A **layering** of an n-molecule is a decomposition into a sequence of layers, each a single n-dimensional atom pasted with lower-dimensional cells. Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)) proves: frame-acyclic molecules have layerings, and their layerings correspond to linear orders compatible with a partial order on the top cells (Prop. 2.18); the poset of subdivisions is contractible (Thm 2.52); every molecule of dimension ≤ 3, and every acyclic molecule, is frame-acyclic.
- **Presenting a molecule in CaTT.** To present a molecule U as a CaTT context, each cell x needs a type `⌈∂⁻x⌉ → ⌈∂⁺x⌉` whose two sides are CaTT terms composing the boundary molecules, by induction on dimension. A **U-composite** is a term t with `Var(t) = Var(U)` and `t : ⌈∂⁻U⌉ → ⌈∂⁺U⌉`.

> **Conjecture G(n).** For every frame-acyclic molecule U of dimension ≤ n presented in CaTT: (existence) U-composites exist; (uniqueness) any two U-composites are connected by a CaTT term `t → t′` (which is then invertible, being built from coherences).

G(n) for all n is equivalent to the statement that extending the coherence rule from pasting contexts to frame-acyclic molecules, with the same two side conditions, is conservative over CaTT.

## 2. What is known

Write RC(n) for the property:

> **RC(n) for a context Γ.** Any two parallel n-terms `T, T′` of Γ with `π(T) = π(T′)` are connected by an (n+1)-term `T → T′`.

1. **G(1)**: 1-molecules are paths, which are pasting contexts.
2. **Theorem A (proved): RC(2) holds for every CaTT context.** Proof sketch:
   - Two 1-terms with the same flattened path w are full parallel terms over the chain context of w, so the coherence rule connects them. Any 2-term with no 2-variable pulls back to that chain and is connected to the comparison cell with the same boundary.
   - Every 2-term is connected to a vertical composite of whiskered 2-variables and 2-terms without 2-variables (coherences over its arity and over small pasting contexts).
   - Each whiskered 2-variable x, with whisker paths λ and ρ, is connected to a fixed normal form built from one composition coherence over the pasting context "chain, 2-disc, chain", with the disc sent to x and all comparisons made over the expanded paths.
   - Two 2-paths of whiskered generators give the same strict 2-cell iff they are related by exchange moves. Each exchange move is a coherence over "chain, 2-disc, chain, 2-disc, chain", substituted and normalised. ∎
3. **G(2) (proved).** In a 2-molecule, every 2-path from `∂⁻U` to `∂⁺U` uses each 2-cell exactly once (the 2-cycles of a molecule are zero), and two such paths are related by exchange moves (linear extensions are connected by adjacent swaps, and two incomparable consecutive 2-cells sit side by side). So any two U-composites have the same strict image, and Theorem A connects them. Existence is by a layering, with Theorem A's 1-dimensional comparison cells between layers.
4. **Existence in G(3) (proved).** Take a layering of the 3-molecule. Realise each layer as a 3-term `U₁ ∗₁ (a ∗₀ X ∗₀ b) ∗₁ U₂` (X the layer's 3-cell, whiskers chosen with the right strict images, boundaries adjusted by 2-dimensional comparison cells). Consecutive layers meet at 2-terms with equal strict images, so Theorem A connects them. Hence **every Gray generator of dimension ≤ 4** (e.g. of `D²⊗D²`, `D³⊗D¹`, `D¹⊗D¹⊗D¹⊗D¹`) has a CaTT type.
5. **General pattern.** The same argument shows: existence in G(n) follows from RC(n−1) for the (n−1)-skeleton of U, and uniqueness in G(n) follows from RC(n) for U.

## 3. Why dimension 3 is different

RC(3) is false for arbitrary contexts. In `Γ = (x : ⋆, a : id_x → id_x)`, the Eckmann–Hilton 3-cell `a ∗₀ a → a ∗₀ a` and the identity have equal strict images but are expected not to be connected (in the fundamental weak ω-groupoid of S², with a a generator of π₂, the Eckmann–Hilton cell is non-zero in π₃(S²); *sketch, not checked in detail*). So a proof must use **loop-freeness**. Molecules are loop-free, and Campion ([arXiv 2311.00205](https://arxiv.org/abs/2311.00205), Cor. 3.5) and Chanavat (Thm 3.29) show that their free strict ω-categories are also their free (∞,ω)-categories, so RC holds for them in (∞,ω)-semantics.

The dimension-2 argument fails at one step. Between two consecutive 3-generators, a 3-dimensional proof has runs of 3-cells with no 3-variable, between 2-terms with equal strict image. In dimension 2 the analogous runs live over a single path, where the coherence rule settles everything. In dimension 3 they live over a 2-dimensional context that is not a pasting context, such as the lax square `f⁻ ∗₀ y↑ → x↑ ∗₀ f⁺` or the boundary 2-sphere of the Gray cube. A Squier-style argument (critical branchings of elementary 3-cells close up to 4-cells) is the natural attack. The hard branchings pair a move of a 2-generator with a reassociation that splits that generator's boundary composite; no pasting context contains both.

## 4. Questions

Each question asks for explicit CaTT terms, built with the coherence rule over pasting contexts and substitution.

1. **Smallest open case: RC(3) for the lax square.** Let S be the context `x⁻, x⁺, y⁻, y⁺ : ⋆; x↑ : x⁻ → x⁺; y↑ : y⁻ → y⁺; f⁻ : x⁻ → y⁻; f⁺ : x⁺ → y⁺; F : f⁻ ∗₀ y↑ → x↑ ∗₀ f⁺`. Are any two parallel 3-terms of S connected by a 4-term?
2. **Uniqueness in G(3) for the Gray cube.** For `U = D¹ ⊗ D¹ ⊗ D¹`, presented with hexagon composites as the boundary of its 3-cell X, show that any two U-composites are connected. The essential case: a 3-term from `⌈∂⁻U⌉` to itself built from coherences only (no X) is connected to the identity. This is RC(3) for the boundary 2-sphere of the cube.
3. **RC(3) for loop-free contexts.** Prove RC(3) for every context presenting a frame-acyclic molecule (or its skeleta), or for every finite loop-free computad. Equivalently for molecules: uniqueness in G(3), and hence existence in G(4).
4. **G(n) for all n.** Prove RC(n) for loop-free contexts for all n, or the weaker G(n). In particular: does Chanavat's contractibility of the subdivision poset (Thm 2.52) translate into CaTT cells, with a 1-cell for each edge of the poset and higher cells for its higher simplices, each a substituted coherence over a pasting context?

## 5. What counts as a solution

Explicit terms for question 1 or 2; a proof of RC(3) or RC(n) on loop-free contexts; or a counterexample: a frame-acyclic molecule with two U-composites (or a loop-free context with two parallel terms of equal strict image) not connected by any CaTT term. A published reference also counts.

## 6. Literature (searched 2026-11-18)

- No paper treats composites of non-globular molecules inside CaTT or inside Grothendieck–Maltsiniotis weak ω-categories.
- Chanavat ([arXiv 2603.22242](https://arxiv.org/abs/2603.22242)) and Campion ([arXiv 2311.00200](https://arxiv.org/abs/2311.00200)) prove the (∞,n) pasting theorem, the semantic analogue of G. No comparison between CaTT's models and (∞,ω)-categories is known, so it does not transfer directly.
- Hadzihasanovic's diagrammatic sets ([arXiv 1909.07639](https://arxiv.org/abs/1909.07639), [arXiv 2007.14505](https://arxiv.org/abs/2007.14505)) take "every round molecule has a weak composite, unique up to equivalence" as the definition of a weak higher category. G asks whether CaTT's models satisfy it.
- Benjamin–Markakis–Sarti ([arXiv 2406.12127](https://arxiv.org/abs/2406.12127)) and ICaTT ([arXiv 2602.16602](https://arxiv.org/abs/2602.16602)): composites of coherences are invertible, so uniqueness only needs some connecting cell.
- Ara, Burroni, Guiraud, Lafont, Métayer, *Polygraphs* ([arXiv 2312.00429](https://arxiv.org/abs/2312.00429)): 2-cells of free 2-categories as 2-paths modulo exchange; Squier-style coherence.
- Ara–Lucas ([arXiv 1909.13564](https://arxiv.org/abs/1909.13564)), Cor. 3.11, and Steiner (HHA 6, 2004): Gray tensors of free strict ω-categories are free on their atoms.
