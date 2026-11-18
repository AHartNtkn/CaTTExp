# A finite test for when a map of computads presents a cartesian fibration

*Self-contained problem statement. No project context needed.*

## Background

**(∞,ω)-categories and marking.** Work in Loubaton's model of (∞,ω)-categories (F. Loubaton, *Categorical theory of (∞,ω)-categories*, arXiv:2406.05425).
- A *marked* (∞,ω)-category is one with a chosen class of cells of positive dimension, containing the equivalences and closed under composition.
- A^♯ marks every cell, A^♭ marks only the equivalences, and D_n^t is the n-globe with its top cell marked.
- ⊗ is the (marked) Gray tensor product.

**Left cartesian fibrations (Loubaton Def. 3.2.2.1).** A map p : E → B of marked (∞,ω)-categories is a *left cartesian fibration* if it has the unique right lifting property against the maps

```
K ⊗ {0} → K ⊗ [1]^♯,        K ∈ { D_n^♭ : n ≥ 0 } ∪ { D_n^t : n ≥ 1 }.        (19)
```

Equivalently (Loubaton Thm 3.2.2.24(5)), the following three conditions hold:
1. every 1-cell of B has a marked lift with prescribed source, unique up to a contractible space;
2. for every marked u : x → x′ and every z, `E(x′, z) ≃ E(x, z) ×_{B(px, pz)} B(px′, pz)`;
3. every hom map `E(x, y) → B(px, py)` is a *right* cartesian fibration, defined dually with endpoint 1.

Condition 3 makes the variance **alternate with dimension**: cocartesian 1-cells, cartesian 2-cells, cocartesian 3-cells, and so on.

**Why fibrations matter here.** Left cartesian fibrations over B^♯ correspond to functors B → ω (Loubaton's lax Grothendieck construction, Thm 4.1.4.2). A weighted limit with weight W is the *marked lax limit* over the total space ∫W, with its fibration marking (this is proved; see "What is known").

**Computads.** A finite computad (polygraph) is a finite list of generating cells, each with a boundary built from earlier ones. `Free(Ψ)` is the free (weak) ω-category it generates.

A map of computads `π : Ψ → Γ` sends each generator of Ψ to a cell of `Free(Γ)`, possibly an identity. A *marking* μ of Ψ is a subset of its positive-dimensional generators. It generates a marking of `Free(Ψ)` by closing under identities, composites and equivalences, and that closure needs no condition on μ.

## Statement

**Problem.** Find a **finite, generator-level** condition (FT) on `(π : Ψ → Γ, μ)`, for finite computads Ψ and Γ, such that

```
(FT)  ⟹  Free(Ψ)^μ → Free(Γ)^♯ is a left cartesian fibration in the sense of (19).
```

"Finite" means: checkable by inspecting finitely many generators and their boundaries, without quantifying over all globes K or all cells of `Free(Ψ)`.

Ideally (FT) should also be **complete for a natural class of weights**: every weight W : Free(Γ) → ω in the class should have some finite presentation satisfying (FT).

## What is known

1. **The infinite criterion is exact.** (19) itself is necessary and sufficient. Restricting it to generators of the saturation is what Loubaton's definition does. It is an infinite schema.
2. **Mere existence of marked lifts of generators is not enough.** Take I = (0 → 1) and a free category E on arrows u : x → y and v : x → z, both over the generator. A lift exists at x, but u is not cocartesian, since factoring v through u needs an arrow y → z.
3. **Solved case: set-valued weights over graphs.** Let Γ and Ψ be graphs, with π sending vertices to vertices and edges to edges, and every edge of Ψ marked. Then (19) holds iff **π is a discrete opfibration of graphs**: each vertex e of Ψ and each edge u of Γ out of π(e) has exactly one edge of Ψ over u out of e.
   - Proof: unique edge lifting gives unique path lifting. The free weak ω-category on a graph is equivalent to the free category (Dean–Finster–Markakis–Reutter–Vicary, Leinster, Benjamin–Markakis), so homs are discrete and condition 3 is trivial. Condition 2 is unique factorisation.
   - Every functor Free(Γ) → FinSet has such a presentation (its category of elements is free on the covering graph), so the test is complete for finite-set-valued weights.
4. **Weighted limits are marked lax limits** in Loubaton's model, in all dimensions (Loubaton Cor. 4.2.2.6, Cor. 4.2.3.18, Thm 4.1.4.2). Marking a k-cell of the index makes the (k+1)-dimensional cone cell invertible (Remark 4.2.3.7).

## The first open case, and a candidate

Let Γ be a graph and `W : Free(Γ) → Cat` a functor to 1-categories, each `W(i)` the free category on a finite graph G_i, and each `W(u)` induced by a map of graphs `G_i → paths(G_j)`.

The Grothendieck construction ∫W is a 1-category in which each square

```
β ; u_{e′}  =  u_e ; W(u)(β)          (β : e → e′ vertical in G_i, u : i → j in Γ)
```

commutes. ∫W is **not free**. A computad presentation Ψ has:
- the vertical generators (edges of the G_i, unmarked);
- marked horizontal lifts u_e, one per vertex e of G_i and edge u of Γ;
- **2-generators `θ_{u,β}`** filling these squares, which must be **marked**.

The marking is the "cartesian 2-cells" part of the alternating pattern. Since `π(θ_{u,β})` is an identity of Free(Γ), marking θ makes its cone cell invertible.

**Candidate (FT₂).** π : Ψ → Γ, with Γ a graph and Ψ of dimension ≤ 2, satisfies FT₂ if:
1. π sends each 1-generator to an edge or an identity (call these *horizontal* and *vertical*), and each 2-generator to an identity;
2. for each vertex e and each edge u out of π(e), there is exactly one marked horizontal generator over u out of e;
3. for each vertical generator β : e → e′ and each such u, there is exactly one marked 2-generator θ_{u,β}, with boundary `β ; u_{e′} ⇒ u_e ; t_{u,β}` for some vertical path t_{u,β}, its "transport";
4. there are no other generators.

**Conjecture.** FT₂ implies that `Free(Ψ)^μ → Free(Γ)^♯` is a left cartesian fibration *after inverting the marked 2-generators*. The marked lax limit over Ψ^μ of any diagram pulled back along π equals the marked lax limit over that localisation.

The second sentence is a **localisation lemma**, of independent interest:

> **(Loc)** Let J be a marked (∞,ω)-category and θ a marked k-cell, k ≥ 2, that every diagram under consideration sends to an equivalence. Then marked lax limits over J and over J[θ⁻¹] (with θ⁻¹ and its witnesses marked) agree.

*Sketch for (Loc).* A marked cone over J has an invertible cone cell over θ. It extends to J[θ⁻¹] by inverting that cell, and the space of extensions is contractible, since the inverse and its witnesses are determined up to contractible choice. Making "contractible" precise needs Loubaton's localisations of marked (∞,ω)-categories.

## Why it matters

A type theory for higher categories with lax limits and a per-generator "invertible cone cell" flag gets **all weighted limits for free**: write the weight as a finite computad over the diagram shape, with a marking, and take a marked lax limit. To accept only correct weight presentations, a proof checker needs a decidable test on the presentation. Loubaton's criterion is exact but infinite. A finite test would make weighted limits a checkable rule rather than a semantic side condition.

## What would count as a solution

Any of:
- a proof of the conjecture for FT₂ and its extension to graphs Γ with weights in free n-categories (alternating the variance in each dimension);
- a proof or disproof of (Loc);
- a different finite criterion, with a proof that it implies (19);
- a proof that no finite criterion can be complete for category-valued weights, e.g. because transports need not be finitely presentable.

## Literature search (2026-11-18)

- **Loubaton** (arXiv:2406.05425): exact criterion (Def. 3.2.1.1, 3.2.2.1, Thm 3.2.2.24), stated for arbitrary marked (∞,ω)-categories, with no computad-level test.
- **Abellán–Haugseng–Martini** (arXiv:2602.07604) and **Gagna–Harpaz–Lanari** (arXiv:2012.04537): (∞,2)-dimensional theory of fibrations and partially lax limits. Generator-level criteria are not discussed.
- For 1-categories, "discrete opfibrations over a free category are free on a covering graph" is folklore, and the graph-level test of item 3 is standard.
- **Nothing found** on finite criteria for cocartesian fibrations between free (strict or weak) higher categories presented by polygraphs.
