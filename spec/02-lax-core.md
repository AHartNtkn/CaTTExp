# Chapter 2. The lax core L

The lax core keeps all of chapter 1: the same syntax, the same judgments, the same `coh` rule. It changes **only the side condition** of `coh`. Plain CaTT reads the side condition off the free strict ω-category on the coherence's pasting context, where interchange holds as an equation. L reads it off a free structure in which interchange is a directed cell.

There is one rule, parameterised by the strict theory the side condition computes in:

| Theory the side condition computes in | Name | Role |
|---|---|---|
| V + S, S ⊆ {inner law, R} | **uniform L**, setting S | **the kernel** (§2.3) |
| the free Gray-enriched category 𝔉(Γ) | two-tier L | the fragment where interchange is directed only across objects; the implemented checker (§2.5) |
| the free strict ω-category ν(λΓ) | plain CaTT (P) | the reference instance of chapter 1 (§2.2) |

Each row's free objects map onto the next row's, so (§2.6) every derivation in a row above is a derivation in the rows below. That is the precise sense in which uniform L ⊂ two-tier L ⊂ P.

## 2.1 Notation

- Every pasting context decomposes uniquely as a wedge of suspensions Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ, with objects a₀, …, aₙ. Θᵢ is the pasting context of the cells in the hom from aᵢ₋₁ to aᵢ.
- For a strict theory 𝕋 (one of the rows above), **F_𝕋(Γ)** is its free object on Γ. Every term t over Γ has a **strict interpretation** ⟦t⟧_𝕋, a cell of F_𝕋(Γ), defined by induction: a variable goes to its generator, and a coherence goes to the cell its side condition provides (§2.3), transported along the map of free objects its substitution induces (requirement 5 below).
- **supp(c)**, for a cell c of ν(λΓ) or 𝔉(Γ), is the downward-closed set of Steiner basis elements used by c and by its iterated boundaries. Support is always measured in these **finite** Steiner bases. It is never measured in the expanded basis of F_{V+S}(Γ), which is infinite already on Σ[2] ∨ Σ[2] (lax r10 (K45)/(K50)).
- **π** is the requirement-4 projection F_{V+S}(Γ) → 𝔉(Γ), which makes every interchanger along a k-cell with k ≥ 1 an identity. For ν and 𝔉 themselves, π is the identity.
- Composition order is diagrammatic, and composition across objects is 𝒦(a, b) ⊗ 𝒦(b, c) → 𝒦(a, c) in execution order (`notes/conventions.md` §1, §4).

## 2.2 The side condition, in one form for every row

**Rule.** The `coh` rule of chapter 1, §1.4, with

```
SC_𝕋(Γ, t →_A u)   :⟺   F_𝕋(Γ) has a cell  c : ⟦t⟧_𝕋 → ⟦u⟧_𝕋  (an identity allowed)
                          whose projection π(c) has full support in 𝔉(Γ)  (in ν(λΓ) for 𝕋 = ν).
```

The coherence is in the **coherence case** if ⟦t⟧ = ⟦u⟧ in F_𝕋(Γ), and in the **operation case** otherwise. By Lemma 2.2.1, π(c) is then the total cell τ_Γ or an identity on a full-support cell.

**Interpretation of the coherence (the designated lift).** For ν and 𝔉, c is unique by support-determines-cells, and it is the interpretation. In F_{V+S}(Γ) it need not be unique: distinct cells can share a Gray image (on Σ[2] ∨ Σ[2] the loop H and 1_w do). The interpretation is therefore fixed **per coherence head** (Γ, t →_A u), once:
- in the coherence case, c := the identity on ⟦t⟧;
- in the operation case, c := the first witnessing path of minimal length found by the decision procedure of §2.3, in its fixed enumeration order. This is well defined even where F_{V+S}(Γ) has loops.

Because substitution never changes a coherence's head, ⟦coh_{Γ,A}[σ]⟧ := σ_*(c_{Γ,A}) is stable under substitution by construction (requirement 5). The kernel's judgments do not depend on the choice, only the interpretation in the free objects of V + S does. Whether all candidate lifts for one head are connected by higher cells, so that the choice is irrelevant up to coherence, is **open** (ledger S11).

**Lemma 2.2.1 (agreement with the support form).** For 𝕋 = ν (plain CaTT) and 𝕋 = 𝔉 (two-tier L), SC_𝕋 holds iff one of
```
(operation)  ⟦t⟧ = ∂⁻τ_Γ  and  ⟦u⟧ = ∂⁺τ_Γ,  where τ_Γ is the total cell of F_𝕋(Γ)
(coherence)  ⟦t⟧ = ⟦u⟧  and  supp⟦t⟧ = all generators
```
and, by support-determines-cells, these are the support conditions `supp(t:A) = Supp(∂⁻τ), supp(u:A) = Supp(∂⁺τ)`, respectively `supp(t:A) = supp(u:A) = everything`, of `notes/pseudo-vs-gray.md` §3.3.

*Proof.* Here π is the identity. The total cell τ_Γ has full support (`Gray/FullSupp.agda`). If c has full support it contains the top generator, so dim c ≥ dim τ_Γ. If dim c = dim τ_Γ then c = τ_Γ by support-determines-cells (`Strict/Recon.b-supp`), which is the operation case. If dim c > dim τ_Γ then c has no generator in its own dimension, so it is an identity, which is the coherence case. Conversely τ_Γ and the identity on a full-support cell are cells of the required kind. ∎

**Status.** The single form SC_𝕋 is **stated here**. It is how `notes/design-decisions.md` §1.1 describes the rule ("read off the free object F_T(Γ)"), but no note writes it out (ledger S1). A first version of this chapter measured support in the expanded basis of F_{V+S}(Γ); the independent check of S1 showed that version rejects even the composite interchanger on Σ[2] ∨ Σ[2], and recommended the projected form above, which this chapter now uses. The designated lift is a SPEC decision (S11). Lemma 2.2.1 is **stated here** with the proof above, whose two inputs are Agda-checked. On a single hom (n = 1), the 𝔉 instance equals Finster–Mimram's Var condition: **Agda-checked** (`Gray/SingleHom.agda` for the rule level, `Gray/SuppVars.agda` and `Strict/SuppFV.agda` for the term level; ledger E1).

**Source.** `notes/design-decisions.md` §1.1; `notes/pseudo-vs-gray.md` §3.2–3.3, §3.6; ledger E1.

## 2.3 The kernel: the side condition computed in V + S

### The theory V

An **admissible** theory is a strict theory on the T₁₂ signature (strict associative and unital composition, an elementary interchanger χ for every pair k < l, naturality cells per varying argument with Leibniz-signed orientation, higher cells between routes) whose free objects on finite pasting diagrams satisfy:

1. an explicit combinatorial description by generators with explicit boundaries;
2. two cells of the same dimension using the same generators, in the expanded basis, are equal;
3. every elementary interchanger exists and its reverse does not;
4. making every interchanger with k ≥ 1 an identity gives the free Gray-enriched category 𝔉(Γ), and making every interchanger an identity gives the free strict ω-category ν(λΓ);
5. closure under substitution of cells for generators.

**V** is the forced base B together with the guarded round-5 equations. On every finite pasting diagram Γ, F_V(Γ) maps generator-preservingly into F_E(Γ) for every admissible E. So a directed cell or an equality exists in F_V(Γ) **iff** it exists in every admissible theory. V is the least admissible theory on pasting diagrams.

### The switch settings

Two laws of T₁₂ are **visible** on pasting diagrams, meaning that switching them on changes some free object F(Γ):
- the **inner law** (inner composite-crossing law, the left split): the direct crossing of A₁ ∗ A₂ past B equals the paste of the crossings of A₁ and of A₂;
- **R** (the right split): the mirror statement, splitting a composite right operand.

A **setting** is a subset S ⊆ {inner law, R}. The side condition of setting S computes in V + S. All four settings are admissible and pairwise distinct:

| Setting | Theory | Cells on the suspended 2 × 3 interval |
|---|---|---|
| ∅ (no switch) | V | 49 |
| {R} | V + R | 14 |
| {inner law} | V + inner law | 29 |
| {inner law, R} | T₁₂'s pasting profile | 2 |

The other laws once catalogued as switches (the prime left splits L_p and the divisibility laws D_{d,p}) are **invisible** on pasting diagrams, because every chronological 3-endomorphism of a free object on a pasting diagram is an identity. They do not change the kernel, so they are not switches.

**Rule.** The kernel's `coh` rule is the rule of §2.2 with 𝕋 = V + S:

```
Δ ⊢ps     Δ ⊢ t →_A u     SC_{V+S}(Δ, t →_A u)     Γ ⊢ σ : Δ
──────────────────────────────────────────────────────────────── (coh_S)
            Γ ⊢ coh_{Δ, t →_A u}[σ] : (t →_A u)[σ]
```

A development **declares its setting S** once, and every coherence in it is checked against V + S. The kernel has no default setting (chapter 0, §0.5). V (S = ∅) is the most general setting.

**Imports run upwards.** If S ⊆ S′, the identity on letters maps F_{V+S}(Γ) to F_{V+S′}(Γ) and sends cells to cells, so every judgment derivable in setting S is derivable in setting S′, and a development checked in S can be imported into one checked in S′. A development checked in S′ cannot be imported into S. The step from a map of free objects to SC is Agda-checked for any map that sends letters to letters and full supports to full supports (`Uniform/Rule.agda`, `Transport.sc-map`). On the grid layer the comparison maps are checked (`Grid.nf-compare`).

**Side condition and decision procedure.** SC_{V+S}(Δ, t →_A u) is decided as follows.
1. Compute ⟦t⟧ and ⟦u⟧ in F_{V+S}(Δ) (normal forms by rank increments; r9 (K65), r10 Response 1).
2. Decide whether ⟦t⟧ = ⟦u⟧. If so, check that π⟦t⟧ has full support in 𝔉(Δ); this is the coherence case.
3. Otherwise search for a path ⟦t⟧ → ⟦u⟧ in F_{V+S}(Δ) whose projection π(c) has full support in 𝔉(Δ), i.e. by Lemma 2.2.1 π(c) = τ_Δ or an identity on a full-support cell.
   - **No length bound is used.** Paths in F_{V+S}(Δ) are not bounded by their endpoints: some free objects have loops. Examples are the loop H of V at degree 4 on Γ_{2,2}, which has pairwise distinct powers, and a positional self-loop at degree 5 on the 2 × 2 grid in T₁₂ (ledger S14).
   - **What is finite** is the set of vertices. At fixed lower faces and weight there are finitely many vertex normal forms (K58), and the native generating steps between them are finitely many and listable (r10 Response 3).
   - The support of a composite path is the union of its steps' supports. So search breadth-first over pairs (vertex, support accumulated so far in 𝔉(Δ)). This state space is finite, since supports are subsets of the finite Steiner basis of 𝔉(Δ). Accept when the target ⟦u⟧ is reached with full accumulated support.
   - Reachability in a finite closed universe is decidable without a length hypothesis: loop removal plus pigeonhole, with breadth-first saturation proved exact. It is Agda-checked in `Uniform/FiniteGraph.agda` (PR #380). The search over pairs is Agda-checked for any layer with finite closed universes (`Uniform/RuleFin.agda`, `DecideFin.sc?`), and `Uniform/KernelDec.agda` runs the kernel over it.
   - The **designated lift** is the first witnessing path of minimal length, in the fixed enumeration order of steps. A shortest witness exists whenever any witness exists. There are finitely many paths of each length, so the choice is well defined.

Equality and reachability in F_{V+S}(Γ) are decidable for every setting, in every dimension, uniformly in Γ, the degree and the switch bits, and the comparison maps between settings are computable (r10 Response 3, by breadth-first search over the finite vertex list). An earlier version of this section derived decidability from a length bound on paths. That bound fails where free objects have loops (ledger S14). The abstract step that needs no bound is `Uniform/FiniteGraph.agda`. `Join/BoundedReach.agda` (`Reach.Bounded.reach?`) still holds, but only for loop-free layers.

**Cost.** Decidable is not cheap. The problem is P-hard; shared reachability is coNP-complete already on a fixed grid; a uniform 2-EXPSPACE bound holds; equality is polynomial for structural terms, on two-row grids in each fixed degree, and for exponential-width schedules (r10 Responses 3–21). A polynomial algorithm on arbitrary shared terms is open (ledger E9, E12). None of this changes the rule.

**Example (a): the interchanger, every setting.** Δ = ΣD¹ ∨ ΣD¹: α : f ⇒ f′ : x → y and β : g ⇒ g′ : y → z.
- `coh_{Δ, (f◁β);(α▷g′) → (α▷g);(f′◁β)}` is accepted in every setting. Its cell is the elementary interchanger χ_{α,β}, which is the lax naturality cell when β is a transformation and α an arrow of an element.
- The reverse, `coh_{Δ, (α▷g);(f′◁β) → (f◁β);(α▷g′)}`, is rejected in every setting: requirement 3 for every admissible theory, and in the Gray quotient no term at all has that type (below).
- There is no horizontal composite: a cell from f ; g to f′ ; g′ has hom-dimension 1, so it cannot use the generator α ⊗ β, which has hom-dimension 2, and no such cell has full support.

**Example (b): the strip, where the settings differ.** Inside a hom, take composable inner cells A₁, A₂ and a cell B in interchange position (the strip C_{2,1}). Let u = W(A₁ ∗ A₂, B), the direct crossing, and v the paste of W(A₁, B) and W(A₂, B).
- Settings ∅ and {R}: ⟦u⟧ ≠ ⟦v⟧ and neither reaches the other, so neither `coh(u → v)` nor `coh(v → u)` is accepted. In the tagged model of (K44) they really differ.
- Settings {inner law} and {inner law, R}: ⟦u⟧ = ⟦v⟧, and its Gray image has full support, so `coh(u → v)` and `coh(v → u)` are both accepted, in the coherence case, and are invertible.
- The law cannot be added as a hypothesis instead: a declared cell κ : u ≅ v is not seen by the side condition, so its two uses in a three-fold composite are unrelated until the user declares a 6-cell, then a 7-cell, without end (`notes/design-decisions.md` §1.4(c)).

**Example (c): inside an object.** In one object C, take two 2-cells of C composable along a 1-cell (the context Σ(ΣD¹ ∨ ΣD¹) placed in the hom 𝒦(X, C)). Uniform L gives a directed interchanger one dimension up, as for transformations across objects; two-tier L and P make it invertible. Directed Eckmann–Hilton is therefore a pair of directed cells b ∗ a ⇛ a ∗ b and a ∗ b ⇛ b ∗ a, not inverse to each other, and it is invertible only with the `ord` mark, or with a switch and an `inv` input (chapter 3, §3.6 Example (a)). The rule-level computation is checked by evaluation (`Uniform/Marks.agda`). The run on the actual F_V waits for the uniform checker (ledger S3).

**Semantics.**
- **Admissible theories.** A judgment derivable in setting S holds in the free objects of every admissible theory satisfying S. In particular a setting-∅ development is valid in the models of every admissible theory.
- **Gray-enriched models.** By requirement 4 every cell of F_{V+S}(Γ) projects to a cell of 𝔉(Γ). Every accepted coherence projects to an accepted two-tier coherence: if c witnesses SC_{V+S}(Δ, t → u), then π(c) : π⟦t⟧ → π⟦u⟧ has full Gray support, which is SC_𝔉 for the projected terms. So every model of two-tier L (in particular strict ω-Cat with lax transformations, and every oriented (∞,ω)-category) is a model of uniform L, interpreting each coherence through its projection. This is immediate from the form of the rule (ledger S2).
- **What uniform L adds.** Objects need not be ordinary ω-categories: their own compositions may interchange directedly (Gepner–Heine's oriented categories are examples of such objects). The ambient and its objects are then the same kind of structure, which keeps a future lax universe object possible without a mismatch.

**Status.**
- V exists, is least on pasting diagrams, and decides equality and reachability: **proved** (verified researcher answers r8, r9, r10; ledger E6, E12).
- The four settings are admissible and distinct: **proved** (r9 Responses 2–5, K73) and computed (`scripts/e6/interchange_fibre_decorations.py`).
- Reachability in a finite closed universe, with no length bound: **Agda-checked** (`Uniform/FiniteGraph.agda`, PR #380). The bounded-path version (`Join/BoundedReach.agda`) applies only to loop-free layers (S14).
- The switch maps extend functorially to the cospan completions, and the switched laws keep seed lists: **Agda-checked** (`Join/SwitchCospan.agda`, `Join/SwitchLaws.agda`), with the link between raw syntax and the completion by inspection only (ledger E12 items (a)–(c), owner LCORE).
- The rule (coh_S) as a single condition on F_{V+S}: **stated here**, in the projected form recommended by the independent check (ledger S1). Uniqueness of the lift up to coherence: open (S11).
- **The checker for (coh_S), relative to the free objects: Agda-checked** (`Uniform/Kernel.agda`, `Uniform/Rule.agda`; `notes/uniform-checker.md`). For any family of free-object layers with a grading bound, SC is decidable, the judgments are those of `TypingWith` at that side condition, and the checker is sound and complete. The layers of F_{V+S} in every degree are not yet constructed in Agda, so this is the kernel checker relative to them (ledger S3a).
- **The switch layer: Agda-checked** (`Uniform/Grid.agda`, `Uniform/GridExamples.agda`). In every setting, equality of 4-cells on suspended m × n grids is decided, with normal forms and computable comparison maps. The counts 2, 1, 2, 1 (1 × 2), 2, 2, 1, 1 (2 × 1) and 49, 14, 29, 2 (2 × 3) are computed, and so is example (b) as an equality statement. Directed 5-cells between these 4-cells are not modelled (ledger S3b).
- The implemented checker for actual developments is still two-tier L (§2.5).

**Source.** `notes/design-decisions.md` §1.2, §1.7, Lemma V-dec; `notes/joining-completion.md` §8; `notes/conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`, `-r9-`, `-r10-`; ledger E6, E12.

## 2.4 Which coherences are invertible

| Cell | Invertible? | Reason |
|---|---|---|
| coherence case (⟦t⟧ = ⟦u⟧) | yes | the reversed coherence satisfies the same side condition; Benjamin–Markakis's argument goes through unchanged |
| operation case on a single hom, in the Gray quotient | no, as in CaTT | |
| elementary interchanger, every setting | **no** | requirement 3; in the Gray quotient the reverse type is uninhabited (Agda-checked, below) |
| a crossing of a composite against the paste of crossings | in settings containing the matching split: yes, as a coherence case; otherwise there is no cell either way | §2.3 example (b) |
| interchanger with an invertible or pseudo factor | only through the marks of chapter 3 | chapter 3 |

**Status.** For two-tier L, non-degeneracy (no term of the reverse interchanger's type) is **Agda-checked** with no hypothesis (`Strict/ReverseInterchanger.agda`, `no-reverse-interchanger`, from strict-model soundness `Strict/Soundness.agda`; ledger E3). For V + S it is requirement 3 (**proved**, r8).

## 2.5 The two-tier fragment and the implemented checker

Two-tier L computes the side condition in the free Gray-enriched category 𝔉(Γ), whose homs are Gray tensors of Steiner complexes:

```
𝔉(Γ)(aᵢ, aⱼ)  =  ν(λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ)      (factors in execution order)
```

Generators are tuples θᵢ₊₁ ⊗ … ⊗ θⱼ with dimension the sum and boundary by the Leibniz formula. The total cell τ_Γ is the tensor of the composites ⟨Θᵢ⟩. Supports are Steiner chains, so the side condition of Lemma 2.2.1 is integer linear algebra.

This is not the kernel's default theory. Marking every object `ord` in uniform L gives two-tier L's invertibility judgments exactly (chapter 3, §3.6), but its coherences only up to the relative coherence question of ledger E13, and in settings without the inner law not by the coherence rule alone. It is the theory the checker currently implements, and the one with a full machine-checked soundness proof.

**Decision procedure.** Symbolic supports and an exact cover check (`Gray/Cover.agda`, `Gray/Fast.agda`), proved equal to the explicit support computation (`fastSide ≡ graySide`). Measured growth on n-fold wedges is about n⁶ up to n = 28. Explicit supports are exponential (a term of size O(n) has support of size 3ⁿ), so the symbolic form is required.

**Example (the Gray cube).** Δ = ΣD¹ ∨ ΣD¹ ∨ ΣD¹. The total cell is the top cell of the 3-cube, a 4-cell of 𝒦 between the two hexagons of whiskered interchangers. `hex⁻ ⇛ hex⁺` is accepted as one operation-case coherence over a pasting context, and the reverse is rejected (`Gray/Cube.agda`). No coherence over a non-pasting context is needed; the Gray molecules appear only inside the side-condition computation.

**Semantics.** Every strict Gray-enriched category models two-tier L (Theorem 1 of `notes/pseudo-vs-gray.md` §3.6), and every oriented (∞,ω)-category does (Theorem 2 there, whose hypotheses (D)–(F) are discharged by Campion, arXiv 2311.00205, and Chanavat, arXiv 2603.22242). The coherent-choice gap for interpreting a dependent type theory in an (∞,ω)-category is shared with CaTT (`notes/semantics-gaps.md`).

**Status.** Rule, checker and decidability: **Agda-checked** (`Gray/Support.agda`, `Gray/Typing.agda`, `Gray/Fast.agda`). Soundness of every derivable term in the strict model: **Agda-checked** with no hypothesis (`Strict/Soundness.agda`; (B) and the total-cell fact are theorems, `Strict/Recon.agda`, `Strict/Bridge.agda`). Conservativity over CaTT on a single hom: **Agda-checked** (ledger E1). (∞,ω) soundness: **proved** from the literature. **Source:** `notes/pseudo-vs-gray.md` §3; `notes/agda-gray-findings.md`; ledger E1–E3, E9.

## 2.6 The generality ordering

**Statement.** If SC_{V+S}(Γ, A) then SC_𝔉(Γ, A); and if SC_𝔉(Γ, A) then SC_ν(Γ, A′) for the image A′ of A under the collapse. So every uniform-L derivation is a two-tier derivation, and every two-tier derivation a CaTT derivation, up to the collapse of Gray molecules to cartesian composites.

**Status.**
- Every model of P is a model of two-tier L (change of base along X ⊗ Y → X × Y): **proved** (`notes/pseudo-vs-gray.md` §2.4).
- Uniform to two-tier: immediate from the projected form of the rule (§2.3 *Semantics*; ledger S2).
- The converse directions (P = two-tier L + "every interchanger invertible", two-tier = uniform + `ord`) are the subject of chapter 3. For marks the second holds exactly (§3.6). For coherences it fails by the coherence rule alone in settings without the inner law (the strip), and is otherwise a relative coherence question (ledger E13).

## 2.7 Dualities

CaTT has a duality D_J for every J ⊆ {1, 2, …}: reverse the cells whose dimension is in J (Benjamin–Markakis). Two-tier L keeps four of them as symmetries (`notes/closed-structure.md` §D.2, including op). The uniform core keeps one.

**Statement (Theorem D4).** In every setting S:
- D_J sends every uniform-L derivation to a uniform-L derivation iff **J = ∅**;
- D_J sends uniform L to the oplax core (every elementary interchanger reversed) iff **J = all**. The image of setting S is the oplax core in setting mirror(S), which exchanges the inner law and R: V + {inner law} goes to V^∘ + {R}, and V + {R} to V^∘ + {inner law};
- every other J maps some accepted coherence to a rejected type. Its image is a mixed core D_J(V + S), which can be checked by running the V + S checker on the dualised input.

**Why.** D_J sends the elementary interchanger of two (l+1)-cells juxtaposed along a k-cell to the reverse type iff a_{k+1} + a_{l+1} + a_{l+2} is odd, where a_m = [m ∈ J]. Two necessary conditions follow:
- the Gray interchanger at every level n, over Σⁿ(ΣD¹ ∨ ΣD¹), must keep its orientation;
- J must pass the two-tier test.

Together these force J = ∅. Neither alone does: J = {1,2,4,5,7,…} passes the first and fails the second, while op passes the second and fails the first.

**Example.** op = D_odd reverses 3-cells and keeps 2-cells and 4-cells. Over Σ(ΣD¹ ∨ ΣD¹) (§2.3 example (c)), it sends the accepted interchanger of two 2-cells of an object to the reversed interchanger, which every setting rejects. In two-tier L that interchanger is an identity, which is why op is a two-tier symmetry. So in uniform L the "prove once, get the op-dual free" rule holds only in the `ord` fragment (chapter 3).

**Status.**
- Sign arithmetic, the orientation lemma (the three flips taken as the definition of the action), the classification and the switch exchange: **Agda-checked** (`src/CaTTExp/GrayDualityUniform.agda`: `dual-canonical`, `kernel-theorem`, `J124-gray-rows`, `op-gray-rows`, `dual-has`, `total-mirror`, `level-uniform`; no postulates).
- That the action is the three flips, and that the two-tier witnesses live on contexts ΣD¹ ∨ ΣD^q, where F_{V+S} = 𝔉: **argued** (`notes/closed-structure.md` §D.4.1).

**Source.** `notes/closed-structure.md` §D.4; ledger D8.

## 2.8 Open surface questions

**Q2.1. Which setting a development starts in.** The kernel requires the setting to be declared.
- *Option A: the surface defaults to ∅ (V), and the user switches laws on.* Every development is as general as possible unless the author asks otherwise; a proof that needs a split fails to check until the switch is written, which is visible. Imports from more general developments always work.
- *Option B: the surface defaults to {inner law, R} (T₁₂), and the user switches laws off.* Proofs about composites of crossings go through with no annotation; a development silently proves a statement valid only in T₁₂'s models, and cannot be imported into a more general one.
- *Option C: no default; the surface makes the user write the setting.* One line per file; nothing silent; slightly more ceremony.
- *Worked example.* Example (b) of §2.3: under A, `coh(u → v)` fails with "no cell ⟦u⟧ → ⟦v⟧ in V; the inner law would make them equal"; under B it succeeds silently; under C the file header decides.

**Q2.2. How a horizontal composite across objects is written.** The kernel has no horizontal composite; there are two layerings, ∂⁻τ (later factor first) and ∂⁺τ (earlier factor first), related by the directed interchanger from ∂⁻ to ∂⁺.
- *Option A: no notation; the user writes the layering they mean.* Nothing hidden; every composite of transformations across objects is written twice as long.
- *Option B: one infix operator elaborating to the ∂⁻-layering.* From ∂⁻, every other layering is reachable by a derivable cell, so a user never needs the other layering's inverse. Proposed in `notes/invertibility-markings.md` §6.2.
- *Option C: one infix operator elaborating to the ∂⁺-layering.* Nothing is reachable from it without a pseudo mark; matches the reading "earlier factor first".
- *Worked example.* For an element arrow f (earlier) and a transformation α (later), A writes `α_x ; Gf` or `Ff ; α_y` explicitly; B's `f ⋆ α` means `α_x ; Gf`, and the naturality cell goes out of it; C's `f ⋆ α` means `Ff ; α_y`, and the naturality cell comes into it.

**Q2.3. How a failed side condition is reported.** The kernel's answer is a boolean.
- *Option A: report "not admissible".* Cheapest; useless to a person.
- *Option B: report the two strict images and their supports.* Useful in the Gray fragment, where supports are readable sets of tuples; in V + S the cells are decorated normal words and need their own printer.
- *Option C: report the nearest accepted type* (for example, "the reverse direction is accepted"). Most helpful for the common error of a reversed interchanger; needs a search over candidate types.
