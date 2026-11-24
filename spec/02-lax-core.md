# Chapter 2. The lax core L

The lax core keeps all of chapter 1: the same syntax, the same judgments, the same `coh` rule. It changes **only the side condition** of `coh`.

**What the side condition is.** It is a finite combinatorial test on the coherence's own pasting context Δ and type A. Either t and u name the same cell and each uses every variable of Δ (a coherence), or a cell of the right shape, using every generator of Δ, runs from t to u (an operation). Plain CaTT's test treats interchange as an equation. L's treats it as a directed step.

**Where "strict" enters, and where it does not.** To decide the test, the checker needs a finite description of all the cells a pasting shape has. It uses the free object F_𝕋(Δ) of a strict theory 𝕋 on Δ: finitely many generators with explicit boundaries, in which equality and reachability can be computed. That is the only role of strict structure. It is a **decision device**: nothing in the ambient 𝒦, its objects or the kernel's judgments is strict, and the kernel has no definitional equations (§0.3). The test is trusted because of the soundness theorems in §2.2, which interpret every accepted coherence in weak models (oriented (∞,ω)-categories), not because anything is strict. This is safe only on pasting contexts, which have no loops and no parallel generators, so their free strict and free weak objects agree. General diagrams are never read through a strict object (chapter 4).

**The three versions, on one example.** Take the pasting context Δ of two whiskerable 2-cells: objects x, y, z, 1-cells f, f′ : x → y and g, g′ : y → z, and 2-cells α : f ⇒ f′ and β : g ⇒ g′. In the ambient 𝒦, x, y, z are ω-categories, f, g are functors and α, β are transformations. There are two ways to compose α and β, "β first" (f◁β);(α▷g′) and "α first" (α▷g);(f′◁β). The three versions differ in what the side condition says about a cell between them.

- **Plain CaTT, written P** (chapter 1). The side condition is Finster–Mimram's *variable check*: a coherence of type t → u is accepted if t and u each use every variable of Δ, or if t uses exactly the variables of Δ's source boundary and u those of its target boundary (chapter 1, §1.4). Interchange is an equation here, so the two composites are the same cell, and coherences between them are accepted in both directions and are invertible. In 𝒦 this means α and β commute up to an invertible cell: transformations are pseudo. The device that decides the check is the free strict ω-category ν(λΔ) on Δ.
- **Two-tier L.** The side condition is the *crossing-aware check*. When a cell in the hom 𝒦(x, y) and a cell in 𝒦(y, z) are composed across the object y, swapping their order is a **directed** step, the interchanger χ_{α,β} : (f◁β);(α▷g′) → (α▷g);(f′◁β). So the coherence from "β first" to "α first" is accepted and the reverse is rejected: transformations are lax, and χ is their naturality cell. Inside one hom, where cells compose within a single object's hom, interchange stays an equation, as in P. Hence "two tiers": directed across objects, strict within a hom. Its device is the free Gray-enriched category 𝔉(Δ), whose homs are Gray tensors (§2.5). The implemented checker runs this version with a stronger coherence clause (§2.5).
- **Uniform L.** The crossing-aware check at **every** level, also inside a hom. For two 2-cells a, b composed inside one hom, swapping them is again a directed step, so Eckmann–Hilton becomes a pair of directed cells b ∗ a ⇛ a ∗ b and a ∗ b ⇛ b ∗ a, not inverse to each other (§2.3, example (c)). This is **the kernel**. Its device is the free object F_{V+S}(Δ), where V is the least theory in which every interchanger is a directed cell. S(Δ) is the marking of Δ's objects by crossing laws (left split, right split R), and V + S(Δ) imposes each law only on the crossings landing in an object marked with it; with no marks the device is F_V(Δ). The split marks are explained in §2.3.

| Version | Side condition | Decided in | Role |
|---|---|---|---|
| **uniform L** | crossing-aware at every level | F_{V+S(Δ)}(Δ) | **the kernel** (§2.3) |
| **two-tier L** | crossing-aware across objects, an equation within a hom | 𝔉(Δ) | the implemented checker, with a stronger coherence clause (§2.5) |
| **plain CaTT (P)** | variable check, interchange an equation | ν(λΔ) | the reference instance of chapter 1 (§2.2) |

Each row's free objects map onto the next row's, so (§2.6) every derivation in a row above is a derivation in the rows below. Uniform L accepts the fewest coherences and has the most models; P accepts the most. That is the precise sense in which uniform L ⊂ two-tier L ⊂ P.

## 2.1 Notation

- Every pasting context decomposes uniquely as a wedge of suspensions Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ, with objects a₀, …, aₙ. Θᵢ is the pasting context of the cells in the hom from aᵢ₋₁ to aᵢ.
- For a strict theory 𝕋 (one of the devices in the table above), **F_𝕋(Γ)** is its free object on Γ, the decision device. Every term t over Γ has a **combinatorial image** ⟦t⟧_𝕋, a cell of F_𝕋(Γ), defined by induction: a variable goes to its generator, and a coherence goes to the cell its side condition provides (§2.3), transported along the map of free objects its substitution induces (requirement 5 below).
- **supp(c)**, for a cell c of ν(λΓ) or 𝔉(Γ), is the downward-closed set of Steiner basis elements used by c and by its iterated boundaries. Support is always measured in these **finite** Steiner bases. It is never measured in the expanded basis of F_{V+S}(Γ), which is infinite already on Σ[2] ∨ Σ[2] (lax r10 (K45)/(K50)).
- **π** is the requirement-4 projection F_{V+S}(Γ) → 𝔉(Γ), which makes every interchanger along a k-cell with k ≥ 1 an identity. For ν and 𝔉 themselves, π is the identity.
- Composition order is diagrammatic, and composition across objects is 𝒦(a, b) ⊗ 𝒦(b, c) → 𝒦(a, c) in execution order (`notes/conventions.md` §1, §4).

## 2.2 The side condition, in one form for every row

**Rule.** The `coh` rule of chapter 1, §1.4, with the following test on (Γ, t →_A u). It has two clauses. The coherence clause has Finster–Mimram's shape: t and u use every variable of Γ, and they name the same cell. The operation clause asks for a cell from t's image to u's image that uses every generator of Γ.

```
SC_𝕋(Γ, t →_A u)   :⟺   (coherence)  ⟦t⟧_𝕋 = ⟦u⟧_𝕋  and  Var(t : A) = Var(u : A) = Var(Γ)
                     or   (operation)  F_𝕋(Γ) has a cell  c : ⟦t⟧_𝕋 → ⟦u⟧_𝕋  whose projection
                                       π(c) has full support in 𝔉(Γ)  (in ν(λΓ) for 𝕋 = ν).
```

Var is Finster–Mimram's syntactic set of variables used by a term and its type (chapter 1, §1.4). On derivable terms over a pasting context it is the set of variables in the closed support of the projected image π⟦t⟧, and it is a pasting sub-context (`notes/lax-sc-completeness.md` Lemma 4.2). The coherence is in the **coherence case** if the coherence clause holds, and in the **operation case** otherwise. By Lemma 2.2.1, in ν and 𝔉 the operation case is π(c) = τ_Γ.

For 𝕋 = ν the image equality is automatic: two parallel terms that use every variable both have full support in ν(λΓ), so they are equal by support-determines-cells. So the ν row is exactly plain CaTT's variable check. For 𝔉 and F_{V+S} the image equality is a real condition, and it is what keeps interchange directed: "β first" and "α first" use the same variables but have different images (example (a)).

**Interpretation of the coherence (the designated lift).** For ν and 𝔉, c is unique by support-determines-cells, and it is the interpretation. In F_{V+S}(Γ) it need not be unique: distinct cells can share a Gray image (on Σ[2] ∨ Σ[2] the loop H and 1_w do). The interpretation is therefore fixed **per coherence head** (Γ, t →_A u), once:
- in the coherence case, c := the identity on ⟦t⟧ = ⟦u⟧;
- in the operation case, c := the first witnessing path of minimal length found by the decision procedure of §2.3, in its fixed enumeration order. This is well defined even where F_{V+S}(Γ) has loops.

Because substitution never changes a coherence's head, ⟦coh_{Γ,A}[σ]⟧ := σ_*(c_{Γ,A}) is stable under substitution by construction (requirement 5). The kernel's judgments do not depend on the choice, only the interpretation in the free objects of V + S does. Whether all candidate lifts for one head are connected by higher cells, so that the choice is irrelevant up to coherence, is **open** (ledger S11).

**Why the test is sound.** Acceptance by the test is justified by interpreting every accepted coherence in models: the reference model 𝒦 and the other models below. The chain, by row:
- *Strict Gray models.* For two-tier L, every derivable term over a pasting context is a cell of the free strict Gray-enriched category, and no term has the reverse interchanger's type. The soundness proof uses the coherence clause at exactly one step, that the two sides have equal images, which is the clause itself read through support-determines-cells. That step is **Agda-checked** for the rule above (`Gray/CohCaseVar.cohV-top`). The full soundness theorem is **Agda-checked** for the implemented checker's rule (`Strict/Soundness.sound-tm`, `Strict/ReverseInterchanger.no-reverse-interchanger`, no hypothesis); its typing instance at the rule above is not yet rebuilt (ledger S30). For plain CaTT, soundness in every strict ω-category: **Agda-checked** (`Strict/OmegaSound`, chapter 1, §1.4).
- *Oriented (∞,ω)-categories.* Every oriented (∞,ω)-category in Gepner–Heine's sense, in particular ∞Cat with lax transformations, interprets two-tier L. Operation-case coherences go to lifts of the total cell, coherence-case ones to the invertible cells between parallel cells with equal image; the argument uses only the image equality, not which variables are used. **Proved on paper**: `notes/pseudo-vs-gray.md` Theorem 2, and `notes/lax-sc-completeness.md` §4 for the coherence clause above. Its hypotheses (D)–(F) are discharged from the literature (Campion, arXiv 2311.00205, Ex. 3.2, Cor. 3.5; Chanavat, arXiv 2603.22242, Thm 3.29; Gepner–Haugseng §2.5).
- *Uniform L.* Every accepted uniform coherence projects to an accepted two-tier one (§2.3 *Semantics*), so every model of two-tier L is a model of uniform L.
- *Open ends.* Interpreting a dependent type theory with strict substitution in (∞,ω)-categories needs a coherent choice of composites and coherence cells. This gap is shared with plain CaTT; one direction is done and reconstruction is open (`notes/semantics-gaps.md` §2, (S2′)). For V + S, whether all candidate lifts of one head are connected by higher cells is open (S11).

**Lemma 2.2.1 (agreement with the support form).** For 𝕋 = ν (plain CaTT) and 𝕋 = 𝔉 (two-tier L), SC_𝕋 holds iff one of
```
(operation)  ⟦t⟧ = ∂⁻τ_Γ  and  ⟦u⟧ = ∂⁺τ_Γ,  where τ_Γ is the total cell of F_𝕋(Γ)
(coherence)  ⟦t⟧ = ⟦u⟧  and  Var(t : A) = Var(u : A) = Var(Γ)
```
By support-determines-cells the operation clause is the support condition `supp(t:A) = Supp(∂⁻τ), supp(u:A) = Supp(∂⁺τ)` of `notes/pseudo-vs-gray.md` §3.3, and the coherence clause is `↓supp(t:A) = ↓supp(u:A)` with every variable of Γ occurring in it (`Gray/CohCaseVar.cohCaseV`).

*Proof.* Here π is the identity. The total cell τ_Γ has full support (`Gray/FullSupp.agda`). If c has full support it contains the top generator, so dim c ≥ dim τ_Γ. If dim c = dim τ_Γ then c = τ_Γ by support-determines-cells (`Strict/Recon.b-supp`), which is the operation clause. If dim c > dim τ_Γ then c has no generator in its own dimension, so it is an identity on a full-support cell; then ⟦t⟧ = ⟦u⟧ and both use every variable, which is the coherence clause. Conversely τ_Γ is a cell of the required kind. ∎

**Fullness.** On pasting contexts the rule names every cell. In two-tier L, every cell of 𝔉(Δ) between the images of two derivable terms is the image of a derivable term of exactly that type, so no further side condition on pasting contexts adds a type that is sound in 𝔉 (`notes/lax-sc-completeness.md` Theorem 1, **proved on paper**; its inputs are Lemma 4.2 there, strengthening, and Steiner's generation by atoms). For uniform L the corresponding statement against F_{V+S} is open (ledger S30).

**Status.** The single form SC_𝕋 is **stated here**. The coherence clause in Finster–Mimram's shape is a SPEC decision on the evidence of `notes/lax-sc-completeness.md` §4: it accepts every coherence the full-support form accepted (full support uses every variable), it is sound, and it is complete on pasting contexts, whereas the full-support form rejects a single coherence between two layerings of the same cell (§2.5 example) and reaches that type only through composites. It is how `notes/design-decisions.md` §1.1 describes the rule ("read off the free object F_T(Γ)"), but no note writes it out (ledger S1). Support is read through the projection π because the expanded basis of F_{V+S}(Γ) is infinite on Σ[2] ∨ Σ[2]: measured there, the rule would reject even the composite interchanger (ledger S1). The designated lift is a SPEC decision (S11). Lemma 2.2.1 is **stated here** with the proof above, whose two inputs are Agda-checked. On a single hom (n = 1), the 𝔉 instance equals Finster–Mimram's Var condition: **Agda-checked** (`Gray/SingleHom.agda` for the rule level, `Gray/SuppVars.agda` and `Strict/SuppFV.agda` for the term level; ledger E1).

**Source.** `notes/design-decisions.md` §1.1; `notes/pseudo-vs-gray.md` §3.2–3.3, §3.6 (Theorem 2); `notes/lax-sc-completeness.md` §3–4; `notes/semantics-gaps.md` §2; ledger E1, S11, S29, S30.

## 2.3 The kernel: the side condition computed in V + S(Δ)

Throughout, V + S for S ⊆ {left split, R} is V with the laws of S added everywhere; the kernel uses V + S(Δ), which imposes each law only where the marks of the coherence's own context put it (below). When every object of Δ carries the same set S, V + S(Δ) = V + S on Δ.

### The theory V

An **admissible** theory is a strict theory on the T₁₂ signature (strict associative and unital composition, an elementary interchanger χ for every pair k < l, naturality cells per varying argument with Leibniz-signed orientation, higher cells between routes) whose free objects on finite pasting diagrams satisfy:

1. an explicit combinatorial description by generators with explicit boundaries;
2. two cells of the same dimension using the same generators, in the expanded basis, are equal;
3. every elementary interchanger exists and its reverse does not;
4. making every interchanger with k ≥ 1 an identity gives the free Gray-enriched category 𝔉(Γ), and making every interchanger an identity gives the free strict ω-category ν(λΓ);
5. closure under substitution of cells for generators.

**V** is the forced base B together with the guarded round-5 equations. On every finite pasting diagram Γ, F_V(Γ) maps generator-preservingly into F_E(Γ) for every admissible E. So a directed cell or an equality exists in F_V(Γ) **iff** it exists in every admissible theory. V is the least admissible theory on pasting diagrams.

### The split marks

Two laws of T₁₂ are **visible** on pasting diagrams, meaning that imposing them changes some free object F(Γ):
- the **left split** (the inner composite-crossing law): the direct crossing of A₁ ∗ A₂ past B equals the paste of the crossings of A₁ and of A₂;
- the **right split** R: the mirror statement, splitting a composite right operand.

Both are splits of an interchanger along a k-cell with k ≥ 1, so both sides of each law are built from inner letters, identities, composition and whiskering only. (The splits along a 0-cell, for outer interchangers, are axioms of the base B, so they are in V.) At degree 4 this is **Agda-checked** (`Join/SwitchLaws.law-inner`, `Uniform/SplitMarks.Degree4.law-trivial`; that the two sides are parallel is by the typing of T, not mechanized); in higher degrees the law schema is the same at every level k ≥ 1 (`notes/closed-structure.md` §D.4.3), on paper.

A split is a property of a particular object, like `iord` and `ord` (chapter 3, §3.6): it says how crossings inside the homs into that object behave. So it is a **mark on an object variable**, written in the context:

```
(C : ⋆)^lsplit     every inner crossing in a hom 𝒦(X, C) satisfies the left split
(C : ⋆)^rsplit     every inner crossing in a hom 𝒦(X, C) satisfies the right split
```

`ord` implies both, because it makes inner letters into C trivial and both sides of each split are pure inner. A substitution may send a variable marked lsplit (rsplit) only to a variable marked lsplit (rsplit) or `ord`, as for the other object marks. An unmarked object assumes neither law.

For a pasting context Γ with objects a₀, …, aₙ, each object possibly marked, write **S(Γ)** for the marking aᵢ ↦ (the splits aᵢ carries), with `ord` counting as carrying both. **V + S(Γ)** is V together with every instance of the left split (right split) whose crossing lands in an object aⱼ marked `lsplit` (`rsplit`), closed under composition and whiskering. The crossing of an instance lands in aⱼ when its hom is 𝒦(aᵢ, aⱼ). a₀ is the target of no hom of Γ, so its marks are irrelevant, as for (COH-ord). When every object a₁, …, aₙ carries the same set S, V + S(Γ) is V + S; on a single hom (n = 1) this is always the case. The four uniform markings give pairwise distinct free objects:

| marks on every object | Theory | Cells on the suspended 2 × 3 interval |
|---|---|---|
| none | V | 49 |
| rsplit | V + R | 14 |
| lsplit | V + left split | 29 |
| lsplit, rsplit (or `ord`) | T₁₂'s pasting profile | 2 |

A mixed marking lies between: F_{V+S∧}(Γ) → F_{V+S(Γ)}(Γ) → F_{T₁₂}(Γ), where S∧ is the set of splits carried by every aᵢ (`Uniform/SplitMarksPerObject.agda`, `meet→perObject`, `perObject→all`, on raw degree-4 syntax). Equality and reachability in F_{V+S(Γ)}(Γ) are decidable by the procedure below, with the selected ground instances restricted to those landing in marked objects (`notes/design-decisions.md` §1.9).

The other laws once catalogued (the prime left splits L_p and the divisibility laws D_{d,p}) are **invisible** on pasting diagrams, because every chronological 3-endomorphism of a free object on a pasting diagram is an identity. They change no free object, so they are not marks.

**Rule.** The kernel's `coh` rule is the rule of §2.2 with 𝕋 = V + S(Δ), where Δ is the coherence's own (possibly marked) pasting context:

```
Δ ⊢ps     Δ ⊢ t →_A u     SC_{V+S(Δ)}(Δ, t →_A u)     Γ ⊢ σ : Δ
──────────────────────────────────────────────────────────────────── (coh)
              Γ ⊢ coh_{Δ, t →_A u}[σ] : (t →_A u)[σ]
```

σ must respect Δ's marks. With no marked object in Δ, the side condition computes in V, the least admissible theory. A head all of whose objects a₁, …, aₙ are `ord` is also accepted by (COH-ord), on SC_𝔉 (chapter 3, §3.6). There is no setting, no file header and no default: every assumption a coherence uses is a mark in its own context (chapter 0, §0.1).

**Why marks and not a file setting** (ledger S31, `notes/design-decisions.md` §1.8). Until 2026-11-24 the two laws were switches declared once per development. That made them the only assumption not stated in the context, and it split developments into four classes with one-way imports. A mark says the same thing about the objects it is placed on and nothing about others. For a context with at least one hom, marking every object a₁, …, aₙ with a set S gives S(Δ) = S, the old setting (`Uniform/SplitMarks.uniform-recovers`), so nothing expressible before is lost.

**Why the laws are not hypotheses either.** A declared cell κ : u ≅ v is not seen by the side condition, so its two uses in a three-fold composite are unrelated until the user declares a 6-cell, then a 7-cell, without end (`notes/design-decisions.md` §1.4(c)). A mark acts through the side condition, as `ord` does, so all of the law's higher coherences come from the oracle.

**Substitution only strengthens.** If every object of Δ′ carries at least the marks of the corresponding object of Δ, then every law instance of V + S(Δ) is one of V + S(Δ′) (`SplitMarksPerObject.mark-mono`), the identity on letters maps F_{V+S(Δ)} to F_{V+S(Δ′)} and sends cells to cells, so a coherence accepted over Δ is accepted over Δ′. The step from a map of free objects to SC is Agda-checked for any map that sends letters to letters and full supports to full supports (`Uniform/Rule.agda`, `Transport.sc-map`). On the grid layer the comparison maps are checked (`Grid.nf-compare`).

**Side condition and decision procedure.** SC_{V+S}(Δ, t →_A u) is decided as follows.
1. Compute ⟦t⟧ and ⟦u⟧ in F_{V+S}(Δ) (normal forms by rank increments; r9 (K65), r10 Response 1).
2. Decide whether ⟦t⟧ = ⟦u⟧. If so, check Var(t : A) = Var(u : A) = Var(Δ); if that holds, this is the coherence case.
3. Otherwise search for a path ⟦t⟧ → ⟦u⟧ in F_{V+S}(Δ) whose projection π(c) has full support in 𝔉(Δ), i.e. by Lemma 2.2.1 π(c) = τ_Δ or an identity on a full-support cell.
   - **No length bound is used.** Paths in F_{V+S}(Δ) are not bounded by their endpoints: some free objects have loops. Examples are the loop H of V at degree 4 on Γ_{2,2}, which has pairwise distinct powers, and a positional self-loop at degree 5 on the 2 × 2 grid in T₁₂ (ledger S14). Both are whiskered binary interchangers (the second is the suspension of H), not elementary interchangers, so neither contradicts requirement 3 or the directedness theorem (K49) (`design-decisions.md` §1.7).
   - **What is finite** is the set of vertices. At fixed lower faces and weight there are finitely many vertex normal forms (K58), and the native generating steps between them are finitely many and listable (r10 Response 3).
   - The support of a composite path is the union of its steps' supports. So search breadth-first over pairs (vertex, support accumulated so far in 𝔉(Δ)). This state space is finite, since supports are subsets of the finite Steiner basis of 𝔉(Δ). Accept when the target ⟦u⟧ is reached with full accumulated support.
   - Reachability in a finite closed universe is decidable without a length hypothesis: loop removal plus pigeonhole, with breadth-first saturation proved exact. It is Agda-checked in `Uniform/FiniteGraph.agda` (PR #380). The search over pairs is Agda-checked for any layer with finite closed universes (`Uniform/RuleFin.agda`, `DecideFin.sc?`), and `Uniform/KernelDec.agda` runs the kernel over it.
   - The **designated lift** is the first witnessing path of minimal length, in the fixed enumeration order of steps. A shortest witness exists whenever any witness exists. There are finitely many paths of each length, so the choice is well defined.

Equality and reachability in F_{V+S}(Γ) are decidable for every law set S, in every dimension, uniformly in Γ, the degree and S, and the comparison maps between law sets are computable (r10 Response 3, by breadth-first search over the finite vertex list). No bound on path length is used, since some free objects have loops (ledger S14). The abstract step is `Uniform/FiniteGraph.agda`, reachability in a finite closed universe. `Join/BoundedReach.agda` (`Reach.Bounded.reach?`) applies only to loop-free layers.

**Cost.** Decidable is not cheap. The problem is P-hard; shared reachability is coNP-complete already on a fixed grid; a uniform 2-EXPSPACE bound holds; equality is polynomial for structural terms, on two-row grids in each fixed degree, and for exponential-width schedules (r10 Responses 3–21). A polynomial algorithm on arbitrary shared terms is open (ledger E9, E12). None of this changes the rule.

**Example (a): the interchanger, with any marks.** Δ = ΣD¹ ∨ ΣD¹: α : f ⇒ f′ : x → y and β : g ⇒ g′ : y → z.
- `coh_{Δ, (f◁β);(α▷g′) → (α▷g);(f′◁β)}` is accepted whatever the marks. Its cell is the elementary interchanger χ_{α,β}, which is the lax naturality cell when β is a transformation and α an arrow of an element.
- The reverse, `coh_{Δ, (α▷g);(f′◁β) → (f◁β);(α▷g′)}`, is rejected whatever the marks: requirement 3 for every admissible theory, and in the Gray quotient no term at all has that type (below).
- There is no horizontal composite: a cell from f ; g to f′ ; g′ has hom-dimension 1, so it cannot use the generator α ⊗ β, which has hom-dimension 2, and no such cell has full support.

**Example (b): the strip, where the marks matter.** Inside a hom, take composable inner cells A₁, A₂ and a cell B in interchange position (the strip C_{2,1}). Let u = ι(A₁ ∗ A₂, B), the direct inner crossing, and v the paste of ι(A₁, B) and ι(A₂, B). (Earlier versions wrote W here. W is the outer lift, and the outer W-strip behaves differently: it stays distinct under every mark short of `ord`, ledger E13.) Let C be the object the strip's hom lands in.
- C unmarked, or marked rsplit only: ⟦u⟧ ≠ ⟦v⟧ and neither reaches the other, so neither `coh(u → v)` nor `coh(v → u)` is accepted. In the tagged model of (K44) they really differ.
- C marked lsplit (or `ord`): ⟦u⟧ = ⟦v⟧, and both use every variable, so `coh(u → v)` and `coh(v → u)` are both accepted, in the coherence case, and are invertible.
- The law cannot be added as a declared cell instead: a declared cell κ : u ≅ v is not seen by the side condition, so its two uses in a three-fold composite are unrelated until the user declares a 6-cell, then a 7-cell, without end (`notes/design-decisions.md` §1.4(c)).

**Example (c): inside an object.** In one object C, take two 2-cells of C composable along a 1-cell (the context Σ(ΣD¹ ∨ ΣD¹) placed in the hom 𝒦(X, C)). Uniform L gives a directed interchanger one dimension up, as for transformations across objects; two-tier L and P make it invertible. Directed Eckmann–Hilton is therefore a pair of directed cells b ∗ a ⇛ a ∗ b and a ∗ b ⇛ b ∗ a, not inverse to each other, and it is invertible only with the `ord` mark, or with a split mark on C and an `inv` input (chapter 3, §3.6 Example (a)). The rule-level computation is checked by evaluation (`Uniform/Marks.agda`; with split marks, `Uniform/SplitMarks.agda`, `eh-lsplit`). The run on the actual F_V waits for the uniform checker (ledger S3).

**Semantics.**
- **Admissible theories.** A coherence over Δ holds in every algebra of an admissible theory in which the objects assigned to Δ's marked objects satisfy their marks: each generating instance of V + S(Δ) lands in some aⱼ marked with its law, in a hom 𝒦(aᵢ, aⱼ), so the assignment sends it to an instance in a hom 𝒦(γaᵢ, γaⱼ), where it holds; equalities are preserved by composition and whiskering, so the algebra's map out of F_V(Δ) factors through F_{V+S(Δ)}(Δ). This is the factorization argument of (COH-ord), proved on paper (`notes/design-decisions.md` §1.8, §1.9). In particular a coherence over an unmarked context is valid in every admissible theory.
- **Gray-enriched models.** By requirement 4 every cell of F_{V+S}(Γ) projects to a cell of 𝔉(Γ). Every accepted coherence projects to an accepted two-tier coherence: in the coherence case equal images project to equal images and Var is unchanged; in the operation case, if c witnesses SC_{V+S}(Δ, t → u), then π(c) : π⟦t⟧ → π⟦u⟧ has full Gray support. Either way SC_𝔉 holds for the projected terms. So every model of two-tier L (in particular strict ω-Cat with lax transformations, and every oriented (∞,ω)-category) is a model of uniform L, interpreting each coherence through its projection. This is immediate from the form of the rule (ledger S2).
- **What uniform L adds.** It is the most general row of the ordering, which is why it is the kernel. A consequence for models: objects need not be ordinary ω-categories, since their own compositions may interchange directedly (Gepner–Heine's oriented categories are examples of such objects).

**Status.**
- V exists, is least on pasting diagrams, and decides equality and reachability: **proved** (verified researcher answers r8, r9, r10; ledger E6, E12).
- The four law sets V + S are admissible and distinct: **proved** (r9 Responses 2–5, K73) and computed (`scripts/e6/interchange_fibre_decorations.py`).
- Reachability in a finite closed universe, with no length bound: **Agda-checked** (`Uniform/FiniteGraph.agda`, PR #380). The bounded-path version (`Join/BoundedReach.agda`) applies only to loop-free layers (S14).
- The comparison maps between law sets extend functorially to the cospan completions, and the split laws keep seed lists: **Agda-checked** (`Join/SwitchCospan.agda`, `Join/SwitchLaws.agda`), with the link between raw syntax and the completion by inspection only (ledger E12 items (a)–(c), owner LCORE).
- The rule (coh) as a single condition on F_{V+S(Δ)}, with S(Δ) read from split marks: **stated here** (ledger S31); monotonicity in the marks: **Agda-checked** (`Uniform/SplitMarks.agda`, `meet-mono`, `invM-mono` for the marks rules; `Uniform/SplitMarksPerObject.agda`, `mark-mono`, `const-⊆`/`const-⊇`, `meet→perObject`, `perObject→all` for the per-object laws on raw degree-4 syntax), with substitution itself on paper; `ord` carries both splits by definition, justified by: at degree 4 both sides of each law are pure-inner (**Agda-checked**, `law-inner`, `Degree4.law-trivial`), and their equality under `ord` (parallel identities) is on paper, in the projected form recommended by the independent check (ledger S1). Uniqueness of the lift up to coherence: open (S11).
- **The checker for (coh), relative to the free objects: Agda-checked** (`Uniform/Kernel.agda`, `Uniform/Rule.agda`; `notes/uniform-checker.md`). For any family of free-object layers with a grading bound, SC is decidable, the judgments are those of `TypingWith` at that side condition, and the checker is sound and complete. The layers of F_{V+S} in every degree are not yet constructed in Agda, so this is the kernel checker relative to them (ledger S3a).
- **The law-set layer: Agda-checked** (`Uniform/Grid.agda`, `Uniform/GridExamples.agda`). For every law set, equality of 4-cells on suspended m × n grids is decided, with normal forms and computable comparison maps. The counts 2, 1, 2, 1 (1 × 2), 2, 2, 1, 1 (2 × 1) and 49, 14, 29, 2 (2 × 3) are computed, and so is example (b) as an equality statement. Directed 5-cells between these 4-cells are not modelled (ledger S3b).
- The implemented checker for actual developments is still two-tier L (§2.5).

**Source.** `notes/design-decisions.md` §1.2, §1.7, Lemma V-dec; `notes/joining-completion.md` §8; `notes/conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`, `-r9-`, `-r10-`; ledger E6, E12.

## 2.4 Which coherences are invertible

| Cell | Invertible? | Reason |
|---|---|---|
| coherence case (⟦t⟧ = ⟦u⟧) | yes | the reversed coherence satisfies the same side condition; Benjamin–Markakis's argument goes through unchanged |
| operation case on a single hom, in the Gray quotient | no, as in CaTT | |
| elementary interchanger, any marks | **no** | requirement 3; in the Gray quotient the reverse type is uninhabited (Agda-checked, below) |
| a crossing of a composite against the paste of crossings | if the hom's target object is marked with the matching split (or `ord`): yes, as a coherence case; otherwise there is no cell either way | §2.3 example (b) |
| interchanger with an invertible or pseudo factor | only through the marks of chapter 3 | chapter 3 |

**Status.** For two-tier L, non-degeneracy (no term of the reverse interchanger's type) is **Agda-checked** with no hypothesis (`Strict/ReverseInterchanger.agda`, `no-reverse-interchanger`, from strict-model soundness `Strict/Soundness.agda`; ledger E3). For V + S it is requirement 3 (**proved**, r8).

## 2.5 The two-tier fragment and the implemented checker

Two-tier L computes the side condition in the free Gray-enriched category 𝔉(Γ), whose homs are Gray tensors of Steiner complexes:

```
𝔉(Γ)(aᵢ, aⱼ)  =  ν(λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ)      (factors in execution order)
```

Generators are tuples θᵢ₊₁ ⊗ … ⊗ θⱼ with dimension the sum and boundary by the Leibniz formula. The total cell τ_Γ is the tensor of the composites ⟨Θᵢ⟩. Supports are Steiner chains, so the side condition of Lemma 2.2.1 is integer linear algebra.

This is not the kernel's default theory. Marking every object `ord` in uniform L gives exactly two-tier L, through the rule (COH-ord), which computes the side condition of an all-`ord` head in 𝔉 (chapter 3, §3.6; ledger S16(b)). Merely inverting inner letters would not suffice: relative coherence of V + S over 𝔉 fails even after every inner letter is inverted (ledger E13). It is the theory the checker currently implements, with one difference in the coherence clause, described next.

**The implemented checker.** `graySide` (`Gray/Pure.agda`) decides the operation clause as stated. Its coherence clause is stronger than §2.2's: it asks that t and u each have full Gray support, not merely use every variable. So it accepts fewer coherence heads, and it is the rule with a full machine-checked soundness proof (`Strict/Soundness`). The rule of §2.2 is `graySideV` (`Gray/CohCaseVar.agda`). The two derive **the same types**: every cell of 𝔉(Δ) between term images is named under either rule (relative-coherence r9 Response 1 for `graySide`, verified, non-constructive; `notes/lax-sc-completeness.md` §3.3). The difference is how: under §2.2's rule one explicit coherence names it (Theorem 1), under `graySide` sometimes only a composite does (example below).

**Decision procedure.** Symbolic supports and an exact cover check (`Gray/Cover.agda`, `Gray/Fast.agda`), proved equal to the explicit support computation (`fastSide ≡ graySide`). Measured growth on n-fold wedges is about n⁶ up to n = 28. Explicit supports are exponential (a term of size O(n) has support of size 3ⁿ), so the symbolic form is required.

**Example (two layerings of one cell).** Δ = ΣD¹ ∨ ΣD¹ as in §2.3 example (a). Let βα = (f◁β);(α▷g′) and βα₂ = (1_{f;g};(f◁β));(α▷g′), the same composite padded with an identity. Both have type f;g → f′;g′, the same image in 𝔉(Δ), and use every variable. So `coh_{Δ, βα → βα₂}` and its reverse are accepted in the coherence case, and they are invertible. Their image is the identity, which does not contain the generator α ⊗ β, so the full-support form rejects them: `graySide` rejects both directions, and no single coherence over Δ has this type (`Gray/CohCaseGap.agda`, `gap`, `no-single`), though a composite of two does (`CohCaseGap.e`). `graySideV` accepts both directions, still accepts the interchanger βα → αβ, and still rejects the reverse and the horizontal composite (`Gray/CohCaseVar.agda`, by evaluation).

**Example (the Gray cube).** Δ = ΣD¹ ∨ ΣD¹ ∨ ΣD¹. The total cell is the top cell of the 3-cube, a 4-cell of 𝒦 between the two hexagons of whiskered interchangers. `hex⁻ ⇛ hex⁺` is accepted as one operation-case coherence over a pasting context, and the reverse is rejected (`Gray/Cube.agda`). No coherence over a non-pasting context is needed; the Gray molecules appear only inside the side-condition computation.

**Semantics.** Every strict Gray-enriched category models two-tier L (Theorem 1 of `notes/pseudo-vs-gray.md` §3.6), and every oriented (∞,ω)-category does (Theorem 2 there, whose hypotheses (D)–(F) are discharged by Campion, arXiv 2311.00205, and Chanavat, arXiv 2603.22242). The coherent-choice gap for interpreting a dependent type theory in an (∞,ω)-category is shared with CaTT (`notes/semantics-gaps.md`).

**Status.** Rule, checker and decidability: **Agda-checked** (`Gray/Support.agda`, `Gray/Typing.agda`, `Gray/Fast.agda`). Soundness of every derivable term in the strict model: **Agda-checked** with no hypothesis (`Strict/Soundness.agda`; (B) and the total-cell fact are theorems, `Strict/Recon.agda`, `Strict/Bridge.agda`). Conservativity over CaTT on a single hom: **Agda-checked** (ledger E1). (∞,ω) soundness: **proved** from the literature. **Source:** `notes/pseudo-vs-gray.md` §3; `notes/agda-gray-findings.md`; ledger E1–E3, E9.

## 2.6 The generality ordering

**Statement.** If SC_{V+S}(Γ, A) then SC_𝔉(Γ, A); and if SC_𝔉(Γ, A) then SC_ν(Γ, A′) for the image A′ of A under the collapse. So every uniform-L derivation is a two-tier derivation, and every two-tier derivation a CaTT derivation, up to the collapse of Gray molecules to cartesian composites.

**Status.**
- Every model of P is a model of two-tier L (change of base along X ⊗ Y → X × Y): **proved** (`notes/pseudo-vs-gray.md` §2.4).
- Uniform to two-tier: immediate from the projected form of the rule (§2.3 *Semantics*; ledger S2).
- The converse directions (P = two-tier L + "every interchanger invertible", two-tier = uniform + `ord`) are the subject of chapter 3. The second holds exactly with `ord` on every object and the rule (COH-ord) (§3.6). Without (COH-ord) it would fail for coherences under every split mark: the loop H and 1_w, and the outer W-strip, have equal Gray images and stay unconnected after every inner letter is inverted (ledger E13). For the first, the relative coherence lemma for 𝔉 → ν now holds (ledger E5).

## 2.7 Dualities

CaTT has a duality D_J for every J ⊆ {1, 2, …}: reverse the cells whose dimension is in J (Benjamin–Markakis). Two-tier L keeps four of them as symmetries (`notes/closed-structure.md` §D.2, including op). The uniform core keeps one.

**Statement (Theorem D4).** For every law set S:
- D_J sends every uniform-L derivation to a uniform-L derivation iff **J = ∅**;
- D_J sends uniform L to the oplax core (every elementary interchanger reversed) iff **J = all**. The image of V + S is the oplax core with mirror(S), which exchanges the left split and R: V + {left} goes to V^∘ + {R}, and V + {R} to V^∘ + {left}. On marks, D_all exchanges lsplit and rsplit;
- every other J maps some accepted coherence to a rejected type. Its image is a mixed core D_J(V + S), which can be checked by running the V + S checker on the dualised input.

**Why.** D_J sends the elementary interchanger of two (l+1)-cells juxtaposed along a k-cell to the reverse type iff a_{k+1} + a_{l+1} + a_{l+2} is odd, where a_m = [m ∈ J]. Two necessary conditions follow:
- the Gray interchanger at every level n, over Σⁿ(ΣD¹ ∨ ΣD¹), must keep its orientation;
- J must pass the two-tier test.

Together these force J = ∅. Neither alone does: J = {1,2,4,5,7,…} passes the first and fails the second, while op passes the second and fails the first.

**Example.** op = D_odd reverses 3-cells and keeps 2-cells and 4-cells. Over Σ(ΣD¹ ∨ ΣD¹) (§2.3 example (c)), it sends the accepted interchanger of two 2-cells of an object to the reversed interchanger, which is rejected whatever the marks. In two-tier L that interchanger is an identity, which is why op is a two-tier symmetry. So in uniform L the "prove once, get the op-dual free" rule holds only in the `ord` fragment (chapter 3).

**Status.**
- Sign arithmetic, the orientation lemma (the three flips taken as the definition of the action), the classification and the split exchange: **Agda-checked** (`src/CaTTExp/GrayDualityUniform.agda`: `dual-canonical`, `kernel-theorem`, `J124-gray-rows`, `op-gray-rows`, `dual-has`, `total-mirror`, `level-uniform`; no postulates).
- That the action is the three flips, and that the two-tier witnesses live on contexts ΣD¹ ∨ ΣD^q, where F_{V+S} = 𝔉: **argued** (`notes/closed-structure.md` §D.4.1).

**Source.** `notes/closed-structure.md` §D.4; ledger D8.

## 2.8 Open surface questions

*Q2.1 (which switch setting a development starts in) was removed on 2026-11-24: there are no settings, and the crossing laws are object marks (§2.3, ledger S31). Their surface defaults fall under Q3.3.*

**Q2.2. How a horizontal composite across objects is written.** The kernel has no horizontal composite; there are two layerings, ∂⁻τ (later factor first) and ∂⁺τ (earlier factor first), related by the directed interchanger from ∂⁻ to ∂⁺.
- *Option A: no notation; the user writes the layering they mean.* Nothing hidden; every composite of transformations across objects is written twice as long.
- *Option B: one infix operator elaborating to the ∂⁻-layering.* From ∂⁻, every other layering is reachable by a derivable cell, so a user never needs the other layering's inverse. Proposed in `notes/invertibility-markings.md` §6.2.
- *Option C: one infix operator elaborating to the ∂⁺-layering.* Nothing is reachable from it without a pseudo mark; matches the reading "earlier factor first".
- *Worked example.* For an element arrow f (earlier) and a transformation α (later), A writes `α_x ; Gf` or `Ff ; α_y` explicitly; B's `f ⋆ α` means `α_x ; Gf`, and the naturality cell goes out of it; C's `f ⋆ α` means `Ff ; α_y`, and the naturality cell comes into it.

**Q2.3. How a failed side condition is reported.** The kernel's answer is a boolean.
- *Option A: report "not admissible".* Cheapest; useless to a person.
- *Option B: report the two strict images and their supports.* Useful in the Gray fragment, where supports are readable sets of tuples; in V + S the cells are decorated normal words and need their own printer.
- *Option C: report the nearest accepted type* (for example, "the reverse direction is accepted"). Most helpful for the common error of a reversed interchanger; needs a search over candidate types.
