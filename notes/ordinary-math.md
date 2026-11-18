# Toward ordinary mathematics: h-levels, induction, presentations, object-indexed colimits, lax functors

*Design notes, 2026-11-18. Owner of ledger items F1–F6 at the time of writing: thread "Extend toward ordinary mathematics". Companion to `limits-representables.md` (limits, colimits, shapes ⟦Γ⟧, hom objects, the ℕ-like object) and `pseudo-vs-gray.md` (P vs L). Fixed constraints: no universes; no definitional β/η; universal properties witnessed by generated cells; rules in the style of published CaTT variants; no algebraic structure in the meta-theory (`catt-survey.md` §13).*

*Markers, as in the other notes. **[paper]**: checked against the cited source this session (for an abstract-level check, the marker says so). **[recall]**: background knowledge, not re-checked. **[proved here]**: a proof written out in this note. **[conj]**: unproved; each has a proof attempt here and, where the design hinges on it, a problem in `notes/conjectures/`. **[proposal]**: a design choice. **[agda]**: machine-checked in `src/`.*

---

## 0. Summary

"Ordinary mathematics in principle" is read here as Anthony's criterion (`catt-survey.md` §13): for any ordinary structure we can *build an object that behaves like an instance of it*. Concretely we need, inside the ambient: sets (discrete objects), the natural numbers with induction, quotients (the integers first), indexed families and their dependent sections, colimits indexed by objects (sequences), and lax functors where the mathematics is lax. The note proposes the following, item by item.

| Item | Proposal | Status |
|---|---|---|
| **F3** h-levels | A judgment `C trunc n` ("C is an n-category"; n = 0 is "C is a set") with a filler rule, an invertibility rule, and closure rules: limits, hom objects (which lower the level by one), coproducts, and two semantic base rules (free objects on graphs, and on graphs with inverted edges, are 1-categories). §2. | Closure under limits and homs **[proved here]** (sketches at the level of the other notes). Base rules sound by `free-on-graph.md` and Dwyer–Kan **[paper]**. T-graph is not derivable from R-A, even under this note's reading with cotensors as exponentials (E) (researcher countermodels, verified: `conjectures/answered/non-derivability-2026-11-18.md` Q2 for enriched cotensors, `conjectures/answered/non-derivability-q2-2026-11-18.md` under (E)). So T-graph stays a rule (Prop. 2.5). |
| **F2** filler tactic | An admissible meta-operation: in a graph context, two parallel cells with the same path are connected by one coherence over the chain Θ_k. No new rule. §3. | **[proved here]** on paper; implemented with certified output and examples **[agda]** (`CaTTExp.GraphFiller`); total in every dimension **[agda]** (`CaTTExp.GraphFillerTotal`, `.Higher`). Extension to globular contexts **[proved here]** semantically, implemented with certified output **[agda]** (`CaTTExp.GlobularFiller`). |
| **F1** families, induction | Families are maps p : E → B, sections are maps with an invertible cell; dependent elimination is *derived* from non-dependent universal properties (Awodey–Gambino–Sojakova's argument). §4. Three routes to ℕ's recursion, compared in §4.5. The one that adds no ℕ-specific rule (route III) uses two general principles: lax colimits are Grothendieck constructions (G), and comma objects are free cocartesian fibrations (DJ, "directed J"). | Dependent elimination for shapes ⟦Γ⟧ and for ℕ from recursion **[proved here]**. Induction, and hence recursion with uniqueness, for ℕ from G + DJ **[proved here, Thm 4.4]** (a circular uniqueness step in the first version is corrected). G and DJ are sound semantically: DJ by Riehl–Verity's Yoneda lemma **[paper]**, G by AHM/Loubaton **[paper, F5a]**. |
| **F4** integers | ℤ := Hom(x, x) in the localisation of the loop ⟦L⟧ at s, a finite pushout. Discreteness: proved, by Dwyer–Kan's comparison lemma. General quotients (ℚ, quotient sets) need an n-truncation rule Trunc (two levels; the higher levels and dependent elimination are derived), and effectiveness needs a further rule EX. §5. | ℤ ≃ ℤ_disc semantically **[proved here]**, from DK 1980 Lemma 2.3 **[paper]** and `free-on-graph.md`. Trunc's derived levels and the quotient's universal property **[proved here]**. EX is not derivable **[paper, researcher-verified]**: a countermodel in posets (`conjectures/answered/non-derivability-2026-11-18.md`). |
| **F5** object-indexed colimits | Diagrams indexed by an object I are cocartesian fibrations E → I. Lax colimits are then the total space, pseudo colimits are a finite localisation of it, and left Kan extensions are a comma object followed by a localisation. **No new rule.** Sequential colimits are a pseudo coequaliser. Colimits *inside* an object C are a declared universal structure (a marking with a filler rule). §6. | The constructions are finite **[proved here]**; agreement with the semantic colimits rests on Lurie HTT 3.3.4.3 and Gepner–Haugseng–Nikolaus **[paper, G4]** and on Loubaton and Gepner–Heine **[paper, F5a]**. |
| **F6** lax functors | For loop-free finite shapes P, lax functors ⟦P⟧ ⇝ C are maps out of a finite context P^lax glued from Street's orientals: no new rule. For lax-functor *variables* between arbitrary objects, a directed coherence rule `dcoh_S` that names its support S (a set of generators of the oriental complex with the right boundary), parallel to L's interchange rule. §7. | The oriental classifier is in the literature for dimension ≤ 3 (Gagna) and as a definition in general. The support rule is exact for `c_∞N(A)` **[paper, researcher-verified]**; the first version (a cell whenever supports allow, unique) was **refuted** (two distinct 2-cells in O₃). |

**New open item found:** function sets. Ordinary mathematics needs exponentials of sets (ℕ → ℕ, Cauchy sequences). Shapes give cotensors, but `[A, B]` for an arbitrary set A is an internal hom. Recorded as **F8** and proposed in §6.5.1: a product-parametrised exponential rule (exp-λ, exp-uni) for any A and B, sound under P, with `[A, B]` a set whenever B is (Prop. 6.3, T-exp), and Mimram's CCCaTT over sets as an admissible tactic on top.

---

## 1. Conventions

- **Ambient.** CaTT over ωCat, as in `limits-representables.md` §1: ⋆ is "ω-categories", 1-cells are functors. Elements of C are 1-cells `⊤ → C`; a *generalised element* is a 1-cell `c → C`.
- **Cells into C.** A cell *into C* is an ambient cell whose iterated 1-dimensional base type is `c →_⋆ C` for some c. It has *level* k if it is a k-cell of the hom `Hom(c, C)`; so maps `c → C` have level 0, and an ambient d-cell into C has level d − 1.
- **Invertibility.** `Γ ⊨ u` means u comes with inverse data (Mikhail's `⊨`, or ICaTT's invertibility types; which one is ledger items E4/F7). Nothing here depends on the choice.
- **Orientation conventions** are those of `conventions.md`; this note fixes an orientation only where it says so (the lax recursion form in §4.3, and lax functors in §7).
- **Options P and L.** Everything below is stated under P (pseudo ambient, repaired CaTT_lim of `limits-representables.md` §4.1). Where L differs, it says so. A useful fact for this note: **for discrete targets P and L agree**. The defect of P's comma objects (only invertible 2-cells as arrows, `limits-representables.md` §10.1) is invisible when every 2-cell of the target is already invertible. In particular N = Hom_{⟦L⟧}(x, x) is the right object under P as well, because ⟦L⟧ is a 1-category (§2.4).
- **Pullbacks** are the all-marked (pseudo) limits of cospans. Fibres are pullbacks along elements.

---

## 2. h-levels (F3)

### 2.1 The judgment

For n ≥ −2, **`Γ ⊢ C trunc n`** reads "C is an n-category": every cell into C of level > n is invertible and fillable, with level n + 1 the place where existence of fillers starts. Read for small n:

| n | meaning | example |
|---|---|---|
| −2 | contractible | ⊤ |
| −1 | proposition (subterminal) | ⊥, a mono's domain over ⊤ |
| 0 | set (discrete ω-category) | ℕ, ℤ, Bool |
| 1 | 1-category | ⟦Γ⟧ for a graph Γ |

`trunc` is a judgment, not a type. It produces no terms of its own and quantifies over nothing; it enables the rules below. This keeps it inside the CaTT aesthetic in the same way as `⊨` and marked declarations.

### 2.2 Rules [proposal]

Use rules (what a truncation gives):

```
(T-fill)  Γ ⊢ C trunc n    Γ ⊢ u : B    Γ ⊢ v : B    u, v cells into C of level ≥ n + 1
          ─────────────────────────────────────────────────────────────────────────
          Γ ⊢ fill(u, v) : u →_B v        and   Γ ⊨ fill(u, v)

(T-inv)   Γ ⊢ C trunc n    Γ ⊢ u : B    u a cell into C of level n + 1
          ──────────────────────────────────────────────────
          Γ ⊨ u

(T-ctr)   Γ ⊢ C trunc (−2)    Γ ⊢ c : ⋆
          ───────────────────────────
          Γ ⊢ ctr(c) : c → C
```

For n = −1 and −2, "level ≥ n + 1" includes level 0, so T-fill gives a 2-cell between any two maps `c → C`. Parallel maps of level 0 are just any two maps with the same domain.

Introduction rules (how a truncation is established):

```
(T-var)    declarations may carry a truncation:  Γ, C : ⋆^{≤n}  ⊢ C trunc n.
           A substitution into such a variable must supply a derivation of
           Δ ⊢ C[σ] trunc n for its image (a certified marking, as in §4.1 of
           limits-representables.md).
(T-cum)    C trunc n  ⟹  C trunc (n+1)
(T-unit)   ⊤ trunc (−2);    ⊥ trunc (−1)
(T-lim)    every object vertex of the diagram γ has trunc n  ⟹  lim_{Γ^μ}[γ] trunc n
           (any marking μ, lax or pseudo)
(T-hom)    C trunc n,  a, b : ⊤ → C  ⟹  Hom_C(a, b) trunc (n − 1)          (n ≥ −1)
(T-coprod) A trunc n, B trunc n, n ≥ 0  ⟹  A ⊔ B trunc n
(T-graph)  Γ a finite graph context (only objects and 1-cells between variables)
           ⟹  ⟦Γ⟧ trunc 1
(T-loc)    the same, with a set M of edges inverted (§5.1)  ⟹  ⟦Γ⟧[M⁻¹] trunc 1
(T-trunc)  ‖X‖_n trunc n, for the n-truncation of §5.3
(T-exp)    B trunc n  ⟹  [A, B] trunc n, for any A   (derived from F8's rule, Prop. 6.3)
```

*Stability.* Every rule is stable under substitution: the premises mention only C, its diagram and its declared marks, and substitution into a declared mark requires a certificate (T-var). This is the same discipline as certified comparison cells.

**Consequences used later.** N := Hom_{⟦L⟧}(x, x) is a set: T-graph gives ⟦L⟧ trunc 1 and T-hom gives N trunc 0. Bool := ⊤ ⊔ ⊤ is a set (T-unit, T-cum, T-coprod). Products, pullbacks and equalisers of sets are sets (T-lim). ℤ is a set (T-loc, T-hom).

### 2.3 Proofs

**Proposition 2.1 (T-inv above level n + 1 is derivable) [proved here].** If C trunc n and u : a → b is a cell into C of level k ≥ n + 2, then u is invertible.
*Proof.* a and b are parallel of level k − 1 ≥ n + 1, so T-fill gives w = fill(b, a) : b → a. Then u·w and 1_b are parallel of level k, and T-fill gives an invertible cell between them; likewise w·u and 1_a. So w is a two-sided inverse up to invertible higher cells, which is the coinductive notion of invertibility used throughout (Benjamin–Markakis). ∎

So T-inv is only needed at level n + 1. The rule keeps it at that level.

**Proposition 2.2 (T-lim) [proved here, sketch].** If every object vertex of a finite diagram γ has trunc n, then so does `L = lim_{Γ^μ}[γ]`, for any marking μ.
*Proof.* Let u, v : B be parallel cells into L of level k ≥ n + 1. Under the repaired limit rules, cells into L correspond to *cone transfors* (`ctrf` shapes):
1. Post-compose u and v with the universal cone (`ucone`). This gives two parallel level-k cone transfors.
2. Build a level-(k+1) cone transfor between them variable by variable, in the order of the `ctrf` context. Each new component is a cell into a vertex `γ(x)` of level ≥ k + 1 ≥ n + 1, between two composites that are already parallel because the earlier components were chosen. So T-fill for `γ(x)` provides it, invertibly. Components over positive-dimensional diagram variables are also cells into vertices, of even higher level.
3. The `uni` rule (J1) lifts this cone transfor to a cell `u' : u → v` up to the invertible J2 cells, and composing with those gives the filler. Invertibility: every component is invertible, and the universal property reflects invertibility (an ω-functor that is essentially surjective at every level reflects equivalences, by the coinductive argument of Proposition 2.1).

For T-inv at level n + 1: a level-(n+1) cell into L has components of level ≥ n + 1 in the vertices, all invertible, so its cone transfor is invertible, and so is the cell. ∎

The proof uses the two facts that every cone component lands in a vertex and that `uni` reflects invertibility. It is independent of the marking. It does use the repaired rules: under the unchanged CaTT_lim the cone categories are wrong (§10.1 there), though the conclusion would still hold for them.

**Proposition 2.3 (T-hom) [proved here, sketch].** If C trunc n with n ≥ −1, then H = Hom_C(a, b) trunc (n − 1).
*Proof.* H is the partially lax limit of `x, y : ⋆, z : ⋆, f : x → z, g : y → z` with g marked, at `x, y ↦ ⊤`, `z ↦ C`, `f ↦ a`, `g ↦ b` (`limits-representables.md` §6.2). A level-k cell of cones into H has: trivial components at x and y; a level-k component θ_z into C; an invertible level-(k+1) component θ_g relating θ_z to the identity on b (because the g-leg is constant at b); and a level-(k+1) component θ_f into C.

Take two parallel level-k cone cells θ, θ′ with k ≥ n. We need a level-(k+1) filler Φ.
- Φ_z: θ_z and θ′_z are both connected to identities by the invertible θ_g and θ′_g. Take Φ_z := (θ′_g)⁻¹ · θ_g, suitably whiskered. It is invertible.
- Φ_g, Φ_f: level k + 2 ≥ n + 2 cells into C between parallel composites. T-fill for C gives them, invertibly.

Then `uni` lifts Φ. For T-inv at level n: such a cell has θ_z invertible (through θ_g), and θ_f of level n + 1, invertible by T-inv for C. For n = −1 the conclusion is trunc (−2), which also needs T-ctr for H: a map `c → H` is a cone, and its only non-trivial datum is a level-1 cell `a ∘ ! → b ∘ !` into C, which T-fill provides because `a ∘ !` and `b ∘ !` are level-0 cells and n + 1 = 0. ∎

The marked leg g is what lowers the level: it pins θ_z down, so the "free" data starts one level higher. For a comma object with neither leg marked, only T-lim's level n is available, which is correct (lax comma objects of sets need not be sets; they are posets of arrows, e.g. the arrow category of a 1-category).

**Proposition 2.4 (soundness of the base rules) [paper].**
- *T-graph:* by `free-on-graph.md` (solved, verified), F_ω(G) → F_1(G) is a trivial fibration, so ⟦Γ⟧ ≃ F_1(Γ) is a 1-category; functor categories into a 1-category are 1-categories, so all cells into ⟦Γ⟧ of level ≥ 2 are fillable and level-2 cells invertible.
- *T-loc:* §5.1.
- *T-coprod:* in ωCat, Hom(c, A ⊔ B) is a coproduct of products of homs over the connected components of c **[proved here, G4]**: coproducts are universal (pullback-stable) and disjoint, so a map `c → A ⊔ B` splits c as `c_A ⊔ c_B` (pull the two summands back), and such splittings are unions of connected components; hence `Hom(c, A ⊔ B) ≃ ∐_{π₀c = S ⊔ S'} Hom(c_S, A) × Hom(c_{S'}, B)`. Universality and disjointness hold for strict ω-categories (a functor from a connected ω-category lands in one summand, since connectedness is that of the underlying graph), and for complete Segal Θ-spaces, where coproducts are computed levelwise because every Θ-cell is connected, so the Segal and completeness conditions are preserved. Truncation levels n ≥ 0 are preserved by both. It fails for n = −1 (⊤ ⊔ ⊤ is not a proposition), hence the restriction.

**Proposition 2.5 (T-graph is not derivable from R-A).** *Proved, both for enriched cotensors and under the exponential law (E) this note uses [paper, researcher-verified 2026-11-18].* A countermodel (`conjectures/answered/non-derivability-2026-11-18.md`, Q2). In the comma (∞,1)-category `(H₁(–)[1] ↓ id_{D(ℤ)})`, finite limits, colimits, shape cotensors, Trunc₀ and hom-wise R-A all hold, Bool is a set and coproducts of sets are disjoint. But `⟦L⟧ = (S¹, ℤ[1], id)`, and N has a K(ℤ, 1) of maps from the test object `(∅, ℤ[−1], 0)`, so N is not a set. The countermodel fails the cartesian exponential law (E) `Hom(A × ⟦D⟧, C) ≃ Hom(A, [⟦D⟧, C])` and the product-parameterised form of R-A. This note uses (E): §6.1 needs `W × ⟦D¹⟧` to be the tensor, and §4 runs recursion with a parameter object B. *Under (E)* (`conjectures/answered/non-derivability-q2-2026-11-18.md`): the algebras of the monad M(X) = ∐_c X_c × K(H₁(X_c), 2) on spaces form a cartesian closed model in which products with free algebras are copowers, so (E) and parameterised R-A hold; it has universal disjoint coproducts and Trunc₀ = π₀U. There U⟦L⟧ ≃ S¹ × K(ℤ,2) and UN ≃ ℤ × K(ℤ,1), so N is not a set. Hence `N trunc 0` and T-graph are not derivable even with full cartesian closure, and F8 alone does not give them. *The original heuristic, kept for the record:* R-A's universal property describes maps *out of* ⟦Γ⟧. T-graph is about maps *into* ⟦Γ⟧ from an arbitrary c. In the term model of R-A plus limits, a variable `c : ⋆`, two variables `u, u' : c → ⟦L⟧` and two parallel variables `α, β : u → u'` have no term `α → β`: the coh rule needs a pasting context in which α and β are variables of the same pasting scheme, and no rule introduces cells between variables whose target is a constant. A proof needs a normal-form theorem for the extended theory, which does not exist yet. **Alternative being kept open (standard 1):** a Hedberg-style derivation, as in HoTT's proof that ℕ is a set. It needs decidable equality `N × N → Bool` (available from recursion, §4) and that `true : ⊤ → Bool` is a mono (needs T-coprod's disjointness). In HoTT the step from "the path space retracts onto a proposition" to "set" uses only path induction; here it would use DJ (§4.6) on the path object. This derivation would make T-graph's ℕ instance a theorem. (By the countermodel, with enriched cotensors only any such derivation needs a principle beyond R-A, limits and colimits, such as G + DJ.)

*Attempt at the Hedberg route under route III (2026-11-18).* With G and DJ (§4.6) the argument goes through as far as the following, and stops at one identified step.
1. `eq : N × N → Bool` by recursion with parameters (Corollary 4.4.1), and `eq(n, n) ≅ true` by induction (Theorem 4.4).
2. Let `P ↪ N × N` be the pullback of `true : ⊤ → Bool` along eq. Since Bool is a set (T-coprod), `true` is a mono, so P is a predicate. For fixed m, `P_m → N` is closed under arrows of N (an arrow n → n' maps to an invertible arrow of the set Bool), so it is a cocartesian fibration, and a mono.
3. *Encode.* DJ-sec for `P_m` and the point `(m, m)` gives a map `m ↓ N → P_m` over N.
4. *Decode.* Needs a map `P_m → m ↓ N` over N, i.e. "eq(m, n) = true implies an invertible arrow m → n". The usual proof is induction on m **for all n** at once, because the step from (succ m, succ n) to (m, n) changes n. Without exponentials (F8) there is no object "for all n", and Theorem 4.4 in the slice over a parameter object only allows parameters that stay fixed along the step.
5. Given encode and decode, DJ-uni makes `m ↓ N` a retract of `P_m` over N, so `m ↓ N → N` is a mono: every hom of N is a proposition, and every arrow is invertible (it is parallel to the invertible one from decode). That is `N trunc 0`.

So the Hedberg route reduces F3b to either F8 (Π over N) or a **parameter-varying induction** principle (step maps over `succ × θ` for an endomap θ of the parameter object). The latter is itself a recursion principle into a function object, so it is expected to need F8 as well [conj]. *Update (2026-11-18):* the cartesian closed countermodel of Prop. 2.5 shows that function objects alone do not make N a set, so the Hedberg route needs genuinely dependent Π over N (or the parameter-varying induction itself), not just exponentials.

### 2.4 Relative truncation and predicates

A map `p : E → B` is **relatively n-truncated**, `p trunc_B n`, when its fibres are: the rules are T-fill and T-inv with "cells into E" replaced by "pairs of cells into E together with an invertible cell between their images in B", and the filler lies over that cell. Absolute truncation is the case B = ⊤.
- **Predicates** on a set B are relatively (−1)-truncated maps `P → B` ("subsets").
- **Set-valued families** over B are relatively 0-truncated maps.

Closure rules are the same as in §2.2, read over B, plus: pullback along any map preserves relative truncation (the fibres do not change).

### 2.5 The payoff: coherence is automatic for sets

Take a ring object `R : ⋆^{≤0}` with `+, · : R × R → R` and the usual equations as invertible 2-cells between maps `Rᵏ → R`. In a weak ω-categorical setting each equation witness raises coherence questions (pentagon for the associator witness, compatibility of distributivity witnesses, and so on). Here every such question is a parallel pair of cells into R of level ≥ 1, so T-fill answers it, and every equation witness is invertible by T-inv at level 1. The user writes the classical axioms and nothing else. This is what "the theory of rings" means for sets, without any algebraic structure in the meta-theory: R is just a declared set, the operations are maps, and the laws are cells.

---

## 3. The discreteness filler tactic (F2)

### 3.1 Statement

A **graph context** is a pure context whose variables are objects `x : ⋆` and edges `f : x → y` between object variables. Every term t of dimension ≥ 1 in a graph context has a **path** `path(t)`: the list of edges of its strict image (the image in the free 1-category). For a 1-cell:
- `path(f) = [f]` for an edge variable;
- `path(coh_{Θ, A}[τ]) = path(τ(e₁)) ++ … ++ path(τ(e_k))` if Θ is the chain with edges e₁ … e_k (an operation), and `[]` if Θ is the point (an identity).

For a higher cell, `path(t)` is the path of its iterated 1-dimensional source. Parallel cells of dimension ≥ 2 automatically have the same path.

**Theorem 3.1 (filler) [proved here; agda for instances].** Let Γ be a graph context and `Γ ⊢ u : A`, `Γ ⊢ v : A` parallel, of dimension n ≥ 1, with `path(u) = path(v) = p` of length k. Then

```
fill(u, v)  :=  coh_{Θ_k, ũ →_{Ã} ṽ} [σ_p]
```

is a well-typed cell `u →_A v` of plain CaTT, where:
- `Θ_k` is the chain pasting context `v₀ —e₁→ v₁ → … —e_k→ v_k`;
- `σ_p : Θ_k → Γ` sends e_i to the i-th edge of p and v_i to its endpoints (`σ_p` need not be injective: a loop traversed three times is fine);
- `ũ = lift(u, 0)` is u re-read in Θ_k with every edge occurrence sent to the edge *at its position along the path*: `lift(f, o) = e_{o+1}` for an edge, `lift(x, o) = v_o` for an object, and `lift(coh_{Θ', B}[τ], o) = coh_{Θ', B}[τ′]` with `τ′(y) = lift(τ(y), o + off(y))`, where `off(y)` is the total path length of τ along Θ′'s spine up to the 0-source object of y;
- `Ã` lifts A the same way, with the 0-target of a cell of path length k placed at position k.

*Proof.* Three facts, each by induction on the term.
1. **Re-substitution:** `lift(t, o)[σ_p] ≡ t` syntactically, whenever t's path occupies positions o+1 … o+|path t| of p. For variables this is the definition of σ_p; for a coh, `coh_{Θ′,B}[τ′][σ_p] = coh_{Θ′,B}[τ′ ∘ σ_p]` and each `τ′(y)[σ_p] = τ(y)` by induction, because the offsets of the arguments are exactly the positions of their paths inside the composite's path.
2. **Typing:** if `Γ ⊢ t : B` then `Θ_k ⊢ lift(t, o) : lift(B, o)`. For a coh this needs `Θ_k ⊢ τ′ : Θ′`, i.e. each `τ′(y)` has type `B_y[τ′]`. By induction `τ′(y)` has type `lift(B_y[τ], ·)`, and lifting commutes with substitution into Θ′ because objects of Θ′ are sent to positions that add up along the spine. This is where positions, not names, matter: two occurrences of the same edge of Γ at different positions lift to different edges of Θ_k, so the lifted boundaries agree *in Θ_k*, not merely after σ_p. This is the canonical lift of the free-on-graph response (§3 there), made syntactic; the uniqueness argument there is what guarantees that lifted sources and targets coincide.
3. **Full support:** for t of dimension ≥ 1 with path of length k, `FV(lift(t,0) : lift(B,0)) = Var(Θ_k)`. Every edge e_i occurs (each position of the path comes from an edge occurrence), v₀ and v_k occur in the type, and the inner vertices occur as arguments of the coh that composes across them.

So ũ, ṽ are parallel cells of full support in the pasting context Θ_k, which is exactly the side condition of CaTT's full-coherence case, and `coh_{Θ_k, ũ → ṽ}` is a valid coherence. Its type substituted along σ_p is `u →_A v` by fact 1. ∎

**Corollaries.** In the loop L = (x, s : x → x), every equation between numerals that holds in ℕ holds as a coherence: `(s;s);s ⇒ s;(s;s)` ("3 = 2 + 1 = 1 + 2"), `1_x ; s ⇒ s`, `s ; 1_x ⇒ 1_x ; s`, and so on, and every two parallel cells above them are connected. Conversely the tactic fails exactly when the paths differ, which matches the semantics (`2 ≠ 1`).

### 3.2 Scope: generic cells, not arbitrary elements

The tactic fills cells *built from the generators of Γ*. It does not say that two arbitrary maps `n, m : ⊤ → N` with a cell between them are connected; that is T-graph and T-hom (§2). The two are complementary:
- the tactic is **admissible** (no rule; every filler is an ordinary coh), and covers all *closed* computations, e.g. "2 + 2 = 4";
- the truncation rules are **new rules** and cover *generic* statements, e.g. "addition is associative" for variables, together with induction (§4).

### 3.3 Extension to globular contexts [proved here, semantically; agda tactic]

The free-on-graph response proves more than it was asked: for **every globular set X**, the comparison `ar_X : LX → TX` from the free weak to the free strict ω-category is a trivial fibration (cartesianness of `ar` plus the contraction on `L1`). A *globular context* is one whose every variable's source and target are variables (e.g. `x, s : x → x, α : s ⇒ s`). So:

**Theorem 3.2.** In a globular context Γ, two parallel cells with the same image in the free strict ω-category on Γ are connected by a cell, namely `coh_{τ, ũ → ṽ}[λ]` where (τ, λ) is the common strict image (a pasting tree τ and a labelling λ : τ → Γ) and ũ, ṽ are the unique lifts of `LΓ ≅ L1 ×_{T1} TΓ`.

The algorithm needs strict normal forms (labelled pasting trees, i.e. tree substitution, the operad structure of T), which is more than the path computation of the graph case.

**Implementation [agda] (2026-11-18, F2b).** `src/CaTTExp/GlobularFiller.agda` implements Theorem 3.2 as a tactic with certified output:
- a strict normal form is a labelled tree `lt os cs`: the 0-cells o₀ … oₘ with their labels, and for each consecutive pair the diagram of its hom, one dimension up. A cell and its identities have the same tree;
- k-composition merges trees (concatenation at k = 0, childwise below). The image of `coh_{Θ,A}[σ]` composes Θ's own tree with each locally maximal variable y replaced by the image of σ(y). This is the multiplication of T, and it is the same whether the coh is a composite or a coherence, because in the free strict ω-category on a pasting diagram every cell is the composite of the sub-diagram it covers. The image of a variable is its globe, which is where globularity is used;
- the lift runs the same recursion on *position trees*, whose labels are variables of Θ_τ. Splitting a position tree along a composite gives each argument the cells it occupies (`split`, `assign`).

The certified checker then decides the candidate `coh_{Θ_τ, ũ →_Ã ṽ}[λ]`, so every returned filler is a CaTT derivation. Examples in `GlobularFillerExamples.agda`: the interchange 3-cell `(α ∗₀ g)·(f′ ∗₀ β) ⇛ (f ∗₀ β)·(α ∗₀ g′)`; associativity, unit and interchange for a 2-loop `α : s ⇒ s` on `s : x → x`; the graph examples (same term as `GraphFiller` by `refl`); rejection of `α·α` vs `α` and of the non-globular context `x, β : 1_x ⇒ 1_x`. Totality of this tactic in Agda is F2c.

For *non-globular* contexts the statement fails in general **[conj]**. Expected counterexample: `x, α : 1_x ⇒ 1_x`. The braiding-type 3-cell `α ∗₀ α ⇛ α ∗₀ α` coming from Eckmann–Hilton and the identity 3-cell have the same strict image, and should not be connected in the free weak ω-category (as in a free braided monoidal category, where the self-braiding of an object is not the identity).

### 3.4 Formalisation [agda]

`src/CaTTExp/GraphFiller.agda` implements path, lift, σ_p and the candidate filler on raw syntax, then runs the existing **certified checker**: `fill Γ u v A` returns a term together with a derivation of `Γ ⊢ fill ∶ u →_A v`. So every filler it returns is a theorem of plain CaTT; soundness needs no proof about the tactic. `src/CaTTExp/GraphFillerExamples.agda` checks:
- in L: the associator of `s;s;s` (and that it *is* the associator of `CaTTExp.Examples` substituted along the path s, s, s, by `refl`); the two unit laws; `1;1 ⇒ 1`; a four-letter word with units in two bracketings;
- dimension 3: a 3-cell between the associator and the associator composed with an identity 2-cell; dimension 4: a 4-cell between two different 3-cells (that one, and its composite with a filler of the associator with itself);
- a two-vertex graph `x ⇄ y`: `(f;g);f ⇒ f;(g;f)`;
- negative: the tactic rejects `s;s` vs `s`, `s` vs `1_x`, and two different loops at x (their paths differ). That no cell exists at all is the paper argument via the path invariant, not a machine-checked statement.

**Totality for 1-cells [agda] (2026-11-18).** `src/CaTTExp/GraphFillerTotal.agda` proves Theorem 3.1 for 1-cells, for all inputs:

```
total : Γ ⊢ u ∶ a → b   →   Γ ⊢ v ∶ a → b   →   path u ≡ path v   →   Γ ⊢ fill₁ Γ u v (a → b) ∶ u → v
```

`fill₁` is a structural (fuel-free) version of the tactic, and it agrees with `GraphFiller.fill` on the examples (checked by `refl` in `GraphFillerTotalExamples.agda`). Γ is arbitrary: the theorem is about the 1-cells of any pure CaTT context, so it also covers contexts with higher variables. The proof has five parts:
1. every 1-dimensional coherence is over a chain Θ_k from x₀ to x_k (`Chains.chain-side`: a pasting context of dimension ≥ 2 has two variables in its source boundary, and one of dimension ≤ 1 is a chain);
2. the lift is well typed in Θ_K at every offset (`lift-ty`);
3. the path of a 1-cell is a walk from its source to its target (`walk`);
4. substituting σ back into the lift gives the original term (`lift-sub`);
5. the lift has full support in Θ_k (`lift-fs`, `fs-cell`), which is the coh side condition.

It uses the scoping lemmas and `lookup-sub` from `CaTTExp.Subst`, and weakening; it does not need the full substitution theorem.

**Totality for higher cells [agda] (2026-11-18).** `src/CaTTExp/GraphFillerTotal/Higher.agda` proves Theorem 3.1 for parallel n-cells, n ≥ 2, in every graph context (no variable of dimension ≥ 2; `Graph Γ`, decidable by `isGraph`):

```
totalN : Graph Γ → Γ ⊢ u ∶ A → Γ ⊢ v ∶ A → Γ ⊢ fillN Γ u v A ∶ u →_A v      (A = (B, s, t) → … of dimension ≥ 2)
```

There is no path hypothesis: parallel cells of dimension ≥ 2 share their 1-dimensional source, so their paths agree. `fillN Γ u v A = coh Θ_k (liftTy A 0 k → liftN u 0 → liftN v 0) [σ]`, with k the length of the path of A's 1-dimensional source and σ the walk along it. A coherence over any pasting context Θ is lifted argument by argument; each argument is lifted at the position of its leftmost object, i.e. the length of the path from the image of Θ's first object to the image of that object (`pp`). It agrees with `GraphFiller.fill` on the dimension-3 and dimension-4 examples (`refl` in `GraphFillerTotal/HigherExamples.agda`). The proof:
1. **path invariant** (`PI`): in a graph context a 2-cell s ⇒ t has path s = path t, so parallel edges of a pasting context are sent to equal paths (`pedge`); the path of the image of a 1-cell of Θ joins the positions of its ends (`D'`, `πty`);
2. **range lemma** (`GraphFillerTotal/Range.agda`): the type of a valid coherence spans its whole pasting context: its source starts at Θ's first object and every object of Θ lies between the ends of its 1-dimensional boundary (in the prefix order of positions). So the lift starts at offset 0 and stays inside Θ_k;
3. **lifting commutes with substitution** (`Comm.comm-tm`, `comm-ty`), which makes the lifted arguments well typed (`liftN-ty`, `liftSN-ty`);
4. **substituting σ back** gives the original cell and type (`liftN-sub`, `liftSN-sub`, `liftTy-sub`);
5. **full support** of the lifted cell in Θ_k, through the lift of its 1-dimensional source (`coverN`, `fs-cellN`).

The graph hypothesis is what this construction uses: in `x, y, f, g : x → y, α : f ⇒ g` the path invariant fails for α itself (path f ≠ path g), and the variable α has no lift into a chain, so `fillN` is not defined there. Globular contexts are F2b.

Together, `total` (1-cells with equal paths, any context) and `totalN` (n ≥ 2, graph contexts) machine-check Theorem 3.1 in every dimension.

---

## 4. Families and dependent eliminators (F1)

### 4.1 Families without universes

- A **family over B** is a map `p : E → B`. The **fibre** over an element `b : ⊤ → B` is the pullback `E_b := ⊤ ×_B E`.
- A **section of p over f : A → B** is a map `h : A → E` with an invertible cell `θ : p ∘ h ≅ f`. A *dependent function* is a section over `id_B`.
- There is no fibration condition for groupoidal bases. Over a set B (or any B whose cells are invertible) every map is equivalent to a fibration, sections are taken up to the invertible θ, and transport along a cell of B is not needed separately: it is built into θ. This is the ∞-categorical reading of "families are maps", and it is what lets us avoid a universe.
- **Directed bases** need transport along non-invertible arrows, so families must be *cocartesian fibrations* there. Universe-free, that is structure, not a code: §4.6.
- **Dependent products over shapes** are limits: the object of sections of `p : E → ⟦Γ⟧` is the pullback of `[⟦Γ⟧, p] : [⟦Γ⟧, E] → [⟦Γ⟧, ⟦Γ⟧]` along the element `id` of the cotensor. Over a non-shape base (e.g. ℕ) this needs exponentials, F8 (§6.5).

### 4.2 Dependent elimination for shapes is derivable

Write η_Γ for the generic Γ-family in ⟦Γ⟧ (each variable of Γ as an element of ⟦Γ⟧), and `h_* e` for the image of a Γ-family under a map h.

**Theorem 4.1 [proved here].** Assume R-A (`limits-representables.md` §5.2): restriction along η_Γ, `Hom(⟦Γ⟧, C) → Fam_Γ(C)`, is essentially surjective at every level, where cells of Fam_Γ(C) are marked cylinder families. Let `p : E → ⟦Γ⟧`, let e be a Γ-family in E, and let `θ : p_* e ≅ η_Γ` be an invertible cylinder ("e lies over the generic family"). Then there are `h : ⟦Γ⟧ → E`, an invertible `ρ : h_* η_Γ ≅ e`, and an invertible `Θ : p ∘ h ≅ id`, whose restriction is `θ · p_*ρ` up to an invertible cell.

*Proof.* Level 0 of the universal property gives h and ρ. Now `p ∘ h` and `id` are two maps `⟦Γ⟧ → ⟦Γ⟧` whose restrictions are connected by the invertible cylinder `θ · p_*ρ : (p∘h)_* η = p_* h_* η ≅ p_* e ≅ η = id_* η`. Level 1 gives `Θ : p ∘ h → id` restricting to it up to an invertible 2-cell. Θ is invertible because restriction reflects invertibility (Proposition 2.1's argument, applied to an ω-functor essentially surjective at every level). ∎

This is "induction on a free object": to define a dependent function on ⟦Γ⟧ it suffices to give it on the generators, lying over them. It needs no fibration condition on p, because the base ⟦Γ⟧'s cells are only used through invertible cylinders (under P, cells between maps are pseudo transformations). Under L, the same argument goes through with the marked (pseudo) cylinders, since θ and ρ are invertible.

### 4.3 The natural numbers: recursion and its h-initiality

Write N := Hom_{⟦L⟧}(x, x), with `zero := 1_x` and `succ := (– ; s)`, the post-composition map N → N (functoriality of Hom in its second argument). By §2, N trunc 0.

**Recursion with parameters.** For any objects B, A and maps `a : B → A`, `f : A → A`, we want

```
rec(a, f) : B × N → A,     ε₀ : rec ∘ ⟨1, zero ∘ !⟩ ≅ a,     ε_s : rec ∘ (B × succ) ≅ f ∘ rec,
```

and uniqueness: any `h : B × N → A` with invertible `c₀ : h ∘ ⟨1, zero!⟩ ≅ a`, `c_s : h ∘ (B × succ) ≅ f ∘ h` has an invertible cell `h ≅ rec` compatible with (c₀, c_s), and any two such compatible cells are connected, and so on up all levels. The parameter object B is needed because without exponentials `B × N` is not determined by N (Lawvere's parametrised NNO). The input is the context `(B, A : ⋆, a : B → A, f : A → A)`: a linear computad, no equations, so no algebraic structure enters the meta-theory.

**Lax form (standard 4).** The most general version replaces "invertible" in the uniqueness clause by directed cells: for any *lax* (h, c₀ : h∘⟨1,zero!⟩ → a, c_s : h∘(B×succ) → f∘h) there is a cell `h → rec`, unique up to contractible choice. **[proved here, for 1-categories]**: in Cat with N = ℕ discrete, the components θ_n : h_n → rec_n are forced by `θ_0 = c₀` and `θ_{n+1} = f(θ_n) ∘ c_{s,n}`, so rec is *terminal among lax morphisms*, and the pseudo form follows (θ is invertible when c is). In ωCat the same recursion defines the components at every level. The pseudo form is what induction needs; the lax form is what an L-style kernel would state.

**Proposition 4.2 (all levels from levels 0 and 1) [proved here, sketch].** If recursion and uniqueness at level 1 (existence of compatible cells between any two algebra maps) hold for every algebra (A, a, f) and parameter B, then uniqueness holds at all levels. *Proof:* a level-k cell between algebra maps into A is an algebra map into the cotensor `[⟦D^k⟧, A]` with the pointwise structure (the pseudo cotensor exists as a marked limit), lying over the given boundary; apply level-1 uniqueness there. This is the path-object argument of Awodey–Gambino–Sojakova, with cotensors by disks in place of identity types. ∎

### 4.4 Induction from recursion

**Theorem 4.3 (induction) [proved here].** Let `p : E → N` be a family, `e₀ : ⊤ → E` with `p ∘ e₀ ≅ zero`, and `t : E → E` with `p ∘ t ≅ succ ∘ p`. Then there is a section `h : N → E`, `p ∘ h ≅ id_N`, with `h ∘ zero ≅ e₀` and `h ∘ succ ≅ t ∘ h`.

*Proof (AGS).* (E, e₀, t) is an algebra, and the cells make p an algebra map E → N. Recursion gives `r : N → E`, an algebra map. Then `p ∘ r` and `id_N` are both algebra maps N → N, so uniqueness gives an invertible `p ∘ r ≅ id`. Take h := r. (Parameters: the same with B × N.) ∎

For a **predicate** (p relatively (−1)-truncated, §2.4) this is ordinary induction: if 0 satisfies P and P is closed under successor, every n does. Since N and P are sets, every compatibility cell in the proof is automatic by T-fill.

**Worked example.** `add := rec(a = 1_N, f = succ) : N × N → N` (parameter B = N), so `add(m, 0) ≅ m` and `add(m, n+1) ≅ succ(add(m, n))`.
- `add(0, n) ≅ n`: both `add ∘ ⟨zero!, 1⟩` and `1_N` are algebra maps (N, zero, succ) → (N, zero, succ), so they are connected by uniqueness.
- `add(succ m, n) ≅ succ(add(m, n))`: induction on n, with the predicate given by the equaliser of the two sides (a mono, since N is a set).
- Commutativity: induction on n using the two lemmas.

Each step is an instance of Theorem 4.3 or of uniqueness, and every coherence between the resulting cells is T-fill on N. On *numerals* the tactic of §3 proves the same equations directly, e.g. `add(2, 1) ≅ add(1, 2)` as the associator over Θ₃.

### 4.5 Three routes to recursion

Standard 3: what each route can and cannot do, without asking which is preferred.

- **Route I (primitive NNO).** Add constants `ℕ, zero, succ`, a rule `rec` with the cells above, and `ℕ trunc 0` as a rule.
- **Route II (hom object plus a rule).** Keep N := Hom_{⟦L⟧}(x, x). zero, succ and `N trunc 0` are derived (§2). Add `rec` as a rule about this object.
- **Route III (no ℕ-specific rule).** Keep N := Hom_{⟦L⟧}(x, x). Add two general principles, G and DJ (§4.6), each a statement about all shapes and all comma objects. Induction and recursion (with uniqueness) for N are theorems (Theorem 4.4, Corollary 4.4.1).

| | I | II | III |
|---|---|---|---|
| New rules | ℕ, rec (+ levels), trunc | rec (+ levels) | G, DJ (general) |
| N's truncation | a rule | derived (T-graph, T-hom) | derived |
| Numerals computed by the §3 tactic | no (ℕ is not a presentation) | yes | yes |
| Other inductive objects | one rule per signature (§4.7) | one rule per signature | lists, words, paths in any graph come from the same two principles; with R-A⁺ and G⁺, lists over any object and every finitary signature (trees included) too (§4.8) |
| Algebra in the meta-theory | an "algebra" (a, f) appears in the rule, though only as a linear context | same | none |
| Semantic justification | ℕ_disc is the NNO of ωCat [recall] | same, plus `free-on-graph.md` | Grothendieck construction (Loubaton Thm 4.1.4.2; AHM Thm F) [paper, F5a] and fibrational Yoneda (Riehl–Verity, *Fibrations and Yoneda's lemma in an ∞-cosmos*, Thm 6.0.1) [paper, G4] |
| Cost to implement | smallest | small | largest: needs cocartesian fibrations as structure, and cotensors by ⟦D¹⟧ |

*Can route II derive rec from R-A and limits alone?* **No [paper, researcher-verified 2026-11-18].** Countermodel (`conjectures/answered/non-derivability-2026-11-18.md`, Q1): categories with an auxiliary equivalence relation on objects, functors preserving it, and all natural transformations. Limits, colimits, cotensors and R-A (even product-parameterised) hold; N is the discrete ℕ and a set, but its relation is total, so every map N → Bool is constant and recursion into Bool fails. So route II must add `rec` as a rule, and route III's G or DJ fails in that model. *The heuristic that led to the question:* A map N → A must come from somewhere. R-A gives maps out of ⟦L⟧, and functoriality gives maps between hom objects, `Hom_{⟦L⟧}(x,x) → Hom_C(c,c)`. To land in an arbitrary A we would need a C with `Hom_C(c, c) ≃ A` on which s acts by f, i.e. "the ω-category with one object whose endomorphisms are A acted on by f". That object is the lax colimit T of the diagram (A, f) over L, but T's homs are known only through maps *into* T, and colimit rules never describe maps into a colimit. So something must describe maps *out of* hom objects; route III supplies it as DJ.

### 4.6 Route III: two general principles

**Cocartesian fibrations as structure (no universe).** `p : E → B` is a cocartesian fibration when the map `r : [⟦D¹⟧, E] → p ↓ B` (an arrow of E ↦ its source and its image in B) has a left adjoint ℓ whose unit is invertible (Riehl–Verity, *Fibrations and Yoneda's lemma in an ∞-cosmos* (arXiv:1506.05500), Thm 4.1.10(iii): p is a cartesian fibration iff `k : E² → B ↓ p` has a right adjoint right inverse; dually for cocartesian fibrations and `p ↓ B` [paper, G4]). Every piece is a cotensor by a shape, a comma object, or cells (an adjunction is two maps and two cells with invertible triangle cells), so a cocartesian fibration is a *substitution into a finite context* of the extended theory. Pseudo cotensors suffice, so this works under P.

**Conventions for this section.** A *diagram over L* is an object P with an endomap t : P → P. A *map of diagrams* (P, t) ⇒ (Q, u) is a map p : P → Q with an invertible cell τ : p ∘ t ≅ u ∘ p. For a cocartesian fibration q : E → C and `c : ⊤ → C`, the *fibre* `E_c` is the pullback of q along c. A *CF-morphism* over C between cocartesian fibrations E → C and E' → C is a map over C (with its invertible cell) sending cocartesian arrows to cocartesian arrows, i.e. commuting with the left adjoints ℓ up to an invertible cell. The lax colimit of (P, t) has legs `q_P : P → T_P` and a cell `λ_P : q_P ⇒ q_P ∘ t` (the covariant convention, so that the Grothendieck construction is cocartesian).

**(G) Grothendieck principle [proposal].** Stated as structure, with no new judgment. For a finite diagram γ over Γ, the lax colimit `T := laxcolim_Γ γ` comes with:
- **G-fib.** `π : T → ⟦Γ⟧`, the map induced by the cocone `(x ↦ x, f ↦ f)` (using R-B, or R-A for the universal property of ⟦Γ⟧), carrying a specified cocartesian-fibration structure (ℓ and its invertible unit).
- **G-fibre.** For each object variable x, an equivalence `φ_x : γ(x) ≃ T_x` whose composite with the fibre inclusion `T_x → T` is the leg `q_x`, up to an invertible cell.
- **G-transport.** For each 1-cell variable `f : x → y` and `e : ⊤ → γ(x)`, the cell `λ_f(e) : q_x(e) → q_y(γ(f)(e))` is cocartesian over f. Equivalently, transport along f is `γ(f)` up to the cells φ.
- **G-nat.** For a map of diagrams α : γ ⇒ γ' (a map per object variable and an invertible naturality cell per 1-cell variable), the induced map `T(α) : T → T'` (the universal property of T applied to the cocone `q' ∘ α`) is a CF-morphism over ⟦Γ⟧ whose restriction to the fibre over x is `α_x`, up to the cells φ.

Semantics: the lax colimit of a diagram is the total space of its Grothendieck construction, naturally in the diagram (AHM Thm F; Loubaton Thm 4.1.4.2 and Ex. 4.2.3.12) [paper, F5a: checked at statement level; G is over 1-dimensional shapes, where the fully lax and AHM conventions agree]. *Convention:* this is the (∞,2)/(∞,ω) convention of AHM and Loubaton. Gepner–Haugseng–Nikolaus (arXiv:1501.02161, Thm 1.1) call the total space of the cocartesian fibration of `F : C → Cat∞` the **oplax** colimit of F, and the total space of the cartesian fibration of `F : Cᵒᵖ → Cat∞` the lax colimit [paper, G4]; the construction here is the same, only the name differs. G-fib and G-fibre are the content of those theorems; G-transport says the cocone cells are the cocartesian lifts; G-nat is the functoriality of the construction.

**(DJ) Directed J / fibrational Yoneda [proposal].** For `a : ⊤ → C`, let `π_a : a ↓ C → C` be the comma object and `ι := (a, 1_a) : ⊤ → a ↓ C`, with `π_a ∘ ι ≅ a`. Then:
- **DJ-cocart.** `π_a` is a cocartesian fibration and **every arrow of `a ↓ C` is cocartesian**. (So every map over C *into* `a ↓ C` is a CF-morphism.)
- **DJ-sec (J1).** For every cocartesian fibration `q : E → C` and `e : ⊤ → E` with `q ∘ e ≅ a`, there is a CF-morphism `h : a ↓ C → E` over C with an invertible cell `h ∘ ι ≅ e` over a.
- **DJ-uni (J2).** For two CF-morphisms `h, h' : a ↓ C → E` over C and an invertible cell `θ : h ∘ ι ≅ h' ∘ ι` over a, there is an invertible cell `h ≅ h'` over C whose restriction along ι is θ, up to an invertible cell.
- **Higher levels.** A cell `h ⇒ h'` over C is a map over C into the *fibrewise cotensor* `E^{D¹}_C := [⟦D¹⟧, E] ×_{[⟦D¹⟧, C]} C` (pulled back along the constant map), which is again a cocartesian fibration over C with the pointwise cocartesian arrows [paper, G4: Lurie HTT Prop. 3.1.2.1 (p : X → S cartesian ⇒ p^K : X^K → S^K cartesian, with the pointwise cartesian edges), dualised, and pulled back along the diagonal S → S^K]. DJ-sec and DJ-uni applied to `E^{D¹}_C`, and then to its fibrewise cotensors, give the levels 2, 3, …, coinductively, exactly as `uni`'s higher levels are generated in `limits-representables.md`.

Every clause is a finite piece of syntax over limits, comma objects, cotensors by ⟦D¹⟧ and cells, so DJ is one rule schema about *all* objects C and points a, not about ℕ. Semantics: the dependent Yoneda lemma (Riehl–Verity, *Fibrations and Yoneda's lemma in an ∞-cosmos*, Thm 6.0.1: restriction along `1 → B ↓ b` is an equivalence from cartesian functors `B ↓ b → E` over B to points of the fibre `E_b`; dually `a ↓ C` is the free cocartesian fibration on a) [paper, G4]; Riehl–Shulman's synthetic version for covariant families [recall]. DJ is the directed analogue of path induction.

**Correction (2026-11-18).** The version of Theorem 4.4 merged in PR #35 proved existence and the two equations of recursion, and then argued uniqueness by extending an algebra map g : N → A to a CF-morphism `x ↓ ⟦L⟧ → T` "by transport". That extension is a map out of `x ↓ ⟦L⟧`, and the only source of such maps is DJ itself, so the step was circular. The proof below does not need it: it proves **induction** directly from G and DJ, and recursion with its uniqueness follows from induction, as in AGS run backwards.

**Theorem 4.4 (induction from G and DJ) [proved here, relative to G and DJ].** Let `p : P → N` be any map, `e₀ : ⊤ → P` with `p ∘ e₀ ≅ zero`, and `t : P → P` with `τ : p ∘ t ≅ succ ∘ p`. Then there is `σ : N → P` with invertible cells `p ∘ σ ≅ 1_N`, `σ ∘ zero ≅ e₀` and `σ ∘ succ ≅ t ∘ σ`.

*Proof.*
1. (p, τ) is a map of diagrams (P, t) ⇒ (N, succ) over L. By G, `π_P : T_P → ⟦L⟧` and `π_N : T_N → ⟦L⟧` are cocartesian fibrations, and `T(p) : T_P → T_N` is a CF-morphism over ⟦L⟧ restricting to p on the fibres over x.
2. Let `e := q_P(e₀) : ⊤ → T_P`; then `π_P ∘ e ≅ x`. DJ-sec for `π_P` and e gives a CF-morphism `h : x ↓ ⟦L⟧ → T_P` over ⟦L⟧ with `h ∘ ι ≅ e`.
3. **A map back, ψ : T_N → x ↓ ⟦L⟧.** By the universal property of the lax colimit T_N, a map out of it is a lax cocone on (N, succ): a map `c : N → x ↓ ⟦L⟧` and a cell `c ⇒ c ∘ succ`. Take for c the fibre inclusion `N = Hom_{⟦L⟧}(x, x) = (x ↓ ⟦L⟧)_x → x ↓ ⟦L⟧` (the hom object *is* this pullback). Take for the cell the map `N → [⟦D¹⟧, x ↓ ⟦L⟧]` given by the comma's universal property from the composition cells `n ; s ⇒ (n;s)` (a coh), i.e. the arrow `(x, n) → (x, n;s)` lying over s. Then `π_x ∘ ψ ≅ π_N`, by the uniqueness clause of the lax colimit applied to the cocone `(const x, s)` that defines π_N. By DJ-cocart ψ is a CF-morphism.
4. Let `k := ψ ∘ T(p) ∘ h : x ↓ ⟦L⟧ → x ↓ ⟦L⟧`, a CF-morphism over ⟦L⟧. On ι: `k(ι) ≅ ψ(T(p)(q_P e₀)) ≅ ψ(q_N(p e₀)) ≅ ψ(q_N(zero)) ≅ c(zero) = (x, 1_x) = ι` (using G-nat for the second step, and `q_N(zero)` being `zero` in the fibre for the fourth). So DJ-uni, with id as the second CF-morphism, gives an invertible cell `k ≅ 1` over ⟦L⟧.
5. Restrict to fibres over x (pulling back along `x : ⊤ → ⟦L⟧` is functorial, by the universal property of the pullbacks). Let `σ := h_x : N → P`, read through `φ_x : P ≃ (T_P)_x`. G-nat gives `T(p)_x ≅ p`, and `ψ_x ≅ 1_N` since c is the fibre inclusion. Step 4 restricted is `p ∘ σ ≅ k_x ≅ 1_N`.
6. `σ(zero) ≅ h(ι) ≅ e = q_P(e₀)`, which is e₀ under φ_x. For n : N, the arrow `(x, n) → (x, n;s)` of `x ↓ ⟦L⟧` lies over s, and h sends it to a cocartesian arrow over s out of `h(n)`. By G-transport, the cocartesian arrow over s out of `q_P(σ n)` ends at `q_P(t(σ n))`, and cocartesian lifts are unique up to an invertible cell (the unit of ℓ is invertible). Its target is `h(n;s) = σ(succ n)`, so `σ ∘ succ ≅ t ∘ σ`. Each step is a cell natural in n because it is built from maps out of N, not pointwise.
∎

**Corollary 4.4.1 (recursion with uniqueness, route III).** For `a : ⊤ → A` and `f : A → A`:
- *Existence.* Apply Theorem 4.4 to `pr₁ : N × A → N`, `e₀ := (zero, a)`, `t := succ × f`. Then `rec := pr₂ ∘ σ` satisfies `rec ∘ zero ≅ a` and `rec ∘ succ ≅ f ∘ rec`.
- *Uniqueness, level 1.* Let g, g' : N → A be algebra maps (with cells `γ₀ : g ∘ zero ≅ a`, `γ_s : g ∘ succ ≅ f ∘ g`, and γ'₀, γ'_s). Let `I(A) := [⟦J⟧, A]` (the cotensor by the walking equivalence, a finite limit; F7), with its endpoint map `I(A) → A × A`, and let `P := N ×_{A×A} I(A)` be the pullback along `⟨g, g'⟩`, with `p := pr₁`. A point of P over n is an invertible cell `g n ≅ g' n`. Take `e₀ := γ'₀⁻¹ ∘ γ₀`, and t the map sending `α : g n ≅ g' n` to `γ'_s⁻¹ ∘ f(α) ∘ γ_s : g(n+1) ≅ g'(n+1)` (built from `[⟦J⟧, f]` and composition with the γ cells, all of which are maps out of P). Theorem 4.4 gives `σ : N → P` over N, i.e. an invertible cell `g ≅ g'`, compatible with γ₀, γ'₀ and with γ_s, γ'_s (by the two cell equations of the theorem).
- *Higher levels.* Two such cells are compared by the same argument with `[⟦J⟧, A]` replaced by the object of invertible 2-cells between two parallel maps (a further cotensor), and so on, coinductively.
- *Parameters.* Run everything in the slice over B (`B × –` preserves the limits, commas and lax colimits used [lax colimits are stable under product with an object because `B × –` is a left adjoint: this is the exponential law (E) the note assumes, not a cited fact (G4)]).

So route III gives exactly the content of the recursion rule of routes I and II, uniqueness included, with Theorem 4.3 and N trunc 0 following as before. It also gives induction and recursion out of `Hom_{⟦Γ⟧}(a, b)` for every finite graph Γ (lists, words, paths): replace L by Γ and run the same proof with a family over each object variable.

**What the proof uses.** From G: G-fib, G-fibre, G-transport, G-nat. From DJ: DJ-cocart, DJ-sec, DJ-uni (level 1 only for Theorem 4.4; the higher levels for the higher levels of Corollary 4.4.1). An initiality clause "ι is initial in `(a ↓ C)_a`" is not needed.

### 4.7 Other inductive objects

- **Routes I/II, generalised.** Finitary polynomial signatures `P(X) = Σ_i B_i × X^{n_i}` (a list of arities n_i and parameter objects B_i): an initial-algebra rule per signature, with the same cells, Proposition 4.2 and Theorem 4.3 (the AGS argument is uniform in the signature). Covers Bool (two nullary constructors), Fin k, lists over B, binary trees.
- **Route III** directly covers what is a hom object of a free object on a graph: ℕ, lists and words over a finite alphabet (one loop per letter), paths in finite graphs. Binary trees are not paths. The first idea was to get them as homs of free *operad-like* objects (a 2-computad with `m : a;a ⇒ a`), which needs a tensor or deloopings to state recursion. §4.8 takes a different route: **lists over an arbitrary object** (F1b, part a), and then **every finitary polynomial inductive object, trees included, as a subobject of lists** (F1b, part b).

### 4.8 Lists over an arbitrary object, and trees from lists (F1b)

**(a) Lists over B.** For any object B, let L_B be the free object on the one-vertex graph whose loops are labelled by B: one object x, and maps `L_B → Z` are pairs `(z : ⊤ → Z, B → Hom_Z(z, z))`. Two ways to have it:
- **(R-A⁺) [proposal]**, R-A for *object-labelled* finite graphs. Vertices v, edges `e : v → w` with a parameter object `B_e`, and maps out of the free object `⟦G⟧` are points `z_v` with maps `B_e → Hom_Z(z_v, z_w)`. The case where every B_e = ⊤ is R-A for graphs. This is a declared universal object, like the shapes of R-A.
- **As a finite colimit, given the Gray tensor.** `L_B = ⊤ ⊔_{⊤ ⊔ ⊤} ΣB`, where the suspension `ΣB` is `B ⊗ ⟦D¹⟧` with `B ⊗ {0}` and `B ⊗ {1}` collapsed (Loubaton Prop. 2.3.3.6, as used in `conjectures/gray-vs-cartesian.md`). The *cartesian* `B × ⟦D¹⟧` does not work: collapsing its ends gives the wrong hom already for `B = ⟦D¹⟧`, because the square commutes.

Put `List(B) := Hom_{L_B}(x, x)`. For B = ⊤, L_B = ⟦L⟧ and List(⊤) = N. For a finite set B it is the one-vertex graph with B loops.

**Proposition 4.5 [proved here, from the literature].** `List(B) ≃ ∐_{n ≥ 0} B^n`, with concatenation as composition.

*Proof.* Present (∞,ω)-categories as categories enriched in V := Cat_(∞,ω) (cartesian, so ⊗ = × preserves colimits in each variable). In Gepner–Haugseng's enriched ∞-categories (arXiv:1312.3178), the free V-category on a V-graph is a left adjoint, so it preserves pushouts. L_B is the free V-category on the one-object V-graph with loop object B: this is R-A⁺'s universal property, and also the pushout description, since ΣB is free on the graph with objects {0, 1} and one hom object B from 0 to 1 (their Def. 4.3.3; their worked example: the free V-category on a linear graph 0 → 1 → … has homs `V_i ⊗ … ⊗ V_j`) **[paper]**, and pushing the objects out to a point is a pushout of graphs. The free V-category on the one-object graph is i.e. the free associative algebra on B in V. That is `∐_n B^{⊗n}` (Lurie, HA Prop. 4.1.1.18) **[recall]**. Completion is a left adjoint and a Dwyer–Kan equivalence, so the pushout of complete objects has the same homs. ∎

**Recursion for List(B) in route III** needs G for diagrams indexed by L_B. A diagram over L_B is an object C with an *action* `a : B × C → C`: a functor out of L_B is a functor out of the free category on the loop graph, i.e. an object together with `B → End(C)` (by (E), `B × C → C`). So the proposal extends G:

- **(G⁺) [proposal].** G is stated for finite diagrams over shapes ⟦Γ⟧. G⁺ states it over *object-labelled graphs*: vertices v with objects C_v, and edges e : v → w with a parameter object B_e and a map `γ_e : B_e × C_v → C_w`. Its free object is R-A⁺'s ⟦G⟧ (L_B is the one-vertex, one-edge case; ⟦Γ⟧ for a finite graph Γ is the case where every B_e = ⊤). The lax colimit T, its projection to the free category, the fibres and G-nat are as in G. G-transport becomes: for `(b, c) : ⊤ → B_e × C_v`, the cell `q_v(c) → q_w(γ_e(b, c))` is cocartesian over the arrow b of ΣB_e. Semantics: the same straightening theorems, since a functor out of the free category is exactly this data. *Caveat (F5a):* when some B_e has non-invertible cells, the free object has non-invertible 2-cells, and "lax colimit" must be read as *fully* lax, i.e. the Grothendieck construction itself (Loubaton Ex. 4.2.3.12, Gepner–Heine Thm 1.8.5 with E = ∅). AHM's lax colimit would invert the cartesian 2-morphisms (§6.1). Step 3 of Theorem 4.4 then needs a fully lax cocone into `x ↓ L_B`, with cells over B's 1-cells as well. The composition cells provide one, but this is the first place to check in a full proof.

With R-A⁺, G⁺ and DJ, **Theorem 4.4 and Corollary 4.4.1 hold for List(B)** with the same proof **[proved here, relative to R-A⁺, G⁺ and DJ]**. Replace (N, succ) by (List(B), cons), where `cons : B × List(B) → List(B)` is composition with the arrow b, i.e. `n ↦ n ; b`, read as snoc in diagrammatic order. Replace the step-3 cells `n ; s ⇒ (n;s)` by the family `n ; b ⇒ (n;b)`, which is a map `B × List(B) → [⟦D¹⟧, x ↓ L_B]` given by the comma's universal property. Every step that used "the arrow s" now uses "the arrow b, uniformly in `b : ⊤ → B`", and is a map out of `B × List(B)`. So the recursion principle is: for `(A, nil_A, cons_A : B × A → A)`, there is a unique algebra map List(B) → A, with all higher levels.

**(b) Finitary inductive objects from lists.** Fix a finitary polynomial signature: constructors i ∈ {1 … k}, each with a parameter object B_i and an arity n_i ∈ ℕ. Let `A := ∐_i B_i` (a finite coproduct) and, for any object C, let

```
S_C := List(C) ⊔ ⊤      (a stack, or failure)
```

`fold_C : List(A) → S_C` is the list recursion with `nil ↦ inl []` and, for a letter `(i, b)`, the step "pop n_i elements c₁ … c_{n_i} (c_{n_i} on top), push `c_i(b, c₁, …, c_{n_i})`, or fail if fewer than n_i are on the stack". Here C carries an algebra structure `c_i : B_i × C^{n_i} → C`. The step is a map `A × S_C → S_C`: coproduct elimination on A, and n_i rounds of the uncons `List(C) → ⊤ ⊔ C × List(C)` (itself a list recursion).

- **The object of trees.** Take C := ⊤ with its unique algebra structure. Then `S_⊤ = List(⊤) ⊔ ⊤ = N ⊔ ⊤` is a set, and `W := List(A) ×_{S_⊤} ⊤`, the pullback of `fold_⊤` along the point `inl [∗]`, is a **subobject** of List(A): it is the pullback of a point of a set, so the inclusion is (−1)-truncated. W is the object of well-formed words, i.e. trees in reverse Polish notation.
- **Constructors.** Words are in *reverse* Polish notation, since cons is snoc (`n ↦ n ; b`) and the recursion reads a word left to right: `con_i(b, w₁, …, w_{n_i}) := w₁ ++ … ++ w_{n_i} ++ [(i, b)]`. This lands in W because `fold(u ++ w) ≅ run_w(fold(u))`, where `run_w` runs the steps of w from a given stack (a list induction).
- **Recursion.** For an algebra C, the forgetful map `S_C → S_⊤` commutes with the folds (uniqueness of list-algebra maps), so on W the fold lands in the fibre over `inl [∗]`, which is C. This gives `rec_C : W → C` as the induced map into a pullback. It is an algebra map by the concatenation lemma.
- **Induction, hence uniqueness, at all levels.** Let `p : P → W` carry an algebra structure lying over that of W. Then `σ := rec_P` is a section: `p_* ∘ fold_P ≅ fold_W` (both are list-algebra maps `List(A) → S_W`, so uniqueness for List(A) connects them), and `fold_W(w) ≅ inl [w]` for w ∈ W. The second holds because a list induction on w shows that `fold_W(w) = inl [t₁, …, t_k]` implies `t₁ ++ … ++ t_k ≅ w`, and the inclusion W → List(A) is a mono. So `p ∘ σ ≅ 1_W`, with the constructor cells. Uniqueness and its higher levels then follow as in Corollary 4.4.1, using the path objects `[⟦J⟧, C]`.

**Theorem 4.6 [proved here, sketch; relative to R-A⁺, G⁺ and DJ].** Every finitary polynomial signature (Bool, Fin k, binary trees, trees with B-labelled nodes, …) has an initial algebra in route III, namely the subobject W of `List(∐_i B_i)` of well-formed reverse-Polish words, with induction and recursion with uniqueness at all levels. No signature-specific rule is added. R-A⁺ and G⁺ are needed only for lists over the *carriers* `C`, which are arbitrary.

This closes the gap recorded in §4.5's table ("trees do not"): with R-A⁺ and G⁺ in place of R-A and G, route III covers every finitary inductive object. What route III still does not give is **infinitary** signatures (W-types with infinite arities, e.g. countably branching trees): the encoding by words needs finite arities. Those would need exponentials (F8).

---

## 5. Presentations with equations: the integers (F4)

### 5.1 ℤ as a localised loop

Let ⟦J⟧ be the walking (coherent) equivalence (ICaTT's walking equivalence as a context; F7). Define

```
⟦L⟧[s⁻¹] := pushout of  ⟦L⟧ ←s− ⟦D¹⟧ −→ ⟦J⟧          (a finite colimit)
ℤ := Hom_{⟦L⟧[s⁻¹]}(x, x)
```

zero is `1_x`, successor is `– ; s`, predecessor is `– ; s⁻¹`, and **cancellation** `s ; s⁻¹ ≅ 1` is the unit of the equivalence, a cell, not an equation.

**Theorem 5.1 (ℤ is the integers) [proved here, from the literature].** ⟦L⟧[s⁻¹] ≃ Bℤ, so ℤ ≃ ℤ_disc. More generally, for a finite graph G and a set M of edges, the localisation of F_ω(G) at M is a 1-category, equivalent to the 1-categorical localisation F_1(G)[M⁻¹].

*Proof.*
1. F_ω(G) ≃ F_1(G), a 1-category (`free-on-graph.md`).
2. The pushout is taken in (∞,ω)-categories, but every object in it (F_1(G), ⟦D¹⟧, ⟦J⟧) is an (∞,1)-category, and the inclusion of (∞,1)-categories into (∞,ω)-categories has a right adjoint (keep the cells whose higher structure is invertible), so it preserves colimits. The pushout is therefore the (∞,1)-categorical one, i.e. the Dwyer–Kan localisation of F_1(G) at M.
3. **Dwyer–Kan, *Calculating simplicial localizations* (JPAA 18, 1980), Lemma 2.3 ("Comparison lemma") [paper]:** "Let C ∈ O-Cat be such that C = D ∗ W, where D and W are free. Then the obvious functor L^H C → C[W⁻¹] is a weak equivalence." Here C = F_1(G) is the free product of F_1(G∖M) and W = F_1(M), both free. So the localisation is homotopically discrete: it is the 1-category F_1(G)[M⁻¹].
4. For one loop with M = {s}: F_1(L)[s⁻¹] is the one-object groupoid on ℤ. ∎

*Step 3, re-checked (G4, 2026-11-18).* Read from the page image of the published article (p. 20), not its OCR layer. The result is **Lemma 2.3**, the Comparison lemma, quoted above (earlier drafts called it Prop. 2.3). The reduction from the standard simplicial localisation L to L^H is **Prop. 2.2**: `L^H C ← diag L^H F_* C → F_* C[F_* W⁻¹] = LC` are weak equivalences. Both say what step 3 uses. Here O is the vertex set of G, D = F_1(G∖M) and W = F_1(M) are free on all of O, and C = D ∗ W.

This justifies **T-loc** and gives ℤ trunc 0 by T-hom. It also gives a filler tactic for localised graphs in principle (paths become reduced words in G ∪ M̄), but the proof of §3 does not transfer as it stands: the weak-to-strict comparison for a localised graph is not a globular-set instance of the trivial-fibration theorem. Recorded as F4a.

**Filler on 1-cells [agda] (2026-11-18, F4a).** `src/CaTTExp/LocalisedFiller.agda` works in plain CaTT. The context holds a graph together with the 2-dimensional part of a walking equivalence on each m ∈ M: `m̄`, `ρ : m;m̄ ⇒ 1`, `ρ̄ : 1 ⇒ m;m̄`, `λ : m̄;m ⇒ 1` and `λ̄ : 1 ⇒ m̄;m`. Under the marking of `invertibility-markings.md` §1.2, these are the destructors of `m inv` and their inverses. Two parallel 1-cells with the same **reduced word** are connected by an explicit 2-cell:

```
u ⇒ canon(path u) ⇒ … ⇒ canon(r) ⇒ … ⇒ canon(path v) ⇒ v
```

- The two outer steps are graph fillers (§3).
- Each forward step cancels one adjacent pair m m̄ or m̄ m, as graph filler ; (whiskered ρ or λ) ; graph filler.
- Each backward step inserts a pair with ρ̄ or λ̄.

The certified checker decides the result. Examples in `LocalisedFillerExamples.agda` for ℤ: `s;s̄ ⇒ 1`, `s;(s̄;s) ⇒ s`, `(s;s);(s̄;s̄) ⇒ 1`, `s̄;s ⇒ s;s̄` (one cancellation each way), and `s̄;(s;s) ⇒ s;1`. There is also a two-object example with an uninverted edge, and the tactic rejects pairs whose reduced words differ.

**Cells between parallel 2-cells and higher (F4a, 2026-11-18).** Two readings, with opposite answers.
- *In the finite context of the tactic, they do not exist in general* **[proved here, relative to the recall that strict ω-categories model CaTT]**. Take the localised loop Z = (x, s, s̄, ρ, ρ̄, λ, λ̄). Interpret it in B²ℕ, the strict ω-category with one object, one 1-cell, 2-cells the commutative monoid (ℕ, +) and only identities above: s, s̄ ↦ the 1-cell, ρ, λ ↦ 1 and ρ̄, λ̄ ↦ 0. Every boundary condition holds, because all 1-cells are equal. A CaTT 3-cell `ρ̄ · ρ ⇛ 1_{1_x}` would be interpreted as an identity 3-cell, forcing 0 + 1 = 0 in ℕ. So no such term exists, although both sides are parallel 2-cells with the same reduced word (empty). One level of inverse data is not enough; the missing cells are exactly the higher data of the walking equivalence (the triangle identities and up). With ICaTT/⊨ markings (E4/F7) that data is coinductive, and this obstruction disappears.
- *In the localisation as an object, they are T-fill* **[agda]**. T-loc says `L = ⟦Γ⟧[M⁻¹] trunc 1`. Cells of level ≥ 2 into L are exactly the cells between parallel 2-cells of the localisation and above, so T-fill gives all of them. This is now checked in `CaTTExp.Trunc.Examples` §5 (`loc-3cell`, with the negative at level 1). Level 1 (cells between parallel 1-cells) is below a 1-category's filler level, and there the reduced-word tactic above is the content.

So F4a is complete in the form the ambient needs: the tactic for level 1, and T-loc with T-fill above. A syntactic tactic for level ≥ 2 inside a context would first need ⊨-style coinductive inverse data in the core syntax. That is the MARK thread's area, not this item's.

### 5.2 Operations on ℤ

Addition is composition in Hom(x, x), negation is inversion of loops (every loop of ⟦L⟧[s⁻¹] is invertible, being a composite of s and s⁻¹), and multiplication comes from recursion on N followed by the sign split. Ring axioms are cells between maps ℤᵏ → ℤ, and all their coherence is T-fill (§2.5). So ℤ "behaves like the integers", with cancellation given by the equivalence data, not by a definitional rule.

### 5.3 Quotients beyond localisation: the truncation rule

ℚ, ℤ/n and quotient sets in general are not localisations of free objects on graphs. Coequalisers alone do not give sets: in an (∞,1)- or (∞,ω)-setting the coequaliser of two maps ⊤ ⇉ ⊤ is the circle Bℤ, not a point. What is needed is **n-truncation**, a reflection onto n-truncated objects, stated with the same J1/J2 pattern as Mikhail's `uni` and with the certified judgment `C trunc n` as its side condition.

**The rule Trunc_n (n ≥ −1) [proposal].** For every object X:

```
(Tr-form)  ‖X‖_n  an object,  and  ‖X‖_n trunc n          (a new clause T-trunc of §2.1)
(Tr-unit)  |–| : X → ‖X‖_n
(Tr-J1)    C trunc n,  g : X → C
           ⊢  ext_g : ‖X‖_n → C,   ε_g : ext_g ∘ |–| ≅ g
(Tr-J2)    C trunc n,  k, k' : ‖X‖_n → C,  θ : k ∘ |–| ≅ k' ∘ |–|
           ⊢  θ̄ : k ≅ k',   and an invertible cell  θ̄ ∘ |–| ≅ θ
```

Only these two levels are rules. All higher levels are derived (Proposition 5.3).

**Lemma 5.2 (total spaces) [proved here].** If `p : E → B` is relatively n-truncated and B trunc n, then E trunc n.
*Proof.* Take parallel cells u, v into E of a level where T-fill or T-inv is required. Their images p u, p v are parallel cells into B of the same level, so B trunc n gives a filler or an inverse ω. The relative rule for p, applied to (u, v, ω), gives a filler or an inverse over ω. Both rules are coinductive in the same way as Proposition 2.1, and the argument is uniform in the level. ∎

**Proposition 5.3 (dependent elimination and the higher levels) [proved here].**
1. *(Dependent elimination.)* Let `p : E → ‖X‖_n` be relatively n-truncated and `s : X → E` with `p ∘ s ≅ |–|`. Then there is `σ : ‖X‖_n → E` with `p ∘ σ ≅ 1` and `σ ∘ |–| ≅ s`.
2. *(Higher levels.)* For C trunc n, any two parallel j-cells between maps `‖X‖_n → C` whose restrictions along |–| are connected by an invertible (j+1)-cell are themselves connected by an invertible (j+1)-cell restricting to it. So restriction along |–| is essentially surjective at every level, which is the full universal property.

*Proof.* (1) E trunc n by Lemma 5.2. Tr-J1 gives `ext_s : ‖X‖_n → E` with `ext_s ∘ |–| ≅ s`. Both `p ∘ ext_s` and `1` restrict along |–| to maps isomorphic to |–|, so Tr-J2 (with C := ‖X‖_n, which is trunc n by Tr-form) gives `p ∘ ext_s ≅ 1`. Take σ := ext_s (the AGS argument of §4.1).
(2) A j-cell between maps `‖X‖_n → C` with a fixed boundary `b : ‖X‖_n → [∂⟦Dʲ⟧, C]` is a section of the pullback `E_b := ‖X‖_n ×_{[∂⟦Dʲ⟧, C]} [⟦Dʲ⟧, C]`, a family over ‖X‖_n. Its fibres are j-fold hom objects of C, which are trunc (n − j) by T-hom and so trunc n by T-cum; hence `E_b → ‖X‖_n` is relatively n-truncated. Two parallel j-cells are two sections of E_b, and the cell between them is a section of the relatively n-truncated family of cells between them (the same construction one level up). Part (1) gives it, with the restriction condition. ∎

**Quotients.** For a set X and an equivalence relation `R ⇉ X` (R a set, `⟨r₀, r₁⟩ : R → X × X` a mono, with reflexivity, symmetry and transitivity maps), put

```
X/R := ‖ coeq(r₀, r₁) ‖₀        [ · ] : X → X/R
```

where coeq is the pseudo coequaliser (the colimit with an invertible cell `c ∘ r₀ ≅ c ∘ r₁`).

**Proposition 5.4 (universal property of the quotient) [proved here].** For C trunc 0, maps `X/R → C` correspond, up to invertible cells at every level, to pairs (g : X → C, an invertible cell `g ∘ r₀ ≅ g ∘ r₁`); no compatibility of that cell with reflexivity or transitivity is required, since C is a set and T-fill supplies it.
*Proof.* Compose the universal properties of coeq (maps out of it are such pairs) and of Trunc₀ (Tr-J1, Tr-J2 and Proposition 5.3(2)). ∎

So ℤ/n is the quotient of ℤ by "differ by a multiple of n" (the relation is an equaliser, so a set), and **ℚ is the quotient of ℤ × N by `(a, m) ~ (b, k) ⟺ a·(k+1) = b·(m+1)`**, reading (a, m) as a/(m+1). This avoids a "non-zero integers" object. The relation is an equaliser of two maps `(ℤ × N)² → ℤ` into a set, so a mono, and its reflexivity, symmetry and transitivity are proved by the induction of §4 (transitivity uses cancellation of the non-zero factor m+1, itself an induction).

**Effectiveness [conj].** The quotient is *effective* when the canonical map `R → X ×_{X/R} X` is an equivalence: two elements become equal in X/R only if they are related. Without it, ℚ could identify more fractions than intended, and the construction would not provably be ℚ.
- Semantically it holds: sets in ωCat are ordinary sets, `‖–‖₀ ∘ coeq` computes the ordinary quotient (π₀ of the groupoid generated by R, which for an equivalence relation is X/R), and the category of sets is exact.
- In HoTT it is proved with univalence (encode–decode against a family of propositions `x ∼ –` on X/R). Here the analogous family would be a map `X/R → Prop`, which needs a classifier for propositions, i.e. a universe. Standard 5 forbids that.
- **Rule (EX) [proposal].** For a set X and an equivalence relation R on it, the map `R → X ×_{X/R} X` is an equivalence. It is a statement *about maps into* a pullback, so no colimit rule implies it, which is why a separate rule is expected to be needed. **EX is not derivable** from finite limits, colimits, R-A, Trunc and the T-rules, even with cartesian exponentials by shapes [paper, researcher-verified]: in posets with discrete homs, the relation on X = {0 < 1} whose only strict comparison is (0,0) < (1,1) has quotient 1, and `R → X × X` is a bijection whose inverse is not monotone (`conjectures/answered/non-derivability-2026-11-18.md`, Q3). So EX is a genuine rule.
- **What Trunc + EX give.** Sets with finite limits, quotients and effectiveness form an exact category (a pretopos once T-coprod's disjointness is added). Together with N from §4, this is the arithmetic part of ordinary mathematics: ℤ, ℚ, ℤ/n, and finite combinatorics. The reals and function sets still need exponentials (F8).

| | localisation only (§5.1) | with Trunc | with Trunc + EX |
|---|---|---|---|
| ℤ | yes | yes, also as a quotient of ℕ × ℕ | yes |
| ℤ/n, ℚ, quotient sets | no | yes, with the right universal property | yes, and provably effective |
| new rules | none (pushout) | Trunc_n (two levels; higher ones derived) | Trunc_n, EX |

**Vector-space-like objects.** A field object K is a set with ring structure and an inverse on the non-zero part (a pullback). A K-module is a set M with maps `K × M → M`, `M × M → M`, and laws as cells; coherence is again automatic. Free modules on a finite set are products Kⁿ. Free modules on an arbitrary set, quotients of modules, and dual spaces need Trunc (quotients) and F8 (function sets).

---

## 6. Object-indexed colimits (F5)

### 6.1 Ambient-valued diagrams are fibrations

A diagram indexed by an *object* I and valued in the ambient is a functor I → ωCat, which a universe-free theory cannot name. Its Grothendieck construction can be named: **an I-indexed diagram is a cocartesian fibration `p : E → I`** (§4.6 for the structure). Then:

- **A cocone** under the diagram with vertex Z is, by definition, a map `E → Z` sending p-cocartesian arrows to invertible ones. This is the straightening of "a transformation from the diagram to the constant diagram at Z", with no universe [paper, G4: Lurie HTT Cor. 3.3.4.3, for `p : Kᵒᵖ → Cat∞` classifying a cartesian fibration X → K, gives `colim p ≃ X^♮`, the marked simplicial set with the cartesian edges marked; so maps from the colimit to Z are maps X → Z sending the marked edges to equivalences. Dually for cocartesian fibrations].
- **The lax colimit is E itself** (no colimit rule at all): cocones that are not required to invert anything are just maps out of E. Here "lax" means *fully* lax, in every dimension: Loubaton (arXiv:2406.05425, Ex. 4.2.3.12) gives `laxcolim_{I♭} g ≃ dom(∫ g)` for the minimally marked I, and Gepner–Heine (arXiv:2608.02592, Thm 1.8.5(1)) give the E-lax colimit as `∫ F` localised at the (co)cartesian lifts of the cells in E, so E = ∅ gives `∫ F` [paper, F5a]. *Warning on conventions:* Abellán–Haugseng–Martini's "lax" colimit (arXiv:2602.07604, Thm F(1)) is lax only on 1-morphisms. For `F : 𝔸 → Cat_(∞,2)` it is 𝔼 with **all cartesian 2-morphisms inverted** (and the cocartesian 1-morphisms over I). It agrees with E itself only when the base has no non-invertible 2-cells [paper, F5a]. Gepner–Heine also call `∫ F` the *oplax* colimit in places, with the opposite naming (§1.5 there), like GHN (§4.6).
- **The pseudo colimit is the localisation** `E[W⁻¹]` at the cocartesian arrows W. W is given as a map `w : W → [⟦D¹⟧, E]` (the cocartesian arrows, picked out by ℓ of §4.6), and

  ```
  E[W⁻¹] := pushout of  E ←ev− W × ⟦D¹⟧ −→ W × ⟦J⟧
  ```

  a finite colimit. Its universal property is literally: maps `E[W⁻¹] → Z` are maps `E → Z` inverting w. **Proposition 6.1 [proved here]:** this is the cocone universal property above. (The pushout needs `W × ⟦D¹⟧` to be the tensor of W by the shape, i.e. maps out of it are maps `W → [⟦D¹⟧, Z]`. Under P this holds because ⟦D¹⟧ is exponentiable via the pseudo cotensor; in ωCat, `Fun(W × D¹, Z) ≃ Fun(W, Fun(D¹, Z))` because (∞,ω)-categories are cartesian closed [paper, F5a: Gepner–Heine arXiv:2608.02592 §1, "It is even cartesian closed"].)
- **Partially lax colimits** localise a sub-map of w: AHM's I-lax colimits (Thm F(1), in (∞,2), with the cartesian-2-morphism caveat above) and Gepner–Heine's E-lax colimits, which are localised Grothendieck constructions (Thm 1.8.5(1), for `F : S → ∞Cat` with S any (∞,∞)-category) [paper, F5a].
- Higher cocartesian cells (for I an ω-category) are localised in the same way, with ⟦D^k⟧ and the walking k-equivalence. This matches Loubaton's marked colimits, which invert marked cells in every dimension: Ex. 4.2.3.12 gives `laxcolim_I g ≃ ⊥ ι^*(∫ g)`, the localisation of the Grothendieck construction at the marked cells [paper, F5a]. The Grothendieck construction itself is Loubaton Thm 4.1.4.2: functors `A → (∞,ω)-cat` with lax transformations are equivalent to left cartesian fibrations over A [paper, F5a].

Semantic agreement (the localisation computes the colimit of the straightened functor) is Lurie HTT Cor. 3.3.4.3 in (∞,1) [paper, G4: `colim p ≃ X^♮`, the localisation of X at its (co)cartesian edges], AHM Thm F in (∞,2), and Loubaton Ex. 4.2.3.12 and Gepner–Heine Thm 1.8.5 for (∞,∞)/(∞,ω) [paper, F5a: statements checked; all three describe the (partially) lax colimit as a localisation of the Grothendieck construction, with the convention differences noted above]. Inside the theory nothing has to be proved: the encoding defines cocones, and the pushout's universal property is exactly the cocone property.

### 6.2 Sequential colimits

A sequence `X₀ → X₁ → …` is given, as in §4.4, by a family `p : X → N` (the total object, which plays the role of `⊔_n X_n`) and `t : X → X` with `p ∘ t ≅ succ ∘ p`. Its colimit is

```
colim_n X_n := pseudo-coequaliser of  1_X, t : X ⇉ X      (the all-marked colimit over L)
```

**Proposition 6.2 [recall, standard].** A colimit over the free category on a graph is the coequaliser of the coproduct over edges into the coproduct over vertices. This holds in (∞,1)- and (∞,ω)-categories because the free category on a graph is free as an ∞-category: Fun(F(G), C) ≃ Map(G, C). With ω = F(0 → 1 → 2 → …) the coproducts are X itself, so the formula above is the mapping telescope. ∎

So **sequential colimits need no new rule and no fibration structure**: a finite pseudo colimit of the total family suffices. Example: the ascending union of a chain of subsets X_n ⊆ Y.

### 6.3 Left Kan extensions

For `f : I → J` and a diagram `p : E → I`, the left Kan extension `f_! E` is classified by the localisation of the **free cocartesian fibration** on `f ∘ p`, which is the comma `E ×_J [⟦D¹⟧, J] → J` (source on E, target to J), at the arrows coming from p-cocartesian arrows of E [paper, G4, assembled from three sources: (a) the free fibration is Gepner–Haugseng–Nikolaus (arXiv:1501.02161) Thm 1.2, stated there for cartesian fibrations (`E ×_C C^{Δ¹} → C`, pullback along evaluation at 1, projection by evaluation at 0) and dualised here; (b) its fibre over j is `E ×_J J_{/j}`, whose localisation at the arrows from p-cocartesian arrows is `colim_{I_{/j}} F` by HTT Cor. 3.3.4.3, which is the pointwise formula for `(f_! F)(j)`; (c) a fibrewise localisation of a cocartesian fibration is the global localisation at the fibrewise arrows (Hinich, *Dwyer–Kan localization revisited*, Prop. 2.1.4, as stated in Haugseng–Hebestreit–Linskens–Nuiten arXiv:2011.08808 Prop. 4.2.5). GHN do not state the Kan-extension formula themselves]. Both steps are finite constructions (a comma object, then §6.1's localisation). So Kan extensions along arbitrary maps, not only along shapes, are available.

### 6.4 Colimits inside an object

A colimit *inside* an object C (an element of C with a universal cocone) is not an ambient colimit, and a general C has none. So it is **declared structure**: a marking on context variables, like T-var.

```
Γ, d : I → C, L : ⊤ → C, λ : d ⇒ L ∘ !_I   colim-marked
```

with a `uni`-style filler rule: for every `W`, `w : W → C` and cocone `θ : d ∘ π_I ⇒ w ∘ π_W : I × W → C`, a cell `m : L ∘ !_W → w` and invertible cells relating θ to `m · λ`, at every level. Generalised: **Lan-marked** variables `(f : I → J, d : I → C, K : J → C, λ : d ⇒ K ∘ f)` for left Kan extensions, the colimit being the case J = ⊤. Substituting into a marked tuple requires a certificate, as in T-var: an actual universal property derived elsewhere (e.g. an ambient colimit from §6.1, or a previously declared structure). "C has I-colimits" is then a hypothesis a user can take, the way they take a group object.

Pointwise-ness (stability under restriction along comma squares, which ∞-cosmos Kan extensions need, Riehl–Verity) is automatic for the generalised-element form, because the universal property is required for every parameter object W.

### 6.5 Infinite limits, and a new item: function sets

Dually, ambient limits indexed by a cartesian fibration are sections (the lax limit, a "dependent product"), which need the object of maps `[I, E]`. For a shape I it is a cotensor; for an arbitrary object I it is an **internal hom**, not a finite limit. Ordinary mathematics needs exactly this for sets: ℕ → ℕ, sequences in ℚ (for ℝ), power sets (functions into the proposition classifier, which needs a universe and is out of scope; predicates are monos, §2.4).

**F8: exponentials of sets.** Under P the cartesian internal hom of ωCat restricted to sets, `[A, B]` with `Hom(C × A, B) ≃ Hom(C, [A, B])` for all C, is semantically fine (Set is cartesian closed inside ωCat). In-style candidate: Mimram's cartesian closed CaTT rules (`internal-hom.md` §5.7, D12) restricted to targets with `trunc 0`, so the higher-dimensional cartesian pasting criterion is not needed (every cell above level 0 is T-fill).

#### 6.5.1 Proposal (F8, 2026-11-18)

**Ownership.** The ambient's pseudo internal hom `[B, C]` is already proposed in `internal-hom.md` §5.4 (IHOM, done), parametrised by representable Δ only ("currying with × waits on products"). Mimram's rules (D12, thread CLOSED) work *inside* one cartesian closed category. F8 is the product-parametrised exponential law for the ambient plus its interaction with h-levels, which is this note's area, so it stays here. Nothing is handed over.

**Rules (route A, generalised elements).** Standard 4 asks for the most general version, so the rule is stated for every exponent A and every target B, and sets are a corollary.

```
(exp)      Γ ⊢ A : ⋆    Γ ⊢ B : ⋆   ⟹   Γ ⊢ [A, B] : ⋆,   ev : [A, B] × A → B

(exp-λ)    Γ ⊢ W : ⋆    Γ ⊢ f : W × A → B
           ⟹  λf : W → [A, B]   and an invertible   β_f : ev ∘ (λf × A) → f

(exp-uni)  for g, h : W → [A, B] and a cell θ : ev ∘ (g × A) → ev ∘ (h × A),
           a cell θ̂ : g → h and an invertible cell  ev ∘ (θ̂ × A) → θ,
           and the same at every level (coinductively, as for `uni`
           in limits-representables.md; θ invertible ⟹ θ̂ invertible)
```

This is the `uni`/`colim-marked` pattern of §6.4 with the variance reversed: a universal property quantified over every parameter object W, no λ-term former inside B, no β or η as definitional equalities (β_f is a cell, η is the instance of exp-uni with θ = β). Restricted to W = ⟦Δ⟧ it is `internal-hom.md` §5.4's hom-⌜⌝/hom-⌞⌟ (a Δ-cell of [A, B] is a ΣΔ-diagram of functors A → B, i.e. a map `⟦Δ⟧ × A → B`). Restricted to A = ⟦P⟧ it is the cotensor law (E) that §6.1 already uses.

**Soundness under P [proved here, relative to cited facts].** `Cat_(∞,ω)` is cartesian closed [paper, F5a: Gepner–Heine arXiv:2608.02592 §1]. The k-cells of the ambient hom `Hom(W, X)` are pseudo transfors, i.e. maps `⟦Dᵏ⟧ × W → X` (`internal-hom.md` §5.5, Theorem (P), the pseudo cotensor). So k-cells `W → [A, B]` are maps `Dᵏ × W → [A, B]`, which are maps `Dᵏ × W × A → B`, which are k-cells `W × A → B`, naturally in W. That bijection at every level is exactly (exp-λ) plus (exp-uni). Under L the rule is **not** sound as stated for the lax hom (the Gray analogue fails on higher cells, `closed-structure.md` Part E, counterexample B = C = D¹); for discrete targets P and L agree (§1), so the set fragment below is sound under both.

**Proposition 6.3 (T-exp) [proved here].** If `B trunc n`, then `[A, B] trunc n`, for every object A.

*Proof.* A level-k cell into [A, B] from c is, by exp-λ/exp-uni at level k, a level-k cell into B from `c × A`, with the transposition preserving parallelism (it is a bijection on boundaries, level by level). T-fill for B at level ≥ n + 1 gives a filler of the transposed pair; exp-uni transposes it back, and its invertibility is preserved because exp-uni reflects invertibility (the same coinductive argument as Prop. 2.1). T-inv at level n + 1 transfers the same way. For n = −2, T-ctr: a map `c → [A, B]` is λ of the composite `c × A → ⊤ → B`. ∎

So `[A, B]` is a **set** whenever B is, for *any* A. Semantically [proved here]: for B a set, `[A, B] ≃ Set(π₀A, B)` with π₀A the set of objects of A modulo the equivalence relation generated by 1-cells. Indeed maps from any X into a discrete set factor through π₀X [recall], and π₀(X × A) = π₀X × π₀A, because 1-cells of a product are pairs and a pair (f, g) is the composite of (f, 1) and (1, g), so the generated relation on pairs is the product of the generated relations. Hence `Map(X × A, B) = Set(π₀X × π₀A, B) = Set(π₀X, Set(π₀A, B)) = Map(X, Set(π₀A, B))`, naturally in X. This does not even need cartesian closure of `Cat_(∞,ω)`.

**Consequences.**
- **Function sets.** `[N, N]`, `[N, ℚ]` (sequences, for ℝ as Cauchy sequences modulo a relation, with Trunc₀ from §5.3) and `[N × N, Bool]` are sets by T-exp.
- **Global dependent products.** For a family `p : E → I` (any I), the object of sections `Π_I E := [I, E] ×_{[I, I]} ⊤`, the pullback of `[I, p]` along `λ(π₂) : ⊤ → [I, I]` (the element id), is a finite limit after exp. It is a set when E is (T-lim, T-exp). Its universal property: maps `W → Π_I E` are maps `W × I → E` over I, by exp-uni and the pullback's `uni`.
- **What it does not give.** Dependent products *along* maps (local cartesian closure, Π_f for `f : I → J`) are not the pullback above; they would need exp in slices. F3b: the cartesian closed countermodel of Prop. 2.5 has these global Π and N is still not a set there, so F8 does not change F3b's verdict (as recorded in §2.3). Infinitary inductive objects (F1b) need exp *and* an initial-algebra principle for `X ↦ ∐_i [B_i, X]`; exp alone gives only the polynomial functor.

**Route B, compared (standard 3; not chosen).** Mimram's unbiased CCCaTT restricted to sets: object variables `A, B : ⋆^{≤0}`, simple types built from them with × and [–, –], and `coh_T : T` for every pasting type T (decidable, `internal-hom.md` §5.7). Mimram's `ps=` becomes T-fill, which is available because every such type denotes a set (T-exp, T-lim). Since targets are sets, only Mimram's 1-dimensional criterion (published, Thms 15 and 19) is used, not the higher criteria of D12.
- *Soundness* is then a corollary of route A: the sets form a full subcategory closed under × and [–, –] (T-lim, T-exp), hence a cartesian closed 1-category, where any two terms of a pasting type are βη-equal (Mimram Thm 15), so they are interpreted equal and T-fill supplies the cell.
- *Gains:* no λ-rule at all; combinators (S, K, composition, currying) are single coherences; equations are instances of T-fill.
- *Losses:* exponent and target must both be sets (route A allows any A, e.g. `[⟦L⟧, B]`, maps out of the loop into a set), and it says nothing about [A, B] for non-set B.
- *Relation:* every route-B coherence is a route-A term (ev, λ, pairing and projections compose to it), and every route-A term between sets is βη-equal to a route-B coherence by Mimram Thm 19 (completeness for STLC). So over sets the two routes have the same terms up to cells, and route B is a convenient *admissible tactic* over route A, in the same way the graph filler is over coh (§3).

### 6.6 Θ-density as an object-indexed colimit (F5b)

`free-objects-proofs.md` §6 (C9) found that disks are not dense and that Θ is. It asked for the Θ-density principle as an instance of §6.1: B as the localised Grothendieck construction of its Θ-elements. Here is what that takes. Standard 3 applies: two routes, compared, none chosen.

**(i) Extensionality needs nothing new.** In generalised-element form ("two transformations α, β : F ⇒ G : B → C agree if they agree after every `x : W → B`"), the statement is trivial: take W = B. The *shape* restriction (only `x : ⟦P⟧ → B` for pasting contexts P) is about **existence**: building a map or transformation out of B from data given on its Θ-elements. Only existence needs density. **[proved here]**

**(ii) Density as §6.1 needs Θ as an object.** The elements of B are pairs (P, x : ⟦P⟧ → B), and the diagram is `(P, x) ↦ ⟦P⟧`. As an instance of §6.1 the index must be an object, so Θ itself must be internal:
- *Objects of Θ:* Batanin trees, i.e. rose trees, `node : List(T) → T`. This is the §4.8(b) construction with one constructor whose arity is the length of its list. The word encoding allows a letter to carry its own arity (`ar : A → ℕ`, here A = ℕ), and the proof of Theorem 4.6 is unchanged: "pop ar(a)" in place of "pop n_i". **[proved here, as a variant of Thm 4.6]**
- *Morphisms of Θ:* strict functors `⟦S⟧ → ⟦T⟧`, which are finite combinatorial data (maps of trees, Berger; Joyal's description of Θ) and form a set-level object over `Θ₀ × Θ₀`. Defining it is routine recursion on trees, but long. **[not written]**
- *The universal pasting diagram* `U → Θ₀`, with fibre `⟦T⟧` over T. By §6.1 it is a cocartesian fibration, and the localisation of its total space at all cocartesian arrows is the colimit of all shapes.

**(iii) The elements need a relative cotensor.** The object of Θ-elements of B is `el(B) := Σ_{T : Θ₀} [⟦T⟧, B]`, i.e. the **cotensor of B by the family** `U → Θ₀`, relative to Θ₀. For a single shape this is a finite limit (the cotensor `[⟦P⟧, B]`). For the family it is a dependent product along `U → Θ₀`, which is not finite. Two routes:
- **Route A, a fibrewise-shape cotensor (R-cot⁺) [proposal].** For a family of shapes, meaning a map `q : U → I` whose fibres are pasting shapes, uniformly in i (the fibration of §6.1 for a diagram `I → shapes`), there is an object `[q, B] → I` with fibre `[⟦q_i⟧, B]`. Its universal property is the cotensor's, parametrised over I. Every fibre is a finite cotensor, so this is "finite limits, uniformly in a parameter". It is strictly weaker than an internal hom (F8), since its exponent ranges only over families of finite shapes. Semantics: fibrewise right adjoint to pullback, which exists because the fibres are finite and `Cat_(∞,ω)` is cartesian closed (§6.1) **[proved here, sketch]**.
- **Route B, F8 in general.** An internal hom along arbitrary maps (dependent products). It covers R-cot⁺ and much more, at the cost of F8's open questions (D12).

**(iv) The density statement [proposal; semantics proved].** With Θ internal and R-cot⁺, let `E_B → el(B)` be the pullback of U along the projection `el(B) → Θ₀`, mapped to B by evaluation. Then

```
(Θ-dens)    E_B[W⁻¹] ≃ B        (W = cocartesian arrows of E_B over el(B), §6.1)
```

and maps out of B are cocones over the Θ-elements, which is the existence half of extensionality. Semantically, (∞,ω)-categories are Θ-presheaves satisfying the Segal and completeness conditions (Loubaton's definition [paper]). Every presheaf is the colimit of the representables over its elements (HTT Cor. 5.1.5.8 [recall]). The Segal-complete ones are a reflective localisation, and the reflector preserves colimits and fixes representables, so B ≃ colim over Θ/B of ⟦P⟧ in `Cat_(∞,ω)`. By §6.1 that colimit is `E_B[W⁻¹]`. **[proved here, relative to the cited facts]**

**Verdict.** Θ-density *is* an instance of §6.1, but not a finite one. It needs Θ as an internal object (available from §4.8, with the morphisms still to be written) and the relative cotensor R-cot⁺ (route A) or F8 (route B). Extensionality in generalised-element form needs neither (i). Recorded in the ledger as F5b's remaining parts.

**(v) Follow-up (2026-11-18): R-cot⁺ over set bases, Θ's morphisms, and a correction to (iv).**

*R-cot⁺ is sound over a set base* **[proved here, relative to universal coproducts in `Cat_(∞,ω)` [recall] and cartesian closure (§6.1)]**. Let I be a set and q : U → I any map. A discrete I is the coproduct of its elements, so by universality U ≃ ∐_i U_i (fibres), and any p : W → I gives W ≃ ∐_i W_i with `W ×_I U ≃ ∐_i W_i × U_i`. Put `[q, B] := ∐_i [U_i, B] → I`. Then maps W → [q, B] over I are families of maps `W_i → [U_i, B]`, i.e. of maps `W_i × U_i → B`, i.e. maps `W ×_I U → B`, at every level. This is R-cot⁺'s universal property. Θ₀ is a set, so this is the case §6.6 needs, and no exponentiability of q (Conduché-type conditions) is required. Over a non-discrete base, soundness needs q exponentiable in `Cat_(∞,ω)/I`. Cocartesian fibrations are exponentiable in the (∞,1) case (flat fibrations, Lurie HA App. B) **[recall]**, but the (∞,ω) case is not checked, so the general rule stays **[conj]**. In-system, R-cot⁺ over a set base is a rule of the shape of a declared operation (F9b, `CaTTExp.Ops`): an object former `[q, B]` and the λ/uniqueness operations over a fixed generic context.

*Θ's morphisms as an internal set* **[proposal; proved here, sketch, relative to Thm 4.6 and Berger's description [recall]]**. Θ is Joyal's category, Berger's wreath product Δ ≀ Θ (Berger, *A cellular nerve for higher categories*, 2002, §3). A morphism `[m](S₁…S_m) → [n](T₁…T_n)` is a monotone `f : [m] → [n]` together with, for each i and each j in the interval that f assigns to i, a morphism `S_i → T_j`. The theorem number in Berger is not re-checked here, which is why this part is marked **[recall]**. This is finitary data defined by recursion on trees. So morphism candidates form a finitary inductive object M, a node carrying (f, nested lists of sub-morphisms). By Thm 4.6, with letters that carry their own arities as in (ii), M exists in route III. Well-formedness against given source and target trees is decidable by recursion into Bool, so `Θ₁ ⊆ Θ₀ × Θ₀ × M` is a pullback along `true`. Composition, identities, source and target are recursions. The category laws are equalities in a set, i.e. propositions, proved by induction (DJ), and T-fill makes every higher coherence automatic. So (Θ₀, Θ₁) is an **internal category in sets**.

*Correction to (iv).* `el(B) = Σ_T [⟦T⟧, B]` as defined in (iii) is only the **set of objects** of the category of elements Θ/B. A colimit over that discrete index is a coproduct of shapes, not B. Density needs the morphisms of Θ/B, so `el(B)` must be the 1-category realising the internal category `(el₀, el₁)`, where `el₁ ⊆ Θ₁ ×_{Θ₀} el₀` consists of the morphisms compatible with the evaluation maps (a pullback, after R-cot⁺ over Θ₁). Two principles are still missing:
1. **Realisation.** Turn an internal category in sets `(X₀, X₁)` into an object of the ambient, with X₀ as elements and X₁ as arrows. Semantically this is the nerve-realisation of a Segal set, which exists **[recall]**. In-system it is the localisation (§6.1) of the free category on the set-graph `X₁ ⇉ X₀` at the composition relations. That needs R-A⁺ for graphs whose vertex and edge *objects* are sets, a variant not yet stated.
2. **The universal shape functor** `U → el(B)`, cocartesian, with fibre ⟦T⟧ over (T, x) and transport along Θ-morphisms. Over the discrete Θ₀ it is ∐_T ⟦T⟧. Functoriality along Θ₁ needs a declared universal family, an R-A-style rule for "the generic pasting diagram". Semantically it is the Yoneda/realisation functor Θ → `Cat_(∞,ω)`, which exists.

With 1 and 2, (Θ-dens) holds as stated in (iv), with el(B) read as the realised category of elements, and the semantic argument of (iv) applies unchanged.

**(vi) Draft of the two missing rules (2026-11-18, ledger F5c and F5d).**

*F5c, the universal shape family (R-U) [proposal].* This is the one genuinely new principle. Θ₀ is the rose-tree object (ii), and the rule declares an object `U` with `q : U → Θ₀`, with three parts.
- **Fibres by constructor.** For a list of trees `ts = (T₁ … T_k)`, the fibre of q over `node(ts)` is `Σ U_{T₁} ∨ … ∨ Σ U_{T_k}`, the wedge of suspensions: the same recursion that builds ⟦T⟧ from its subtrees (PastingTrees' `build`). Over a closed tree T it is therefore ⟦T⟧. Stated over generalised elements `t : W → Θ₀`, the fibre is a pullback, and the rule gives a specified invertible comparison with the wedge-of-suspensions construction, natural in W.
- **Mapping out.** Maps `U → C` over nothing are sections of R-cot⁺ (over the set Θ₀, sound by (v)). So R-U needs no separate elimination rule beyond the fibre law and R-cot⁺.
- **Functoriality along Θ₁.** For a morphism `φ : S → T` in Θ₁, a map `U_S → U_T` over φ is given by the same recursion on the morphism datum (Berger's wreath description): monotone f on the outer chain, recursively on the hom-pieces. With this, q is a cocartesian fibration over the realised Θ, by the criterion of §6.1.

Semantics: U is `∐_T ⟦T⟧` with the Yoneda/realisation action of Θ, which exists. Status: R-U is **object-valued recursion along rose trees**. There is no universe, so it cannot be derived from recursion into a set, and it is added as a declared rule. In Agda it is an object former and its fibre comparisons are declared operations (`CaTTExp.Ops`), so the encoding mechanism exists; the declaration is not written.

*F5d, realisation of internal categories in sets: reduced to F5c and §6.1 [proposal; proved here, sketch].* Let X = (X₀, X₁, …) be an internal category in sets.
1. Its nerve is a set-family over ℕ: the composable words, a subobject of List(X₁) (F1b) cut out by a decidable predicate, with length to N.
2. Chains are linear trees, so `N → Θ₀` (n ↦ the linear tree of height 1 with n leaves) pulls R-U back to the universal chain family over N.
3. Pull that back to the nerve, giving `E_X → Nerve(X)` with fibre `⟦[n]⟧` over each n-simplex.
4. Localise the total space at its cocartesian arrows (§6.1). The result is |X|.
Semantically, every 1-category is the colimit of its simplices in `Cat_(∞,1)`, because Δ is dense there through complete Segal spaces **[recall]**. The inclusion `Cat_(∞,1) ⊂ Cat_(∞,ω)` is a left adjoint, with right adjoint the underlying (∞,1)-category **[recall]**, so it preserves that colimit. So F5d needs **no rule of its own** once R-U exists. Recorded separately because el(B) (§6.6(v)) uses it.

---

## 7. Lax functors (F6)

### 7.1 What is missing

In every option functors preserve composition up to invertible cells (`pseudo-vs-gray.md`, "What none of the three gives"). A lax functor `F : A ⇝ B` has *directed* comparison cells `F f ; F g → F(f;g)` and `1 → F 1`. Monads are the basic example: a lax functor from the point is a monad (Bénabou) [recall].

### 7.2 Lax functors out of finite loop-free shapes: no new rule

For a finite poset P, normal (op)lax functors `P ⇝ B` into a 2-category B are the simplices of B's Street nerve, i.e. strict maps out of the **orientals** glued along the nerve: `c_∞ N(P)` (Street; Duskin) [recall]. For 3-categories, Gagna proves that normalised oplax 3-functors correspond to simplicial maps between Street nerves, with a constraint on thin simplices, and for 1-categories without split monos or epis identifies `c_∞ N(A)` as the strictification [paper, arXiv 2004.14220, abstract/introduction level]. Maehara proves the orientals are also *free weak* ω-categories on the same generators [paper, arXiv 2102.09736, abstract level].

So, **[proposal]** for a finite loop-free context P (a finite category without non-identity loops, e.g. a pasting scheme), define the context P^lax as the finite computad presenting `c_∞ N(P)`. It is finite because N(P) has finitely many non-degenerate simplices. Then **lax functors ⟦P⟧ ⇝ C are P^lax-families**, i.e. maps `⟦P^lax⟧ → C`. Example: for the chain `0 → 1 → 2`, P^lax is the 2-oriental `(0, 1, 2, f₀₁, f₁₂, f₀₂, α : f₀₁ ; f₁₂ ⇒ f₀₂)`: exactly one comparison cell. No new rule is needed; P^lax must be a *specified construction* (as the cone contexts must be, `limits-representables.md` §10.3).

Shapes with loops (e.g. Bℕ, the point with its identity, needed for monads) have infinite nerves. A lax functor `Bℕ ⇝ C` is an infinite family; it would be given by the family encoding of §6 (a lax functor out of the point is a monad, which is finite data: t, μ, η and coherence cells, but its classifier, the walking monad, has hom Δ₊, which is infinite).

### 7.3 Lax-functor variables: a directed coherence rule that names its support

For lax functors between *arbitrary* objects, a context entry `F : A ⇝ B` (A a finite category whose nerve has finitely many non-degenerate simplices) with:
- action on elements and arrows: `F⟨x⟩ : ⊤ → B`, `F⟨f⟩ : F⟨x⟩ → F⟨y⟩`, and on higher cells of A;
- **support coherence `dcoh`**: for parallel F-image terms u, v of dimension n (composites in B of images of generators of `c_∞N(A)`), and a set S of (n+1)-dimensional generators (non-degenerate (n+1)-simplices of N(A)) satisfying the boundary equation

  ```
  ∂(Σ_{σ ∈ S} σ) = w_n(v) − w_n(u)          (in the normalised chain complex Λ(A))
  ```

  a cell `dcoh_S(u, v) : u → v`. Here `w_n(t)` is the sum of the n-dimensional generators used by t. The side condition is a finite 0/1 linear system, decidable by enumeration.

**What is known (researcher response, verified; `conjectures/answered/lax-functor-refinement-2026-11-18.md`).**
- Λ(A) is a strongly loop-free unital Steiner complex for every A in scope, so `c_∞N(A) ≅ νΛ(A)` (Steiner Thm 5.7) [paper, verified].
- In `c_∞N(A)`, the (n+1)-cells u → v correspond exactly to the subsets S satisfying the boundary equation. So dcoh_S exists exactly when the equation holds, it is unique *for the given S*, and different S give different cells [paper, verified].
- **A cell is not determined by its boundary.** In O₃ there are two distinct 2-cells `f₀₁;f₁₂;f₂₃ ⇒ f₀₃`, with supports `{012, 023}` and `{013, 123}`. They are related by the 3-cell, not equal. This is why the rule names S: a rule "a cell u → v whenever a support condition on (u, v) holds" (the first version of this section, and Conjecture LF part 2) would identify them.
- In dimension 2 for a DAG, the existence test is the refinement criterion ("the partition of the path given by u refines that given by v"), and the cells are counted by a product of Catalan numbers (binary bracketings of each block).
- Weak freeness of `c_∞N(A)` holds as an (∞,ω)-category by Campion (arXiv 2311.00200, Thm 5.11); contractibility applies after a strict cell is chosen, not a boundary. The CaTT-side comparison is part of the general semantic gap.
- The earlier [recall] "`Hom_{O_k}(0, k)` is a Gray cube" is **false for k ≥ 4**: `Hom_{O₄}(0,4)` has 5 one-cells from the longest path to the long edge (the Tamari/associahedral structure of Lack–Street), against 6 edge paths in the Gray 3-cube.

So dcoh has the same shape as L's rule (`pseudo-vs-gray.md` §3), with the lesson of both: **a directed coherence is decided by supports, not by boundaries**, and the term records its support. Under this reading the rule is sound for strict targets B through dimension 3 by Gagna (arXiv 2004.14220, Lemma 1.3.19, Thms 4.0.6, 5.0.17), and for weak B it is taken as the definition: normalised oplax functors A ⇝ B are maps `c_∞N(A) → B`. Conjecture LF is closed as stated (refuted, with the positive replacement above). The remaining question is the CaTT-side comparison, which is shared with the rest of the semantic gap.

---

## 8. Open items left by this note

All rows are added to `notes/open-issues.md` under F.

- **F2a** Agda: totality of the graph filler (Theorem 3.1). Done in every dimension: 1-cells (`GraphFillerTotal.agda`), parallel n-cells for n ≥ 2 in graph contexts (`GraphFillerTotal/Higher.agda`).
- **F2b** Implemented (2026-11-18): `GlobularFiller.agda`, a certified tactic (§3.3). **F2c**: Agda totality of it. *Step 1 done:* the fixed fuel (64) is replaced by one more than the coh-nesting depth of the inputs, which nf, flat, liftT and assign never exhaust, so the tactic has no artificial size bound. *Plan for the proof*, following `GraphFillerTotal` (whose height-1 case it generalises): (1) for globular Γ and `Γ ⊢ t : A`, `nf` returns a well-formed labelled tree whose boundaries are the normal forms of A's endpoints (needs: `merge d a b` well formed when `bd true d a = bd false d b`, and `flat` respects boundaries); (2) `treeOf` succeeds on every pasting context and `ctxOf ∘ treeOf` is the identity up to renaming (PastingTrees); (3) the lift is well typed in Θ_τ (`lift-ty`); (4) it has full support or is an operation (the side condition), via the position-tree split; (5) substituting λ back gives u, v, A (`lift-sub`). Steps (3)–(5) are `GraphFillerTotal/Higher.agda`'s structure with chains replaced by trees. *Progress:* (2) is proved. `treeOf (ctxOf τ) ≡ just τ` for every tree (`CaTTExp.GlobularTotal.Trees`: built contexts have the preorder depth sequence of the tree, and the parser inverts preorder sequences), and every pasting context is `ctxOf` of a tree, so `treeOf` succeeds on it and inverts `ctxOf` (`CaTTExp.GlobularTotal.Surj`, a zipper over ps derivations: pse opens a level, psd closes one). Remaining: (1), (3)–(5). Lemma (1) splits into three statements about strict normal forms, which are the actual mathematics of Thm 3.2:
  - (1a) *Tree algebra.* `bd` commutes with `merge` (`bd b j (merge k a b′)` is `merge k` of the boundaries for j > k, and the outer boundary for j ≤ k), and `flat` over a labelled tree commutes with `bd`. **[agda, the merge half]** `CaTTExp.GlobularTotal.TreeAlg`: source and target of a k-composite, lower boundaries (j < k), higher boundaries (j > k) as composites of boundaries, and preservation of well-formedness by `bd` and `merge`. **[agda, the flat half]** `CaTTExp.GlobularTotal.FlatBd`: with the images of the variables abstracted (`flatG`, equal to `flat` by `flat-is-flatG`) and compatible (`Good`: the image of an (e+1)-cell between o and o′ is a well-formed tree of dimension e+1 whose e-boundaries are the images of o and o′), `flat d T ≡ just a` gives `WF a` and `flat d (bd β i T) ≡ just (bd β (d+i) a)` for all β, i: the i-boundary of the diagram composes to the (d+i)-boundary of the composite. Lemma (1a) is done; `Good` for the identity tree of Θ under σ is what (1)'s induction must supply from `Γ ⊢ σ : Θ`.
  - (1b) *Substitution.* `nf (t[σ]) ≡ flat σ̂ (nf t)`, where σ̂ sends each variable to `nf (σ y)`. This is the strict image being a functor.
  - (1c) *Pasting contexts are contractible strictly.* In Θ = ctxOf τ, a well-typed term whose support is all of Θ has normal form `idTree τ`, and one whose support is ∂^∓Θ has normal form `bd ∓ (dim Θ − 1) (idTree τ)`. This is the strict-side content of the coh side condition.
  With (1a–c), induction on typing derivations gives (1): `nf` succeeds on every well-typed term of a globular context, and its boundaries are the normal forms of the type's endpoints.
- **F3b** Non-derivability of T-graph from R-A (Prop. 2.5), or the Hedberg-style derivation of `N trunc 0` (§2.3, after Prop. 2.5: it reduces to F8 or to a parameter-varying induction). **Closed:** non-derivability is proved for enriched cotensors and under (E) (`conjectures/answered/non-derivability-q2-2026-11-18.md`); T-graph stays a rule.
- **F1c** Closed: recursion in route II is not derivable (§4.5, countermodel).
- **F3c** Full proofs of Props. 2.2 and 2.3 against the specified `ctrf` construction once it exists (B5).
- **F1a** Done (2026-11-18): G and DJ written as rules (§4.6), the uniqueness gap in Theorem 4.4 found and corrected (induction is proved directly from G + DJ; recursion and its uniqueness follow).
- **F1b** Proposed and proved relative to R-A⁺ and G⁺ (§4.8): lists over any object, and every finitary signature as well-formed reverse-Polish words. Open: an independent check of Thm 4.6, and infinitary signatures (F8).
- **F4a** Done (2026-11-18, §5.1): level 1 by `LocalisedFiller.agda`. Levels ≥ 2 are T-fill on T-loc (`Trunc.Examples` §5). With finite inverse data in a context they fail (B²ℕ countermodel).
- **F4b** Trunc written in full (§5.3). Effectiveness of quotients needs EX; EX is not derivable (§5.3, countermodel), so it is a rule.
- **F5a** Done (2026-11-18): §6.1–6.3 checked at statement level (Loubaton, Gepner–Heine, AHM). "Lax colimit = total space" holds in the fully lax sense; AHM's convention inverts cartesian 2-morphisms (§6.1).
- **F5b** Analysed (2026-11-18, §6.6): extensionality in generalised-element form is trivial; Θ-density for existence is a non-finite instance of §6.1, needing Θ internal (§4.8 variant; morphisms not yet written) and a relative cotensor R-cot⁺ (or F8).
- **F6a** Answered (refuted as stated; rule revised to `dcoh_S`, §7.3). Remaining: the CaTT-side comparison, part of the semantic gap.
- **F8** Proposed and proved sound under P (2026-11-18, §6.5.1): exp/exp-λ/exp-uni for any A, B; T-exp (Prop. 6.3); Mimram's CCCaTT over sets as an admissible tactic. Open: Π along maps.
- **F9** `trunc`, T-fill, T-inv and T-ctr encoded (2026-11-18, `CaTTExp.Trunc`): no change to `CaTTExp.Syntax` was needed, since each rule is a `coh` over a fixed non-pasting context (TF k, TI j, TC) applied to a substitution, accepted when the image of C carries a low enough mark. Marks are per declaration (each context carries its own marks), and substitution is admissible for mark-respecting substitutions, which is T-var's certificate with T-cum (`CaTTExp.Trunc.Subst`, 2026-11-18). This is narrower than T-var: a marked variable may only be sent to a *variable* with a low enough mark, since only variables carry marks; sending it to a compound object (a limit, a hom object) needs the closure rules T-lim, T-hom, … as rules of the Agda judgment, not yet encoded. Certified checker, examples: fillers, inverses and inverse laws, Eckmann–Hilton for endo-cells into a set, and the §2.5 pentagon with c standing for R⁴. Open: the ring example with actual products (needs the limit syntax of `CaTTExp.Lim`), and the recursion rule over a parameter context. *Update (2026-11-18, F9b):* the recursion rule is now encoded too, through a general mechanism, **declared operations** (`CaTTExp.Ops`): a list of pairs (Δ, B), each usable as `coh Δ B σ` for every σ : Γ → Δ, with a certified checker and substitution proved admissible (hypotheses: closed constant types, scoped declarations). `CaTTExp.Ops.Nat` declares route II's recursor for N (signature ⊤, N, zero, succ; operations rec, recZ, recS over (A, a, f), and uniq, uniq⁻ over (A, a, f, h, hz, hs)). Parameters come by substitution, so the rule holds over every parameter context. Examples: doubling with its two cells, iteration over a parameter context, and η for N (`1_N ⇒ rec(zero, succ)` from the unit coherences), with negatives. Higher uniqueness is not declared; for sets it is T-fill. What is still not encoded is route III (R-A, G, DJ), where N is a hom object rather than a constant.
