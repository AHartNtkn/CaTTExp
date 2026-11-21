# Chapter 9. Ordinary mathematics

The criterion (`catt-survey.md` §13, in the project files): for any ordinary structure, we can **build an object that behaves like an instance of it**. This chapter lists what that needs (sets, the natural numbers with induction, quotients, families and dependent sections, colimits indexed by objects, function sets, lax functors) and how each is obtained. Most items add **no rule**: they are constructions over chapters 1–8. The rules that are added are judgments in the style of `⊢ps`, filler rules, and two rows of the chapter 8 table (§9.6), all without definitional equations.

The notes state this chapter under P (pseudo ambient) and say where L differs. For **discrete targets P and L agree**, because every 2-cell of the target is already invertible. Restating the non-discrete parts over V + S is ledger S8.

## 9.1 h-levels

**Rule.** For n ≥ −2, the judgment `Γ ⊢ C trunc n` ("C is an n-category": every cell into C of level > n is invertible and fillable). It is a judgment, not a type.

Use rules:
```
(T-fill)  C trunc n,  u, v : B parallel cells into C of level ≥ n + 1   ⟹   fill(u, v) : u →_B v,  fill(u, v) inv
(T-inv)   C trunc n,  u a cell into C of level n + 1                     ⟹   u inv
(T-ctr)   C trunc (−2),  c : ⋆                                          ⟹   ctr(c) : c → C
```
Introduction rules:
```
(T-var)    declarations may carry a truncation  C : ⋆^{≤n};  substitutions must certify it
(T-cum)    C trunc n  ⟹  C trunc (n+1)
(T-unit)   ⊤ trunc (−2);   ⊥ trunc (−1)
(T-lim)    every object vertex of γ has trunc n  ⟹  lim_{Γ^μ}[γ] trunc n   (any marking)
(T-hom)    C trunc n,  a, b : ⊤ → C  ⟹  Hom_C(a, b) trunc (n − 1)          (n ≥ −1)
(T-coprod) A, B trunc n,  n ≥ 0  ⟹  A ⊔ B trunc n
(T-graph)  Γ a finite graph context  ⟹  ⟦Γ⟧ trunc 1
(T-loc)    the same with a set M of edges inverted  ⟹  ⟦Γ⟧[M⁻¹] trunc 1
(T-trunc)  ‖X‖_n trunc n
```

**Side condition and decision procedure.** Syntax-directed on the object; the level of a cell is read off its type. Stable under substitution because declared truncations are certified (T-var).

**Example.** N := Hom_{⟦L⟧}(x, x) for the loop L = (x, s : x → x) is a set: T-graph gives ⟦L⟧ trunc 1 and T-hom gives N trunc 0. Bool := ⊤ ⊔ ⊤ is a set. ℤ is a set (T-loc, T-hom).

**Relation to `grpd_k`.** `C grpd_k` (chapter 3) makes cells of hom-dimension ≥ k invertible: C is an (∞, k−1)-category. `C trunc n` makes them also fillable above level n: C is an n-truncated object. For n ≥ 0, `trunc n` implies `grpd_{n+1}`; the converse fails.

**Semantics.** Closure under limits and homs: proved (sketch level). T-graph and T-loc: sound by the free-on-graph theorem and Dwyer–Kan. T-graph is **not** derivable from R-A (verified countermodels), so it stays a rule.

**Status.** Proposal with proofs at note level (F3); T-fill/T-inv/T-ctr encoded as coherences over fixed non-pasting contexts with a certified checker and examples (`src/CaTTExp/Trunc/`, F9). Open: F3b (Hedberg route, needs Π over N or parameter-varying induction), F3c (blocked on B5, now unblocked by chapter 5). **Source:** `notes/ordinary-math.md` §2; ledger F3, F9.

## 9.2 Filler tactics (admissible, no rule)

**Algorithm (graph filler).** In a graph context, two parallel cells with the same flattened path are connected by one coherence over the chain context Θ_k. This is RC(1) and its higher analogue for graphs.

**Algorithm (globular filler).** Compute strict normal forms as labelled pasting trees (merge = composition, flatten = substitution), lift by position trees, and propose `coh Θ_τ (ũ → ṽ)[λ]`; the certified checker accepts or rejects.

**Algorithm (localised filler).** In a localised graph (inverse data as context variables), same reduced word ⇒ explicit 2-cell from graph fillers and whiskered cancellations.

**Status.** All three: **Agda-checked** as certified tactics; the graph filler is total in every dimension (`GraphFillerTotal`, `.Higher`), the globular filler succeeds on every parallel pair with the same normal form (`FillTotal.fill-ok`). The marked (pseudo) version waits on markings in the Agda core (F4c). **Source:** `notes/ordinary-math.md` §3; ledger F2, F2a–c, F4a, F4c.

## 9.3 Families, induction and the natural numbers

**Construction (no rule).** A family over B is a map p : E → B; a section is a map s : B → E with an invertible cell s ; p ≅ 1. Dependent elimination is **derived** from non-dependent universal properties (Awodey–Gambino–Sojakova's argument).

**Two general principles** (route III, no ℕ-specific rule):
- **(G)** lax colimits are Grothendieck constructions: a diagram indexed by an object is a cocartesian fibration, and its lax colimit is the total space (rules G-fib, G-fibre, G-transport, G-nat);
- **(DJ)** directed J: comma objects are free cocartesian fibrations (rules DJ-cocart, DJ-sec, DJ-uni, higher levels by fibrewise cotensors).

**Example.** Induction for N from G + DJ (Thm 4.4), hence recursion with uniqueness. Lists over any B: List(B) ≃ ∐ Bⁿ from R-A⁺ (free objects on object-labelled graphs) and G⁺.

**Semantics.** DJ by Riehl–Verity's Yoneda lemma; G by Abellán–Haugseng–Martini and Loubaton.

**Status.** Dependent elimination for shapes ⟦Γ⟧ and for ℕ from recursion: **proved** (note level). Induction from G + DJ: **proved** (Thm 4.4, the circular uniqueness step of the first version corrected). Some h-initiality steps are **not derivable** without further rules (F1c, verified countermodel). **Source:** `notes/ordinary-math.md` §4; ledger F1, F1a–c.

## 9.4 Quotients and the integers

**Construction.** ℤ := Hom(x, x) in the localisation of ⟦L⟧ at s, a finite pushout (chapter 7, §7.3). It is discrete (Dwyer–Kan's comparison lemma).

**Rule (Trunc_n).** The n-truncation ‖X‖_n with two rule levels; higher levels and dependent elimination derived. Quotient sets are truncations of localisations; ℚ is a quotient of ℤ × N.

**Rule (EX).** Effectiveness of quotients needs a further rule EX, which is **not derivable** (countermodel in posets, verified).

**Status.** ℤ ≃ ℤ_disc: **proved** from Dwyer–Kan. Trunc's derived levels and the quotient's universal property: **proved** (note level). **Source:** `notes/ordinary-math.md` §5; ledger F4, F4b.

## 9.5 Colimits indexed by objects

**Construction (no new rule).** A diagram indexed by an object I is a cocartesian fibration E → I (G of §9.3). Then
- the lax colimit is the total space E;
- the pseudo colimit is a finite localisation of E at the cocartesian arrows;
- a left Kan extension is a comma object followed by a localisation;
- a sequential colimit is a pseudo coequaliser of the total family.

Colimits *inside* an object C are declared structure: a marking with a filler rule. **Θ-density** (B as the colimit of its pasting-diagram elements) is an instance over an internal Θ and gives extensionality of transformations for arbitrary domains (F5b, F5c drafted).

**Status.** The constructions are finite: **proved**. Agreement with semantic colimits: checked at statement level against Loubaton, Gepner–Heine and AHM (F5a, done), with the finding that AHM's "lax" colimit inverts cartesian arrows. **Source:** `notes/ordinary-math.md` §6; ledger F5, F5a–d.

## 9.6 Function sets

**Rules (two proposed rows of the chapter 8 table).** Function sets come from A\B. Two structural principles are proposed as rows of the F.7.4 table, so they get (GB-cut) and (GB-dcut) like every other row. Both are proposals: GB-shape is the open kernel question of chapter 8, §8.8 (ledger S13, F8a), and L-× awaits an independent check (F8b).
```
(GB-shape)  ⊢ ι_Θ : (⟦Θ⟧ ▸ ⟦Θ⟧♭)        for each pasting shape Θ   (⟦Θ⟧♭ the free object of chapter 7)
            row: H = (L, ⟦Θ⟧♭, R ▸ Z),   B = (L, ⟦Θ⟧, R ▸ Z),      r(x) = x ∘ᵢ ι_Θ

(L-×)       B grpd_2:
            row: H = (A × W, S ▸ B),     B' = (A, W, S ▸ B),        r(x) = x ∘₀ κ_{A,W}
            S empty or one time slot in the last gap
```
- GB-shape at Θ = D⁰, with ⟦D⁰⟧♭ ≃ ⊤, is **weakening**: (L, ⊤, R ▸ Z) ≃ (L, R ▸ Z). From it come the projections out of ⊗, and the comparison κ_{A,W} : (A, W ▸ A × W) by ×'s `uni`. It also identifies chapter 6's elements ⊤ → C with chapter 8's points ( ▸ C).
- L-× is **contraction** at (∞,1)-category targets: maps A × W → B are multimaps (A, W ▸ B). Its set instance (B trunc 0, only n = 0, 1 carry content) is (L-set).

**Derived (F8).** With [A, B] := A\B, the exponential rules (exp), (exp-λ) and (exp-uni) at every level are derived for every B with `B grpd_2`, in particular for sets. Here ev := the L-× cut of e^ℓ, λf := the left-row cut of f ∘ κ, and β comes from L-×'s uniqueness. T-exp follows: `B trunc n ⟹ A\B trunc n`, since the left row keeps the time slot last. F8 is no longer a primitive under L. Under P it keeps its §6.5.1 statement as the general cartesian exponential.

**Side condition and decision procedure.** Template matching as in chapter 8 (Lemma GB-dec). L-× also reads `B grpd_2`, which is syntax-directed (chapter 3).

**Why new rules.** Without them the kernel derives no projection (A, W ▸ A), no comparison κ, and no unitor (W, ⊤ ▸ W). A graded countermodel shows this: Day convolution on ℕ-graded ω-categories, where the ⊗-unit is not ⊤. With GB-shape and even F8, (L-set) is still not derivable: a filtered countermodel has A ⊗ W = y(2) and A × W = y(1). The h-level rules give no maps out of products.

**Example.** For g : N → N\N, the diagonal n ↦ g(n)(n) + 1 needs ev out of N × (N\N), i.e. contraction (L-×). The pointwise sum of two sequences needs only weakening.

**Semantics.** Both rules are sound in Cat_ω.
- GB-shape: ⟦Θ⟧ and ⟦Θ⟧♭ are both Θ.
- L-× at sets: π₀(A ⊗ W) = π₀A × π₀W.
- L-× at all `grpd_2` targets: the (∞,1)-reflection τ₁ sends ⊗ to × (Campion, (OBJ-1)), and τ₁ preserves products.
- Maximality: if κ* is an equivalence into B for all A, W, then `B grpd_2`. So L-× has the most general target class.

**Status.**
- Non-derivability (two countermodels), maximality, the set instance of L-×, and the derivation of F8: **proved** (note level). Soundness of each countermodel for every chapter-1–9 rule is at sketch level.
- L-× at general `grpd_2` targets: **sketch**, relative to two cited facts. Independent check requested.
- Agda (1-truncated derivation over the abstract model interface): in progress.
- Open: whether the kernel derives the cartesian F8 by an unrelated route (moot once L-× is adopted).

**Source:** `notes/ordinary-math.md` §6.5.1–6.5.2; ledger F8, F8a–F8d.

## 9.7 Lax functors

**Construction (no rule) for finite loop-free shapes P.** Lax functors ⟦P⟧ ⇝ C are maps out of a finite context P^lax glued from Street's orientals.

**Rule (dcoh_S) for lax-functor variables F : A ⇝ B.** A context entry with action on elements, arrows and higher cells, and for parallel F-image terms u, v of dimension n and a set S of non-degenerate (n+1)-simplices of N(A) with
```
∂(Σ_{σ ∈ S} σ) = w_n(v) − w_n(u)        (in the normalised chain complex Λ(A))
```
a cell dcoh_S(u, v) : u → v. The term records its support S.

**Side condition and decision procedure.** A finite 0/1 linear system, decided by enumeration.

**Example.** In O₃ there are two distinct 2-cells f₀₁ ; f₁₂ ; f₂₃ ⇒ f₀₃, with supports {012, 023} and {013, 123}, related by the 3-cell. A rule "a cell u → v whenever a support condition on (u, v) holds" would identify them; that is why S is part of the term.

**Semantics.** Λ(A) is strongly loop-free unital Steiner, so c_∞N(A) ≅ νΛ(A); its (n+1)-cells u → v correspond exactly to the admissible S. Sound for strict B through dimension 3 (Gagna); for weak B it is the definition (normalised oplax functors are maps c_∞N(A) → B).

**Status.** **Proved** (verified researcher answer, `notes/conjectures/answered/lax-functor-refinement-2026-11-18.md`); the first version (a cell whenever supports allow, unique) was refuted. **Source:** `notes/ordinary-math.md` §7; ledger F6, F6a.

## 9.8 Open surface questions

**Q9.1. Whether `trunc n` is written or inferred.**
- *Option A: declared only* (T-var), everything else derived by the introduction rules. Visible; a missing declaration is a type error.
- *Option B: inferred for every object built by limits, homs, coproducts and free objects on graphs,* with declarations only for variables. Less writing; inference must run the introduction rules eagerly on every object.

**Q9.2. How inductive objects are introduced.**
- *Option A: as their kernel construction* (N := Hom_{⟦L⟧}(x, x), with recursion and induction as derived terms). No new syntax; the user learns why ℕ is what it is.
- *Option B: a declaration form* (`inductive N | zero | succ N`) elaborated to the free object, the hom and the G + DJ terms. Familiar; the elaborator owns a nontrivial translation, and error messages must refer back to it.

**Q9.3. Whether the filler tactics run automatically.**
- *Option A: on request* (`fill`). Predictable cost.
- *Option B: at every hole whose type is a parallel pair with the same normal form.* Least writing; a failed fill must be reported in terms of normal forms, which the user may not recognise.
