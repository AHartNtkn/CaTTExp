# Chapter 9. Ordinary mathematics

The criterion (`catt-survey.md` §13, in the project files): for any ordinary structure, we can **build an object that behaves like an instance of it**. This chapter lists what that needs (sets, the natural numbers with induction, quotients, families and dependent sections, colimits indexed by objects, function sets, lax functors) and how each is obtained.

Without universes, the jobs a universe would do are taken by **two general rules**:
- **(DESC) descent** (§9.2) says what families over a colimit, and pullbacks of a colimit, look like. This is the *exactness* job: encode–decode arguments define their families by DESC.
- **(INIT) initial models** (§9.3) build an object by a universal property out of it. This is the *construction* job: inductive objects, truncations, free objects and object-valued recursion.

The list is fixed. A new inductive object, quotient, truncation or recursively defined family is a new **instance** of DESC or INIT, never a new rule. Besides these two, the chapter has the h-level judgment with its closure clauses (§9.1), two rows of the chapter 8 table (§9.6), the lax-functor rule dcoh_S (§9.8) and admissible filler tactics (§9.9). None has definitional equations.

**Where each construction of ordinary mathematics comes from.**

| Construction | Obtained as | Status |
|---|---|---|
| Disjoint, universal coproducts (T-coprod) | theorem of DESC-grpd | proved |
| Effective quotients (EX) | theorem of DESC with DESC-tr | proved (sketch) |
| Lax colimits as Grothendieck constructions (G) | DESC + the edge case G₁ | paper only (F10g: G₁-tot) |
| G⁺ (object-labelled edges) | DESC + G₁ relative to a base | paper only (F10g) |
| Directed J (DJ) | theorem of the limit rules (Riehl–Verity) | Agda-checked 1-truncated; higher levels paper only |
| Truncations ‖X‖_n | instance of INIT with the mark `⋆^{≤n}` | proved, given INIT |
| Free objects on graphs and object-labelled graphs (R-A, R-A⁺) | instances of INIT | proved |
| ℕ, lists, finitary W-types | instances of INIT (ℕ is also a theorem of DESC) | proved |
| Object-valued recursion on rose trees (R-U) | instance of INIT + DESC-grpd | proved (sketch) |
| R-cot⁺ over a set base | closed-structure hom + DESC-grpd + INIT | proved (sketch) |
| T-graph, T-loc | encode–decode from DESC, DJ and INIT, plus the closure clauses T-init and T-hom⁻ | paper only (F10g) |

The notes state this chapter under P (pseudo ambient) and say where L differs. For **discrete targets P and L agree**, because every 2-cell of the target is already invertible. Restating the non-discrete parts over V + S is ledger S8.

## 9.1 h-levels

**Rule.** For n ≥ −2, the judgment `Γ ⊢ C trunc n` ("C is an n-category": every cell into C of level > n is invertible and fillable). It is a judgment, not a type.

Use rules:
```
(T-fill)  C trunc n,  u, v : B parallel cells into C of level ≥ n + 1   ⟹   fill(u, v) : u →_B v,  fill(u, v) inv
(T-inv)   C trunc n,  u a cell into C of level n + 1                     ⟹   u inv
(T-ctr)   C trunc (−2),  c : ⋆                                          ⟹   ctr(c) : c → C
```
Introduction and closure rules:
```
(T-var)    declarations may carry a truncation  C : ⋆^{≤n};  substitutions must certify it
(T-cum)    C trunc n  ⟹  C trunc (n+1)
(T-unit)   ⊤ trunc (−2);   ⊥ trunc (−1)
(T-lim)    every object vertex of γ has trunc n  ⟹  lim_{Γ^μ}[γ] trunc n   (any marking)
(T-hom)    C trunc n,  a, b : ⊤ → C  ⟹  Hom_C(a, b) trunc (n − 1)          (n ≥ −1)
(T-hom⁻)   Hom_C(a, b) trunc (n − 1) for generalised points a, b : W → C, W fresh
           ⟹  C trunc n                                                    (n ≥ −1)
(T-init)   Δ positive in X (§9.3); every operation has target X and a source built from
           coproducts, finite products and parameters with trunc n (n ≥ 0); no cell
           variables except inv marks given by bi-invertibility data
           ⟹  μΔ trunc n
```
Derived:
```
(T-coprod) A, B trunc n,  n ≥ 0  ⟹  A ⊔ B trunc n            (from DESC-grpd, §9.2)
(T-trunc)  ‖X‖_n trunc n                                     (from INIT's mark ⋆^{≤n}, §9.3)
(T-graph)  Γ a finite graph context  ⟹  ⟦Γ⟧ trunc 1         (encode–decode, §9.4)
(T-loc)    the same with a set M of edges inverted  ⟹  ⟦Γ⟧[M⁻¹] trunc 1
```

**Side condition and decision procedure.** Syntax-directed on the object; the level of a cell is read off its type. T-init reads the context Δ, which is finite syntax. T-hom⁻'s premise is a hom judgment over a fresh W, proved like any other judgment, not searched for. Stable under substitution because declared truncations are certified (T-var).

**Example.** Bool := ⊤ ⊔ ⊤ is a set (T-coprod). ℕ := μ(X, z : ⊤ → X, s : X → X) is a set (T-init, n = 0). ℤ := μ(X, z : ⊤ → X, s : X → X inv) is a set (T-init; the `inv` mark is given by bi-invertibility data, §9.5). The loop L = (x, s : x → x) has ⟦L⟧ trunc 1 (T-graph).

**Why T-init has no cell variables.** With arbitrary invertible cells T-init is false. The context (X, z, s, s⁻¹, s ; s⁻¹ ≅ 1, s⁻¹ ; s ≅ 1), with quasi-inverse data instead of bi-invertibility data, has an initial model that is not a set: the higher inductive integers without their coherence constructor (Altenkirch–Scoccola, arXiv:2007.00167, §1.2).

**Relation to `grpd_k`.** `C grpd_k` (chapter 3) makes cells of hom-dimension ≥ k invertible: C is an (∞, k−1)-category. `C trunc n` makes them also fillable above level n: C is an n-truncated object. For n ≥ 0, `trunc n` implies `grpd_{n+1}`; the converse fails.

**Semantics.** Closure under limits and homs: proved (sketch level). T-hom⁻: sound, since n-truncation is tested on globes and the fibres of `Map(⟦Dᵏ⟧, C) → C^≃ × C^≃` are maps into homs. T-init: sound, since the Adámek tower stays inside n-truncated objects, which are closed under coproducts (n ≥ 0), finite products and filtered colimits, and an `inv` mark is a reflective condition closed under these.

**Status.**
- T-fill, T-inv, T-ctr: **Agda-checked** as coherences over fixed non-pasting contexts, with a certified checker and examples (`src/CaTTExp/Trunc/`, F9). Closure under limits and homs: **proved** (note level, F3).
- T-coprod: **proved**, from DESC-grpd.
- T-init and T-hom⁻: **paper only**. Both are semantically sound (sketch). Whether they are derivable from the other rules, instead of being closure clauses like T-lim, is open (F10g).
- T-graph and T-loc: **paper only**, by encode–decode (§9.4) relative to T-init and T-hom⁻ (F10d).
- Open: F3b (Hedberg route), F3c.

**Source.** `notes/ordinary-math.md` §2; `notes/universe-free-principles.md` §3.3, §6a; ledger F3, F9, F10d, F10g.

## 9.2 Descent (DESC)

**Rule.** A cocartesian fibration p : E → X is a map with a left adjoint ℓ to `[⟦D¹⟧, E] → p ↓ X` whose unit is invertible. This is finite data over limits, not a new judgment. Let D be a finite diagram (a substitution into a finite context, as for every colimit rule) with colimit X = colim D and legs ι_k : D_k → X.
```
(DESC-pb)   p : E → X cocartesian,  g : Y → X   ⟹   g*p : Y ×_X E → Y cocartesian
(DESC-univ) p : E → X cocartesian   ⟹   the comparison  colim_k (D_k ×_X E) → E  is invertible
(DESC-glue) cocartesian p_k : E_k → D_k for each k, and for each arrow u : k → k' of the
            diagram an invertible cell  E_k ≃ D_k ×_{D_k'} E_k'  over D_k, with the higher
            compatibility cells the diagram's shape requires
            ⟹  p : E → X cocartesian,  with invertible  ι_k*p ≃ p_k  compatible with the data
(DESC-uni)  two gluings of the same data are connected by an invertible cell, at every level;
            maps over X between glued fibrations are glued from compatible maps over the D_k
(DESC-grpd) D indexed by a groupoid (in particular a coproduct, D indexed by a finite set):
            the four clauses above with "cocartesian" deleted, for every map p
(DESC-tr)   Y a groupoid: families over Y with n-truncated fibres descend uniquely
            along the unit  Y → ‖Y‖_{n+1}
(DESC-or)   S the lax (oriented) colimit of D.  Lax gluing data: cocartesian p_k : E_k → D_k
            and, for each arrow u : k → k', a map  E_k → D_k ×_{D_k'} E_k'  over D_k (any map,
            not required invertible or cocartesian-preserving), with the higher cells the
            shape requires
            ⟹  p : E → S cocartesian with  ι_k*p ≃ p_k  and the gluing maps recovered as
            transport;  uniqueness at every level.  No universality clause.
```
DESC-pb is a theorem of the definition (Riehl–Verity, FYL §5.2) and is listed for completeness. DESC-univ says that base change along a cocartesian fibration preserves colimits. DESC-glue and DESC-uni are effectiveness. Localisations and sequential colimits are finite pushouts (§9.7), so DESC for finite diagrams already covers colimits indexed by objects.

**Side condition and decision procedure.** The diagram is finite syntax. "Indexed by a groupoid" is read off the index context: discrete, or marked `grpd_1` (chapter 3). The gluing data are terms and cells the user supplies, and checking them is ordinary type checking.

**Example.** *Why DESC is restricted to cocartesian fibrations.* Pull the pushout `[2] = {a0<a1} ⊔_{a1} {a1<a2}` back along f : [1] → [2], b0 ↦ a0, b1 ↦ a2. The pieces pull back to {b0}, {b1} and ∅, whose pushout is the discrete {b0, b1}, while the pullback of [2] is [1]. So "every colimit is universal" is false in Cat_ω, and f is not a cocartesian fibration.

*Disjointness of coproducts, derived.* The inclusion i_A : A → A ⊔ B is a cocartesian fibration (no arrow leaves A). DESC-grpd glues id_A over A with ∅ → B over B to a map E → A ⊔ B, and universality gives E ≃ A, so A ×_{A⊔B} B ≃ ∅. Together with universality of the coproduct, this proves T-coprod.

**Semantics.** Sound in Cat_ω.
- Cocartesian fibrations over X are the underlying category of [X, ω] (natural straightening, Loubaton Thm 4.1.4.2, Cor. 4.1.4.3), and [–, ω] sends colimits to limits. This gives DESC-glue and DESC-uni along every small colimit. DESC-univ: Loubaton Thm 3.2.3.15, Cor. 3.2.3.16. Sattler–Wärn (arXiv:2603.28688) prove the (∞,1) case and derive straightening from it.
- DESC-grpd: for a groupoid K, colim_K F is the Grothendieck construction ∫F, and every map into it is a cocartesian fibration up to equivalence.
- DESC-tr: n-types are classified by an (n+1)-type. The shift by one is optimal (`* → K(ℤ/2, n+1)`).
- DESC-or: at the oriented colimit, the Gray mapping object into the classifier is the oriented limit of the pieces' mapping objects (Gepner–Heine, arXiv:2608.02592, Def. 3.3.6, Thm 1.8.1–1.8.2). Lax gluing fails at the ordinary colimit: the constant point over the walking arrow has colimit a point, and ∅ → * cannot descend. Universality fails at the oriented colimit: pulling back along E = [1] → * gives E × [1], not the Gray E ⊠ [1]. So DESC-or has no universality clause.
- Exponentiable maps do not descend in general (a counterexample over `* ← {0<2} → [3] ← {1<3} → *`), so DESC is stated for cocartesian fibrations.

**Status.**
- Soundness of every clause: **proved** (researcher answer, verified 2026-11-21, `notes/conjectures/answered/universe-free-descent-and-initial-models-2026-11-21.md`).
- The counterexample to unrestricted descent: **Agda-checked** (`CaTTExp.Descent.PushoutNotUniversal`; that [2] is that pushout is cited, Ayala–Francis Ex. 1.6).
- Agda for the derivations from DESC (T-coprod, EX, encode–decode): open (F10f part 3).

**Source.** `notes/universe-free-principles.md` §3; ledger F10, F10a, F10f.

## 9.3 Initial models (INIT)

**Rule.** A **positive context** is a finite context Δ (the context grammar of chapters 1–9: object, map and cell variables, and marks such as `⋆^{≤n}` and `inv`) with a distinguished object variable X, such that:
- in the **target** of every operation, X occurs only under limit-preserving operations: X itself, ⊤, Hom_X(x, y) for points given by earlier variables, cotensors and lax cotensors [A, X] by objects A not mentioning X, and finite limits of these. Not coproducts, pushouts, ⊗, or a constant other than ⊤;
- in the **source** of every operation, X occurs under any accessible covariant operation: finite limits, colimits, ⊗ and × with fixed objects, and cotensors by fixed objects;
- a **cell** variable is a cell (of any dimension, invertible or not) between composites of earlier operations, and its target obeys the target condition;
- a **mark** restricts X to a reflective class closed under limits and filtered colimits (`⋆^{≤n}`), or marks an operation invertible (`inv`, presented by bi-invertibility data);
- X occurs nowhere contravariantly (no [X, –], no Hom with X in the first argument).

A **model** of Δ with carrier A is a substitution σ : Δ[A/X]. A **model morphism** is a map between carriers with an **invertible** cell for each variable of Δ (the arrow context Δ^→): model morphisms are strong.
```
(INIT-form)  Δ positive in X   ⟹   μΔ : ⋆   and a model  η : Δ[μΔ/X]          (the generic model)
(INIT-J1)    Γ ⊢ σ : Δ[A/X]
             ⟹  rec_σ : μΔ → A  and an invertible cell  rec_σ ∘ η ≅ σ          (a model morphism)
(INIT-J2)    two model morphisms h, h' : μΔ → A from η to σ
             ⟹  an invertible cell  h ≅ h'  of model morphisms
(higher)     derived: a level-k cell between model morphisms is a model morphism into the
             cotensor [⟦Dᵏ⟧, A] with the pointwise model
```
The rule binds the object variable X in a premise, forms an ordinary object μΔ, states its universal property by cells, and makes no judgment a term. It is the kind of binding former §0.2 allows, not a universe.

**Side condition and decision procedure.** Positivity is syntax-directed and decidable, like strict positivity for inductive types: walk the source and target of each operation and check every occurrence of X against the two lists above. No decidable syntax can be exact for single contexts outside this class: with a fixed BG for a finitely presented group G, `⊤ → BG` has an initial model iff G is trivial, which is undecidable (Adian–Rabin). So the kernel checks the uniform class.

**Example.**
- ℕ := μ(X, z : ⊤ → X, s : X → X); List(B) := μ(X, n : ⊤ → X, c : B × X → X); a finitary W-type is μ(X, c_i : B_i × X^{n_i} → X).
- ‖A‖_n := μ(X : ⋆^{≤n}, g : A → X). Here INIT-J1 and INIT-J2 are the two truncation rules Tr-J1 and Tr-J2.
- The free object on an object-labelled graph is μ(X, x_v : ⊤ → X, e : B_e → Hom_X(x_v, x_w)), which is R-A⁺. The target Hom_X(x_v, x_w) is a pullback of [⟦D¹⟧, X], so it is limit-preserving. The initial model is V ⊔_{∐_e (⊤ ⊔ ⊤)} ∐_e ΣB_e.
- *Rejected: a target that does not preserve limits.* Δ = (X, t : ⊤ → ⊤ ⊔ ⊤) has models Cat_ω ⊔ Cat_ω and no initial model. The same holds for (X, t : ⊤ → X ⊔ X).
- *Why morphisms are strong.* With lax model morphisms, pointed objects with a non-invertible comparison f(i) → y have no initial model: every candidate has two inequivalent maps to ([1], 1). Cells *declared in* Δ may still be non-invertible, so directed structure is available inside models.

**The impredicative reading.** Write ∀Δ. X for μΔ. A map W → ∀Δ. X is the same as a family of maps W → A, one for each model (A, σ), natural along model morphisms. System F's ∀X. (ΦX → X) → X is the case Δ = (X, a : ΦX → X). The naturality is built into INIT-J2, and it is essential: without it the encoding lacks η (Awodey–Frey–Speight, arXiv:1802.02820), and the plain dinatural end is wrong already for ℕ in Set, whereas strong (Barr) dinaturals are exactly the numerals (Paré–Román 1998, Prop. 1). The end ∫_{(A,σ)} A is a consequence of initiality, not equivalent to it: for ⊤ → 2 the end exists (it is ∅) but no initial model does. So the rule is stated as initiality.

**Semantics.** Sound in Cat_ω for limit-preserving accessible targets, accessible sources and strong morphisms: the forgetful functor from models creates limits and is accessible, so an initial model exists (Adámek–Rosický; Kerodon 9.4.9, 9.5.1–9.5.2), extended to finite contexts with cells. The target class is maximal among uniform ones: for a constant source A, having initial models for every A is a left adjoint to the target, which forces the target to preserve limits. The dual rule, final models of copositive contexts, is unsound in general (the right adjoint to base change along the non-exponentiable {0<2} → [2] does not exist), and it is not part of the system.

**Status.**
- Soundness and maximality: **proved** (researcher answer, verified 2026-11-21).
- **Not derivable** from finite limits, finite colimits and DESC: **proved** (researcher answer, verified 2026-11-22, `notes/conjectures/answered/universe-free-initial-models-r2-2026-11-22.md`). A model with full finite descent and DESC-tr (eventually-connected sequences of arrows of spaces) has no initial model for (X, a : A → X, l : X ×_{X×X} X → X). ℕ on its own *is* a theorem of DESC (ΩS¹ with Sattler–Wärn's sign construction), but which contexts follow from descent is undecidable (contractibility of finite complexes), so INIT stays one rule.
- Agda: INIT as a declared operation over the abstract model interface, with the derivations: open (F10f).

**Source.** `notes/universe-free-principles.md` §4; ledger F10, F10f, F10h.

## 9.4 Families, induction and the natural numbers

**Construction (no rule).** A family over B is a map p : E → B; a section is a map s : B → E with an invertible cell s ; p ≅ 1. Dependent elimination is **derived** from non-dependent universal properties (Awodey–Gambino–Sojakova's argument). For ℕ = μ(X, z, s), this gives recursion with uniqueness (INIT-J1, INIT-J2) and induction.

**Theorem (DJ, directed J).** For a : ⊤ → C, the comma projection π_a : a ↓ C → C is the free cocartesian fibration on a:
- *DJ-cocart:* π_a is a cocartesian fibration;
- *DJ-sec:* for a cocartesian q : E → C and e over a, there is a cocartesian-preserving h : a ↓ C → E over C with h ∘ ι ≅ e, where ι = (a, 1_a);
- *DJ-uni:* any cell ρ : h(ι) → h'(ι) over a extends uniquely to a transformation h ⇒ h' over C, invertible when ρ is; higher levels by fibrewise cotensors.

DJ follows from the limit rules (commas, cotensors by ⟦D¹⟧, pullbacks, ⊤) and the definition of cocartesian fibration, by Riehl–Verity's proof of Yoneda (FYL §6.2, Lemmas 6.2.9 and 6.2.12), which works in an abstract homotopy 2-category. It is not a rule.

**Theorem (G, lax colimits are Grothendieck constructions).** A diagram γ over a graph shape ⟦Γ⟧ has a lax colimit, which is the total space of a cocartesian fibration E → ⟦Γ⟧ with fibres γ_x and transport γ_f (clauses G-fib, G-fibre, G-transport, G-nat). Proof: ⟦Γ⟧ is a pushout of vertices and edges. Over an edge, the collage of γ_f is a cocartesian fibration (the edge case **G₁**). DESC-glue glues the collages, DESC-univ identifies the total space with the lax colimit, and DESC-uni gives G-nat. G₁'s existence, transport and uniqueness come from DESC-or, since ⟦D¹⟧ is the lax colimit of the point over D¹. G⁺ (object-labelled edges ΣB_e) reduces by DESC-glue to G₁ relative to the base B_e.

**Example.** *Encode–decode for a graph.* Let Γ be a finite graph, a a vertex, and Π the initial model of the multi-sorted context (X_v for v ∈ V, nil : ⊤ → X_a, snoc_e : X_v → X_w), read over the finite set V by DESC-grpd. Π_v is the set of paths from a to v.
1. DESC-glue, with G₁ over each edge, builds a cocartesian fibration E → ⟦Γ⟧ with fibres Π_v and transport snoc_e.
2. DJ-sec gives enc : a ↓ ⟦Γ⟧ → E with enc ∘ ι ≅ nil.
3. INIT-J1, applied to the model v ↦ Hom(a, v), gives dec fibrewise; DESC-uni assembles it over ⟦Γ⟧.
4. DJ-uni gives dec ∘ enc ≅ 1, and INIT-J2 gives enc ∘ dec ≅ 1.

So Hom_{⟦Γ⟧}(a, b) ≃ Π_b, a set by T-init. The same argument in the slice over W gives the homs between generalised points, and T-hom⁻ then gives T-graph. Lists over any B: List(B) ≃ ∐ Bⁿ from R-A⁺ and G⁺.

**Semantics.** DJ: Riehl–Verity's Yoneda lemma. G: Abellán–Haugseng–Martini and Loubaton; Sattler–Wärn derive straightening from descent in the same way.

**Status.**
- Dependent elimination for shapes ⟦Γ⟧ and for ℕ: **proved** (note level).
- DJ: **Agda-checked, 1-truncated**: DJ-cocart and the lemmas on cocartesian arrows (`CaTTExp.Descent.CocartLemmas`), DJ-sec and the directed DJ-uni (`CaTTExp.Descent.DJOneTruncated`: `dj-sec`, `dj-ext`, `dj-uni`, `dj-ext-uni`). Higher levels: **paper only** (F10b).
- G from DESC: **paper only**. Open: **G₁-tot**, that the total space of DESC-or's fibration over ⟦D¹⟧ is the collage; and DESC-or in slices, needed for G₁ relative to a base and so for G⁺ (both F10g).
- Encode–decode for graphs and localised graphs: **paper only** (F10d; Agda in F10f part 3).

**Source.** `notes/ordinary-math.md` §4; `notes/universe-free-principles.md` §3.3, §5, §6a; ledger F1, F10b, F10d, F10f, F10g.

## 9.5 Quotients and the integers

**Construction.** ℤ := μ(X, z : ⊤ → X, s : X → X inv), the initial object with a point and an automorphism. The `inv` mark is presented by bi-invertibility data l, r : X → X with l ; s ≅ 1 and s ; r ≅ 1, whose witnesses form a proposition, so maps out of ℤ are determined by z and s (Altenkirch–Scoccola, Thm 2.4). Equivalently, ℤ ≃ Hom(x, x) in the localisation of ⟦L⟧ at s, a finite pushout (chapter 7, §7.3), by encode–decode with M = {s} inverted (§9.4).

**Truncations and quotient sets.** ‖X‖_n is an INIT instance (§9.3); its higher levels and dependent elimination are derived. A quotient set is the 0-truncation of a localisation (a pseudo coequaliser); ℚ is a quotient of ℤ × ℕ.

**Theorem (EX, effective quotients).** For a set X and an equivalence relation R ↪ X × X, let q : X → Q := ‖coeq(r₀, r₁)‖₀. Then the canonical map R → X ×_Q X is invertible. The proof is encode–decode against the family x ↦ R(x, –), which DESC builds where HoTT uses univalence:
1. DESC-grpd glues R → X × X, with the descent cells R(x, r₀ρ) ≃ R(x, r₁ρ), to a family over X × coeq(r₀, r₁);
2. its fibres are propositions, so DESC-tr descends it to X × Q;
3. transport along q x ≅ q y gives X ×_Q X → R, inverse to the canonical map because both are subobjects of X × X.

**Status.** ℤ ≃ Hom(x, x) in the localised loop: **proved** (Dwyer–Kan); by encode–decode, **paper only** (F10d). Trunc_n's derived levels and the quotient's universal property: **proved** (note level). EX from DESC: **proved** (sketch). Without DESC, EX is not derivable from limits, colimits, R-A and Trunc (countermodel in posets, verified); that model fails DESC. **Source:** `notes/ordinary-math.md` §5; `notes/universe-free-principles.md` §3.3, §6a; ledger F4, F4b, F10d.

## 9.6 Function sets

**Rules (two rows of the chapter 8 table).** Function sets come from A\B. Two structural principles are rows of the F.7.4 table, so they get (GB-cut) and (GB-dcut) like every other row. GB-shape is adopted (chapter 8, §8.8; ledger S13). L-× is proposed and awaits its independent check (F8b). Neither replaces a use of a universe: they relate ⊗ to ×.
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

**Example.** For g : ℕ → ℕ\ℕ, the diagonal n ↦ g(n)(n) + 1 needs ev out of ℕ × (ℕ\ℕ), i.e. contraction (L-×). The pointwise sum of two sequences needs only weakening.

**Semantics.** Both rules are sound in Cat_ω.
- GB-shape: ⟦Θ⟧ and ⟦Θ⟧♭ are both Θ.
- L-× at sets: π₀(A ⊗ W) = π₀A × π₀W.
- L-× at all `grpd_2` targets: the (∞,1)-reflection τ₁ sends ⊗ to × (Campion, (OBJ-1)), and τ₁ preserves products.
- Maximality: if κ* is an equivalence into B for all A, W, then `B grpd_2`. So L-× has the most general target class.

**Status.**
- Non-derivability (two countermodels), maximality, the set instance of L-×, and the derivation of F8: **proved** (note level). Soundness of each countermodel for every chapter-1–9 rule is at sketch level.
- L-× at general `grpd_2` targets: **proved relative to cited theorems** (Campion Thm 3.14 / Cor. 3.15; Goldthorpe Lemma 3.0.3; researcher answer verified 2026-11-21, `notes/conjectures/answered/gray-cartesian-local-targets-2026-11-21.md`). Holds in the inductive and coinductively complete models of Cat_ω.
- Agda (1-truncated derivation over the abstract model interface): in progress.
- Open: whether the kernel derives the cartesian F8 by an unrelated route (moot once L-× is adopted).

**Source:** `notes/ordinary-math.md` §6.5.1–6.5.2; ledger F8, F8a–F8d.

## 9.7 Colimits indexed by objects

**Construction (no new rule).** A diagram indexed by an object I is a cocartesian fibration E → I (G, §9.4). Then
- the lax colimit is the total space E;
- the pseudo colimit is a finite localisation of E at the cocartesian arrows;
- a left Kan extension is a comma object followed by a localisation;
- a sequential colimit is a pseudo coequaliser of the total family.

Colimits *inside* an object C are declared structure: a marking with a filler rule. **Θ-density** (B as the colimit of its pasting-diagram elements) is an instance over an internal Θ and gives extensionality of transformations for arbitrary domains (F5b, F5c drafted).

**Object-valued recursion (no rule).** The internal Θ and the realisation functor (F5d) come from a family U → Θ₀ over the set of rose trees, defined by recursion. It is an INIT instance: U := μ(X, p : X → Θ₀, a : Φ_p(X) → X over Θ₀), where Φ_p(X) has fibre ∨_j ΣX_{t_j} over node(ts). Lambek's lemma and DESC-grpd over Θ₀ give the fibres U_{node(ts)} ≃ ∨_j ΣU_{t_j}.

**R-cot⁺ over a set base (no rule).** For a set I and q : U → I, the object [q, B] → I, whose maps from W over I are the maps W ×_I U → B, is an equaliser inside I × U\(B ⊔ ⊤) (the closed-structure hom of chapter 8, read as partial maps): the i-th component lands in B and the others in ⊤. DESC-grpd splits W over I, and decidable equality on I comes from INIT. Over a non-discrete base, R-cot⁺ would be a right adjoint to base change along q, which exists only for exponentiable q; it is not part of the system.

**Status.** The constructions are finite: **proved**. Agreement with semantic colimits: checked at statement level against Loubaton, Gepner–Heine and AHM (F5a, done), with the finding that AHM's "lax" colimit inverts cartesian arrows. R-U and R-cot⁺ from INIT and DESC: **proved** (sketch; F10c). **Source:** `notes/ordinary-math.md` §6; `notes/universe-free-principles.md` §4.3, §6b; ledger F5, F5a–d, F10c.

## 9.8 Lax functors

**Construction (no rule) for finite loop-free shapes P.** Lax functors ⟦P⟧ ⇝ C are maps out of a finite context P^lax glued from Street's orientals.

**Rule (dcoh_S) for lax-functor variables F : A ⇝ B.** A context entry with action on elements, arrows and higher cells, and for parallel F-image terms u, v of dimension n and a set S of non-degenerate (n+1)-simplices of N(A) with
```
∂(Σ_{σ ∈ S} σ) = w_n(v) − w_n(u)        (in the normalised chain complex Λ(A))
```
a cell dcoh_S(u, v) : u → v. The term records its support S.

**Side condition and decision procedure.** A finite 0/1 linear system, decided by enumeration.

**Example.** In O₃ there are two distinct 2-cells f₀₁ ; f₁₂ ; f₂₃ ⇒ f₀₃, with supports {012, 023} and {013, 123}, related by the 3-cell. A rule "a cell u → v whenever a support condition on (u, v) holds" would identify them; that is why S is part of the term.

**Semantics.** Λ(A) is strongly loop-free unital Steiner, so c_∞N(A) ≅ νΛ(A); its (n+1)-cells u → v correspond exactly to the admissible S. Sound for strict B through dimension 3 (Gagna); for weak B it is the definition (normalised oplax functors are maps c_∞N(A) → B).

**Status.** **Proved** (verified researcher answer, `notes/conjectures/answered/lax-functor-refinement-2026-11-18.md`). **Source:** `notes/ordinary-math.md` §7; ledger F6, F6a.

## 9.9 Filler tactics (admissible, no rule)

**Algorithm (graph filler).** In a graph context, two parallel cells with the same flattened path are connected by one coherence over the chain context Θ_k. This is RC(1) and its higher analogue for graphs.

**Algorithm (globular filler).** Compute strict normal forms as labelled pasting trees (merge = composition, flatten = substitution), lift by position trees, and return `coh Θ_τ (ũ → ṽ)[λ]`. That this term is well typed whenever the two cells have the same normal form is proved (`FillTotal.fill-total`), so the output needs no separate check.

**Algorithm (localised filler).** In a localised graph (inverse data as context variables), same reduced word ⇒ explicit 2-cell from graph fillers and whiskered cancellations.

**Status.** All three: **Agda-checked** as certified tactics; the graph filler is total in every dimension (`GraphFillerTotal`, `.Higher`), the globular filler succeeds on every parallel pair with the same normal form (`FillTotal.fill-ok`). The marked (pseudo) version waits on markings in the Agda core (F4c). **Source:** `notes/ordinary-math.md` §3; ledger F2, F2a–c, F4a, F4c.

## 9.10 Open surface questions

**Q9.1. Whether `trunc n` is written or inferred.**
- *Option A: declared only* (T-var), everything else derived by the closure rules. Visible; a missing declaration is a type error.
- *Option B: inferred for every object built by limits, homs, coproducts and INIT instances,* with declarations only for variables. Less writing; inference must run the closure rules eagerly on every object.

**Q9.2. How INIT instances are introduced.**
- *Option A: as a positive context* (`μ(X, z : ⊤ → X, s : X → X)`, with rec and the uniqueness cells as INIT's terms). No new syntax; the user sees the context INIT checks.
- *Option B: a declaration form* (`inductive N | zero | succ N`) elaborated to the positive context and INIT's terms. Familiar; the elaborator owns the translation, and positivity errors must refer back to the declaration.

**Q9.3. How descent data are supplied.**
- *Option A: explicitly,* as the fibres and gluing cells of DESC-glue. Every family over a colimit is visible as its pieces.
- *Option B: by recursion syntax* (a family over ⟦Γ⟧ defined by cases on vertices and edges), elaborated to DESC-glue. Closer to HoTT's families by recursion into a universe; the elaborator must produce the higher compatibility cells.

**Q9.4. Whether the filler tactics run automatically.**
- *Option A: on request* (`fill`). Predictable cost.
- *Option B: at every hole whose type is a parallel pair with the same normal form.* Least writing; a failed fill must be reported in terms of normal forms, which the user may not recognise.
