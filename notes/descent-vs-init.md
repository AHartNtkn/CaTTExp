# Descent and initial models: what each one gives

*Question (Anthony, 2026-11-23).* Chapter 9 has two object-forming rules, DESC (§9.2) and INIT (§9.3). INIT with cell constructors gives full directed HITs, and arguably coinductive types too. What does descent give that INIT doesn't?

*Short answer.* Neither rule is derivable from the other, so both stay.
- **INIT builds objects by their maps out.** Every INIT conclusion is a map out of μΔ, or a cell between two such maps.
- **DESC is about pullbacks of colimits.** Its conclusions identify a pullback of a colimit (DESC-univ), or the fibres of a family over a colimit (DESC-glue, DESC-or, DESC-tr). No INIT conclusion has that form, and §3 below gives models in which INIT holds and descent fails.
- **Coinductive objects are not INIT instances.** Final models of copositive contexts are unsound in general (§9.3). Streams are derivable from INIT and the closed structure; general M-types need DESC-grpd as well (§5).

Status tags follow `conventions.md`: [proved here], [sketch], [agda], [recall].

---

## 1. The two jobs, stated precisely

**INIT.** Its conclusions are INIT-form (μΔ and the generic model η), INIT-J1 (rec_σ : μΔ → A) and INIT-J2 (cells between model morphisms *out of* μΔ). Dependent elimination (Theorem D of `higher-inductive.md`) is also a map out of μΔ: a section of a family p : E → μΔ that is **already given**. INIT never computes a pullback E ×_{μΔ} Y, and it never computes the fibres of a family.

**DESC.** Its conclusions are:
- an invertible comparison into a pullback (DESC-univ: colim_k (D_k ×_X E) → E);
- a family over a colimit with **prescribed fibres** and prescribed transport (DESC-glue, DESC-or, DESC-tr);
- uniqueness of such families (DESC-uni).

The total space of a glued family always exists without DESC. Over X = colim D, the colimit of the total spaces E_k is an object over X, and with INIT over a base (§9.3) it is even an initial model: μ(Y over X; c_k : E_k → Y over ι_k; cells for the gluing). What INIT cannot supply is the **identification ι_k*(colim E) ≃ E_k**. Its inverse is a map out of a pullback of μΔ, and pullback is not one of INIT's operations.

**Why "INIT is stable under pullback" cannot be one uniform clause.** It would say that g*(μΔ) is the initial model of the pulled-back context, for every g. That is false in Cat_ω. [2] is the free category on the graph 0 → 1 → 2 (an R-A, hence INIT, instance), and pulling it back along {0 < 2} → [2] does not give the free category on the pulled-back graph ([agda] `CaTTExp.Descent.PushoutNotUniversal`). DESC-univ is the stability statement restricted to cocartesian fibrations, the class for which it holds (Loubaton Thm 3.2.3.15). So the restriction lives in DESC, not in INIT.

## 2. INIT is not derivable from DESC [recall: ledger F10h]

Researcher answer verified 2026-11-22 (`conjectures/answered/universe-free-initial-models-r2-2026-11-22.md`). A model with finite limits, finite colimits, full finite descent and DESC-tr has no initial model for (X, a : A → X, l : X ×_{X×X} X → X). ℕ alone is a theorem of DESC (ΩS¹ with the Sattler–Wärn sign construction), but which contexts descent proves is undecidable.

Non-recursive cell constructors need neither rule: by Theorem A of `higher-inductive.md` they are finite colimits, which the base rules already have. INIT is needed for **recursive** constructors (ℕ, lists, W-types, truncations, the squash constructor, families defined by induction over a base).

## 3. DESC is not derivable from INIT [proved here, sketch; agda shadow]

**Theorem 1.** Take all rules of chapters 1–9 except DESC (with INIT, INIT over bases, the h-level clauses, the closed structure, GB-shape, L-× and dcoh_S). DESC is not derivable from them. More precisely, each of the following is underivable:
1. disjointness of coproducts (T-coprod's disjointness half, a theorem of DESC-grpd);
2. ΩS¹ ≃ ℤ, Hom_{⟦L⟧}(x, x) ≃ ℕ for the loop L, and more generally T-graph's computation of homs (encode–decode, §9.4);
3. effective quotients (EX).

The proof gives three locally discrete models. In each one INIT holds and the stated clause fails.

**The common pattern.** Let 𝒱 be a locally presentable, cartesian closed 1-category. Give it **discrete homs**: ambient cells of dimension ≥ 2 are identities, and the internal cells of every object are identities (⟦Dᵏ⟧ ↦ 1). This is the pattern of the verified Pos model (`conjectures/answered/non-derivability-2026-11-18.md` §1, V1–V2). Then the non-DESC rules hold:
- *Limits, colimits, lax and pseudo versions.* A lax comparison cell exists exactly when its boundary maps are equal, so lax colimits and cotensors are ordinary ones ([⟦D⟧, C] = C).
- *R-A and the free objects of chapter 7.* ⟦Γ⟧ = the set of 0-generators modulo the endpoints of 1-generators, as in V2 (in Model B below: 1 if Γ has a 0-generator, else 0).
- *Gray structure (chapter 8).* ⊗ = ×, A\B = B/A = the exponential. Every template of GB-cut and GB-dcut is a bijection of hom-sets, or a cell between parallel identities.
- *Markings (chapter 3), filler tactics, dcoh_S.* Every cell of dimension ≥ 1 is an identity, so every positive rule that asks for a cell between parallel things holds. Every rule of chapters 1–9 is positive, so none of them forces a non-identity cell.
- *h-levels.* Every object is trunc 0. T-ctr and T-hom⁻ at n = −1 hold, because trunc −2 (declared and certified) forces C ≅ 1.
- *INIT.* A model of a positive context Δ is a 𝒱-object with structure maps satisfying the equations its cell variables impose (a cell between parallel maps becomes an equation). The category of models is cut out of a presentable category by inserters and equifiers of accessible functors, so it is presentable, and its forgetful functor preserves limits and is accessible [recall: Adámek–Rosický 2.78, 2.72; the same argument as the verified INIT soundness answer]. So an initial model exists. Strong model morphisms are strict homomorphisms (invertible cells are equalities), so INIT-J2 is uniqueness of the homomorphism, and the higher clause is trivial. INIT over bases works the same way in 𝒱/B.

What fails is DESC, which is the one rule that says more than "some object exists with some maps out".

**Model A: 𝒱 = Set (descent fails at non-trivial gluing).** Set is a topos, so colimits are universal (DESC-univ holds) and quotients are effective (EX holds). But gluing along a non-identity automorphism fails:
- S¹ = μ(X, b : ⊤ → X, l : b → b, l inv) is the point, because l is forced to be an identity. Hence ΩS¹ = Hom_{S¹}(b, b) = 1.
- ℤ = μ(X, z : ⊤ → X, s : X → X inv) is the integers.
- So ΩS¹ ≄ ℤ.
- DESC-glue for the descent data (ℤ, suc) over S¹ = coeq(⊤ ⇉ ⊤) has no solution: transport along the coequalising cell is the identity, so it cannot be suc.

The same model kills Hom_{⟦L⟧}(x, x) ≃ ℕ, where ⟦L⟧ = 1 so that hom is 1, while INIT's ℕ is ℕ. [agda] `CaTTExp.Descent.InitNotDesc` Part I checks `S¹-initial`, `ℤ-initial`, `ΩS¹≄ℤ` and `no-glue-ℤ`.

**Model B: 𝒱 = 2 = {0 < 1}, truth values (descent fails at disjointness).** A complete Heyting algebra is a locally presentable, cartesian closed small category [recall]. Here ⊤ = 1, ∅ = 0, ⊔ = ∨, × = ∧, and initial models are least prefixed points (Knaster–Tarski). Universality holds (frame distributivity), but ⊤ ×_{⊤⊔⊤} ⊤ = 1 ≠ 0, so the coproduct injections are not disjoint. DESC-grpd's gluing of (⊤ over the first summand, ∅ over the second) has no solution. [agda] `InitNotDesc` Part II checks `lfp-pre`, `lfp-least` and `≤-prop` (INIT-form, J1 and J2 for a single operator), `distrib` (binary coproducts), `not-disjoint` and `no-glue-coprod`.

**Model C: 𝒱 = Pos (descent fails at universality and effectiveness).** This is the verified model of `non-derivability-2026-11-18.md` §1. EX fails there. The [2]-pushout is not stable under pullback ([agda] `PushoutNotUniversal`), and every map is a "cocartesian fibration" in this locally discrete model, so DESC-univ fails. Pos is locally presentable, so INIT holds by the common pattern. This upgrades the old Q3 result (EX independent of R-A and Trunc) to EX independent of all of INIT.

**Which part of descent is irreducible.** Model A satisfies INIT and universality but not gluing. So the content INIT cannot reach is **effectiveness**: families over a colimit may be glued from fibres along *equivalences*, including non-trivial ones. That is exactly the job univalence does in HoTT (the universal cover of S¹ via ua(suc)). Universality alone could be read as "INIT objects are stable under pullback along cocartesian maps", but it would not remove DESC-glue.

## 4. Worked examples: which rule each construction needs

| Construction | Needs | Why |
|---|---|---|
| ℕ, lists, W-types, ‖A‖_n, free objects, recursive HITs, directed HITs | INIT | maps out of a recursively generated object |
| non-recursive HITs (S¹, spheres, suspension, torus, directed circle) | neither (finite colimits); INIT restates their universal property | Theorem A, `higher-inductive.md` |
| dependent elimination into a **given** family | INIT (Theorem D) | a section is a model morphism out of μΔ |
| families over S¹ defined by a fibre and an automorphism (universal cover) | DESC-glue | prescribed fibres; fails in Model A |
| true ≠ false, disjoint and universal coproducts (T-coprod) | DESC-grpd | fails in Model B |
| effective quotients (EX) | DESC-grpd, DESC-tr, plus INIT for ‖–‖₀ | fails in Model C |
| lax colimits as Grothendieck constructions (G, G⁺) | DESC-glue, DESC-or, DJ | fibres of a glued fibration |
| ΩS¹ ≃ ℤ, Hom_{⟦Γ⟧}(a, b) ≃ paths (T-graph, T-loc) | **both** | INIT for ℤ / the path set and for decode; DESC for the code family; fails in Model A |
| object-valued recursion R-U (fibres U_{node(ts)} ≃ ∨ ΣU_{t_j}) | **both** | INIT over Θ₀ builds U; DESC-grpd computes its fibres |
| streams ℕ\B (all B, directed too) | INIT + closed structure | §5 |
| M-types (non-wellfounded trees) over sets | INIT + DESC-grpd + closed structure [sketch] | §5 |

**Example (π₁ of the circle, step by step).** INIT gives S¹, ℤ and decode: rec of the model (Hom(b, –) over S¹) yields ℤ → ΩS¹. It also gives the dependent eliminator used to check that decode ∘ encode ≅ 1. Encode needs a family C → S¹ with fibre ℤ over b and transport suc around l. INIT over the base S¹ can build μ(Y : grpd over S¹, y₀ : ⊤ → Y over b), which is the free family on a point (= b ↓ S¹ by DJ). But computing its fibre is the very theorem being proved. DESC-glue instead builds C with fibre ℤ **by construction**. Model A shows no other route exists.

## 5. Coinductive objects (checking the premise)

**Not an instance of INIT.** INIT's soundness needs targets that preserve limits, and gives left adjoints. Final coalgebras are the dual (right adjoints), and §9.3 already records that the dual rule (final models of copositive contexts) is unsound: the right adjoint to base change along the non-exponentiable {0<2} → [2] does not exist. Nor is a coalgebra structure X → B × X a positive context. B × X violates the target condition (a constant other than ⊤), and even ignoring that, its initial model is ∅. So coinductive types are not a special case of INIT. Some of them are **derivable** from INIT plus other rules:

**Prop S (streams) [proved here, sketch].** For any object B, Str B := ℕ\B with head = evaluation at zero and tail = precomposition with succ is the final coalgebra of X ↦ B × X (strong morphisms, all levels). It uses only INIT(ℕ) and chapter 8.

*Proof.* −⊗C is left adjoint to (−)/C (right evaluation row), and ⊤ ⊗ C ≃ C (GB-shape at D⁰). A left adjoint L with L(⊤ ⊔ X) ≅ C ⊔ L(X) carries the initial (⊤ ⊔ –)-model to the initial (C ⊔ –)-model: model maps L(ℕ) → (Y, c, s) transpose to model maps ℕ → (Y/C, ĉ, s/C), and GB-cut at every n transposes the cells. So ℕ ⊗ C = μ(X, c : C → X, s : X → X).
- *Corecursion.* Given a coalgebra (C, h, t), rec of the model (C, 1, t) gives it : ℕ ⊗ C → C. Then h ∘ it is a multimap (ℕ, C ▸ B), and the left row turns it into f : C → ℕ\B. The two coalgebra cells come from rec's computation cells.
- *Uniqueness.* A coalgebra morphism g : C → ℕ\B transposes to ĝ : ℕ → B/C, which is a model morphism from ℕ to (B/C, h, t*), where t* is precomposition with t. INIT-J2 makes any two such morphisms invertibly connected, at every level by the cotensor clause. ∎

No DESC is used, since ℕ ⊗ C (not ℕ × C) is what appears. If one wants ℕ × C, identifying it with ℕ ⊗ C at sets uses L-×, and in general it uses DESC-grpd (universality of the coproduct ℕ = ∐ ⊤), which the proof avoids.

**General M-types [sketch; open as F12b].** For a polynomial P(X) = Σ_{a:A} B(a)\X with A, B(a) sets, the terminal chain gives νP = lim_n Pⁿ(⊤) (Adámek's theorem, ω^op-continuity of P; Ahrens–Capriotti–Spadotti, arXiv:1504.02949, in HoTT). The chain's limit needs three things:
- the family n ↦ Pⁿ⊤ over ℕ, built by INIT over the base ℕ, whose fibres are computed by Lambek plus DESC-grpd, as for R-U;
- its product over ℕ (R-cot⁺ over a set base, which uses DESC-grpd and INIT);
- ω^op-continuity of Σ_a, which is universality and disjointness of coproducts, i.e. DESC-grpd.

So general coinductive types use **both** rules. Model B suggests that DESC-grpd is really needed here: Σ_a over a non-disjoint coproduct does not commute with connected limits. But in a complete lattice greatest fixed points exist anyway, so Model B is not a countermodel. Whether M-types can avoid DESC is open. Directed M-types (A, B(a) non-discrete) are also open.

## 6. Literature

That DESC does not follow from INIT is the higher, rule-level form of a standard fact. Locally presentable categories have initial algebras for accessible functors (Adámek–Rosický), while descent characterises toposes among them (Lurie, HTT Thm 6.1.3.9, for (∞,1)). Sets and frames are presentable and fail higher descent. No new conjecture arises, so nothing is sent out.

## 7. Open items

| Row | Item | Owner |
|---|---|---|
| F12 | DESC vs INIT: neither derivable (this note) | this thread (done) |
| F12a | Agda shadow `CaTTExp.Descent.InitNotDesc`: independent honesty review passed with nits, fixed | this thread (done) |
| F12b | Coinductive objects: Prop S in Agda (abstract interface), M-types (§5) at sketch level checked, whether M-types need DESC, directed M-types | "Build coinductive objects from initiality" thread |
