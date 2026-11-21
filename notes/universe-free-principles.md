# Closing the universe-free rule list (F10)

*Design notes, 2026-11-21. Owner: thread "Replace ad hoc rules with general principles" (ledger F10). Companion to `ordinary-math.md` (where every rule discussed here was introduced) and `spec/09-ordinary-math.md`. Fixed constraints: no universes; universal properties witnessed by cells; rule classes in the style of published CaTT variants; most general version first. Anthony's additional direction (2026-11-21): impredicative definitions do not need an explicit universe (System F), and an adaptation of (co)end calculus is welcome.*

*Markers as in the other notes. **[paper]**: checked against the cited source this session (abstract or statement level, said where it matters). **[recall]**: background knowledge, not re-checked. **[proved here]**: a proof written out in this note. **[conj]**: unproved, with an attempt here and, where the design hinges on it, a researcher problem. **[proposal]**: a design choice. **[agda]**: machine-checked in `src/`.*

---

## 0. Summary

Without universes, the rule list for "ordinary mathematics" has grown one rule at a time: R-U, EX, Trunc_n, T-coprod (disjointness), G, DJ, R-A⁺, G⁺, R-cot⁺, and the function-set rows GB-shape and L-×. This note sorts the list by **what job a universe would have done** and finds that the universe-shaped rules do only two jobs, each of which one general schema covers.

| Job a universe does | Rules on the list doing that job | General schema proposed here |
|---|---|---|
| **Exactness**: say what maps *into* a colimit, or pullbacks of a colimit, look like ("encode–decode") | EX, T-coprod and disjointness, G (fibres and transport of lax colimits), G⁺, the fibre clauses of R-U | **(DESC)** descent for cocartesian fibrations, plus descent for all maps along groupoid-indexed colimits |
| **Construction**: build an object by a universal property *out of* it, including object-valued recursion | Trunc_n, R-A, R-A⁺, ℕ (route I), lists, W-types, R-U, Θ as an object | **(INIT)** every strictly positive finite context has an initial model; read impredicatively, this is a System-F quantifier `∀Δ. X` with naturality |
| Representability (Yoneda) | DJ | none new: DJ is a candidate theorem of the limit rules (Riehl–Verity prove Yoneda from limit axioms only), **[conj]**, §5 |
| Not universe-related | GB-shape, L-× | already instances of one schema, the chapter 8 row table (`spec/08`, F.7.4); out of F10's scope, §6 |

With DESC and INIT, every rule in F10's list is either an instance of one of the two schemata or a candidate theorem; §7 gives the status of each. Two schemata are a **fixed, finite** list: a new inductive object, quotient, truncation or recursively defined family is a new *instance*, never a new rule. The open points are semantic (does Cat_ω satisfy the schemata in the stated generality?) and are sent out as one general researcher question (§8).

Candidate (b) of the ledger, a W-types-over-a-base schema, is the special case of INIT for polynomial contexts. It cannot be derived from colimits alone (§4.1): building the Adámek tower already needs object-valued recursion. So INIT is the most general form of (b) (standard 4).

---

## 1. What a universe does, and why the list kept growing

A universe 𝒰 gives three things at once:
1. **Families by recursion.** A map `B → 𝒰` is a family over B, and recursion into 𝒰 defines families whose fibres are computed by a formula (U_T = ⟦T⟧ in R-U; `x ↦ R(x, –)` in the HoTT proof of effectiveness).
2. **Descent.** Univalence makes families over a colimit the same as compatible families over its pieces (Rezk: descent is equivalent to the existence of univalent object classifiers for bounded classes; Rijke's thesis gives the type-theoretic version for pushouts) **[recall; Rezk's theorem number not re-checked, see §2]**.
3. **Impredicative constructions** (with an impredicative 𝒰): truncations, quotients and inductive types as System-F encodings (Awodey–Frey–Speight).

Each rule on F10's list replaced one *use* of one of these, at one place. That is why the list grows. Replacing the three capabilities themselves, without the object 𝒰, gives (1)+(3) as INIT and (2) as DESC.

---

## 2. Literature (standard 2)

- **Descent and local classes.** Rezk, *Toposes and homotopy toposes* (v0.15): descent (§6.5, properties P1, P2), with the equivalent forms "homotopy colimits commute with homotopy pullback", "coproducts are disjoint" and "groupoid objects are effective" (§6.8) **[paper, partly via summary]**. The equivalence with local classes and object classifiers is in the later sections, not re-read here **[recall]**. Lurie HTT 6.1.3.9 is the ∞-topos version **[recall]**.
- **van Kampen colimits.** A colimit is van Kampen when the self-indexing `x ↦ 𝒞/x` sends it to a limit (Sobociński–Heindel; nLab *van Kampen colimit*) **[paper]**. Lextensive = coproducts van Kampen; no statement there about which colimits in Cat are van Kampen.
- **Cat is not a topos.** Ayala–Francis, *Fibrations of ∞-categories* (Higher Structures 4, 2020), Example 1.6: `{0<2} → [2]` is not exponentiable, because base change along it does not preserve the pushout `{0<1} ⊔_{1} {1<2} ≃ [2]` **[paper]**. Their Main Theorem 1 (Thm 0.8): the flagged ∞-category Corr classifies exponentiable fibrations; Thm 0.9: the classifying map factors through Cat exactly for locally cocartesian fibrations **[paper]**. Exponentiable = base change is a left adjoint (Def. 0.7), the homotopy-invariant form of Conduché's condition (Lemma 1.11) **[paper, via summary for Lemma 1.11]**.
- **Cocartesian fibrations descend.** Sattler–Wärn, *A synthetic construction of universal cocartesian fibrations* (arXiv:2603.28688): "cocartesian fibrations descend along cocommas, sequential colimits, and localisations" (Thm 5.7, Lemmas 6.1–6.2); from this they construct directed univalent cocartesian fibrations (Thm 7.7) and *derive* straightening (Thm 8.1). They assume that left fibrations descend along pushouts (§2.10) **[paper, intro and statements]**. This is the (∞,1) version of exactly the move this note proposes: straightening (our G) as a consequence of descent.
- **Cocartesian = exponentiable + locally cocartesian.** Gepner–Heine, *Colimits in oriented category theory* (arXiv:2608.02592), Thm 1.8.11 (= 4.7.18), for (∞,∞)-categories **[paper]**. So base change along a cocartesian fibration has a right adjoint and preserves colimits. Loubaton (arXiv:2406.05425): Thm 2.2.2.10 (base change along a discrete Conduché functor preserves colimits), Thm 3.2.3.15 (the same for classified left cartesian fibrations), Thm 4.1.4.2 (lax Grothendieck construction) **[paper]**.
- **Impredicative encodings need naturality.** Awodey–Frey–Speight (arXiv:1802.02820): System-F encodings lack η; restricting to the subtype cut out by a naturality condition gives the correct universal property for ℕ, sums, ‖A‖₀, W-types, and (§5) 1-types such as S¹; no univalence is used, one impredicative universe is **[paper; §5–6 via summary]**. Paré–Román, *Dinatural numbers* (JPAA 128, 1998): ordinary dinaturals `X^X → X^X` on Set are **not** the numerals (Johnstone's and Freyd's examples; a proper class), but Barr (strong) dinaturals are exactly the iterates `f ↦ fⁿ`, Prop. 1 **[paper]**. Piróg–Sieczkowski (arXiv:2510.06777): ends of strong dinaturals give generalised codensity monads, which exist only under conditions (Def. 3.1, Thm 4.2, Thm 6.4) **[paper]**.
- **Elementary higher toposes.** Rasekh (arXiv:1805.03805) takes universes as axioms; elementary toposes satisfy weak descent without universes (Prop. 1.49, citing Mac Lane–Moerdijk) **[paper]**. Nothing there constructs truncations or ℕ without universes.
- **Yoneda from limits.** Riehl–Verity, *Fibrations and Yoneda's lemma in an ∞-cosmos* (arXiv:1506.05500), Thm 6.0.1, proved in an arbitrary ∞-cosmos, whose axioms have no colimits; the intro says most results hold in an abstract homotopy 2-category with weak comma objects **[paper for the statement and axioms; the proof in §6.2 was not read]**.

---

## 3. Candidate A: descent (DESC)

### 3.1 The schema [proposal]

All pieces are finite syntax over objects, maps, pullbacks and cocartesian-fibration structure (`ordinary-math.md` §4.6: a left adjoint ℓ to `[⟦D¹⟧, E] → p ↓ B` with invertible unit). Let `D` be a finite diagram (a substitution into a finite context, as for every colimit rule) with colimit `X = colim D` and legs `ι_k : D_k → X`.

```
(DESC-pb)   p : E → X cocartesian,  g : Y → X   ⟹   g*p : Y ×_X E → Y cocartesian
(DESC-univ) p : E → X cocartesian   ⟹   the comparison  colim_k (D_k ×_X E) → E  is invertible
(DESC-glue) cocartesian p_k : E_k → D_k for each k, and for each arrow u : k → k' of the
            diagram an invertible cell  E_k ≃ D_k ×_{D_k'} E_k'  over D_k (with the
            higher compatibility cells the diagram's shape requires)
            ⟹  p : E → X cocartesian  with invertible  ι_k*p ≃ p_k  compatible with the data
(DESC-uni)  two such gluings are connected by an invertible cell, at every level (uni-style)
(DESC-grpd) D indexed by a groupoid (in particular a coproduct, D indexed by a finite set):
            the same four clauses with "cocartesian" deleted, for every map p
```

DESC-pb is a theorem of the definition (Riehl–Verity prove pullback stability of cartesian fibrations in any ∞-cosmos, FYL §5.2) **[paper, statement]**, listed for completeness. DESC-univ is "base change along a cocartesian fibration preserves colimits". DESC-glue and DESC-uni are effectiveness. DESC-grpd is extensivity generalised from coproducts to groupoid-indexed colimits.

Because the localisation `E[W⁻¹]` (§6.1 of `ordinary-math.md`) and the sequential colimit (§6.2) are finite pushouts, DESC for finite diagrams already covers object-indexed colimits.

### 3.2 Where descent holds in Cat_ω, and where it fails

- **Fails for arbitrary maps and pushouts.** Pull the pushout `[2] = {a0<a1} ⊔_{a1} {a1<a2}` back along `f : [1] → [2]`, `b0 ↦ a0, b1 ↦ a2`. The pieces pull back to `{b0}`, `{b1}` and `∅`, whose pushout is the discrete `{b0, b1}`; the pullback of `[2]` is `[1]`. **[agda]** `CaTTExp.Descent.PushoutNotUniversal`: the pullbacks of the pieces, that the two-point coproduct has no order isomorphism to `[1]` (so the comparison is not invertible), and that f fails Conduché factorisation lifting (`a0 ≤ a1 ≤ a2` has no lift). The fact that `[2]` is that pushout in Cat is cited (Ayala–Francis Ex. 1.6), not encoded. So "all colimits are van Kampen" is false in Cat_ω, and DESC must be restricted.
- **Holds for cocartesian fibrations.** Semantically, `Cocart(X) ≃ Fun(X, Cat_ω)` (straightening), and `Fun(–, Cat_ω)` sends colimits to limits; so DESC-glue and DESC-uni hold. DESC-univ holds because cocartesian fibrations are exponentiable (Gepner–Heine Thm 1.8.11) **[paper for (∞,∞); for (∞,ω) via Loubaton Thm 4.1.4.2 and 3.2.3.15, whose hypotheses ("classified") must be checked: §8 Q1]**. Sattler–Wärn prove descent along cocommas, sequential colimits and localisations in the (∞,1) case **[paper]**.
- **Holds for all maps along groupoid-indexed colimits.** For a groupoid K, `colim_K F` is the Grothendieck construction `∫F` itself (cocartesian lifts of invertible arrows are invertible, so nothing is localised), and every map into an object over a groupoid is a cocartesian fibration up to equivalence. So `Cat/(colim_K F) ≃ lim_k Cat/F(k)` **[proved here, sketch, relative to straightening]**. Coproducts are the case K discrete: this is the extensivity `ordinary-math.md` §2.3 already uses for T-coprod.
- **Under L (lax ambient).** The intended model of spec 0.1 is the oriented category 𝒦. DESC is about the underlying (∞,1)-category of objects and maps, plus cocartesian structure, which is stated with cotensors and commas. Whether the gluing cells should be lax (oriented descent, Gepner–Heine's *Fibrations in oriented category theory*, arXiv:2607.18418, which builds the Grothendieck construction for oriented categories) is part of §8 Q1. Standard 4 says to state the oriented version once it is known to hold.

### 3.3 What DESC derives

**T-coprod's disjointness [proved here].** The summand inclusion `i_A : A → A ⊔ B` is a cocartesian fibration (no arrow leaves A). DESC-grpd for the coproduct, applied to the family that is `id_A` over A and `∅ → B` over B, gives a map `E → A ⊔ B` with `E ×_{A⊔B} A ≃ A` and `E ×_{A⊔B} B ≃ ∅`; by DESC-grpd's universality `E ≃ A ⊔ ∅ ≃ A` and the map is `i_A`. So `A ×_{A⊔B} B ≃ ∅`. ∎

**T-coprod itself [proved here, from DESC-grpd].** `ordinary-math.md` §2.3 proves `A ⊔ B trunc n` from "coproducts are universal and disjoint". DESC-grpd's universality applied to any `c → A ⊔ B` gives `c ≃ c_A ⊔ c_B`, and disjointness is above. So T-coprod is a theorem of DESC-grpd. ∎

**EX, effectiveness of quotients [proved here, sketch, relative to DESC and the truncation clause below].** Let X be a set, `R ↪ X × X` an equivalence relation, `C := coeq(r₀, r₁)` (pseudo) and `Q := ‖C‖₀`, `q : X → Q`. The HoTT proof (encode–decode against the family `x ↦ R(x, –)`) uses univalence in exactly one place: to define a family over Q. DESC replaces it.
1. *A family over X × C.* `X × –` preserves colimits (exponential law (E), which `ordinary-math.md` assumes), so `X × C = coeq(1 × r₀, 1 × r₁)`. Give the family `R → X × X` over the vertex `X × X` and, over `X × R`, the descent cell `R(x, r₀ρ) ≃ R(x, r₁ρ)`, composition with ρ and with its symmetric (maps between propositions in both directions, so invertible by T-fill). The bases are sets, so DESC-grpd applies with no cocartesian condition. It glues to `P → X × C` with fibre `R(x, y)` over `(x, c y)`.
2. *Down to X × Q.* The fibres of P are propositions. **Clause (DESC-tr):** for a groupoid Y, families over Y with n-truncated fibres descend uniquely along `Y → ‖Y‖_{n+1}`. In ∞-topos theory this is the statement that n-types are classified by an (n+1)-type **[recall]**; semantically in Cat_ω it is the same statement in spaces, since C is a groupoid (colimits of groupoids are computed in spaces, the inclusion having a right adjoint, the core). It is a descent statement, so it belongs in DESC. It gives `P' → X × Q`.
3. *Encode–decode.* `refl` gives a point of `P'` over `(x, q x)`. For `(x, y)` with `q x ≅ q y` (a point of `X ×_Q X`), transport (P' is a family over a set, so transport along the cell `q x ≅ q y` is part of the descended family) gives a point of `R(x, y)`. This is a map `X ×_Q X → R` over `X × X`; both are subobjects of `X × X` (Q is a set, R is a mono), so it is inverse to the canonical `R → X ×_Q X`. ∎

So EX moves from "a genuine rule" (`ordinary-math.md` §5.3, with a countermodel in posets) to an instance of DESC. The poset countermodel fails DESC; that is consistent, since it was a countermodel to EX from limits, colimits, R-A and Trunc, without descent.

**G, the Grothendieck principle [proved here, sketch, following Sattler–Wärn].** For a diagram γ over a graph shape ⟦Γ⟧, `⟦Γ⟧` is the pushout of its vertices and edges. Over the edge `⟦D¹⟧`, the collage `cyl(γ_f) := (γ_x ⊗ ⟦D¹⟧) ⊔_{γ_x ⊗ {1}} γ_y → ⟦D¹⟧` is a cocartesian fibration with fibres γ_x, γ_y and transport γ_f (**base clause G₁**). DESC-glue glues the collages to `π : E → ⟦Γ⟧`; DESC-univ (along π) shows `E` is the colimit of the collages, which is the lax colimit of γ: G-fib and G-fibre. G-transport is G₁'s transport, and G-nat is DESC-uni applied to the glued map. So G reduces to its **edge case G₁**, plus DESC. G₁ itself is a statement about one collage over one arrow. Sattler–Wärn derive the analogous base case from descent along localisations and cocommas, so G₁ is a candidate theorem as well **[conj]**; until then G shrinks to G₁.

**G⁺ [proposal; proved here, sketch].** Object-labelled edges are suspensions `ΣB_e = ⊤ ⊔ ⊤ ⊔_{B_e ⊗ ∂⟦D¹⟧} B_e ⊗ ⟦D¹⟧`. DESC-glue over that pushout reduces G⁺ to the collage over `B_e ⊗ ⟦D¹⟧` of the map `B_e × C_v → B_e × C_w` over `B_e`. That is G₁ in the slice over `B_e`, so G₁ should be stated relative to a base (most general version, standard 4); the relative statement is part of §8 Q1.

**R-U's fibre clauses [proved here, relative to INIT].** If U is built by INIT (§4.3), its fibre over `node(ts)` is computed by Lambek's lemma plus DESC-grpd over the set Θ₀ (pullback along a point of a set preserves the colimits in Φ). No separate fibre clause is needed.

---

## 4. Candidate C: initial models of positive contexts (INIT), the impredicative quantifier

### 4.1 Why candidate (b) cannot come from colimits alone

The ledger's candidate (b) is "initial algebras of polynomial functors on fibrations (W-types over a base)". The obvious derivation is Adámek's: `μΦ = colim_k Φᵏ(∅)`. But the chain `k ↦ Φᵏ(∅)` is an ℕ-indexed family of objects with `E_{k+1} = Φ(E_k)`. Building it is object-valued recursion over ℕ, the very thing (b) is meant to provide. A sequential colimit needs its family as input (`ordinary-math.md` §6.2: a total object `X → N` with `t : X → X`), and for `Φᵏ(∅)` the total object is `∐_k Φᵏ(∅)`, which is again `μ` of a related functor. So (b) is a construction principle and has to be a rule. The question is only which rule is most general. **[proved here, as an observation about the construction; not a non-derivability theorem]** A non-derivability proof would need a model of everything else in which some positive context has no initial model; listed as §8 Q3.

### 4.2 The schema [proposal]

A **positive context** is a finite context Δ (the usual context grammar of chapters 1–9: object variables, map and cell variables, marks such as `⋆^{≤n}` and `inv`) together with a distinguished object variable X, such that X occurs *strictly positively*:
- in the **target** of every variable's type, X appears only as X itself or under colimit-preserving operations (coproducts, pushouts, ⊗ with a fixed object, `Σ`);
- in the **source** of every variable's type, X appears only under accessible covariant operations (finite limits including pullbacks over fixed objects, colimits, ⊗, cotensors `[A, X]` by objects A not mentioning X);
- X does not appear contravariantly anywhere (no `[X, –]`, no `Hom` with X in the first argument).

The check is syntax-directed and decidable, like strict positivity for inductive types.

```
(INIT-form)  Δ positive in X   ⟹   μΔ : ⋆   and a model  η : Δ[μΔ/X]          (the generic model)
(INIT-J1)    Γ ⊢ σ : Δ[A/X]   (a model with carrier A)
             ⟹  rec_σ : μΔ → A  and an invertible cell  rec_σ ∘ η ≅ σ          (a model morphism)
(INIT-J2)    two model morphisms h, h' : μΔ → A from η to σ
             ⟹  an invertible cell  h ≅ h'  of model morphisms
(higher)     derived, as for Trunc (`ordinary-math.md` Prop. 5.3(2)) and the recursor
             (Prop. 4.2): a level-k cell between model morphisms is a model morphism into
             the cotensor [⟦Dᵏ⟧, A] with the pointwise model.
```

"Model morphism" is itself a finite context (the arrow context `Δ^{→}`: two copies of Δ, a map between the carriers, and a cell per variable of Δ, invertible where the variable's mark requires). So the whole schema is a substitution-stable rule of the shape of R-A's `uni`, quantified over contexts, as R-A is quantified over pasting contexts.

**The impredicative reading (Anthony's System-F suggestion).** Write `∀Δ. X` for μΔ. A map `W → ∀Δ. X` is the same as a family of maps `W → A`, one for each model `(A, σ)`, natural along model morphisms. That is the limit of the forgetful functor from models to the ambient, i.e. the end of the codensity form `∫_{(A,σ)} A`, and System F's `∀X. (ΦX → X) → X` is the case `Δ = (X : ⋆, a : ΦX → X)`. Two points from the literature fix how it must be stated:
- **Naturality is essential.** The plain System-F encoding, i.e. a product over all A, lacks η (AFS). The plain end over *dinatural* families is wrong already for ℕ in Set: the dinaturals `X^X → X^X` form a proper class (Paré–Román §2.2). The *strong* (Barr) dinaturals are exactly the numerals (Paré–Román Prop. 1). The model-morphism naturality in INIT-J2 is the strong-dinaturality condition; it is built into the rule, not left to a meta-level parametricity theorem.
- **No universe is introduced.** INIT binds an object variable inside the *rule* (as `coh` binds a pasting context), not in a term or type: no term has type ⋆, nothing ranges over "all objects" as an object, and `∀Δ. X` is an ordinary object. Spec §0.2, as reworded under S15 (PR #397), allows exactly this: a binding former in Lawvere's style that binds an object variable in a premise, states its universal property by cells, and makes no judgment a term. INIT fits it as written.
- **Lax by default.** Model morphisms carry a cell per variable of Δ, invertible only where Δ's marks require it. So the unmarked schema is the lax one (lax ends, standard 4), and the pseudo version is recovered by marking Δ's cells `inv`.

**Why "initial model" and not a general end.** Ends `∫_A G(A, A)` for arbitrary mixed-variance G are large limits that need not exist (Piróg–Sieczkowski Def. 3.1: "may or may not exist"). The codensity form over models of a positive context is the case where the end is the carrier of an initial object, and there existence is a theorem about accessible functors on a presentable category (Adámek–Rosický) **[recall]**, extended to finite contexts in §8 Q2. The dual, **final models** of copositive contexts (coends, `∃Δ. X`), would give final coalgebras and right adjoints such as R-cot⁺ and the cartesian `[A, B]`. It is **unsound in general**: the right adjoint to base change along the non-exponentiable `{0<2} → [2]` (§3.2) does not exist, so the final model of `(W, p : W → [2], e : W ×_{[2]} [1] → B)` does not exist. A final-model schema would need an exponentiability side condition. Recorded, not proposed.

### 4.3 What INIT derives

Each line is an instance: give Δ.
- **R-A and R-A⁺ (free objects on graphs, object-labelled graphs) [proved here].** `Δ = (X : ⋆, x_v : ⊤ → X, e : B_e → Hom_X(x_v, x_w))`. Maps `μΔ → C` are Δ-models in C, which is R-A⁺'s universal property; positivity needs the reformulation in the caveat. *Caveat:* `B_e → Hom_X(x_v, x_w)` has X inside a hom in the *target*. Hom of fixed points is a pullback, a limit, not colimit-preserving. Use the equivalent form with the suspension in the source, `ΣB_e → X` under `x_v, x_w`, which is positive. **[proved here]**
- **ℕ, lists, finitary W-types (route I without per-signature rules) [proved here].** `Δ = (X : ⋆, z : ⊤ → X, s : X → X)` for ℕ; `Δ = (X, n : ⊤ → X, c : B × X → X)` for List(B); `Δ = (X, c_i : B_i × X^{n_i} → X)` for a finitary signature. Theorem 4.6 of `ordinary-math.md` becomes unnecessary as a construction; it stays as a proof that route III already had them.
- **Trunc_n [proved here].** `Δ = (X : ⋆^{≤n}, g : A → X)`. Its initial model is `(‖A‖_n, |–|)`; INIT-J1 and INIT-J2 are Tr-J1 and Tr-J2. The mark `⋆^{≤n}` restricts models to n-truncated carriers, which form a reflective subcategory, so the initial model exists **[recall]**.
- **Object-valued recursion, R-U [proved here, sketch].** Take the base Θ₀ (rose trees, itself an INIT instance) and `Δ = (X : ⋆, p : X → Θ₀, a : Φ_p(X) → X over Θ₀)`, where `Φ_p(X)` is the family over Θ₀ with fibre `∨_j Σ X_{t_j}` over `node(ts)`, built fibrewise from pullbacks over the set Θ₀, iterated wedges and suspensions. X occurs positively (pullbacks in the source, colimits). The initial model is `U → Θ₀`. Lambek's lemma (derivable from INIT-J1/J2 as usual) gives `U ≃ Φ_p(U)`, which with DESC-grpd over Θ₀ is R-U's fibre clause `U_{node(ts)} ≃ ∨ Σ U_{t_j}`. R-U's Θ₁-functoriality (`ordinary-math.md` §6.6(vii)) is a map out of U, i.e. INIT-J1 for a suitable model. So R-U is not a separate rule.
- **Θ as an internal category, el(B), realisation (F5d)** inherit from the above; `ordinary-math.md` §6.6 already reduced F5d to R-U.

### 4.4 Comparison of the construction options (standard 3)

| | (b) W-types over a base | INIT (positive contexts) | small-object argument + compactness |
|---|---|---|---|
| Statement | initial algebras of polynomial endofunctors on slices | initial model of any strictly positive finite context | localisation at a set of maps between finite shapes, as a sequential colimit, plus "finite shapes are compact" |
| Covers ℕ, lists, W-types | yes | yes | no (needs the tower, §4.1) |
| Covers Trunc_n | no (not polynomial) | yes, with the `⋆^{≤n}` mark | yes |
| Covers R-A⁺, R-U | R-U only if Φ is polynomial (it is not: wedges and suspensions) | yes | no |
| New rule shape | one schema over signatures | one schema over contexts, `uni`-shaped | two rules (tower, compactness) |
| Semantic risk | low (Gambino–Kock for polynomial functors in lccc; Cat_ω is not lccc, so even this needs a check) | positivity class must be proved sound (§8 Q2) | compactness is true in Cat_ω, low risk |
| Impredicative reading | partial | exactly System F's `∀X.(ΦX→X)→X` with naturality | none |

The evidence favours INIT: it is the only option that removes every construction rule on the list at once, and (b) is its polynomial special case.

---

## 5. DJ: a candidate theorem of the limit rules [conj]

Riehl–Verity prove the Yoneda lemma for cartesian fibrations (FYL Thm 6.0.1) in any ∞-cosmos, and the ∞-cosmos axioms contain only limits (cotensors by finite simplicial sets, pullbacks of isofibrations, a terminal object). Most of the paper is stated to work in a homotopy 2-category with weak comma objects. The project's limit rules (commas, cotensors by shapes, `uni` at every level) give at least weak 2-universal commas in the homotopy 2-category of the ambient. So DJ-sec and DJ-uni are candidates for theorems of the limit rules, which would remove DJ from the rule list. **Attempt.** The step to transfer is FYL §6.2's proof; it was not read in this session, so the dependency list is not confirmed. The one place to watch is FYL §5.2 ("a somewhat delicate result", pullback stability of cartesian fibrations), which uses the cosmos's strict pullbacks of isofibrations; under P the project's pullbacks are pseudo, which is the invariant version, so this should be the easier direction. Consistency check: `ordinary-math.md` §4.5's countermodel (categories with an auxiliary equivalence relation) has all limits and R-A and kills route III. If DJ follows from limits, then G must fail there, and so must DESC + G₁ (§3.3); which clause fails is not yet checked **[conj]**. Owner: this thread (ledger F10b).

---

## 6. GB-shape and L-× are outside F10

GB-shape (weakening) and L-× (contraction at `grpd_2` targets) are rows of the chapter 8 table: they are instances of the single schema F.7.4, with GB-cut and GB-dcut applied uniformly to every row (`spec/08`, §8.8; `spec/09` §9.6). They do not replace a use of a universe: they say how the Gray tensor relates to the cartesian product, which a universe would not supply either. Their necessity is proved by countermodels (graded and filtered, `spec/09` §9.6). So they do not count against F10's goal. What would shrink them is a statement that makes ⊗ and × agree on a declared class of targets in one rule, of which L-× (maximal class `grpd_2`) already is the general form. No action for this item.

---

## 7. Status of every rule on F10's list

| Rule | Becomes | Status |
|---|---|---|
| EX | theorem of DESC (with DESC-tr) | **[proved here, sketch]**, §3.3 |
| T-coprod, disjointness | theorem of DESC-grpd | **[proved here]**, §3.3 |
| Trunc_n | instance of INIT | **[proved here]** given INIT; INIT's soundness §8 Q2 |
| G | DESC + edge case G₁ | **[proved here, sketch]**; G₁ derivable **[conj]** (Sattler–Wärn's route) |
| G⁺ | DESC + G₁ relative to a base | **[proposal; sketch]** |
| DJ | theorem of the limit rules | **[conj]**, §5, F10b |
| R-A, R-A⁺ | instances of INIT | **[proved here]** |
| R-U (fibres and Θ₁-action) | instance of INIT + DESC-grpd | **[proved here, sketch]** |
| R-cot⁺ (over set bases) | DESC-grpd: `[q, B] := ∐_i [U_i, B]` is already a construction from extensivity (`ordinary-math.md` §6.6(v)); the coproduct over an infinite set is an INIT instance (`Δ = (X, p : X → I, a : … )`) | **[conj]**, needs a check that the coproduct over a set I is an initial model; F10c |
| route I's ℕ, lists, W-types | instances of INIT | **[proved here]** |
| T-graph, T-loc | unchanged for now; candidate theorems by encode–decode once DESC is in (the word family over ⟦Γ⟧ glued by DESC, as π₁(S¹) is computed in HoTT) | **[conj]**, F10d |
| GB-shape, L-× | chapter 8 rows, not universe substitutes | out of scope, §6 |

After this, the list of universe-substitute rules is **DESC (one schema) and INIT (one schema)**, with G₁ and DJ as candidate theorems.

---

## 8. Open questions and researcher problem

The semantic questions are merged into one general prompt (standard 11): `notes/conjectures/outbox/universe-free-descent-and-initial-models.md`. It asks for:
- **Q1 (main).** Descent in `Cat_(∞,ω)` in the most general form: for every small diagram with colimit X, `Cocart(X) ≃ lim Cocart(D_k)` and base change along cocartesian fibrations preserves colimits; the same for all maps along groupoid-indexed colimits; the exact class of van Kampen colimits; and the oriented (lax) version. Or counterexamples marking the boundary.
- **Q2.** Every strictly positive finite context (in the grammar given there) has an initial model in `Cat_(∞,ω)`, with the maximal syntactic class, and a counterexample just outside it.
- **Q3 (fallback).** Non-derivability: a model of finite limits, colimits and DESC with a positive context lacking an initial model.

Ledger entries: F10 (this note), F10a (Agda: descent counterexample, done, honesty review passed), F10b (DJ from limits), F10c (R-cot⁺ as DESC + INIT), F10d (T-graph and T-loc by encode–decode), F10e (spec wording: §0.2 already fits; chapter 9 once adopted). All owned by this thread.
