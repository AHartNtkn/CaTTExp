# Coinductive objects from initiality

*Ledger F12b.* `descent-vs-init.md` §5 shows that final coalgebras are not INIT instances, but that some of them are derivable. This note settles which ones, in Agda where possible, and records what is open.

*Short answer.*
- **Streams and every constant-arity M-type are derivable from INIT and chapter 8, with no DESC.** For any objects A and E (directed or not), νX. A × (E\X) is SnocList(E)\A. Streams are the case without E. [agda, 1-truncated] `CaTTExp.Coinductive.Streams`, `CaTTExp.Coinductive.ConstArity`.
- **Dependent arities (a map p : E → A, a family of arity sets): settled (2026-11-23).** In *coalgebra form*, for P given inductively, they need no DESC (routes 5–6, §4; the conaturals are [agda]). In *dialgebra form* (a terminal p-dialgebra), they are not derivable without universality of finite coproducts (a consequence of DESC-grpd), even for the conaturals, p = 1 → 1 + 1. The countermodel is rectangular bands ([agda] `Coinductive/RectBandNoDialgebra.agda`). Universality restores every map between finite copowers. Researcher answer, verified: `conjectures/answered/dependent-m-types-without-descent-2026-11-23.md`.
- **Anthony's question (2026-11-23): does the HoTT construction hinge on univalence?** No. It hinges on a *universe* (§3).

Status tags follow `conventions.md`.

---

## 1. Prop S: streams [agda, 1-truncated; proved here, sketch at all levels]

**Statement.** Let ℕ = μ(X, z : ⊤ → X, s : X → X) and let B be any object. Put Str := ℕ\B, with
- head := e^ℓ ∘₀ z̄ : (Str ▸ B), evaluation at the point z̄ : ( ▸ ℕ) that GB-shape at D⁰ makes from z;
- tail := curL(e^ℓ ∘₀ s) : (Str ▸ Str).

Then (Str, head, tail) is a final coalgebra of X ↦ B × X. A coalgebra is (C, h : C → B, t : C → C).

**Proof (simpler than the sketch in `descent-vs-init.md` §5; no ⊗ is needed).** Fix a coalgebra (C, h, t). Multimaps k : (ℕ, C ▸ B) correspond to maps g : C → ℕ\B by the left row, and to maps f : ℕ → B/C by the right row. Through these transposes:
- head ∘ g ≅ h ⟺ k ∘₀ z̄ ≅ h ⟺ f ∘ z ≅ h̄, where h̄ = wk(curR h) : ⊤ → B/C;
- tail ∘ g ≅ g ∘ t ⟺ k ∘₀ s ≅ k ∘₁ t ⟺ f ∘ s ≅ t* ∘ f, where t* = curR(e^r ∘₁ t) : B/C → B/C.

So coalgebra morphisms C → Str correspond bijectively to model morphisms ℕ → (B/C, h̄, t*). INIT-J1 gives one, and INIT-J2 makes it unique. ∎

**What is used.** INIT(ℕ), the left and right evaluation rows (GB-cut at n = 0, 1), and GB-shape at D⁰ (weakening, to pass between the element z : ⊤ → ℕ and the point z̄). No DESC, no products, no ⊗, no L-×.

**All levels [sketch].** At level n, the same three steps apply to cells: GB-cut at every n transposes cells of coalgebra morphisms to cells of model morphisms, and INIT's higher clause (model morphisms into the cotensor [⟦Dⁿ⟧, B/C]) gives contractibility. The Agda covers level 1 only.

**Agda.** `src/CaTTExp/Coinductive/Streams.agda`, over the abstract model interface (`Gray/Biclosed/Model`) with the weakening row (`FunSets.Weak`). INIT(ℕ) is a record of assumptions (`INITℕ`), as in `HIT/DependentElim.agda`. Results: `transpose-mor`, `untranspose-mor`, `round-trip-1/2` (the bijection), `corec-mor`, `corec-uni`, `Str-final`. No postulates; checks under `--safe`.

## 2. Constant arities [agda, 1-truncated]

**Statement.** Let A, E be objects and L := μ(X, n : ⊤ → X, c : X ⊗ E → X), the snoc lists on E. Put M := L\A, with head := e^ℓ ∘₀ n̄ and tail := curL(e^ℓ ∘₀ c) : (E, M ▸ M). Then M is a final coalgebra of X ↦ A × (E\X). Here a coalgebra is h : (C ▸ A) together with t : (E, C ▸ C), which by the left row is a map C → E\C.

**Proof.** As in §1, with k : (L, C ▸ A) and the model (A/C, h̄, c′ := curR(e^r ∘₁ t)) of the list context. The tail condition reads k ∘₀ c ≅ k ∘₁ t, both of type (L, E, C ▸ A). ∎

**Orientation (directed case).** No hypothesis on A or E is made: they may be arbitrary (∞,ω)-categories, and E\X is the lax hom. Planarity forces the list to be a **snoc** list: the label of a tree at address ℓ·e is the label at ℓ of its e-subtree. With cons lists the two sides would have inputs in the orders (E, L, C) and (L, E, C), which no rule identifies. The mirror (chapter 8, §8.7) gives the oplax version: νX. A × (X/E) = A/ConsList(E).

**Agda.** `src/CaTTExp/Coinductive/ConstArity.agda`, the same interface and results (`M-final`). The constructor of L is assumed in multimap form (X, E ▸ X). The pair row identifies that with X ⊗ E → X, but the translation is not encoded.

## 3. What the HoTT construction uses

Ahrens–Capriotti–Spadotti, *Non-wellfounded trees in homotopy type theory* (TLCA 2015, arXiv:1504.02949), build (indexed) M-types from ℕ:
- **Univalence:** used directly only in Lemma 5 (being a final coalgebra is a proposition). Elsewhere they use only funext (their §7). Existence and finality do not use univalence.
- **The universe:** the chain W_n := Pⁿ(1) is a family ℕ → U, defined by recursion on ℕ. Lemma 13 (P preserves the chain limit) uses W_{n+1} = P(W_n), which is the computation rule of that large recursion.
- Σ, Π, identity types, and the limit L := Σ_{x : Π_n W_n} Π_n (π_n x_{n+1} = x_n) (Def. 9). Lemmas 11–12 (cochain tuples, shifted chains) use only these and the initiality of ℕ.

**Our rules, item by item.**
- Funext is built in, since equality of maps is cells.
- The chain limit needs no new rule. For a family Y → ℕ, the sections live in ℕ\Y, and compatibility is an equaliser. The earlier sketch's appeal to R-cot⁺ is unnecessary.
- **The universe is what we lack.** Without one, INIT over the base ℕ builds the total space Y → ℕ of n ↦ Pⁿ⊤. Lambek gives Y ≅ z_!⊤ ⊔ s_!(P Y). Reading off the fibres (Y_{n+1} ≅ P(Y_n)) means pulling a coproduct back along a summand. That is universality plus disjointness, i.e. DESC-grpd. Large elimination computes fibres by fiat; DESC computes them by descent.

So the analogy "DESC plays the role of univalence" in `descent-vs-init.md` §3 is right for gluing along equivalences, but for M-types the relevant role is the universe's **classification of families**.

## 4. Dependent arities: what is known and where it stalls

**Formulation without a universe or Π_p.** For p : E → A, the polynomial functor P(X) = Σ_a (p⁻¹a)\X needs a dependent hom Π_p, which our system does not have (R-cot⁺ exists over set bases, and only through DESC-grpd). Uncurrying avoids it. A **p-dialgebra** is (C, h : C → A, t : C ×_A E → C), and a morphism is g : C → C′ over A, commuting with t. When Π_p exists this is exactly a P-coalgebra, and a final one is the M-type. The constant case (§2) is p = π₁ : A × E → A.

**Five routes tried.**
1. *Terminal chain.* Needs the fibres of an INIT family over ℕ (§3), i.e. DESC-grpd.
2. *Address encoding.* Trees as label functions on all snoc lists of E, with inconsistent addresses filled canonically (for example, an inconsistent step stays at the current node). Extending t to E × C needs a case split on whether p(e) = h(c): a decomposition E × C ≅ (C ×_A E) ⊔ complement, which needs decidable equality on A and disjoint universal coproducts (DESC-grpd). Partial label maps L → A ⊔ ⊤ need disjointness as well.
3. *Reduce to the constant case.* Same obstacle: a constant-arity coalgebra on C has to give t a value at inconsistent pairs.

4. *Case analysis by ⊗-distributivity (partial progress) [sketch, needs checking].* For finitely many constructors, P(X) = ∐_{j∈J} A_j × (E_j\X) with J an external finite set, write a coalgebra as c : C → P(C), a map **into** a coproduct, not as a dialgebra. Then every case split the construction needs is a split of an **input** that is a coproduct, and it is available without DESC: ⊗ and \, / are biclosed, so X ⊗ – and – ⊗ X preserve coproducts. Take addresses L = SnocList(∐_j E_j) and labels Lab = (∐_j A_j) ⊔ ⊤, with ⊤ meaning "absent". The step map of the right-row model, (Lab/C, E ▸ Lab/C), is defined by copairing over the shape of c(x) and the shape of e. The candidate M is the equaliser inside L\Lab cutting out the consistent label functions. Transposition plus INIT-J1/J2 then gives existence and uniqueness of coalgebra morphisms C → M, as in §2.
   - **The one step that still needs descent:** M's own structure map M → P(M). To build it, M has to be split along its root label M → Lab, which means pulling the coproduct ∐_j A_j ⊔ ⊤ back along a map. That is **universality** of finite coproducts (the coproduct case of DESC-univ inside DESC-grpd). Disjointness does not seem to be used.
   - With universal finite coproducts, the whole construction appears to go through: dependent M-types with finitely many constructors would follow from INIT + chapter 8 + universal finite coproducts [sketch]. With an internal shape object A (say A = ℕ), comparing shapes needs decidable equality on A, and deriving x = y from eq(x, y) = true seems to need disjointness as well.
   - Universality of finite coproducts holds in all three countermodels of `descent-vs-init.md` §3, but it is **not derivable** (Model D below).

5. *Distributivity instead of universality: the conatural numbers [agda, 1-truncated; proved here].* Checked in `CaTTExp.Coinductive.Conat` (existence `corec-mor`, uniqueness `corec-uni`) over an abstract cartesian closed category with strict equations, coproducts, equalisers and an NNO; no universality or disjointness hypothesis appears in its record. Route 4 needed to split M along its root label. Distributivity of × avoids the split. Setting: a cartesian closed 𝒱 with finite limits, finite coproducts and an NNO (ℕ, 0, s). Write 2 = 1 + 1 with ff = inl, tt = inr. Distributivity gives 2 × 2 ≅ 1 + 1 + 1 + 1, hence ∧ : 2 × 2 → 2 and sel : 2 × Z × Z → Z ("if b then x else y"). Every Boolean identity between such maps then holds, by case analysis on the coproduct *input* 2 × … ≅ … + … .
   - **Carrier.** M ↪ 2^ℕ is the equaliser of u ↦ u ∘ s and u ↦ (u ∘ s) ∧ u, the decreasing sequences. u(n) = tt reads "the value is > n".
   - **Structure map, no split.** head := ev₀ : M → 2, and pred := (– ∘ s) : M → M. out := (! + 1) ∘ δ ∘ ⟨head, pred⟩ : M → 1 + M, where δ : 2 × M ≅ M + M is the distributivity iso.
   - **Corecursion.** For a coalgebra c : C → 1 + C, put χ := (! + !) ∘ c : C → 2 and step : 2^C → 2^C, φ ↦ [ff, φ] ∘ c. The latter is a transpose through 2^C × (1 + C) ≅ 2^C + 2^C × C, by distributivity again. The NNO gives r : ℕ → 2^C. Its transpose C → 2^ℕ lands in M (an induction, below) and is a coalgebra morphism.
   - **Uniqueness.** Let g : C → M be a coalgebra morphism. Post-composing out ∘ g = (1 + g) ∘ c with (! + !) gives head ∘ g = χ, because (! + !) ∘ δ = π₁. Post-composing with [0, 1] : 1 + M → M gives pred ∘ g = [0, g] ∘ c, because [0, 1] ∘ out = sel(head, pred, 0) = pred on M. So the transpose of g is a model morphism ℕ → (2^C, χ, step), equal to r by initiality, and g is determined because M ↪ 2^ℕ is mono.
   - **Inductions.** The one fact about decreasing sequences that is used is u(n+1) = u(n+1) ∧ u(0) on M. It is proved by induction through the equaliser of the two maps ℕ → 2^M: that equaliser is a sub-NNO-algebra, hence all of ℕ. The step uses only the defining equation of M and Boolean identities.
   - **No universality, no disjointness, no extensivity** is used: only distributivity, which every cartesian closed category has, together with equalisers and the NNO. So the conatural numbers exist in Model D and in Model B by construction, as they must.
   - **In the system [proved here, note level; 2026-11-23].** Both earlier open checks are discharged.
     - *Every target is a set without DESC.* 2 := μ(X; tt, ff : ⊤ → X) and 1 + M := μ(X; ⊤ → X, M → X) are the coproducts ⊤ ⊔ ⊤ and ⊤ ⊔ M: an initial algebra of constants represents pairs of points, which is the coproduct's universal property. Both are `trunc 0` by T-init, since their sources are ⊤ and the set M. ℕ is a set by T-init, ℕ\2, C\2 and M\2 by T-exp, and M by T-lim. So L-× (contraction) applies at every target, and that is all the cartesian closed structure the Agda record uses. Products are limits, exponentials into sets are A\B (F8, derived), and coproducts are used only through their universal property for maps out. The coalgebra C itself is arbitrary, directed included, because it only ever appears as a source.
     - *Higher levels.* The object of coalgebra morphisms C → M is a limit of cotensors into the sets M and 1 + M, hence a set (T-lim, T-exp). Every cell of level ≥ 1 between maps into a set is invertible and fillable (T-inv, T-fill). So contractibility of that object is exactly existence plus uniqueness up to a cell. The Agda ≡-chains transcribe to composites of cells: each CCC law at a set target is a cell given by L-×, the limit rules or INIT(ℕ).
     - *Side result.* T-coprod at n ≥ 0 is the T-init instance μ(X; A ⊔ B → X) ≃ A ⊔ B. So that h-level clause does not need DESC-grpd: only disjointness and universality do.
   - **Generalisation [sketch].** For finitely many constructors, P(X) = ∐_j A_j × (E_j\X) over sets, the same pattern works with label functions L → ∐_j A_j on snoc lists of E = ∐_j E_j. An inconsistent step stays at the current node, so the subtree map E × M → M is total and needs no split. The convention uses the current node twice, so it needs the diagonal (cartesian structure). The directed (⊗) case stays open.

6. *Internal arities in coalgebra form: trees with list-many children [sketch].* Take P(X) = List X := μY.(⊤ ⊔ X × Y). This is the polynomial of p : Fin → ℕ in coalgebra form, so a coalgebra is c : C → List C. Route 5's pattern goes through with ℕ as the label set.
   - **Carrier.** Label functions ℓ : List ℕ → ℕ on cons-addresses, with ℓ(a) = 0 for "no node" and k + 1 for "node with k children". M ↪ ℕ^{List ℕ} is the equaliser of the conditions pos(ℓ[]) = tt and pos(ℓ(a ++ [i])) = lt(i + 1, ℓ a) for all a, i. Here pos and lt are maps into 2 defined by recursion on ℕ, and all conditions are equations of maps into 2.
   - **Structure map.** out(ℓ) := build(ℓ[] − 1, i ↦ sel(lt(i + 1, ℓ[]), ℓ(i :: –), ℓ)) : M → List M. Here build(k, f) = [f 0, …, f (k − 1)] is defined by recursion on k into the set (ℕ\M)\List M. Out-of-range positions stay at the current node, so the subtree map ℕ × M → M is total and needs no split (it uses the diagonal, as in route 5).
   - **Corecursion.** R : List ℕ → C\ℕ is defined by cons-recursion, with R[] = s ∘ len ∘ c and R(i :: a) = λx. nth_φ(c x, R a, i). Here nth_φ(l, φ, i) is the label φ of the i-th entry of l, or 0 if there is none. nth_φ is a recursion on List C into the set (C\ℕ × ℕ)\ℕ, so it never needs 1 + C as a target, and C stays arbitrary.
   - **Uniqueness.** As in route 5, post-compose out ∘ g = List(g) ∘ c with the "label of child i" map List M × ℕ → ℕ. This shows that ℓ ∘ g satisfies R's recursion. The case i ≥ arity needs "absent nodes have absent descendants", a snoc induction proved through reverse.
   - **Targets.** Every target is a set: ℕ, 2, List ℕ and List M by T-init, and the exponentials by T-exp. So the construction transfers to the system with arbitrary C, as in route 5.
   - **What it does not give: the dialgebra form for p : Fin → ℕ.** A p-dialgebra has t : C ×_ℕ Fin → C, defined on the subobject {(x, i) | i < h x} ↪ C × ℕ. Extending t to the corecursion's total step needs that subobject to be a summand, that is, the pullback of tt : ⊤ → 2 along lt must be complemented. This is universality of 2 = ⊤ ⊔ ⊤ (route 4, and Known 3 of the prompt). Coalgebras of List and p-dialgebras agree when List C ≃ Σ_n C^{Fin n}, which needs the same universality. So for internal A, the residual question is exactly the comparison between the coalgebra form and the dialgebra form.

**Model D: universality of finite coproducts is not derivable [proved here; agda].** Let T : Set → 2 send X to "X is inhabited". T preserves finite products and filtered colimits, but not pullbacks. Its Artin gluing Gl(T) has as objects sets X with a flag y ∈ {0, 1}, where y = 1 only if X is inhabited. A map is a function with y ≤ y′.
- Gl(T) is cartesian closed. Products are (X × X′, y ∧ y′). The exponential is X′^X with flag (y ⇒ y′), cut down to 0 when X′^X is empty.
- It is locally presentable [recall: a comma category of accessible functors between locally presentable categories, Adámek–Rosický 2.43]. So with discrete homs it satisfies every non-DESC rule, INIT included, by the common pattern of `descent-vs-init.md` §3.
- Coproducts are (X ⊎ X′, y ∨ y′). Take z : 𝟙 → D₀ + 𝟙 with D₀ = (⊤, 0), hitting D₀. The two pullbacks of the injections along z are (⊤, 0) and (∅, 0). Their sum (⊤, 0) is not 𝟙 = (⊤, 1), and there is no map back. So finite coproducts are not universal.
- They are still disjoint. So Model D also separates universality from disjointness, the opposite of Model B (the lattice 2), where coproducts are universal but not disjoint.
- [agda] `CaTTExp.Descent.GlueNotUniversal`: category laws, the terminal object, products, exponentials (given a classical decision of whether X′^X is inhabited, passed as an argument), coproducts, both pullbacks with their universal properties, `not-universal`, the initial object 𝟘, and `disjoint` for every A ⊕ B (the pullback of the two injections is 𝟘). Local presentability and the remaining non-DESC rules are argued here, not encoded.

**What Model D says about M-types.** In Model D, as in every locally presentable model, final coalgebras of accessible endofunctors exist (the category of coalgebras is accessible, and its forgetful functor creates colimits). That includes the conatural numbers and all coproduct-form M-types. So route 4's use of universality is a limitation of the route, not of the system. Two consequences:
- A proof that dependent M-types are *not* derivable needs a model of the non-DESC rules that is not locally presentable, or not locally discrete.
- A derivation has to avoid splitting M along its root label.

The literature constructions all assume disjoint coproducts: Abbott–Altenkirch–Ghani Prop. 4.1 (Martin-Löf categories: LCCC, disjoint coproducts, W-types); van den Berg–De Marchi, *Non-well-founded trees in categories* (arXiv:math/0409158), in LCC pretoposes, where Prop. 2.9 also uses decidable equality on A.

**Evidence the other way.** All three countermodels of `descent-vs-init.md` §3 (Set, the lattice 2, Pos) are locally presentable, and there final dialgebras exist for set-like p. So nothing yet shows DESC is needed. A separating model would have to be non-extensive or not locally presentable, and still have every INIT instance.

**Status: answered (researcher, verified 2026-11-23; `conjectures/answered/dependent-m-types-without-descent-2026-11-23.md`).**
- **Dialgebra form is not derivable without DESC.** In the rectangular-band model R (pairs of sets, with the empty pair), the axioms hold: R is locally finitely presentable and cartesian closed, with disjoint but non-universal coproducts and a complemented diagonal on the labels. Yet there is no terminal p-dialgebra for the first injection 1 → 1 + 1, nor for Fin → ℕ. Two labels u = (0, 1) and v = (1, 0) have empty fibres, but their band product has a fibre point, so the maps from two constant-step dialgebras into a terminal one must agree there and then disagree after one step. [agda] `CaTTExp.Coinductive.RectBandNoDialgebra` (`inactive-product`, `no-first`, `no-fin`), an independent port of the response's Lean certificate. R still has the terminal *coalgebras* of 1 + X and List (routes 5 and 6), so the separation is exactly the coalgebra/dialgebra gap that route 6 located.
- **Classification for finite copowers.** For f : J → I finite, p_f has a terminal dialgebra in every model iff |I| ≤ 1 or f is bijective. The other cases fail in R, in affine spaces over 𝔽₃ (with a non-cartesian tensor) and in augmented vector spaces [checked in outline].
- **Restoration.** Universality of finite coproducts alone (a theorem of DESC-grpd) gives the terminal p-dialgebra for every p between finite copowers, coherently and with a non-cartesian tensor [checked in outline]. So in the system, finite-constructor dependent M-types in dialgebra form follow from DESC-grpd.
- **Internal labels: decidable families [proved here; agda, 1-truncated; 2026-11-23].** [agda] `CaTTExp.Coinductive.DecidableDialgebra`: over an abstract category with terminal object, products, coproducts, equalisers and U-⊔ at 2 (no disjointness, no exponentials), `dom-pb` shows that the tt-part of C × B is the pullback C ×_A E, and `Final.terminal`/`Final.unique` give the terminal dialgebra, *assuming* a terminal constant-arity machine (Known 1, taken as a module parameter). Call p : E → A a *decidable B-family* if E ≅ χ*(tt) ⊆ A × B for some χ : A × B → 2, with p the first projection. Examples:
  - Fin → ℕ, with B = ℕ and χ(n, i) = (i < n), defined by recursion.
  - Any p whose label object A has decidable equality δ : A × A → 2 (δ*(tt) = diagonal), with B = E and χ(a, e) = δ(a, p e).
  - Every map between finite copowers.

  *Theorem.* Assume 𝒱 satisfies (a)–(c) with ⊗ = ×, and finite coproducts are universal (U-⊔, `descent-vs-init.md` §5b). Then every decidable B-family has a terminal p-dialgebra.
  1. **Split.** By pullback pasting, C ×_A E ≅ (χ ∘ (h × B))*(tt) ⊆ C × B. U-⊔ along χ ∘ (h × B) : C × B → ⊤ ⊔ ⊤ gives C × B ≅ (C ×_A E) ⊔ Q with Q the ff-part. No disjointness is needed.
  2. **Machines.** Let K be the category of (C, h : C → A, t̄ : C × B → C). It has a terminal object, SnocList(B)\A (Known 1 / §2).
  3. **Retraction.** R : K → D restricts t̄ to C ×_A E. J₀ : D → K extends t by "stay": [t, π₁] on (C ×_A E) ⊔ Q. J₀ is functorial because a dialgebra map g preserves h, so g × B maps each part to the same part. And R J₀ = id.
  4. **Idempotent equaliser.** η_D := R(!_{J₀D}) : D → X := R(T_K) is natural (terminality in K), so η_X ∘ η_Z = η_Z. The equaliser of id_X and η_X in D (created by 𝒱, since dialgebra maps commute with t) is terminal. η_Z factors through it, and any f into it satisfies e f = η_X e f = η_Z, with e mono.

  **In the system:** with U-⊔ and L-×, the same holds when A and B are sets and C is arbitrary (directed included). L-× turns the ⊗-machines of §2 into ×-machines, because their carrier SnocList(B)\A is a set, and maps C × B → (set) are multimaps. The equaliser and the higher levels are trivial, as in route 5, because every map compared lands in a set.

  **Open:** non-decidable families; non-cartesian ⊗ without L-× (internal B needs B × C ≃ B ⊗ C); and directed labels, where {0<2} → [2] already fails even though Cat_(∞,1) has universal coproducts. The coalgebra form (route 6) needs no DESC.

## 5. Directed M-types

- **Constant arity:** done (§2) for arbitrary A and E, lax and oplax versions.
- **Set-level labels, directed coalgebras [proved here, note level].** Routes 5 and 6 map only into sets, so they hold in the system for coalgebras C of any kind, directed included (§4, route 5, "In the system").
- **Dependent arity, p directed: answered (researcher, verified in outline 2026-11-23).** In Cat_(∞,1) and Cat_(∞,ω), p has a terminal dialgebra iff its terminal chain W = lim P_p^n(1), computed in presheaves on Δ or Θ, satisfies the Segal and completeness conditions. Exponentiable p (cartesian or cocartesian fibrations) suffices, by the terminal chain. The inclusion {0<2} → [2] has **no** terminal dialgebra: the images of 0 → 1 and 1 → 2 compose through the shared middle object to an arrow over 0 → 2, and one step turns it into an arrow over 2 → 0. Exponentiability is not necessary: the rank map of the diamond b < m₀, m₁ < t onto [2] is not exponentiable but has a terminal dialgebra, a poset of trees.

## 6. Open items

| Row | Item | Owner |
|---|---|---|
| F12b | Streams and constant-arity M-types: Agda written, checked on Agda 2.7.0.1 and 2.6.3; honesty review passed (PR #556) | this thread |
| F12c | Dependent-arity M-types without DESC: answered (researcher, verified). `RectBandNoDialgebra.agda`: honesty review | this thread |
