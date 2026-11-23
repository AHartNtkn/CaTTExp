# Coinductive objects from initiality

*Ledger F12b.* `descent-vs-init.md` §5 shows that final coalgebras are not INIT instances, but that some of them are derivable. This note settles which ones, in Agda where possible, and records what is open.

*Short answer.*
- **Streams and every constant-arity M-type are derivable from INIT and chapter 8, with no DESC.** For any objects A and E (directed or not), νX. A × (E\X) is SnocList(E)\A. Streams are the case without E. [agda, 1-truncated] `CaTTExp.Coinductive.Streams`, `CaTTExp.Coinductive.ConstArity`.
- **Dependent arities (a map p : E → A, a family of arity sets) are open.** Every known construction (Ahrens–Capriotti–Spadotti in HoTT, Abbott–Altenkirch–Ghani, van den Berg–De Marchi) uses a universe, or disjoint coproducts and local cartesian closure. In our system the analogue of those is DESC-grpd. No countermodel is known: in every model of §3 of `descent-vs-init.md` the M-types exist. Sent out as `conjectures/outbox/dependent-m-types-without-descent.md`.
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
   - **In the system.** The cartesian structure needed here comes from L-× at the set targets 2, 2^ℕ and 2^C (chapter 9 §9.6), which lets × play the role of ⊗. Two points still to check: that 2 = ⊤ ⊔ ⊤ is `grpd_2` without DESC, and that the equaliser with the cotensor clauses gives the higher levels.
   - **Generalisation [sketch].** For finitely many constructors, P(X) = ∐_j A_j × (E_j\X) over sets, the same pattern works with label functions L → ∐_j A_j on snoc lists of E = ∐_j E_j. An inconsistent step stays at the current node, so the subtree map E × M → M is total and needs no split. The convention uses the current node twice, so it needs the diagonal (cartesian structure). The directed (⊗) case stays open.

**Model D: universality of finite coproducts is not derivable [proved here; agda].** Let T : Set → 2 send X to "X is inhabited". T preserves finite products and filtered colimits, but not pullbacks. Its Artin gluing Gl(T) has as objects sets X with a flag y ∈ {0, 1}, where y = 1 only if X is inhabited. A map is a function with y ≤ y′.
- Gl(T) is cartesian closed. Products are (X × X′, y ∧ y′). The exponential is X′^X with flag (y ⇒ y′), cut down to 0 when X′^X is empty.
- It is locally presentable [recall: a comma category of accessible functors between locally presentable categories, Adámek–Rosický 2.43]. So with discrete homs it satisfies every non-DESC rule, INIT included, by the common pattern of `descent-vs-init.md` §3.
- Coproducts are (X ⊎ X′, y ∨ y′). Take z : 𝟙 → D₀ + 𝟙 with D₀ = (⊤, 0), hitting D₀. The two pullbacks of the injections along z are (⊤, 0) and (∅, 0). Their sum (⊤, 0) is not 𝟙 = (⊤, 1), and there is no map back. So finite coproducts are not universal.
- They are still disjoint. So Model D also separates universality from disjointness, the opposite of Model B (the lattice 2), where coproducts are universal but not disjoint.
- [agda] `CaTTExp.Descent.GlueNotUniversal`: category laws, the terminal object, products, exponentials (given a classical decision of whether X′^X is inhabited, passed as an argument), coproducts, both pullbacks with their universal properties, `not-universal` and `disjoint`. Local presentability and the remaining non-DESC rules are argued here, not encoded.

**What Model D says about M-types.** In Model D, as in every locally presentable model, final coalgebras of accessible endofunctors exist (the category of coalgebras is accessible, and its forgetful functor creates colimits). That includes the conatural numbers and all coproduct-form M-types. So route 4's use of universality is a limitation of the route, not of the system. Two consequences:
- A proof that dependent M-types are *not* derivable needs a model of the non-DESC rules that is not locally presentable, or not locally discrete.
- A derivation has to avoid splitting M along its root label.

The literature constructions all assume disjoint coproducts: Abbott–Altenkirch–Ghani Prop. 4.1 (Martin-Löf categories: LCCC, disjoint coproducts, W-types); van den Berg–De Marchi, *Non-well-founded trees in categories* (arXiv:math/0409158), in LCC pretoposes, where Prop. 2.9 also uses decidable equality on A.

**Evidence the other way.** All three countermodels of `descent-vs-init.md` §3 (Set, the lattice 2, Pos) are locally presentable, and there final dialgebras exist for set-like p. So nothing yet shows DESC is needed. A separating model would have to be non-extensive or not locally presentable, and still have every INIT instance.

**Status.** Open, [conj] either way. Paste-ready prompt: `conjectures/outbox/dependent-m-types-without-descent.md`. Its main question asks for the class of maps p for which final dialgebras exist in every model of the non-DESC rules, together with a uniform construction, or a separating model. In-house: route 4 localises its own need to universality of finite coproducts (for finitely many constructors). Model D shows that universality is not derivable, yet M-types exist in Model D. Route 5 does that for the conatural numbers and, at sketch level, for finitely many constructors over sets. Next: an Agda check of route 5 for the conaturals over an abstract cartesian closed category with NNO.

## 5. Directed M-types

- **Constant arity:** done (§2) for arbitrary A and E, lax and oplax versions.
- **Dependent arity, p directed:** the dialgebra formulation makes sense for every p. Semantically, when p is exponentiable (for example a cocartesian fibration) Π_p exists in Cat_ω and P is accessible, so a final coalgebra exists. For non-exponentiable p (such as {0<2} → [2]) the dialgebra category need not be a coalgebra category, and whether a terminal object exists is not known. This is part 2 of the outbox prompt.

## 6. Open items

| Row | Item | Owner |
|---|---|---|
| F12b | Streams and constant-arity M-types: Agda written, checked on Agda 2.7.0.1 and 2.6.3; honesty review passed (PR #556) | this thread |
| F12c-D | Model D (`Descent/GlueNotUniversal.agda`): honesty review | this thread |
| F12c | Dependent-arity M-types without DESC (undirected and directed): outbox prompt; in-house attempt on route 2 | this thread (prompt ready to send) |
