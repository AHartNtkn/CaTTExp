# Operation heads in the Agda kernel (ledger S27 (b)–(d))

*Owner: thread "Extend Agda metatheory to operation heads" (HEADS). Written 2026-11-23.*

Spec §1.1 (since PR #534) has three kinds of term former: variables, coherences `coh(Δ, A)[σ]`, and **operation heads** `h[σ]`, where the head h has an arity context Γ_h, a type A_h over Γ_h and a decidable validity test, with the rule

    Δ ⊢ σ : Γ_h    Valid(h)
    ─────────────────────── (op)
    Δ ⊢ h[σ] : A_h[σ]

A closed constant c : A is the head with empty arity, c = c[⟨⟩]. Before this work the Agda formalisation had only closed constants (`CaTTExp.Signature`), so chapter 6's lim_Γ[γ], the universal cone λ and uni[σ] were encoded separately (`Lim/Named`, `Lim/Rules`), with no substitution, weakening, decidability or suspension. This note records how heads now enter the Agda kernel and what is proved about them.

## 1. Where constants come from, and why "constant-free" mattered

A **constant** is a former of the signature with a fixed closed type: `cst k : ty(k)`, the type mentioning no variable. Constants enter a context only through the types of its variables or the terms in them: a context "has a constant" when some type in it mentions `cst k`, e.g. `x : ⋆, f : x → c` for a constant object c. Plain CaTT has none; every extension of chapters 3–9 used to be described as adding constants or families of them.

Two metatheorems were stated only for constant-free syntax, for a reason that is not a technicality:

- **Suspension** Σ adds two objects N, S below everything and raises dimensions by one. A coherence suspends to a coherence over the suspended pasting context. A constant cannot: Σ c would need a constant of type Σ ty(c), and the signature need not have one.
- **Collapsing substitutions** `!_Γ` send every object variable to one object; a type that mentions a constant of another object breaks them.

Operation heads have the same issue, since a head's type A_h is fixed by the signature. The general fix (§3 below) is the one spec §1.5 states: a head suspends when the signature also provides its suspension Σh, a head with arity ΣΓ_h and type ΣA_h. Heads without one block suspension of the terms containing them, exactly as constants did.

## 2. Heads as closed binders (S27 (b))

The binder kernel (`CaTTExp.Binder.*`, BIND) already has a former `bnd b y Δ ts`: former b, selector y, a telescope Δ of bound variables and arguments ts. Its interface gives an argument telescope and a result type, written with bound variables. A head is the case of an empty telescope Δ = ε with **closed** data (no free variable). DES was already such a head. This route was chosen so that heads compose with binders (INIT) and reuse every theorem of the binder kernel.

| Module | What it proves |
|---|---|
| `Binder.Heads` | `HeadAt b`: the former's data is closed. `head-laws`: every family of heads satisfies `BinderLaws`, hence substitution (`Binder.Subst`), weakening, the certified checker and its completeness (`CheckWith`, `Completeness`). `head-presup`: with `HeadOK` (Γ_h ⊢ A_h), the presupposition law `PresupLaws`. |
| `Binder.Close` | Closing an ordinary context Γ into bound-variable form (`clTel 0`), and opening it back: `opTy 0 ts (clTy 0 A) ≡ A[ts]`. `Honest G`: every entry of G is scoped by its position and locally closed (decided by `honest?`). |
| `Binder.HonestHeads` | For a head given by an honest arity G and type A: arguments for `clTel 0 G` are exactly substitutions into G (`args→sub`, `sub→args`), so the kernel's binder rule at h is rule (op), both ways (`op-intro`, `op-inv`). `honest-ok`: HeadOK is G ⊢ A. |
| `Binder.HeadSpec` | A family given as in spec §1.6, by arity contexts, types and a validity test (`HeadSpec`). `Laws`: every such family is honest (`spec-honest`, so its rule is (op)) and satisfies `BinderLaws` (`spec-laws`), with no proof specific to the family. The honesty checks are decided, not assumed. |
| `Binder.LimHeads` | lim_Γ (arity Γ, type ⋆) and the universal cone λ_{Γ,g} (arity Γ, type the type of cell g of the cone over Γ with apex lim_Γ[id] and earlier cells the earlier legs) as a `HeadSpec`, for **any** cone shape `shape : P.Ctx → Maybe P.Ctx` (a cocone shape gives colimits the same way). |
| `Binder.LimHeadsExamples` | With the specified cone of `CaTTExp.Cones`: the limit of an arrow f : A → B has legs λ_x : L → A, λ_y : L → B and λ_f : λ_y ⇒ f ∘ λ_x; the binary product has π₁, π₂; the limit over the empty context is a typed object (a head with empty arity; that it is terminal needs uni, S27 (e)); ill-formed bases, missing cells and wrong argument counts are rejected. All by computation. |

## 3. Suspension with heads (S27 (c))

`Binder.Suspension` is suspension for the kernel with heads, under plain CaTT's side condition and any mark judgment that suspension preserves (`MarkΣ`; rule (MARK) alone does, `varMarkΣ`):

    Γ ⊢ctx ⇒ ΣΓ ⊢ctx     Γ ⊢ty A ⇒ ΣΓ ⊢ty ΣA     Γ ⊢tm t ∶ A ⇒ ΣΓ ⊢tm Σt ∶ ΣA     Γ ⊢sub σ ∶ Δ ⇒ ΣΓ ⊢sub Σσ ∶ ΣΔ

for **suspendable** syntax: every head h in it has a provided suspension (`canΣ`), and Σ sends h[σ] to (Σh)[Σσ]. The signature's obligation (`HeadSusp`) is that at each such head, h is honest with arity G and type A, Σh is honest with arity ΣG and type ΣA, and Σh is valid. With no head suspendable this is the old constant-free theorem. Pasting-context facts are transferred from the pure `CaTTExp.Suspension` along the embedding of pure syntax.

`Binder.SpecSusp` reduces `HeadSusp` for a `HeadSpec` family to equations on its data: the arity of Σh is Σ of the arity of h, the type likewise, and Σh passes the family's own test. Honesty of Σh is not assumed: suspension preserves scoping and local closure (`scΣty`, `lcΣty`, `honestΣ`).

`Binder.DesSusp` shows the hypotheses are met by a real family, at every dimension: DES (t⁻ˡ, t⁻ʳ, λ_t, ρ_t) written as a `HeadSpec` (`desSpec`, whose closed data is exactly `desBinders`', `args-agree`, `res-agree`), valid at every dimension n ≥ 1 (`des-valid`), suspends with Σ(destructor at n) = (same destructor at n + 1) (`des-susp`). The proof is ΣDⁿ⁺¹ = Dⁿ⁺², Σ of the composite over Dⁿ⁺¹ ∨ Dⁿ⁺¹ is the composite one dimension up, and Σ of a head application is the head one dimension up.

## 4. Which heads suspend (S27 (d))

A head h suspends only if the theory also provides Σh, with arity ΣΓ_h and type ΣA_h, and its models interpret it.

- **DES suspends** (§3). The inverse of a suspended invertible cell is the suspension of its inverse, and the unit witnesses likewise; `des-susp` is the proof.
- **lim_Γ and λ do not suspend in general.** Σ lim_Γ would have type Σ⋆ = (N → S), so it would be a limit of the suspended diagram **inside the hom** 𝒦(N, S). A category with limits need not have limits in its homs: in Set, viewed as a (2-)category with discrete homs, the hom Set(A, B) is a discrete category, which has a binary product of x and y only when x = y. So Σ(binary product) is not interpretable in Set, and providing it would be unsound for the intended models. Spec §1.5 had suggested the limit heads suspend "when Σ of a limit is the limit of the suspended diagram"; that condition fails in the basic model, and the sentence is corrected in this PR.
- **⊗ and the multimap heads mm do not suspend in general**, for the same reason: a Gray tensor of objects says nothing about tensors in homs. mm is built from ⊗ (GRAY thread, PR #537), so it does not either.

So suspension acts on the fragment built from coherences, variables and DES; a term containing lim, λ, ⊗ or mm is not suspended, which is what the semantics requires. A theory that wants limits in homs (e.g. locally complete 2-categories) can add Σlim as a separate family with `SpecSusp` as the proof obligation.

## 5. Limits of this work, logged in open-issues S27 (e)–(h), owner HEADS

1. (e) **uni** is a head family since `Binder.UniHeads`, generic over the horn shape: one pure context laid out as Cone(Γ; L), the horn entries, w, the components, read against the universal cone (L := lim_Γ[id], λ_g := λ_{Γ,g}[id], w := uni^w[id]). Marked horn entries are marked inv in the arity, so the kernel's mark premise is §6.2's "σ must supply inv derivations". `UniHeadsExamples` instantiates the horns of `Lim/Horn` (arrow, n = 0, 1). Remaining: (e′) horn shapes for every Γ and n, which need F(w)_g in general; (e″) J2's "uni^y[σ] inv", a clause of the mark judgment.
2. (f) **HeadOK for the legs λ_{Γ,g}** (that each leg's type is well-formed over Γ) is not proved for a general shape, so `head-presup` is not instantiated for `LimHeads`. lim itself (type ⋆) is immediate. It needs the cone shape's well-formedness carried through `coneSub`.
3. (g) **Heads indexed by a non-empty closed telescope** are covered by `head-laws` but not by suspension: suspending them would need a strengthening lemma that the binder kernel does not have. lim is therefore indexed by a pure context carried in the former (`limF Γ`) rather than by a telescope.
4. (h) `Lim/Rules` (recognition judgments over named contexts) is not yet stated as an instance of `LimHeads`; the two encodings coexist.
