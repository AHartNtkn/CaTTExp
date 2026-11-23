# Chapter 1. Core syntax

This chapter fixes the syntax and the judgments shared by every later chapter. It is Finster–Mimram's CaTT, parameterised in two places:
- a **signature** of closed constants, through which every later kernel extension (limits, free objects, the closed structure) adds its term formers;
- the **side condition** of the `coh` rule. This chapter states the rule with the side condition as a parameter. Chapter 2 gives the side condition the kernel uses; plain CaTT's is given here as the reference instance.

Metatheory proved once for the parameterised rules holds for every instance, so substitution admissibility and checker completeness below cover the lax core of chapter 2 as well.

## 1.1 Raw syntax

```
Contexts       Γ, Δ ::= ε | Γ, x : A
Types          A, B ::= ⋆ | t →_A u
Terms          t, u ::= x | c | coh_{Δ, A}[σ] | h[σ]
Substitutions  σ, τ ::= ⟨⟩ | ⟨σ, x ↦ t⟩
```

- `c` ranges over the constants of the signature 𝕊. Each constant has a closed type `ty(c)` and a decidable validity predicate `Valid(c)`.
- `coh_{Δ, A}[σ]` is a coherence over the context Δ, at the type A (which must be an arrow type), substituted by σ.
- `h[σ]` is an **operation head** h applied to a substitution σ. Each head h of the signature has an **arity context** Γ_h, a type A_h with Γ_h ⊢ A_h, and a decidable validity predicate `Valid(h)`. A head works like a coherence whose context and type are fixed by the signature, not by the term: σ supplies its arguments, and h[σ] has type A_h[σ]. A constant c is the case Γ_h = ε, so `c` abbreviates c[⟨⟩].
- The **dimension** of a type is dim ⋆ = −1 and dim (t →_A u) = dim A + 1. The dimension of a term is the dimension of its type plus one, so objects have dimension 0.
- Substitution `t[σ]`, `A[σ]`, `σ ∘ τ` acts on raw syntax by replacing variables; on a head it acts on the arguments, `h[σ][τ] = h[σ ∘ τ]`, as on a coherence. It is the only operation on terms, and it is syntactic: there is no other definitional equality (chapter 0, §0.3).

**Binders (INIT).** The kernel's one binding former, INIT (chapter 9, §9.3), adds a binder and five term formers:
```
Binders        β ::= X. Δ              Δ a context whose first entry is X : ⋆
Terms          t, u ::= … | μ(β) | η_y(β) | rec(β; A, σ) | rec_y(β; A, σ) | uni(β; A, σ; ρ, ρ′) | uni_y(β; A, σ; ρ, ρ′)
```
- In `X. Δ`, the variable X and every variable declared in Δ are **bound**. The free variables of β are the variables of the surrounding context that Δ's types mention (the parameters).
- `μ(β)` is the initial model's carrier; `η_y(β)` is the generic model at the variable y of Δ, so η = ⟨X ↦ μ(β), y ↦ η_y(β), …⟩ is a substitution Δ[μ(β)/X].
- For a carrier A and a model σ : Δ[A/X], `rec(β; A, σ)` is the map μ(β) → A and `rec_y(β; A, σ)` its invertible cell at y (INIT-J1).
- For two model morphisms ρ, ρ′ from η to σ (substitutions into the arrow context Δ^→), `uni(β; A, σ; ρ, ρ′)` is the invertible cell between their carrier maps and `uni_y` its compatibility cell at y (INIT-J2). Higher levels are derived (§9.3), so they need no syntax.
- Bound variables are **locally nameless**: inside a binder, X and Δ's variables form a separate syntactic class (`bvar d j`: entry j of the binder d levels out), while free variables stay de Bruijn levels. Substitution acts on the parameters only, `μ(X. Δ)[τ] = μ(X. Δ[τ])`, with no shift and no possible capture, and likewise for the other formers. Checking a binder opens Δ with fresh free variables. Extending a context still never renames.
- Equality of terms stays syntactic identity. Positivity of Δ in X (§9.3) is a typing side condition, not part of the grammar.

**Status.** Agda-checked: raw syntax and substitution, `CaTTExp.Syntax` (de Bruijn levels, so extending a context never renames); with binders, `CaTTExp.Binder.Syntax` (locally nameless) and `CaTTExp.Binder.Subst`. INIT's six formers are an instance of the generic binder interface, `CaTTExp.Binder.Init`, with laws in `InitLaws` and checked examples in `InitExamples` (ℕ with all six formers; the circle with μ, η, rec). The Agda positivity check covers only the fragment whose sources are X or X-free and whose targets are X or ⊤ (ledger S26f). Not yet formalized: rec_y, uni, uni_y at cell variables (S26b), several sorts (S26c), marks in Δ (S26d), and the inverses that make rec_y and uni_y invertible (S26e). **Source:** `notes/agda-sketch-findings.md` "What is formalized"; for INIT, `notes/universe-free-principles.md` §4.2.

## 1.2 Judgments

```
Γ ⊢           Γ is a well-formed context
Γ ⊢ A         A is a well-formed type in Γ
Γ ⊢ t : A     t is a term of type A in Γ
Δ ⊢ σ : Γ     σ is a substitution from Γ into Δ
Γ ⊢ps         Γ is a pasting context
```

### Rules for contexts, types, terms and substitutions

```
                    Γ ⊢    Γ ⊢ A                Γ ⊢                Γ ⊢ t : A    Γ ⊢ u : A
──────── (ε)       ─────────────── (ext)       ────── (⋆)          ─────────────────────── (→)
  ε ⊢               Γ, x : A ⊢                 Γ ⊢ ⋆                 Γ ⊢ t →_A u

Γ ⊢    (x : A) ∈ Γ              Γ ⊢    Valid(c)              Δ ⊢ σ : Γ_h    Valid(h)
───────────────── (var)        ───────────────── (const)     ──────────────────────────── (op)
   Γ ⊢ x : A                     Γ ⊢ c : ty(c)                 Δ ⊢ h[σ] : A_h[σ]

  Δ ⊢                   Δ ⊢ σ : Γ    Δ ⊢ t : A[σ]
────────── (⟨⟩)        ───────────────────────────── (ext-sub)
Δ ⊢ ⟨⟩ : ε              Δ ⊢ ⟨σ, x ↦ t⟩ : Γ, x : A
```

**Side condition.** (const) checks `Valid(c)` and (op) checks `Valid(h)`, which every signature must make decidable. (const) is (op) at Γ_h = ε. The other rules have none.

**Status.** For constants: Agda-checked, `CaTTExp.TypingWith` (parameterised in 𝕊 and in the side condition). For heads with a non-empty arity: Agda-checked in the kernel with binders, where a head is a binder with empty telescope and closed data and its binder rule is (op) (`CaTTExp.Binder.HonestHeads`; families given by arities and types, `CaTTExp.Binder.HeadSpec`; lim_Γ and the universal cone, `CaTTExp.Binder.LimHeads`; ledger S27b). uni is not yet encoded as a head (S27). The checker `CaTTExp.CheckWith` is certified (every success returns a derivation) and complete (`CaTTExp.Completeness`), so all five judgments are decidable, given that equality of constants is decidable and `valid?` is complete. **Source:** `notes/agda-sketch-findings.md`; ledger A1, A2 (closed).

## 1.3 Pasting contexts

A pasting context is a context that presents a globular pasting diagram, listed in a canonical order. The judgment is Finster–Mimram's, through an auxiliary judgment `Γ ⊢ps x : A` ("Γ is a partial pasting context whose current dangling variable is x : A").

```
───────────────────── (pss)
(x : ⋆) ⊢ps x : ⋆

Γ ⊢ps x : A
──────────────────────────────────────────── (pse)     y, f fresh
Γ, y : A, f : x →_A y ⊢ps f : x →_A y

Γ ⊢ps f : x →_A y                    Γ ⊢ps x : ⋆
──────────────────── (psd)          ─────────────── (ps)
Γ ⊢ps y : A                            Γ ⊢ps
```

**Boundaries.** For a pasting context Γ of dimension n and k < n, the source and target k-boundaries ∂⁻_k Γ and ∂⁺_k Γ are the sub-pasting contexts obtained by dropping every variable of dimension > k and, at dimension k, keeping the first (source) or last (target) variable of each maximal chain. Write ∂^± Γ for ∂^±_{n−1} Γ.

**Decision procedure.** Parse Γ left to right; at each object, descend with (psd) to the dimension of the next variable; reject on a mismatch. Equivalently, parse Γ to a Batanin tree and compare it with the context the tree generates.

**Example.**
- `(x : ⋆, y : ⋆, f : x → y, z : ⋆, g : y → z)` is a pasting context: a composable pair. Its source boundary is `(x : ⋆)` and its target boundary is `(z : ⋆)`.
- The 2-sphere `(x, y : ⋆, f, g : x → y, α, β : f ⇒ g)` is not: after (pse) adds α, (psd) can only move to g, and β would need a source variable equal to the dangling variable, which is g, not f.

**Semantics.** A pasting context Γ presents a pasting diagram, i.e. an object of Joyal's Θ. In a strict ω-category, Γ presents the free strict ω-category ν(λΓ) (Steiner), whose cells are determined by their supports (chapter 2, §2.2).

**Status.** Agda-checked: the judgments `CaTTExp.Pasting`; tree construction `CaTTExp.PastingTrees` (`psOf`); deterministic decision `CaTTExp.PastingCheck`. **Source:** `notes/agda-sketch-findings.md`; Finster–Mimram, *A type-theoretical definition of weak ω-categories* (LICS 2017).

## 1.4 The coherence rule

```
Δ ⊢ps     Δ ⊢ t →_A u     SC(Δ, t →_A u)     Γ ⊢ σ : Δ
──────────────────────────────────────────────────────── (coh)
         Γ ⊢ coh_{Δ, t →_A u}[σ] : (t →_A u)[σ]
```

**Side condition.** `SC(Δ, t →_A u)` is a decidable predicate that sees **only** the coherence's own pasting context Δ and its type. It never looks at Γ or σ. This is what makes substitution admissible for every choice of SC (§1.5).

The kernel's side condition is the lax one of chapter 2. For reference, plain CaTT's is:

```
(full coherence)   Var(t : A) = Var(Δ) = Var(u : A)
(operation)        Var(t : A) = Var(∂⁻Δ)   and   Var(u : A) = Var(∂⁺Δ),   with dim A + 2 = dim Δ
```

where Var(t : A) is the set of variables of t and of the terms in A.

**Decision procedure.** For plain CaTT: compute the two variable sets and compare. For the lax side condition: chapter 2, §2.3.

**Example (plain CaTT).** Over the composable pair Δ above, take A = ⋆, t = x, u = z. Then Var(x : ⋆) = {x} = Var(∂⁻Δ) and Var(z : ⋆) = {z} = Var(∂⁺Δ), so `coh_{Δ, x → z}` is the composite of f and g, written f ; g after substitution. The "inverse" `coh_{(x,y,f), y → x}` is rejected: Var(y : ⋆) = {y} ≠ {x} = Var(∂⁻(x, y, f)).

**Semantics.** In a model, a coherence over Δ with the operation side condition is a chosen composite of the pasting diagram Δ; with the full-coherence condition it is a chosen cell between two parallel composites that are equal in the free strict ω-category, and it is invertible (Benjamin–Markakis, arXiv 2406.12127).

**Status.** Agda-checked for every decidable SC: `CaTTExp.TypingWith` (the rule), `CaTTExp.Typing` (the CaTT instance), `CaTTExp.Gray.Typing` (the two-tier L instance, chapter 2). Soundness of plain CaTT in every strict ω-category: Agda-checked, `CaTTExp.Strict.OmegaSound.sound-in` (ledger A3a). **Source:** `notes/agda-sketch-findings.md`; `notes/strict-omega-soundness.md`.

## 1.5 Metatheorems

| Statement | Status | Where |
|---|---|---|
| **Substitution.** Δ ⊢ σ : Γ and Γ ⊢ t : A give Δ ⊢ t[σ] : A[σ]; likewise for types and substitutions. Holds for every side condition. | Agda-checked, heads included: a head is a binder with empty telescope and closed data, whose binder rule is (op) | `CaTTExp.Subst` (ledger A1); heads `CaTTExp.Binder.Heads` (`head-laws`), `HonestHeads` (`op-intro`, `op-inv`), `HeadSpec` (S27b) |
| **Decidability.** All five judgments are decidable, by a certified and complete checker, given decidable equality of heads and decidable `Valid`. | Agda-checked, heads included | `CaTTExp.CheckWith`, `CaTTExp.Completeness` (A2); heads through `CaTTExp.Binder.CheckWith`, `Completeness` and `head-laws` (S27b) |
| **Weakening.** Γ ⊢ J gives Γ, x : B ⊢ J. | Agda-checked | `CaTTExp.Weakening` |
| **Suspension.** For constant-free syntax, Σ preserves all judgments, both side conditions and the pasting judgment. With heads: for syntax whose heads all have a provided suspension Σh (below), under plain CaTT's side condition. | Agda-checked | `CaTTExp.Suspension`; heads `CaTTExp.Binder.Suspension`, `SpecSusp`, `DesSusp` (S27c) |
| **Constant substitutions.** For constant-free Γ, (c : ⋆) ⊢ !_Γ : Γ. | Agda-checked | `CaTTExp.ConstSub` |
| **Soundness in strict ω-categories** (plain CaTT). | Agda-checked | `CaTTExp.Strict.OmegaSound` (A3a) |
| **With binders: substitution and decidability.** Both hold for every side condition and every binder interface satisfying the binder laws, INIT included. | Agda-checked | `CaTTExp.Binder.Subst`; `CaTTExp.Binder.CheckWith`, `CaTTExp.Binder.Completeness` (S26a) |
| **Binders are conservative.** The embedding of binder-free syntax preserves and reflects all five judgments, so adding binders derives nothing new about the binder-free fragment (for plain CaTT unconditionally; in general when the side conditions agree on embedded syntax). | Agda-checked | `CaTTExp.Binder.Embed`, `CaTTExp.Binder.InitEmbed` (S26a) |

**Why suspension and constant substitutions are constant-free.** Suspension Σ raises every dimension by one, adding two new objects below. A coherence suspends to a coherence over the suspended context. A constant cannot: its type ty(c) is fixed by the signature, so Σ c would need a second constant of type Σ ty(c), which the signature need not have. Likewise `!_Γ`, which sends every object variable of Γ to one object c, is only well typed when no type in Γ mentions a constant of another object. So both statements are proved for syntax without constants. A head suspends when the signature also gives its suspension, a head Σh with arity ΣΓ_h and type ΣA_h. DES has one (Σ of a destructor at dimension n is the same destructor at n + 1, `CaTTExp.Binder.DesSusp`). The limit heads lim_Γ, λ and the Gray tensor ⊗ do not in general: Σ lim_Γ would be a limit inside the hom 𝒦(N, S), and homs need not have limits (in Set the homs are discrete). Suspension therefore acts on terms built from coherences, variables and heads with a provided suspension (ledger S27; `notes/operation-heads.md` §4).

## 1.6 Signatures

A signature 𝕊 is a set of operation heads with decidable equality, an arity context Γ_h and a type A_h over it for each, and a decidable validity predicate `Valid(h)`. Constants are the heads with empty arity. Pure CaTT is the empty signature.

Later chapters extend the kernel by adding heads, families of heads indexed by syntax, and inductive judgments in the style of `⊢ps`. They add no new definitional equalities. The heads they add:

| Chapter | Head | Arity context Γ_h | Type A_h |
|---|---|---|---|
| 6 | `lim_Γ`, one per finite context Γ | Γ (the diagram) | ⋆ |
| 6 | `λ_{Γ,g}`, one per entry g of the cone shape | Γ | the type of g in Cone(Γ; lim_Γ[id]) |
| 6 | `uni^w_{Γ,n}`, `uni^y_{Γ,n}` | the generic horn H_n(Γ): Γ, an apex c : ⋆, and the horn variables of Horn_n(Γ, id; c) | the filler's cell, and the comparison component y |
| 6 | `colim_Γ`, the cocone components, `couni` | as for limits, with the cocone shapes | as for limits |
| 7 | `⟦Γ⟧`, one per context Γ | ε (a constant) | ⋆ |
| 7 | `η_{Γ,x}`, one per variable x of Γ | ε | the type of the generator x as a cell of ⟦Γ⟧ (§7.2) |
| 7 | `⟨–⟩_Γ` and its fillers | C : ⋆ followed by Diag(Γ, C) | ⟦Γ⟧ → C, and the LIFT cells |
| 8 | `⊗`, `\`, `/` and the multimap formers | (A, B : ⋆) and the row's variables | ⋆, and the row's cells |

A use such as Θ ⊢ uni^w_{Γ,n}[σ] with σ : Horn_n(Γ, γ; c) in chapter 6 is h[σ′] with σ′ = (γ, c, σ) : H_n(Γ), the diagram and the horn data packed into one substitution. The binder INIT is not a head (it binds variables); see below.

A fourth kind of extension is a **binding former** in the sense of chapter 0, §0.2: a rule that binds an object variable in a premise and forms an object or a cell from it, with its universal property witnessed by cells. The kernel has one: INIT (chapter 9, §9.3), whose term μΔ binds the distinguished object variable X of a positive context Δ, together with its generic model η and the recursor rec_σ. Its syntax is given in §1.1 (binders), and the kernel with binders is formalized in `CaTTExp.Binder.*` (§1.5; ledger S26a, with the remaining fragments S26b–S26f).

User declarations enter the same way: a development's postulated objects, cells and marks are a signature (equivalently, a context it is checked in).

**Status.** Agda-checked, `CaTTExp.Signature`. **Source:** `notes/agda-sketch-findings.md` "The sketch".

## 1.7 Open surface questions

**Q1.1. Names or positions.** The kernel uses de Bruijn levels in Agda; the spec writes names.
- *Option A: names with shadowing forbidden.* Simplest to read and to report errors in. Every context must be written with distinct names.
- *Option B: names elaborated to levels, shadowing allowed.* More convenient in long developments; error messages must reconstruct names.

**Q1.2. How much of a coherence the user writes.** The kernel term `coh_{Δ, A}[σ]` carries the whole pasting context Δ, the type A and the full substitution σ.
- *Option A: write everything.* No inference; terms are long (the composite of two arrows names five variables of Δ and five terms of σ).
- *Option B: write only σ's top-dimensional terms*, inferring the lower ones from their types (as in the CaTT implementation of Finster–Mimram). Typical terms shrink by a factor of about two to five; the elaborator must solve unification problems in globular types, which are first-order and decidable.
- *Option C: named operations* (`comp`, `id`, `assoc`, `unitor`) defined once as coherences and applied with inference as in B. Most readable; requires a library of names, and what each name denotes depends on the switch setting and marks (chapter 2, chapter 3).
- *Worked example.* Composing f : x → y and g : y → z: in A, `coh_{(x:⋆, y:⋆, f:x→y, z:⋆, g:y→z), x →_⋆ z}[x, y, f, z, g]`; in B, `coh_{…}[f, g]`; in C, `f ; g`.

**Q1.3. How pasting contexts are presented.** The kernel takes a context and checks `⊢ps`.
- *Option A: contexts written out.* Uniform with ordinary contexts; the user must list variables in the canonical order.
- *Option B: Batanin trees or a bracket syntax*, from which the context is generated. Can never produce a non-pasting context, so (ps) never fails; needs a second notation.
