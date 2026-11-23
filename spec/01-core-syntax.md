# Chapter 1. Core syntax

This chapter fixes the syntax and the judgments shared by every later chapter. It is Finster–Mimram's CaTT, parameterised in two places:
- a **signature** of closed constants, through which every later kernel extension (limits, free objects, the closed structure) adds its term formers;
- the **side condition** of the `coh` rule. This chapter states the rule with the side condition as a parameter. Chapter 2 gives the side condition the kernel uses; plain CaTT's is given here as the reference instance.

Metatheory proved once for the parameterised rules holds for every instance, so substitution admissibility and checker completeness below cover the lax core of chapter 2 as well.

## 1.1 Raw syntax

```
Contexts       Γ, Δ ::= ε | Γ, x : A
Types          A, B ::= ⋆ | t →_A u
Terms          t, u ::= x | c | coh_{Δ, A}[σ]
Substitutions  σ, τ ::= ⟨⟩ | ⟨σ, x ↦ t⟩
```

- `c` ranges over the constants of the signature 𝕊. Each constant has a closed type `ty(c)` and a decidable validity predicate `Valid(c)`.
- `coh_{Δ, A}[σ]` is a coherence over the context Δ, at the type A (which must be an arrow type), substituted by σ.
- The **dimension** of a type is dim ⋆ = −1 and dim (t →_A u) = dim A + 1. The dimension of a term is the dimension of its type plus one, so objects have dimension 0.
- Substitution `t[σ]`, `A[σ]`, `σ ∘ τ` acts on raw syntax by replacing variables. It is the only operation on terms, and it is syntactic: there is no other definitional equality (chapter 0, §0.3).

**Status.** Agda-checked: raw syntax and substitution, `CaTTExp.Syntax` (de Bruijn levels, so extending a context never renames). **Source:** `notes/agda-sketch-findings.md` "What is formalized".

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

Γ ⊢    (x : A) ∈ Γ              Γ ⊢    Valid(c)
───────────────── (var)        ───────────────── (const)
   Γ ⊢ x : A                     Γ ⊢ c : ty(c)

  Δ ⊢                   Δ ⊢ σ : Γ    Δ ⊢ t : A[σ]
────────── (⟨⟩)        ───────────────────────────── (ext-sub)
Δ ⊢ ⟨⟩ : ε              Δ ⊢ ⟨σ, x ↦ t⟩ : Γ, x : A
```

**Side condition.** (const) checks `Valid(c)`, which every signature must make decidable. The other rules have none.

**Status.** Agda-checked, `CaTTExp.TypingWith` (parameterised in 𝕊 and in the side condition). The checker `CaTTExp.CheckWith` is certified (every success returns a derivation) and complete (`CaTTExp.Completeness`), so all five judgments are decidable, given that equality of constants is decidable and `valid?` is complete. **Source:** `notes/agda-sketch-findings.md`; ledger A1, A2 (closed).

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

**Decision procedure.** For plain CaTT: compute the two variable sets and compare. For the lax side condition: chapter 2, §2.4.

**Example (plain CaTT).** Over the composable pair Δ above, take A = ⋆, t = x, u = z. Then Var(x : ⋆) = {x} = Var(∂⁻Δ) and Var(z : ⋆) = {z} = Var(∂⁺Δ), so `coh_{Δ, x → z}` is the composite of f and g, written f ; g after substitution. The "inverse" `coh_{(x,y,f), y → x}` is rejected: Var(y : ⋆) = {y} ≠ {x} = Var(∂⁻(x, y, f)).

**Semantics.** In a model, a coherence over Δ with the operation side condition is a chosen composite of the pasting diagram Δ; with the full-coherence condition it is a chosen cell between two parallel composites that are equal in the free strict ω-category, and it is invertible (Benjamin–Markakis, arXiv 2406.12127).

**Status.** Agda-checked for every decidable SC: `CaTTExp.TypingWith` (the rule), `CaTTExp.Typing` (the CaTT instance), `CaTTExp.Gray.Typing` (the two-tier L instance, chapter 2). Soundness of plain CaTT in every strict ω-category: Agda-checked, `CaTTExp.Strict.OmegaSound.sound-in` (ledger A3a). **Source:** `notes/agda-sketch-findings.md`; `notes/strict-omega-soundness.md`.

## 1.5 Metatheorems

| Statement | Status | Where |
|---|---|---|
| **Substitution.** Δ ⊢ σ : Γ and Γ ⊢ t : A give Δ ⊢ t[σ] : A[σ]; likewise for types and substitutions. Holds for every side condition. | Agda-checked | `CaTTExp.Subst` (ledger A1) |
| **Decidability.** All five judgments are decidable, by a certified and complete checker. | Agda-checked | `CaTTExp.CheckWith`, `CaTTExp.Completeness` (A2) |
| **Weakening.** Γ ⊢ J gives Γ, x : B ⊢ J. | Agda-checked | `CaTTExp.Weakening` |
| **Suspension.** For constant-free syntax, Σ preserves all judgments, both side conditions and the pasting judgment. | Agda-checked | `CaTTExp.Suspension` |
| **Constant substitutions.** For constant-free Γ, (c : ⋆) ⊢ !_Γ : Γ. | Agda-checked | `CaTTExp.ConstSub` |
| **Soundness in strict ω-categories** (plain CaTT). | Agda-checked | `CaTTExp.Strict.OmegaSound` (A3a) |

## 1.6 Signatures

A signature 𝕊 is a set of constants with decidable equality, a closed type `ty(c)` for each, and a decidable validity predicate `Valid(c)`. Pure CaTT is the empty signature.

Later chapters extend the kernel only by adding constants, families of constants indexed by syntax (for example, one constant `⟦Γ⟧ : ⋆` per pasting context Γ, chapter 7), and inductive judgments in the style of `⊢ps`. They add no new definitional equalities.

A fourth kind of extension is a **binding former** in the sense of chapter 0, §0.2: a rule that binds an object variable in a premise and forms an object or a cell from it, with its universal property witnessed by cells. The kernel has one: INIT (chapter 9, §9.3), whose term μΔ binds the distinguished object variable X of a positive context Δ, together with its generic model η and the recursor rec_σ. Its syntax is **not yet in §1.1's grammar**, which has no binders. Until it is, chapter 9 states INIT's terms directly, and the Agda signature (`CaTTExp.Signature`) does not cover it (ledger S26).

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
