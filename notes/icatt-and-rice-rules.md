# ICaTT and Rice's strict theories: the rules in full

*Reference notes, 2026-11-18. Closes ledger item F7. Transcribed from the papers (checked this session against the arXiv PDFs), not from the survey's paraphrase. Notation follows each paper; ⊲ is context extension, `[γ]` substitution, `∗` composition in diagrammatic order.*

Sources:
- **ICaTT.** Benjamin, Champin, Markakis, *A type theory for invertibility in weak ω-categories*, [arXiv 2602.16602](https://arxiv.org/abs/2602.16602) (Feb 2026), §2–4 and App. C.
- **Invertibility criterion.** Benjamin, Markakis, *Invertible cells in ω-categories*, [arXiv 2406.12127](https://arxiv.org/abs/2406.12127).
- **CaTT_su.** Finster, Reutter, Rice, Vicary, *A type theory for strictly unital ∞-categories*, [arXiv 2007.08307](https://arxiv.org/abs/2007.08307) (LICS 2022).
- **CaTT_sua.** Finster, Rice, Vicary, *A syntax for strictly associative and unital ∞-categories*, [arXiv 2302.05303](https://arxiv.org/abs/2302.05303) (LICS 2024), §2.5 and §3. (The earlier [arXiv 2109.01513](https://arxiv.org/abs/2109.01513) is the strictly-associative-only predecessor, "Catt_sa".)

**Relevance to this project.** Both families use **definitional equalities**: ICaTT has β/η rules for its invertibility type; CaTT_su/sua add a conversion rule. Project standard 5 rules these out for our kernel. So they are recorded here as references to port *without* their equations (see `invertibility-markings.md` §1 for what survives the port). The survey's note "the walking-equivalence quotients of `limits-representables.md` §6.1 need them" is answered there too: the walking equivalence is a context in ICaTT, and its definition needs only the formation and introduction rules, not the equations.

---

## 1. Base CaTT, as ICaTT presents it

Raw syntax: types `★ | t →_A u`; terms `x | coh_{Γ,A}[γ]`; contexts `∅ | Γ ⊲ (x : A)`; substitutions `⋄ | γ ⊲ (x ↦ t)`.

Judgments `Γ ⊢`, `Γ ⊢ A`, `Γ ⊢ t : A`, `Δ ⊢ γ : Γ`, plus `Γ ⊢ps` and `Γ ⊢ps x : A`.

- Structural rules: empty context; extension `Γ ⊢ A ⇒ Γ ⊲ (x:A) ⊢` (x fresh); variables; empty and extended substitutions (`Δ ⊢ γ : Γ`, `Δ ⊢ t : A[γ]` give `Δ ⊢ γ ⊲ (x ↦ t) : Γ ⊲ (x:A)`).
- Types: `Γ ⊢ ★`; `Γ ⊢ u : ★, Γ ⊢ v : ★ ⇒ Γ ⊢ u →_★ v`; `Γ ⊢ u : v →_A w, Γ ⊢ u′ : v →_A w ⇒ Γ ⊢ u →_{v→_A w} u′`.
- Pasting schemes (Finster–Mimram): PSS `(x:★) ⊢ps x : ★`; PSE `Γ ⊢ps x : A ⇒ Γ ⊲ (y:A) ⊲ (f : x →_A y) ⊢ps f : x →_A y`; PSD `Γ ⊢ps f : x →_A y ⇒ Γ ⊢ps y : A`; PS `Γ ⊢ps x : ★ ⇒ Γ ⊢ps`.
- **Full types.** `Γ ⊢full u →_A v` for Γ of dimension n when either (i) u and v both use all variables of Γ, or (ii) dim u = dim v = n − 1 and u, v use exactly all source, resp. target, variables of Γ of dimension ≤ n − 1. (Equivalent to Finster–Mimram's original by Dean et al., Prop. 2.10.)
- **coh-intro.** `Γ ⊢ps, Γ ⊢full A, Δ ⊢ γ : Γ ⇒ Δ ⊢ coh_{Γ,A}[γ] : A[γ]`.
- Substitution acts structurally; `coh_{Γ,A}[δ][γ] = coh_{Γ,A}[δ ∘ γ]`.
- Disks `Dⁿ` and spheres `Sⁿ`; terms of dimension n correspond to substitutions into Dⁿ, types to substitutions into Sⁿ⁻¹ (their Lemma 2.6).
- Suspension Σ is a meta-operation preserving all judgments.

## 2. Invertibility in models (the target ICaTT internalises)

**Definition (coinductive invertibility, their Def. 3.7).** An invertibility structure on a cell f : x → y consists of cells `f^linv, f^rinv : y → x`, `f^lunit : f^linv ∗ f → id_y`, `f^runit : f ∗ f^rinv → id_x`, together with invertibility structures on f^lunit and f^runit. (Separate left and right inverses; equivalent to the usual notion by Rice and Fujii et al., Prop. 3.3.1.)

**Theorem (Benjamin–Markakis; Hoshino et al.; their Thm 3.8).** If γ : ⟦Γ⟧ → X out of a pasting diagram, and `Γ ⊢full u → v` has dimension n, then `⟦coh_{Γ,u→v}⟧(γ)` is invertible whenever `γ(x)` is invertible for every variable x of Γ of dimension **n + 1**. When dim Γ ≤ n the condition is vacuous: every coherence cell is invertible.

**Converse in free ω-categories (their Prop. 3.9, from Benjamin–Markakis Prop. 37).** A term `Δ ⊢ t : A` of dimension n is invertible in ⟦Δ⟧ iff t = `coh_{Γ,A}[γ]` with `x[γ]` invertible for every n-dimensional x ∈ Var(Γ). (Survey phrasing: "top-dimensional support is empty".)

## 3. ICaTT

**Raw syntax added.** One type former `Inv_A(u)` and nine term formers:

```
can(t, {e_x})      inv(t, t_l, t_r, t_lu, t_ru, t_ilu, t_iru)      rec(t, t_l, t_r, t_lu, t_ru, t_ilu, t_iru, γ)
linv(e)  rinv(e)  lunit(e)  runit(e)  ilunit(e)  irunit(e)
```

Substitution: structural, except `rec(…, γ)[σ] = rec(…, γ ∘ σ)` (the first seven arguments live in a fixed context, see rec). Suspension commutes with every former.

**Rules** (all CaTT rules are inherited):

```
Γ ⊢ t : u →_A v
──────────────────── Inv-intro
Γ ⊢ Inv_{u→_A v}(t)

Γ ⊢ e : Inv_{u→v}(t)                  Γ ⊢ e : Inv_{u→v}(t)
──────────────────────               ──────────────────────
Γ ⊢ linv(e) : v → u                   Γ ⊢ rinv(e) : v → u

Γ ⊢ lunit(e) : linv(e) ∗ t → id v     Γ ⊢ runit(e) : t ∗ rinv(e) → id u      (premise e : Inv(t))
Γ ⊢ ilunit(e) : Inv(lunit(e))         Γ ⊢ irunit(e) : Inv(runit(e))          (premise e : Inv(t))

Γ ⊢ t : x → y   Γ ⊢ t_l : y → x   Γ ⊢ t_r : y → x
Γ ⊢ t_lu : t_l ∗ t → id y   Γ ⊢ t_ru : t ∗ t_r → id x
Γ ⊢ t_ilu : Inv(t_lu)   Γ ⊢ t_iru : Inv(t_ru)
───────────────────────────────────────────────── inv-intro
Γ ⊢ inv(t, t_l, t_r, t_lu, t_ru, t_ilu, t_iru) : Inv(t)

Δ ⊢ coh_{Γ,A}[γ] : A[γ]     { Δ ⊢ e_x : Inv(x[γ]) }  for x ∈ Var_{dim A + 1}(Γ)
───────────────────────────────────────────────────────────────────────────── can-intro
Δ ⊢ can(coh_{Γ,A}[γ], {e_x}) : Inv(coh_{Γ,A}[γ])
```

`Var_n(Γ)` is the set of n-dimensional variables of Γ. can-intro internalises Thm 3.8.

**Walking equivalence (Def. 4.1).** `Eⁿ⁺¹ := Dⁿ⁺¹ ⊲ (eⁿ⁺¹ : Inv(dⁿ⁺¹))`, with weakening `μⁿ⁺¹ : Eⁿ⁺¹ → Dⁿ⁺¹`. Types are classified by Sⁿ (categorical types) or Dⁿ⁺¹ (Inv types); terms by Dⁿ or Eⁿ⁺¹ (their Lemma 4.4), via classifying substitutions `χ_A`, `χ_{t,A}`.

**Recursor.** For `Eⁿ⁺¹ ⊢ t : u → v`, the inductive-hypothesis context is

```
IHₜⁿ⁺¹ := Eⁿ⁺¹ ⊲ (h⁻ : Inv(Σt)[χ_{ilunit(eⁿ⁺¹)}]) ⊲ (h⁺ : Inv(Σt)[χ_{irunit(eⁿ⁺¹)}])

Eⁿ⁺¹ ⊢ t : x → y    Γ ⊢ γ : Eⁿ⁺¹
Eⁿ⁺¹ ⊢ t_l : y → x  Eⁿ⁺¹ ⊢ t_r : y → x
Eⁿ⁺¹ ⊢ t_lu : t_l ∗ t → id y   Eⁿ⁺¹ ⊢ t_ru : t ∗ t_r → id x
IHₜⁿ⁺¹ ⊢ t_ilu : Inv(t_lu)    IHₜⁿ⁺¹ ⊢ t_iru : Inv(t_ru)
───────────────────────────────────────────────── rec-intro
Γ ⊢ rec(t, t_l, t_r, t_lu, t_ru, t_ilu, t_iru, γ) : Inv(t[γ])
```

It builds an invertibility structure on the image of a cell under any functorial construction t, coinductively: recursive calls are the variables h±.

**Equations (the part standard 5 excludes).**
- β for inv: `linv(inv(t, t_l, …)) ≡ t_l`, and likewise for the other five destructors.
- η: `e ≡ inv(t, linv(e), rinv(e), lunit(e), runit(e), ilunit(e), irunit(e))`.
- can: `linv(can(t,{e_x})) ≡ t^linv`, `rinv ≡ t^rinv`, `lunit ≡ t^lunit`, `runit ≡ t^runit` (the cells of the Thm 3.8 construction, App. B), `ilunit(can(t,{e_x})) ≡ can(t^lunit, {−})`, `irunit(can(t,{e_x})) ≡ can(t^runit, {−})`.
- rec: destructors on `e = rec(…, γ)` compute to the corresponding arguments, with `ilunit e ≡ t_ilu[inst_e ∘ γ]`, `irunit e ≡ t_iru[inst_e ∘ γ]`, where `inst_r := id ⊲ (h⁻ ↦ Σ(r)[χ_{ilunit(eⁿ⁺¹)}]) ⊲ (h⁺ ↦ Σ(r)[χ_{irunit(eⁿ⁺¹)}])`.
- Orientation: β-reduction and η-expansion. Locally confluent, **not terminating** (Prop. 4.5), but normalising on categorical types and terms (Prop. 4.6). No rule of ICaTT compares terms of Inv types, so this suffices for type checking.

**Metatheory.** Substitution and suspension admissible (Lemmas 4.2–4.3). Conservative over CaTT, with fully faithful inclusion of syntactic categories (§6). Every model gives a fibrant marked weak ω-category (§7). The walking equivalence ⟦Eⁿ⟧ recovers Ozornova–Rovelli's, which characterises ω-equifibrations.

**Related, equation-free alternative.** Benjamin, Champin, Markakis, *Computads with invertible generators* ([arXiv 2606.30254](https://arxiv.org/abs/2606.30254), abstract checked): computads where some generators are *marked* invertible, with an inductive description of the free ω-categories they generate; walking equivalences get a finite description, and the generalised computads form a presheaf topos. This is the marked-declaration style that our kernel can use directly.

## 4. Rice et al.: CaTT_R, CaTT_su, CaTT_sua

**The framework CaTT_R** (2302.05303 §2.5). Fix a set R of triples (Γ, s, t). Add equality judgments `Γ ⊢ s = t`, `Γ ⊢ A = B`, `Γ ⊢ σ = τ` (not fibred over types), structural equality rules (reflexivity, symmetry, transitivity, congruence for every former, Fig. 6/11), the **conversion rule**

```
Γ ⊢ s : A    Γ ⊢ A = B
──────────────────────
Γ ⊢ s : B
```

and for each (Γ, s, t) ∈ R the (deliberately asymmetric) rule `Γ ⊢ s : A ⇒ Γ ⊢ s = t`. Conditions on R: weakening, substitution, suspension ("tame" = all three), support (supp s = supp t), conversion (t has every type s has). Plain CaTT = CaTT_∅.

**Disc removal.** `Γ ⊢ coh(Dⁿ : U^n_{Dⁿ})[{A, s}] = s`: a unary composite equals its argument.

**Endo-coherence removal.** `Γ ⊢ coh(Δ : s →_A s)[σ] = 1[{A[σ], s[σ]}]`: a coherence from a term to itself is the identity.

**Pruning** (CaTT_su). If `coh(Δ : A)[σ]` has σ sending a *locally maximal* variable α (not the source or target of another variable) to an identity `1[…]`, then `coh(Δ : A)[σ] = coh(Δ//α : A[π_α])[σ//α]`, where Δ//α removes α and its target, π_α : Δ → Δ//α sends α to an identity, and σ//α drops the two corresponding terms.

**su = disc removal ∪ endo-coherence removal ∪ pruning.** CaTT_su: reduction is confluent and terminating, equality decidable; models are strictly unital ∞-categories.

**Insertion** (CaTT_sua, §3). Pasting contexts are presented as planar trees. An *insertion point* (S, P, T): trees S, T and a branch P of S with branch height bh(P) ≤ trunk height th(T) and leaf height lh(S) ≥ dim T. An *insertion redex* adds Γ, σ : S → Γ, τ : T → Γ with `⌊P⌋[σ] ≡ C_T^{lh(P)}[τ]` (the locally maximal argument at P is the standard coherence over T). The constructions: inserted context `S ≪_P T` (a pasting diagram, and a pushout of S ← Dⁿ → T, Thm 28), interior substitution ι : T → S ≪_P T, exterior substitution κ : S → S ≪_P T, inserted substitution σ ≪_P τ. The rule:

```
Γ ⊢ coh(S : A)[σ] = coh(S ≪_P T : A[κ])[σ ≪_P τ]
```

**sua = insertion ∪ disc removal ∪ endo-coherence removal** (insertion subsumes pruning). CaTT_sua: reduction strongly terminating (Cor. 42) and confluent; equality and type checking decidable; formalised in Agda (Rice, thesis 2502.17068).

## 5. What this project takes from each

| Piece | Uses equations? | Portable to our kernel |
|---|---|---|
| Thm 3.8 / Prop 3.9 criterion | no | yes: it is the side condition of a derivable-invertibility rule |
| `Inv` type + destructors + inv-intro + can-intro | only through β/η | yes, as formation/intro/elim rules **without** the β/η and can equations |
| rec | its β-rules | the intro rule alone is sound; whether it is needed once invertibility of every derived cell is given by can-style rules is open (it is used for images under arbitrary constructions; see `invertibility-markings.md` §1.4) |
| Walking equivalence Eⁿ | no | yes |
| Marked generators (2606.30254) | no | yes; matches "marked declarations" in `limits-representables.md` §4.1 |
| CaTT_su / CaTT_sua | yes (conversion) | no (standard 5); useful only as a semantic comparison point |
