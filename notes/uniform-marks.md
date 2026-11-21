# Invertibility marks over the uniform core V + S, and what `ord` recovers

*2026-11-21, thread MKL. Ledger items S4, E7, S8. Builds on `invertibility-markings.md` §1–3 (two-tier marks), `spec/02-lax-core.md` §2.2–2.3 (the side condition read through the Gray projection π), `design-decisions.md` §1.7 (V and the switches), and the verified r8 answer on the forced base B (`conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`, Response 1). Agda: `src/CaTTExp/Uniform/InnerInv.agda`, `src/CaTTExp/Uniform/Marks.agda`.*

*Markers: **[proved]** proved here; **[Agda]** machine-checked; **[cited]** a verified answer, not re-proved; **[finding]**; **[conj]**; **[hyp]** a hypothesis on models, stated so that it can be checked or refuted.*

## 0. Summary

*Superseded in part by §8 (2026-11-21, after the researcher answer): (IL) and (U) are false; (OP-inv_S) is repaired to (OP-inv_S′); relative coherence of V + S over 𝔉 fails in every setting; the Gray-to-strict lemma (E5) holds.*

1. **Restated rules (§3).** Over V + S the propagation rules split by the Gray image of the designated lift c of a coherence. If π(c) is the total cell τ_Γ, the two-tier premises are read on the top generators of U(Γ) exactly as before, plus one new premise for the inner top letters of c. If π(c) is an identity (an *inner coherence*, such as an inner interchanger), the new rules (ORD) and (INN-fac) apply. Nothing else changes: (COH-inv), (DES), (INV⇒PS), (PS*), (OBJ-k) and the marked declarations are as in spec §3.3.
2. **What is proved outright, in every algebra of every admissible theory satisfying S (§4).**
   - (COH-inv), the composite step of (OP-inv), and (ORD), with `C ord` meaning "every inner letter landing in a hom into C is invertible" **[proved]**.
   - (INN-fac): an inner interchanger with an invertible **left** input is invertible when the inner composite-crossing law (left split) is on, and one with an invertible **right** input is invertible when R is on **[proved, Agda: `Uniform.InnerInv.left-inv`, `right-inv`]**.
   - Outer cylinders (a moving globe against an edge: whiskerings, the naturality cells r and t) with an invertible moving input are invertible in **every** setting, from the outer unary subdivisions of B **[proved]**.
3. **Finding: in setting ∅ the two-tier factor rule (INV-fac) for outer letters is exactly as strong as (INV-fac) for inner interchangers (§4.6).** The binary join h(A, B) of V's base satisfies r̄₁ = h · ῑ₋. With A invertible, h is invertible iff the inner interchanger ῑ₋ is. So the two-tier rules cannot be transported letter by letter to V without either a split law or a hypothesis on models. The restated rules are therefore sound for the model class 𝓜_S cut out by one hypothesis (IL, §2.3), which contains every strict Gray-enriched category and every strict ω-category; whether every algebra of every admissible theory satisfying S lies in 𝓜_S is open (outbox Q1).
4. **`ord` everywhere versus two-tier L (§5, E7).**
   - Every two-tier judgment (term and `inv`) whose coherences are lifted by uniform ones is a uniform judgment once every object is `ord` **[proved]**, and the uniform rule set with `ord` everywhere decides `inv` at least as often as the two-tier one on the projected head **[Agda: `Uniform.Marks.ord-covers-two-tier`]**.
   - **Finding: in settings without the inner law, `ord` everywhere does not recover two-tier L by the coherence rule.** In the strip of spec §2.3 Example (b), u and v have the same Gray image and no cell between them in F_V; two-tier L accepts coh(u → v), and no uniform coherence and no inverse of an `ord`-invertible cell gives a term u → v. Whether some longer uniform-plus-`ord` term does is equivalent to a relative coherence statement for V + S over 𝔉 (outbox Q2), and a candidate countermodel (ℤ-valued tags in the model of (K44)) would rule it out.
   - With both splits on (the T₁₂ profile) the strip obstruction disappears; recovery is then exactly relative coherence of F_{T₁₂} over 𝔉, the same shape as the open syntactic half of P = L + marks (E5). Both are posed as one general question (outbox Q2).
   - The E7 experiment: inside an object C, the directed Eckmann–Hilton pair is two separate directed 4-cells; with `(C : ⋆)^ord` each is invertible by (ORD), and with the inner law or R on, by (INN-fac) at an invertible input too (§5.4).
5. **S8, which derived constructions need marks (§6).** A construction is valid verbatim in a core exactly when every coherence head it emits is accepted there. Constructions emitting only heads inside one hom with no interchange inside that hom transfer to every core with no marks. Heads across objects need `ps*`/`inv` marks making the mixed cells invertible (two-tier) and, in addition, `ord` on the target object under V + S. In each case the marks are necessary but not sufficient: the remaining step is the relative coherence lemma of outbox Q2 (E5 for across objects, E7 for inside an object). The table in §6 gives the verdict per construction of spec chapter 5.

---

## 1. What the rules use of F_{V+S}(Γ)

Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ is a pasting context with objects a₀, …, aₙ, and S ⊆ {inner law, R} a setting. F := F_{V+S}(Γ). Facts used, with sources:

- **(F1) Cells are paths of letters.** Every d-cell of F is a ∗_{d−1}-composite (a path) of *contextual letters*: a d-dimensional letter of the T₁₂ signature applied to arguments, whiskered by lower-dimensional cells. [cited: (K50) for T₁₂, pulled back to V by r8 Response 1, "Typed paths, explicit faces, least occurrence representatives".]
- **(F2) Whiskering is strictly functorial, composition strictly associative and unital.** The structural theory of B is that of ω-sesquicategories. [cited: lax r8 §1, "strictly associative and unital"; B contains "the structural theory".]
- **(F3) The Gray projection is generator-preserving.** π : F → 𝔉(Γ) sends each letter to a whiskered Gray generator (the letter is **outer**) or to an identity (the letter is **inner**). [cited: spec §2.3 *Semantics*; r8 Response 1, "generator-preserving maps".] Consequence used below: if π(p) is an identity for a path p, every letter of p is inner, because in 𝔉(Γ) a nonempty composite of whiskered generators is not an identity (positive Steiner chains, strong loop-freeness).
- **(F4) Unit laws.** An interchanger with an identity input is an identity: ι(1, G) = 1, ι(F, 1) = 1, at every cut. [cited: B's "fixed face and unit declarations"; spec §2.3 requirement 5 with degenerate substitutions.]
- **(F5) Outer unary subdivisions.** At cut 0, a cylinder of a composite moving globe against an edge is the paste of the cylinders, and likewise for a composite edge (stationary subdivision). [cited: B contains "the outer unary subdivisions in both variables", r8 Response 1, proved forced in every admissible theory.]
- **(F6) The switches.** The inner composite-crossing law is the left split of the inner interchanger ι, R the right split; each is an unguarded law of V + S exactly when it is in S. [cited: `joining-completion.md` §8; spec §2.3.] In V itself the binary splits at inner cuts are absent, and the outer binary subdivisions of round 5 are present only in guarded form.
- **(F7) No non-identity invertible cells on pasting diagrams.** Every non-identity cell of F has positive conserved weight, so a cell with a two-sided inverse is an identity. [proved from (K50)'s positive gradings: weights add under composition, so p ∗ q = 1 forces weight(p) = 0.]
- **(F8) The designated lift.** A coherence head (Γ, t →_A u) has a designated lift c with π(c) of full support: π(c) = τ_Γ (**Gray operation case**) or π(c) = an identity on a full-support cell (**Gray coherence case**); in the latter, either ⟦t⟧ = ⟦u⟧ in F (**coherence case**, c an identity) or not (**inner coherence**). [spec §2.2.]

Nothing below uses an explicit description of V's letters beyond (F1)–(F8) and, in §4.6, the binary join of (K45), which lies in P ⊆ B ⊆ V.

## 2. Semantics of the marks over V + S

### 2.1 Models

A **model in setting S** is an algebra 𝒦 of an admissible theory E whose free objects on pasting diagrams receive F_{V+S} generator-preservingly (r8: every admissible E containing the laws of S). A term over a context Δ is interpreted under an assignment ρ : Δ → 𝒦 by transporting designated lifts (spec §2.2). This is the strict semantics in which spec §2.3 states uniform L sound; it is the uniform analogue of the strict model of two-tier L (`Strict/Soundness.agda`). Invertible means strictly invertible.

### 2.2 The marks

- `t inv`: ⟦t⟧ is invertible.
- `t ps`: for every cell y with hd(y) ≥ 1 composed before t, the **uniform Gray cell** G(y, t) is invertible. Here, for a tuple of cells x₁, …, xₙ in consecutive homs with dimensions d₁, …, dₙ, G(x₁, …, xₙ) is the op-case coherence over the wedge of disks ΣD^{d₁} ∨ … ∨ ΣD^{dₙ} with its canonical ∂⁻ → ∂⁺ type, substituted by the xᵢ. Its designated lift is the lift of the top atom of U(ΣD^{d₁} ∨ … ∨ ΣD^{dₙ}) (on ΣD² ∨ ΣD² this is W of (K10)).
- `t ps*`, `C grpd_k`: as in spec §3.2, with the ps above.
- **`C ord`**: for every pasting context Γ, every algebra map σ : F_E(Γ) → 𝒦 and every **inner** letter ℓ of F_{V+S}(Γ) in a hom F(Γ)(aᵢ, aⱼ) with σ(aⱼ) = C, σ(ℓ) is invertible.

The definition of `ord` quantifies over all inner letters, of every dimension, not only elementary interchangers. This is forced: for objects the analogue of the C1″ counterexample (`invertibility-markings.md` §1.3) is the question whether invertibility of the elementary interchangers already makes their naturality cells, joins and higher route cells invertible, which is part of outbox Q1. Under (INN-fac) the elementary ones alone are a sufficient premise only for elementary interchanger heads.

### 2.3 The hypothesis on outer letters

**(IL) [hyp; refuted 2026-11-21, see §8.1].** For every pasting context Γ, every outer letter ℓ of F_{V+S}(Γ) with π(ℓ) a whiskering of the Gray generator x₁ ⊗ … ⊗ xₙ, and every σ : F_E(Γ) → 𝒦: if σ(G(x₁, …, xₙ)) is invertible then σ(ℓ) is invertible.

𝓜_S is the class of models in setting S satisfying (IL).

- **Every strict Gray-enriched category and every strict ω-category is in 𝓜_S, for every S** [proved]. Such a 𝒦 is a T₁₂-algebra with every inner letter sent to an identity (r8: "the inner-identity algebras are precisely those of T with the inner identities"; requirement 4). Then σ factors through 𝔉(Γ) on each hom, σ(ℓ) is a whiskering of σ(G(x)), and whiskering preserves invertibility.
- **(IL) is automatic for outer letters that are themselves whiskered Gray cells**, and for outer cylinders (§4.5).
- **(IL) is not automatic in setting ∅ for the binary join h** unless the inner interchanger it factors through is invertible (§4.6). So (IL) is a genuine restriction of the model class in setting ∅, unless outbox Q1 shows it is derivable.
- **Invisibility.** By (F7), on free objects on pasting diagrams (IL) only constrains letters whose Gray cell is an identity. It holds there iff every outer letter instance whose Gray cell is an identity is itself an identity (**(U)**, part of outbox Q1). If (U) holds, adding (IL) to any admissible E (as partial inverse operations guarded by invertibility of the Gray cell) leaves its free objects on pasting diagrams unchanged, so it does not change the side condition. The kernel's side condition never depends on the marks in any case; (U) only decides whether free algebras on pasting diagrams lie in 𝓜_S.

## 3. The rules over V + S

Notation as in spec §3.1. For a coherence coh_{Γ,A}[γ] with designated lift c, **TopGray(Γ)** is the set of top generators of U(Γ), and **inner-top(Γ, A)** holds iff some lift of the head (any cell ⟦t⟧ → ⟦u⟧ with π of full support) has an inner letter of dimension dim c. Both are computed by the side-condition procedure of spec §2.3 (finitely many bounded paths). **ord-tgt** means γ(aₙ) is an object variable marked `ord`; every letter of c lies in the hom F(Γ)(a₀, aₙ), so this is the only object that matters for c.

```
(COH-inv)    coherence case (c an identity)                                ⇒  inv
(OP-inv_S)   Gray operation case, and
               (a) for every g ∈ TopGray(Γ): g[γ] inv  (g[γ] = G(x₁[γ], …, xₙ[γ]))
               (b) inner-top(Γ, A) ⇒ ord-tgt                                 ⇒  inv
(OP-ps_S)    Gray operation case, and
               (a) for every g ∈ TopGray(Γ): g[γ] inv, or some xⱼ with dⱼ ≥ 1 and xⱼ[γ] ps*
               (b) inner-top(Γ, A) ⇒ ord-tgt                                 ⇒  ps
(ORD)        inner coherence, and ord-tgt                                    ⇒  inv
(INN-fac_S)  inner coherence whose head is the elementary inner interchanger
             Σᵏ(ΣD^p ∨ ΣD^q), k ≥ 1, with inputs F (left) and G (right), and
               (inner law ∈ S and F inv) or (R ∈ S and G inv)                ⇒  inv
(INV-fac), (INV-obj), (PS-fac)   on uniform Gray cells g[γ], as in spec §3.3
(INV⇒PS), (PS*), (OBJ-k), (DES), (mark)   unchanged
```

Remarks.
- Read on a single hom (n = 1) with no interchange inside Θ₁, F = 𝔉 = ν, inner-top is false, and the rules are exactly the two-tier rules, which there are ICaTT's can-intro.
- (OP-inv_S)(a) is literally the two-tier premise, because π(c) = τ_Γ and π is generator-preserving: the outer top letters of every lift project onto TopGray(Γ). Only (b) is new.
- (b) is needed. On Σ(ΣD¹ ∨ ΣD¹) inside an object (hom-1 cells α : f ⇒ f′ and β : g ⇒ g′ of 𝒦(X, C), composable along a hom-0 cell), the strict composite of α and β is the Gray operation case, but a lift from one layering to the other contains the inner interchanger ι(α, β) as a top letter. So a composite of invertible cells inside an object is invertible by this rule only when its inner top letters are, which `ord` (or (INN-fac)) supplies.
- (INN-fac_S) is the spec's "(INV-fac)-style rule for inner generators" (§3.6), restricted to the cases it is sound in. In setting ∅ it is empty.
- **Non-collapse.** Without `ord` marks and with S = ∅, no rule makes an inner interchanger invertible: (ORD) needs a mark and (INN-fac_∅) is empty. With S ∋ inner law, an inner interchanger becomes invertible only from an invertible input, as an outer one does in two-tier L.
- **Decidability.** Every premise is a finite computation given the side-condition procedure; the Agda encoding (`Uniform/Marks.agda`) takes that procedure as a parameter (ledger S3, owner ULC, is implementing it).

## 4. Soundness

Throughout, 𝒦 is a model in setting S, σ = ⟦γ⟧_ρ, and the marks of Δ hold semantically under ρ.

**Lemma 4.1 (composites) [proved].** If every letter of dimension d = dim c in a path representing c has invertible σ-image, σ(c) is invertible.
*Proof.* By (F1), c = w₁ ∗_{d−1} … ∗_{d−1} w_m with wᵢ a whiskered d-letter. σ preserves ∗_{d−1} and whiskering. Whiskering by lower cells is a strict functor (F2), so it sends a two-sided inverse to a two-sided inverse. A ∗_{d−1}-composite of invertible cells is invertible, with the reversed composite of inverses. ∎

**Lemma 4.2 (inner coherences are inner) [proved].** In an inner coherence every letter of c is inner. *Proof.* π(c) is an identity; apply (F3). ∎

**Theorem 4.3 (COH-inv, ORD) [proved].** (COH-inv): σ(c) = σ(1) is an identity. (ORD): by Lemma 4.2 every letter of c is inner and lies in F(Γ)(a₀, aₙ) with σ(aₙ) = ρ(γ(aₙ)) marked `ord`, so each is invertible by the meaning of `ord`; Lemma 4.1 concludes. ∎

**Theorem 4.4 (INN-fac) [proved; Agda `Uniform.InnerInv`].** Let ι(F, G) : (f ◁ G) ∗ (F ▷ g′) ⇛ (F ▷ g) ∗ (f′ ◁ G) be an inner interchanger (orientation of spec §2.3 Example (a)) in a model satisfying the unit laws (F4).
- If the left split ι(F₁ ∗ F₂, G) = (ι(F₁, G) ▹ (F₂ ▷ g′)) ⨾ ((F₁ ▷ g) ◃ ι(F₂, G)) holds and F has a two-sided inverse F′, then ι(F, G) has the two-sided inverse ψ = (F ▷ g) ◃ (ι(F′, G) ▹ (F ▷ g′)), up to the boundary identifications F ∗ F′ = 1, F′ ∗ F = 1.
- If the right split holds and G has a two-sided inverse G′, then ψ = ((f ◁ G) ◃ ι(F, G′)) ▹ (f′ ◁ G) is a two-sided inverse.

*Proof (left case).* Apply the split to F ∗ F′ = 1 and whisker on the right by F ▷ g′: the unit law gives an identity, and the split gives ι(F, G) followed by ψ after (F′ ▷ g′) ∗ (F ▷ g′) = 1 is absorbed. Apply the split to F′ ∗ F = 1 and whisker on the left by F ▷ g: the identity equals ψ followed by ι(F, G). The right case is the mirror image. The Agda proof uses only the ω-sesquicategory axioms of (F2), the unit law and the split, as fields of a record; no postulate. ∎

Consequence for the rule: when the head is the elementary inner interchanger, its designated lift is the elementary interchanger letter (requirement 3 gives it; any other lift would be a different path of inner letters with the same endpoints, which the soundness of the rule as stated does not need, because ρ interprets the head by its designated lift; if S11 identifies all lifts this remark is moot).

**Theorem 4.5 (outer cylinders) [proved; not machine-checked].** In every setting, a cylinder r(A, b) (a moving globe A against an edge b, at cut 0) is invertible when A is, and so is t(a, B) when B is.
*Proof.* Same algebra as Theorem 4.4, with the moving-argument subdivision of (F5) (the cylinder of A₁ ∗ A₂ against b is the paste of the two cylinders, whiskered so that they compose) in place of the split. That subdivision is a law of B, hence of every setting, and the unit declarations of B give r(1, b) = 1. The paste has the shape of the left split (the cylinder of the first piece, whiskered, then the second), so the computation of Theorem 4.4 applies verbatim with r in place of ι. For t(a, B) use the subdivision in the other variable, which has the shape of the right split. Whiskerings are the case of a 0-dimensional stationary input. ∎

This gives (INV-fac) for every uniform Gray cell with one positive-dimensional factor (n = 2, one dᵢ = 0) and (INV-obj) (composites and whiskerings of invertible 1-cells), in every algebra. For Gray cells with two or more positive factors the strict two-tier argument needs the outer *binary* subdivision of the top atom, which V has only in guarded form (F6). That case is part of (IL)'s content and of outbox Q1.

**4.6 Finding: the binary join ties outer invertibility to inner invertibility [proved].** On ΣD² ∨ ΣD² (notation of (K8)/(K10); the binary join is in P, hence in B and V by (K45) and r8), h(A, B) : S → U₀ satisfies
```
r̄₁ = h(A, B) · ῑ₋,      π(h) = π(r̄₁) = (A ⊗ β₁) whiskered,      π(ῑ₋) = identity.
```
Suppose A is invertible. r̄₁ is a whiskered outer cylinder of A, so it is invertible in every setting (Theorem 4.5). Hence h is invertible iff ῑ₋ is: if ῑ₋ is invertible, h = r̄₁ · ῑ₋⁻¹; if h is, ῑ₋ = h⁻¹ · r̄₁. Now ῑ₋ is the whiskered inner interchanger χ₂ of (K8), whose inputs are the A-cylinder a = A ⊗ g (invertible) and the B-cylinder b = f ⊗ B. So:
- with the split for the side on which a sits switched on, ῑ₋ is invertible (Theorem 4.4) and so is h: (IL) holds for h in that setting without hypothesis;
- in setting ∅, (IL) for h is equivalent to (INN-fac) for ῑ₋, which no law of V is known to give.

So the two-tier rule (INV-fac) cannot be read letter by letter on F_V without either a split or a hypothesis such as (IL). This is why §2.3 states (IL), and why (INN-fac) and (IL) are posed together as outbox Q1.

**Theorem 4.7 (OP-inv_S, OP-ps_S, Gray-cell rules) [proved for 𝓜_S; 𝓜_S contains no free algebra, so (OP-inv_S) is replaced by (OP-inv_S′), Theorem 8.1].** In a model in 𝓜_S, all rules of §3 are sound.
*Proof.* (OP-inv_S): the top letters of c are outer or inner. An outer one projects to a whiskered g ∈ TopGray(Γ) (generator-preserving π and π(c) = τ_Γ), and σ(G(g)) is invertible by premise (a), so σ(ℓ) is invertible by (IL). An inner one exists only if inner-top(Γ, A), and then ord-tgt and `ord` make it invertible. Lemma 4.1 concludes. (OP-ps_S): as two-tier Lemma 2.3, with y ⊗ c replaced by the lift of G(y, c), whose top letters over the wedge are handled the same way. (INV-fac), (INV-obj), (PS-fac) on uniform Gray cells: the two-tier proofs (`invertibility-markings.md` §2, Lemmas 2.1–2.2) are statements about the cell σ(G(x)); for one positive factor Theorem 4.5 proves them in every algebra; for several, (IL) applied to the top atom of the wedge reduces them to the two-tier statement in the Gray quotient of the hom when the target is `ord`, and otherwise they are exactly what (IL) asserts. The remaining rules are as in two-tier L. ∎

**Status of soundness.** Sound in every model, with no hypothesis: (COH-inv), (ORD), (INN-fac_S), (INV-fac)/(INV-obj) for one positive factor, (INV⇒PS), (PS*), (OBJ-k), (DES). Sound in 𝓜_S: the rest. (IL) holds in every strict Gray-enriched category and strict ω-category, for every S.

## 5. `ord` everywhere versus two-tier L (E7)

Let Δ have every object variable marked `ord`.

**5.1 Inclusion (S2, closed by SPEC).** Every uniform head is a two-tier head: π(c) witnesses SC_𝔉. So uniform L ⊆ two-tier L on terms, in every setting.

**5.2 Marks cover the two-tier marks [proved; Agda `Uniform.Marks.ord-covers-two-tier`].** For a head accepted by uniform L, with every object `ord`: if the two-tier rules derive `inv` (resp. `ps`) for the projected head, the uniform rules derive it. *Proof.* Two-tier (COH-inv) on the projected head means the Gray coherence case: then the uniform head is a coherence case (uniform (COH-inv)) or an inner coherence ((ORD), ord-tgt holds). Two-tier (OP-inv)/(OP-ps) means the Gray operation case with premise (a); premise (b) holds because ord-tgt does. The factor rules on Gray cells coincide. ∎

**5.3 Two-tier coherences that uniform L lacks.** *(Revised in §8.3: recovery fails in every setting.)* The converse direction asks: for every two-tier-accepted head (Γ, t → u) is there a uniform-plus-`ord` term of type t → u?
- **If the π-fibre is connected by inner coherences [proved].** Call the head *inner-connected* if there are terms t = t₀, t₁, …, t_m with ⟦t_m⟧ = ∂⁻ of a lift and terms u_m′, …, u₀ = u with ⟦u_m′⟧ = ∂⁺ of that lift, consecutive ones related in one direction or the other by a term that is an inner coherence (over some pasting context, substituted). Then each such term is invertible by (ORD), and composing the lift's coherence with these terms and the inverses given by (DES) yields a uniform-plus-`ord` term of type t → u. In the Gray coherence case the lift is an identity and only the zigzag remains. This covers every two-tier head whose two sides differ in V by one inner interchanger in either direction, such as the directed Eckmann–Hilton of §5.4.
- **Finding: the strip [proved for the coherence rule; conj in general].** Spec §2.3 Example (b): inside a hom of C, u = W(A₁ ∗ A₂, B) and v = the paste of W(A₁, B), W(A₂, B). In settings ∅ and {R}, ⟦u⟧ ≠ ⟦v⟧, π(⟦u⟧) = π(⟦v⟧) with full support, and neither reaches the other. So two-tier L accepts coh(u → v) (coherence case), uniform L accepts no coherence of type u → v or v → u, and `ord` cannot help directly because there is no cell to invert. The mirror strip (a composite right operand) does the same in settings ∅ and {inner law}. With both splits on, ⟦u⟧ = ⟦v⟧.
  - **[conj] no uniform-plus-`ord` term of type u → v exists in settings ∅ and {R}.** A countermodel would be the tagged model of (K44) with tags in the free abelian group on operand-length pairs instead of subsets: every inner letter then has an inverse tag, so every object is `ord` and (IL) holds coordinatewise with a Gray-category coordinate, while u and v keep different tags and the tag coordinate has only identities one degree up. What is not checked in-house is that this algebra satisfies all of V's laws (the subset tags of (K44) are idempotent; the group tags are not). Outbox Q2, fallback part.
- **Both splits on.** Recovery is then the statement **RC_{T₁₂/𝔉}**: two parallel uniform terms with equal Gray image are connected by an invertible uniform-plus-`ord` term. This is a relative coherence lemma of the same shape as the open syntactic half of P = L + marks (`invertibility-markings.md` Conjecture 3.2, E5), one level down: inside a hom, uniform L with `ord` should be to two-tier L what L⁺ is to P. Outbox Q2 asks both at once.

So "marking every object `ord` gives two-tier L" is **true for marks** (5.2), **false for the coherence rule alone in settings without both splits** (5.3, the strip), **conjecturally false for all uniform terms in settings without the inner law**, and **open (relative coherence) in the T₁₂ setting**. The design consequence, recorded in the spec rather than decided here: a development that wants ordinary objects in the full sense of two-tier L needs both switches on as well as `ord`; `ord` alone gives invertible inner interchange but not the inner coherence equations.

**5.4 The E7 experiment: directed Eckmann–Hilton inside an object.** Take Δ = (X, C : ⋆, x : X → C, a, b : 1_x ⇒ 1_x) (2-cells of 𝒦, hom-1 cells of 𝒦(X, C), endomorphisms of the hom-0 cell x).
- The inner interchanger head is Γ = Σ(ΣD¹ ∨ ΣD¹) (two hom-1 cells α : f ⇒ f′, β : g ⇒ g′ of 𝒦(X, C) composable along a hom-0 cell), an inner coherence whose lift is the elementary interchanger, oriented by position as at the outer level ((K9)): `coh_Γ((f ◁ β) ∗ (α ▷ g′) → (α ▷ g) ∗ (f′ ◁ β))` is accepted in every setting, and its reverse in none (requirement 3).
- Substituting f, f′, g, g′ := 1_x and (α, β) := (a, b) gives EH₁ : b ∗ a ⇛ a ∗ b; substituting (α, β) := (b, a) gives EH₂ : a ∗ b ⇛ b ∗ a. **Directed Eckmann–Hilton is this pair of directed 4-cells**, which are not inverse to each other: their composites are endomorphisms with identity Gray image, and nothing in V identifies them with identities.
- With `(C : ⋆)^ord`, (ORD) makes EH₁ and EH₂ invertible, so the inverse of EH₁ is a second cell a ∗ b ⇛ b ∗ a beside EH₂. With the inner law or R on and a (resp. b) declared `inv`, (INN-fac) makes them invertible without `ord`.
- In two-tier L the same head is in the coherence case (the hom is strict), so EH is one invertible coherence. P has the same.
- Mechanical run: the rule-level computation is checked by evaluation in `Uniform/Marks.agda` (`eh-*` examples) on the head data above; computing F_V(Σ(ΣD¹ ∨ ΣD¹)) itself needs the uniform checker (S3, owner ULC).

## 6. S8: which derived constructions need marks

**Principle.** A construction of spec chapter 5 emits terms built from coherences coh_{Q,B}[γ] whose correctness is proved with CaTT's side condition (equality in ν(λQ)). In a core K (two-tier, or V + S) the same term is valid iff every emitted head is accepted by K. Classify each emitted head by its pasting context Q = ΣΘ₁ ∨ … ∨ ΣΘₙ:
- **(H1) interchange-free**: at most one hom of Q contains cells of hd ≥ 1, and that hom's pasting diagram is, up to suspension, a globe or a chain of globes glued along consecutive faces (a "vertical" chain). Examples: chain contexts C(w) of 1-cells (no cell of hd ≥ 1 at all), whiskerings, vertical composites, unitors and associators of 1-cells. U(Q) has no mixed generator, so 𝔉(Q) = ν(λQ), and on these arities B forces every inner operation to its killed value (r8 Response 1: the hemisphere argument for a moving globe Dᵖ and for "a nonempty consecutive interval of top generators"), so F_{V+S}(Q) = 𝔉(Q). The head is accepted by every core. **No marks.**
- **(H2) one hom with interchange inside it** (n = 1, Θ₁ a wedge of ≥ 2 suspensions with positive cells in two of them): accepted verbatim by two-tier L (E1 conservativity). Under V + S the CaTT head is in the Gray coherence case or Gray operation case of 𝔉, and is accepted iff its V-fibre is connected (§5.3). Needs **`ord` on the hom's target object** and, beyond that, relative coherence RC_{V+S/𝔉} (outbox Q2); in settings without the matching split the strip-shaped heads fail even with `ord`.
- **(H3) across objects** (n ≥ 2 with positive cells in two homs): two-tier L accepts the head only if CaTT's strict equality is already a Gray equality or a Gray operation; otherwise the head uses a mixed cell backwards and needs every mixed Gray cell it inverts to be invertible: **`ps*` on every later positive factor, or `inv` on a positive factor** (rules (PS-fac), (INV-fac)), and then the relative coherence lemma of E5 (Conjecture 3.2's missing step) to produce the term. Under V + S, add `ord` on the target object for the inner letters of the lifts.

**Per construction.** "Inside one hom" means the input context is a suspension ΣΓ′ lying in a hom 𝒦(X, C), which is how the notes use RC, N and cones for elements of objects (spec §5.0). The algorithms commute with suspension (run them on Γ′ and suspend the output), so every head they emit is then a single-hom head Σ Q′.

**Native naturality needs no construction.** For a native lax transformation α in 𝒦(B, C) and any cell c of 𝒦(X, B) (a coherence term or not), the naturality cell of α at c is the uniform Gray cell G(c, α): one op-case coherence over ΣD^{hd c + 1} ∨ ΣD^{hd α + 1}, accepted in every core with no marks. Its boundary is built from the Gray cells of α at the boundary of c, so its "naturality of naturality" is again a Gray cell. The N construction of spec §5.2 is needed only when the transformation is given as cylinder data inside a context rather than as a cell of 𝒦.

| Construction (spec §) | Emitted heads | Two-tier L | Uniform V + S |
|---|---|---|---|
| RC(1) (5.1) | chain contexts C(w), (H1) | no marks | no marks |
| RC(n ≥ 2), inside one hom (5.1) | (H1) and (H2): sequentialization and exchange use interchange heads of 2-cells along 0-cells of the hom | no marks (E1) | `ord` on C, and RC_{V+S/𝔉} (Q2); fails for strip-shaped exchanges without the matching split |
| RC(n ≥ 2), across objects | (H3): the exchange step inverts mixed Gray cells | `ps*` on later positive variables (or `inv` on one factor) + E5 relative coherence | the same, plus `ord` on the targets |
| N over Q↑Y, Y without objects, inside one hom (5.2) | RC on the cylinder Q↑Y, which stays in the hom | no marks | as RC inside one hom |
| N with objects in Y (cylinder data across objects) (5.2) | cylinder generators of objects are 1-cells between objects, squares are 2-cells across objects; RC there is (H3) | `ps*` on the squares (pseudo cylinder) + E5; for a native transformation use G(c, α) instead: no marks | the same, plus `ord` on the target; G(c, α): no marks |
| Explicit cylinders (5.3.1) | context only, no coherence heads | no marks | no marks |
| M ⊗ Dⁿ templates (5.3.2) | boundary and coherence templates by RC in dim ≤ d − 1 on the tensor context, which is across objects when read in 𝒦 | as RC across objects; inside one hom, no marks | as RC across objects / inside one hom |
| Specified cone, globular Γ (5.4.1) | context only (Mikhail's formula); its types use composites of whiskerings, (H1) | no marks | no marks |
| Cones over arbitrary Γ (5.4.2) | Π(Q, B) by RC on the join Cone(Q; c), which spans the homs 𝒦(c, x) and those of Γ | boundaries of hd 0 (the cases `ConeT.cone` builds): (H1), no marks; higher boundaries: as RC across objects | the same; higher boundaries also need `ord` |
| Cocones, transfors (5.4.3) | duals of the above; transfors iterate cylinders | as cones / N | as cones / N |
| Canonical Gray terms (5.5) | Gray tensors of pasting diagrams, computed in 𝔉 itself | no marks (CT is a two-tier statement) | heads with inner letters in their lifts need `ord` on the target, else no marks |

**Worked example (H2 vs H3).** The associator's naturality 3-cell (spec §5.2), generated over the full chain x → y → z → w inside one hom: every head the ladder emits is over a chain or an interchange of 2-cells of the hom along its 0-cells, so two-tier L accepts the generated term as is (and the certified two-tier checker does accept `Generated/AssociatorNaturality.agda`, which is a single-hom instance). Under V the interchange heads inside the hom are inner coherences: with `ord` on the target they are accepted and invertible; the 3-cell itself is accepted when its V-fibre is connected, which for this instance holds iff the inner exchanges it uses are single inner interchangers (no strip), as they are for chains of 1-cells (no composite operand is crossed).

**What remains open for S8.** The verdicts "(H3) needs E5" and "(H2) needs RC_{V+S/𝔉}" are reductions, not proofs; both lemmas are outbox Q2. The table's "no marks" entries are proved (they are (H1) heads or contexts only).

## 7. Open items from this note

| Item | Owner |
|---|---|
| ~~Outbox Q1, Q2~~: answered 2026-11-21, see §8 (`conjectures/answered/invertibility-in-directed-interchange-2026-11-21.md`) | done |
| Re-encode (OP-inv_S′) in Agda; ps* branch and several-factor rules in every algebra; further outer letters under `ord` | E14, MKL |
| Conjecture 3.2: realize the strict comparison cell as an L⁺ term | E5, MKL |
| Running the E7 head computations on actual F_V (needs the uniform checker) | ULC (S3) |
| S11 (uniqueness of lifts) affects only the remark after Theorem 4.4 | SPEC |

## 8. After the researcher answer (2026-11-21)

The outbox prompt was answered. The answer is verified and filed at `conjectures/answered/invertibility-in-directed-interchange-2026-11-21.md`. This section records what changes here. Where it conflicts with §§0–7, **this section wins**. The superseded statements above are marked inline.

### 8.1 What is now known

- **(IL) is false, and so is (U), in every setting** [cited; verified].
  - On Γ = Σ(D² ∨ D² ∨ D³) ∨ ΣD¹, take the outer unary disk E(Z, b), where Z is the Godement composite of an inner square I and the D³ generator x. Its Gray cell is G(x, b).
  - A substitution that contracts x sends G(x, b) to an identity and sends E(Z, b) to E(I, b).
  - E(I, b) is proper (positive charge), so it is not invertible (M5). This holds with both switches on as well.
  - So 𝓜_S contains no free algebra of V + S. (IL) fails along a substitution between free pasting diagrams.
- **The matching split is necessary** for "invertible input ⇒ invertible inner interchanger" [cited; verified]. This is the converse of Theorem 4.4: in setting ∅ there is a V-algebra with F invertible and ι(F, G) not invertible. So (INN-fac_S) is exactly right.
- **Elementary inner interchangers do not control the other inner letters** [cited; verified]. There is a V + both-splits algebra in which every elementary inner square is an identity but a naturality cell is not invertible. So `ord` must mean every inner letter, as §2.2 defines it.
- **Relative coherence fails for both uniform quotients in every setting** [cited; verified].
  - The parallel pair is H : w ⇛ w (the loop (K34), a whiskered elementary inner interchanger on Σ[2] ∨ Σ[2]) and 1_w. Both have the same image under π₁ and under π₀.
  - In a V + S algebra in which every inner letter (respectively every interchanger letter) is invertible, H and 1_w take different values and no 5-cell exists.
  - So F_{V+S}(Γ)[I_k⁻¹] has no cell H ⇛ 1_w, for k = 1 and k = 0 and every S.
- **Relative coherence holds for the Gray-to-strict map** [cited; verified]. This is the missing lemma of E5 (`invertibility-markings.md` §3.2).
  - Let p and q be parallel in 𝔉(Γ) with π_G(p) = π_G(q).
  - Then there is a strict cell p → q, with a strict two-sided inverse, in the strict presentation of each hom with its mixed atoms inverted. That presentation maps into 𝔉(Γ)[mixed⁻¹].
- **Two strips.** These were run together in §5.3, in spec §2.3 Example (b) and in `design-decisions.md` §1.4(a).
  - The **inner strip** is (K44)/(K51): the inner crossing ι(A₁ ∗ A₂, B) against the paste of ι(A₁, B) and ι(A₂, B). It is equal iff the left split (the inner law) holds. Without it, the pair stays unconnected after inverting all inner letters, by the ℤ-tag model with its base collapsed (the old [conj] of §5.3 is now [cited]).
  - The **outer W-strip** on C_{2,1} is W(A₁ ∗ A₂, B), a degree-5 outer lift, against the paste of W(A₁, B) and W(A₂, B). It stays distinct and unconnected after localization **in every setting**, including with both splits.
- **The per-letter criterion.** Whether a given letter becomes invertible with a given argument can be semi-decided by enumerating bounded derivations of V + S with a fresh inverse adjoined. It is complete, but it is not a decision procedure.

### 8.2 Repaired rules

(IL) is false on free algebras. So (OP-inv_S)(a), which reads the premise on the Gray generator g[γ], can conclude `inv` for a term with no inverse. Concretely, a lift whose top letter is E(Z, b), substituted by the contraction, gets a premise that is an identity, while its top letter is not invertible.

The repair keeps the premise on the letter's own operands. Call an outer top letter ℓ of the designated lift c **operand-pure** if its operands are generators of Γ.

```
(OP-inv_S′)  Gray operation case, designated lift c, and
             (a′) every outer top letter ℓ of c is operand-pure and one of:
                  (i)   ℓ is a whiskered Gray cell G(x₁, …, xₙ), and g[γ] inv;
                  (ii)  ℓ is an outer cylinder with moving input x, and x[γ] inv;
                  (iii) ℓ = h(A, B), A[γ] inv, and (ord-tgt, or the split on
                        the side of the A-cylinder in ῑ₋ is in S)
             (b)  inner-top(Γ, A) ⇒ ord-tgt                                     ⇒  inv
(OP-ps_S′)   as (OP-ps_S), with "for every g ∈ TopGray(Γ)" replaced by
             "every outer top letter ℓ of c is operand-pure, and is case (i)
             with g[γ] inv or some xⱼ[γ] ps* (dⱼ ≥ 1), or case (ii) or (iii)"   ⇒  ps
```

**Theorem 8.1 [proved].** (OP-inv_S′) is sound in **every** algebra of every admissible theory satisfying S, with no hypothesis.

*Proof.* Each top letter has an invertible image:
- *Case (i).* ℓ[γ] is the whiskered Gray cell G(x₁[γ], …, xₙ[γ]), by closure under substitution (requirement 5), because the operands are generators. Whiskering preserves inverses.
- *Case (ii).* Theorem 4.5, applied to the substituted moving input.
- *Case (iii).* §4.6: r̄₁ = h · ῑ₋, where r̄₁ is invertible by Theorem 4.5 and ῑ₋ is invertible by `ord` or by Theorem 4.4.
- *Inner top letters.* By (b).

Lemma 4.1 then concludes. ∎

**The ps* branch.** (OP-ps_S′) keeps the old status: proved for 𝓜_S. Case (i) needs no (IL), because the letter is its Gray cell. What it still needs is that two-tier Lemma 2.3 transfers to a uniform Gray cell with several positive factors in an arbitrary V-algebra. That transfer is open and logged as E14.

**What the repair costs.**
- `ord` everywhere still gives every two-tier `inv` judgement for heads whose designated lift has operand-pure top letters of kinds (i)–(iii). Every head over a wedge of disks qualifies, and so does every head whose lift is a single whiskered Gray cell.
- For other designated lifts, the uniform rules now derive less than §5.2 claimed. Typical examples are lifts with W-type letters on composite operands, or lifts with auxiliary letters K, J or shifted joins at the top.
- `Uniform/Marks.agda` encodes the old (OP-inv_S). Its theorems remain true as statements about that encoding, relative to the `Sem` hypotheses. But `Sem`'s field for the operation case is now known to fail on free algebras. Re-encoding the repaired rule is ledger E14.

### 8.3 E7 and S8, revised

- **E7.** `ord` everywhere does **not** recover two-tier L's coherences **in any setting**.
  - The pair (H, 1_w) is accepted as equal by two-tier L (both have identity image) and is unconnected in uniform L even after every inner letter is inverted.
  - The outer W-strip gives a second witness that survives both switches.
  - The inner-connected case of §5.3 still holds: a head whose sides differ by inner coherences is recovered with `ord`.
  - Recovering marks (§5.2) holds as revised in §8.2.
  - Design consequence: in uniform L an object marked `ord` has invertible inner letters, but it is **not** an ordinary ω-category up to coherence. Its inner coherence equations are genuinely missing, and neither switch supplies them.
- **S8.** In §6, every "and RC_{V+S/𝔉}" for (H2) and (H3) heads under V + S becomes: **accepted iff the head's V-fibre is connected. No general relative coherence is available, and marks cannot supply one.**
  - For two-tier L, the (H3) reduction "plus E5's relative coherence" now has its lemma proved (§8.1). What remains is realizing the strict cell v by an L⁺ term; see E5.
  - The "no marks" entries are unchanged.

### 8.4 Corrections to the sections above

- §0 item 3, §2.3, Theorem 4.7: "(IL) is automatic … for outer cylinders" is **wrong as stated**. It holds when the moving operand is a generator, because then the letter is its own Gray cell. (IL) is false in general (§8.1).
- §0 item 4 and §5.3: "with both splits on … recovery is exactly relative coherence" and "open (relative coherence) in the T₁₂ setting" are **refuted**: relative coherence fails in every setting (§8.1). "With both splits on, ⟦u⟧ = ⟦v⟧" is correct for the **inner** strip ι(A₁ ∗ A₂, B) only. It is wrong for the outer W-strip.
- §5.3 [conj] on the ℤ-tag model: now [cited], in the collapsed form of §8.1.
- §6 table, column "Uniform V + S": read "RC_{V+S/𝔉}" as "fibre connectivity, case by case" (§8.3).
