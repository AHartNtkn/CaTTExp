# Mark schemes: is invertibility special? (S35)

*Design note, 2026-11-24. Ledger S35 (new). Thread "Decide whether invertibility needs special marks". Builds on `marking-alternatives.md` (S17, S21, S22), `invertibility-markings.md`, spec chapter 3, `design-decisions.md` §1.4(c) and §1.8 (E12, S31), `semantics-gaps.md` (S3).*

*Markers: **[proved]** proved here; **[Agda]** machine-checked; **[paper]** checked against the source; **[sketch]** argument given, not written out in full; **[proposal]**; **[conj]**.*

## 0. The question and the short answer

Anthony (2026-11-24): a cell is invertible when it carries an infinite tower of coherences (an inverse, unit cells, inverses and units for those, and so on). Other structure declared as part of a category is also an infinite tower. Why treat invertibility specially, instead of handling it like any other declared tower?

**Short answer.**
1. **Declaring invertibility is not special, and the kernel already treats it as a declared tower.** An `inv` mark is a finite name for an infinite tower: (DES) gives t⁻ˡ, t⁻ʳ, λ_t, ρ_t, the mark on λ_t and ρ_t gives the next level, and so on. The tower it unfolds to is the coinductive walking equivalence. ICaTT writes it as a context (Benjamin–Champin–Markakis, arXiv 2602.16602, Def. 4.1: E^{n+1} = D^{n+1} ▷ (e : Inv(d))) **[paper]**. Nothing about the `inv` mark touches the coherence side condition. So the declaration can be one instance of a general mechanism: a **mark scheme**, a finite marked context extension over a generic cell, read coinductively (§2). In Agda, ICaTT's inv-intro is exactly the generic intro of the Inv scheme, for all inputs (§5).
2. **Three facts about invertibility are special, and they are facts about the kernel rules, not about the declaration.**
   - (a) *Closure across all shapes.* Coherences are invertible, and so are composites, whiskerings and Gray cells with an invertible factor. These are the propagation rules (COH-inv), (OP-inv), (INV-fac), (INV-obj), (OBJ-k), (PS-fac). They are theorems about this one tower. A general scheme does not have them: idempotents do not compose (§4.2).
   - (b) *Property, not structure.* Any two inverse towers on a cell are equivalent. This is why one t⁻ˡ per cell (a proof-irrelevant mark) is sound. A general scheme is structure, so its projections have to depend on evidence (§4.3).
   - (c) *Shape-indexed towers cannot be declared this way, whatever they are about.* A law's coherence tower (E12) and `ord` (E13) range over every pasting shape. They go through the side condition. Invertibility's own tower is indexed by dimension only, which is why a finite scheme can carry it (§4.1).
3. **Verdict (§6).** Adopt mark schemes as the general form of cell marks **[proposal]**. Inv, Ps and Grpd_k become three built-in schemes. Their propagation rules stay as built-in closure rules, until a closure criterion for schemes makes them instances of something general. Users may write further schemes, such as adjoint towers and one-sided inverse towers, which the current marks cannot express. Every current judgment is unchanged. `ord`, `iord`, `lsplit` and `rsplit` stay as object modes acting through the side condition. They are not towers.
4. **What is open.** The closure criterion: which schemes are closed under which operations, and whether Inv's closure rules over L can be derived rather than assumed. In plain CaTT they can be derived (Benjamin–Markakis, arXiv 2406.12127, Prop. 16 and Thm 33) **[paper]**. That question goes out as `conjectures/outbox/mark-scheme-closure.md`, and in-house work continues on it (§7).

## 1. What the `inv` mark already is

**The unfolding.** Take `(x : u → v)^inv`. The rules of spec §3.3 give:
- level 0: x;
- level 1: x⁻ˡ, x⁻ʳ : v → u, λ_x : x⁻ˡ ; x → 1_v and ρ_x : x ; x⁻ʳ → 1_u, with λ_x and ρ_x inv;
- level k + 1: the same four cells for each inv cell of level k, one dimension up.

At each dimension this adds finitely many generators, and the pattern at dimension n + 1 is the suspension of the pattern at dimension n.

- **(DES-inv) is not part of this unfolding.** It makes x⁻ˡ inv, which would add cells in x's own dimension. It is a closure fact: x⁻ˡ is invertible with x as an inverse, using λ and ρ (§3.2 of `marking-alternatives.md`).
- **Semantics.** A model interprets the mark by a chosen tower (spec §3.3, Semantics). That is a map out of the walking tower. The intended semantics are the coinductive ones, or inductive ones with exactly these cells marked (`semantics-gaps.md` (S3), citing Hadzihasanovic–Loubaton–Ozornova–Rovelli 2404.14509 and Henry–Loubaton 2301.11424). In those semantics, mapping out of the walking tower is the same as being invertible **[paper, via S3]**.

**So the current design already does what Anthony proposes, for one tower.** The question is whether to fix that one tower in the kernel or let a context declare any tower of the same kind. The rest of this note answers that.

## 2. The general mechanism: mark schemes [proposal]

**Definition.** A **scheme** P of dimension n consists of:
- the disk context Dⁿ with its top variable t;
- a finite list of **∃-clauses**: clause variables c₁ : A₁, …, c_k : A_k, each Aᵢ a type over Dⁿ ▸ t ▸ c₁ ▸ … ▸ c_{i−1}, each optionally marked with a scheme (P itself, or another scheme);
- a finite list of **∀-clauses**: a parameter context Π over Dⁿ ▸ t (for example "a cell y composed before t"), a term s over Dⁿ ▸ t ▸ Π, and a scheme Q, meaning "s carries Q for every instance of Π".

Schemes are suspension-stable: the scheme at dimension n + 1 is the suspension of the one at dimension n. A scheme is written inline in the mark, like INIT's μΔ (spec chapter 9), so that files carry no meaning (spec §0.1).

**The three built-in schemes.**
```
Inv(t : u → v)  :=  ∃ s, s′ : v → u.  ∃ l : s ; t → 1_v [Inv].  ∃ r : t ; s′ → 1_u [Inv].
Ps(t)           :=  ∀ y with hd(y) ≥ 1 composed before t.  (y ⊗ t) [Inv].         (with ps* on boundaries, spec §3.4)
Grpd_k(C : ⋆)   :=  ∀ t with 0-target C and hd(t) ≥ k.  t [Inv].
```

**Rules, generic in the scheme.**
- (S-mark) `(x : A)^P ∈ Γ` gives `Γ ⊢ x : P` by `hyp`.
- (S-proj) If `Γ ⊢ t : P by e`, then for each ∃-clause cᵢ there is a projection term πᵢ(t; e) : Aᵢ[bd t, t, π₁, …], and it carries cᵢ's mark. For Inv this is (DES): π₁ = t⁻ˡ, π₂ = t⁻ʳ, π₃ = λ_t, π₄ = ρ_t. The projections depend on the evidence e, except for property schemes (§4.3), where they depend on t only.
- (S-intro) If cells c₁ … c_k have the clause types, with evidence for the marked clauses, then `Γ ⊢ t : P by intro(c⃗; e⃗)`. For Inv this is ICaTT's inv-intro.
- (S-∀) If `Γ ⊢ t : P` and P has the ∀-clause (Π, s, Q), then for every substitution of Π, `s[t, π] : Q`. For Ps this is (PS-fac); for Grpd_k it is (OBJ-k). **∀-clauses have no intro rule**: Prop. 8.2 of `marking-alternatives.md` shows that a Ps-intro from data could only certify invertible cells, and the same generic-cell argument applies to any ∀-clause whose test can be freely attached.
- (S-sub) A substitution into a P-marked variable must supply evidence that the image carries P. This is S21(c), generalized.
- (S-coh) **[sketch]** Every coherence-case coh carries every scheme whose ∃-clause types are built only from t, its boundary and earlier clause cells. *Argument:* take each clause cell to be a coherence-case coh over the same pasting context. In F_V(Γ), every ingredient is an identity, and parallel cells built from identities by the operations of V are the same identity (a Gray cell with an identity factor is an identity). So each clause type is again a coherence-case type, and the construction repeats one dimension up. For Inv this is (COH-inv) together with BM's Prop. 16. The fullness half of the coherence case is not written out.

**Decidability.** Evidence is finite and checked structurally. Clause cells are type-checked by the certified checker, and their types are compared syntactically. So checking is decidable, as for the S21 evidence layer **[Agda, dimensions 1–2]**. Theorem 3.3 of `marking-alternatives.md` still applies: no scheme that contains Inv can be saturated *and* proof-irrelevant *and* decidable. Evidence is what makes saturation decidable.

**Soundness.** Read a P-marked variable as the infinite context obtained by unfolding the scheme. Its models are models of the base context together with a chosen P-tower on the variable. Then:
- (S-mark) and (S-proj) are projections from that infinite context;
- (S-intro) supplies the first level and delegates the rest to the evidence, by coinduction (the greatest-postfixed-point argument of BM 2406.12127 §3.4);
- (S-sub) is precomposition;
- (S-∀) is the meaning of a ∀-clause.

**[sketch]**; nothing here depends on which scheme it is. The scheme-specific rules (closure, §4.2) need their own soundness proofs, as now.

## 3. What a general scheme can express that `inv` marks cannot

| Scheme | Clauses | Expressible with `inv` marks today? |
|---|---|---|
| **RInv** (coinductive right inverses) | s : v → u; r : t ; s → 1_u [RInv] | No. Declaring r `inv` is strictly stronger: in Γ₃ below, x is RInv but not inv. |
| **LAdj** (adjoint at every level) | s; η : 1 → t ; s [LAdj]; ε : s ; t → 1 [LAdj]; triangle cells [Inv] | Only one level. Today η and ε would have to be plain variables or marked `inv`. |
| **Full dualizability** (every cell has adjoints on both sides, all the way up) | LAdj and RAdj clauses together, recursively | No. In (∞, n) this is a finite tower of n levels; in ω it is genuinely coinductive. |
| **Inv** | as above | Yes (it is the `inv` mark) |

**Worked example (RInv, Agda).** Γ₃ = (a, b : ⋆)(x : a → b)(s : b → a)(r : x ; s ⇒ 1_a)^{RInv}.
- x carries RInv by intro(s, r; hyp).
- x is not derivably inv, and the same data is rejected as Inv evidence.
- One level up, Γ₄ adds s₂ : 1_a ⇒ x ; s and ρ₂ : r ; s₂ ⇛ 1_{x;s}, with the hypothesis only on ρ₂. Then x carries RInv by intro(s, r; intro(s₂, ρ₂; hyp)). The nested level is checked: the hypothesis on the wrong cell fails.

`src/CaTTExp/Gray/MarkSchemes.agda`.

## 4. What is special about invertibility

### 4.1 Periodic towers versus shape-indexed towers (why E12 and E13 do not apply to `inv`)

E12's argument (`design-decisions.md` §1.4(c)) was against a **law** declared as a cell κ : u ≅ v. Two different splittings of A₁ ∗ A₂ ∗ A₃ past B are composites of κ-instances, and nothing relates them unless a 6-cell is declared, then a 7-cell, and so on. That tower is indexed by the **pasting shapes** κ can be used in: composites of any length, in any position. A finite scheme attached to κ adds finitely many cells per dimension, and its clause types mention only κ and its own cells. So it cannot name a coherence between two arbitrary composites of κ-instances. The only finite device that quantifies over every pasting shape is the side condition. That is why laws are object marks acting through the side condition (§1.8 there), and why `ord` is too (E13: inverting every inner letter does not connect H to 1_w).

Invertibility's tower is indexed by **dimension only**: four cells per inv cell per level. The interaction of inverses with arbitrary shapes is not a further declared tower. It is closure (§4.2): the inverse of a composite is built from the components' inverses. So the dividing line is:

| | Tower indexed by | Declarable as a finite scheme | Where it lives |
|---|---|---|---|
| Inv, RInv, LAdj, … | dimension | yes | marks (schemes) |
| Ps, Grpd_k | dimension, plus a ∀ over cells | yes, with ∀-clauses, declared only | marks (schemes) |
| a law κ, the splits, `ord` | every pasting shape | no | side condition (object modes) |

That is the principled reason the `inv` mark can be a tower and `ord` cannot. It is not a reason for invertibility to be the *only* tower.

### 4.2 Closure is a theorem about Inv, not a consequence of declaring a tower

The propagation rules of spec §3.3 conclude `inv` for cells that are not projections of any marked variable. Examples are a vertical composite of two inv cells, a whiskering, and x ⊗ β with x inv. For a general scheme the analogous closure fails.

**Counterexample [proved].** Let Idem(t : a → a) := ∃ c : t ; t → t [Inv]. In the 1-category Set (an ω-category with identity higher cells, a model of L and of P), Idem(t) holds iff t is idempotent. Take e₁, e₂ on {0, 1, 2}:
- e₁ = (0 ↦ 0, 1 ↦ 2, 2 ↦ 2);
- e₂ = (0 ↦ 1, 1 ↦ 1, 2 ↦ 2).

Both are idempotent. The composite e₁ ; e₂ (e₁ first) is (0 ↦ 1, 1 ↦ 2, 2 ↦ 2), which sends 0 ↦ 1 ↦ 2 when applied twice, so it is not idempotent. So no (OP-Idem) rule is sound, and closure under composition is a property of particular schemes.

**What is known for Inv.**
- In plain CaTT (all of weak ω-categories), closure is a theorem, with a syntactic construction. Full coherences are invertible, with inverse coh(B, v → u) and units coherences (BM 2406.12127, Prop. 16, by coinduction). Composites of invertible cells are invertible, with the inverse built by a meta-operation (Thm 33) **[paper, from the abstract and the stated results; the proofs were not re-checked here]**. ICaTT nevertheless adds `can` as a primitive (BCM 2602.16602 §4.3, internalizing their Thm 3.8).
- In L, the rules are proved sound semantically (spec §3.3, Lemmas 2.1–2.3). Whether they are syntactically admissible from the Inv scheme, (S-coh) and (S-intro), is open. Note that in L some invertible cells have no finite certificate at all (§9–10 of `marking-alternatives.md`), so admissibility cannot be taken for granted.

**Consequence for the design.** Under schemes, Inv keeps its closure rules as kernel rules attached to the Inv scheme, exactly as now. A user scheme gets the generic rules only, until a closure criterion (§7) gives it more. That is why user schemes would be less convenient than Inv today: an adjoint tower on f and one on g do not yet give one on f ; g, although they do in every model.

### 4.3 Property versus structure (the completeness angle)

Spec §3.3 interprets the destructors by a choice of inverse for each invertible cell. That is sound because the space of invertibility data on a cell is contractible in the intended semantics. This is exactly where coinductive completeness (Rezk-style) enters: the walking coinductive equivalence is contractible coinductively, but not in the raw inductive theory (S3). So a mark can be proof-irrelevant, with one t⁻ˡ per cell, and two derivations of `t inv` yield the same term.

A general scheme is **structure**. For RInv, two right inverses s, s′ of x need not be related at all. If the projection π₁(x) depended on x only, a substitution x ↦ t would have to pick one right inverse for t globally. Then the data supplied by intro would be forgotten, and the intro rule would say nothing.

So:
- schemes are proof-relevant by default: projections take the evidence, as `linv(e)` does in S21;
- a scheme may be used proof-irrelevantly only when it is a **property scheme**, i.e. its space of towers on any cell is contractible in the intended semantics;
- Inv is one. So is LAdj (adjoints are unique up to contractible choice) **[conj for the coinductive ω case]**. RInv and Idem are not.

The current proof-irrelevant `inv` judgment is the property-scheme special case of the S21 evidence layer, which becomes the general form.

### 4.4 ∀-towers

Ps and Grpd_k quantify over cells that do not exist yet: every y composed before t, or every cell into C. They fit as ∀-clauses. Prop. 8.2 (`marking-alternatives.md`) is the reason they have no intro rule, and it applies to every ∀-clause of this generic kind. That is a fact about ∀-clauses, not about invertibility.

## 5. Machine check

`src/CaTTExp/Gray/MarkSchemes.agda` (checks under `--safe`, Agda 2.7.0.1, no postulates):
- **Schemes as data.** Clause types over the disk context, clause marks naming schemes. Inv and RInv are presented at dimensions 1 and 2. Clause marks that land in dimension 3 name schemes without a presentation, which accept only `hyp` (and, for Inv, the existing evidence layer).
- **Generic checker `checkS`.** Evidence `hyp`, `old e` (the S21 layer, Inv schemes only) and `intro cs es`. Clause cells are type-checked with the certified checker, and their types are compared with the instantiated clause types.
- **`inv₁-instance`, `inv₂-instance`.** For every marked context, term t, candidate cells s, s′, l, r and S21 evidence eL, eR, the generic intro of the Inv scheme, with the unit cells' evidence given as `old eL`, `old eR`, gives the same answer as `inv₁` / `inv₂` of `Gray/MarksSaturation.agda`. So ICaTT's inv-intro is the generic intro of one scheme. Scheme evidence of other forms on the unit cells (`hyp`, nested `intro`) is outside the theorem and can accept more, since scheme hypotheses are invisible to the S21 layer.
- **The Inv tower is connected inside the mechanism.** Inv₁'s unit cells are marked Inv₂, and an example derives Inv₁ for x in Γ₁ from scheme hypotheses on l and r alone, with a wrong-scheme control.
- **RInv examples.** Γ₃ and Γ₄ of §3, with negative controls (no mark, wrong cell, an Inv intro from the same data failing for lack of a left unit, a scheme with no presentation). That `inv` marks cannot express RInv is the informal argument of §3, not a formal result: the Agda checks `x inv` false only with no inv marks.
- **Assumptions, as in `MarksSaturation`.** t is assumed well-typed, and the scheme marks are assumed well-formed (`hyp` and `old` do not check dimensions).
- **Reviewed** by an independent agent (2026-11-24): honest. Its findings were all fixed: Inv₁'s unit cells had been marked with the dimension-3 name, the theorem scope was stated too broadly, and a negative example failed for an arity reason.
- The Γ₁ example of `MarksSaturation` re-derived through the generic intro.

**Not encoded:** projections as term formers (no destructors in the core syntax, E4), ∀-clauses (they are the existing rules, reached through `old`), suspension to dimensions ≥ 3, (S-coh) and (S-sub).

## 6. Verdict by the evidence

| | Inv as the only built-in tower (now) | Mark schemes with Inv, Ps, Grpd_k built in |
|---|---|---|
| Every current derivation | yes | yes (the built-in schemes keep their rules) |
| inv-intro | a special evidence former (S21) | the generic intro of Inv [Agda] |
| Adjoint towers, one-sided inverse towers, full dualizability | not expressible | expressible (§3) |
| Closure for new schemes | n/a | none until a criterion (§7) |
| Proof-irrelevant marks | yes | for property schemes only (§4.3) |
| Laws, splits, `ord` | object modes | unchanged: not schemes (§4.1) |
| Rule classes (std 5) | ICaTT-style judgment and destructors | the same shapes, indexed by a scheme. A scheme is a finite context extension, intro and projections are ICaTT's Inv-intro and destructors made generic, no equations. Not itself published: ICaTT has the one instance. |
| Decidable | yes | yes |

Standard 4 (most general first) picks schemes. They strictly extend what can be declared, change no existing judgment, and the evidence shows the declaration of invertibility is not special. What is special about invertibility (closure, being a property) stays attached to the Inv scheme. Nothing else needs it.

**Spec.** Chapter 3 gets §3.9, "Marks as declared towers (schemes)", as a proposal. It records Inv, Ps and Grpd_k as the built-in schemes and leaves §3.3 unchanged.

## 7. Open items

| Item | Ledger | Status |
|---|---|---|
| Closure criterion: for which schemes are scheme-structured cells closed under composition, whiskering, Gray cells and coherences, in strict and weak Gray-enriched settings; and whether Inv's closure rules are syntactically admissible over L | S35(a) | out to researcher (`conjectures/outbox/mark-scheme-closure.md`) and in progress here |
| Property schemes: a usable criterion for "the space of towers is contractible" (Inv yes; LAdj conjectured; RInv, Idem no) | S35(b) | in the same prompt |
| (S-coh) written out, with the fullness half | S35(c) | in progress (this thread) |
| Agda: projections on evidence, ∀-clauses as schemes, suspension | S35(d) | blocked on E4 (destructors in the core syntax) for projections; ∀-clauses and suspension unblocked |
| S21(c) substitution with evidence becomes (S-sub) for all schemes | S21 | owner unchanged |

## 8. After the researcher answer (2026-11-25)

`conjectures/answered/mark-scheme-closure-2026-11-25.md`, Response 1, verified there. It answers S35(a) and (b) and changes three statements above.

**8.1 What is now known.**
- **No decidable closure criterion exists** **[proved by the researcher, checked]**. Already for existential schemes on endo-1-cells and vertical composition (c), closure is undecidable: a finitely presented group with unsolvable word problem is encoded by Britton's lemma. So "a criterion on the clause list, as decidable as possible" has no decidable form, even for (c) alone.
- **The exact criterion is semantic** (free-arity theorem, existential schemes, both settings). Form the walking arity A of the operation, glue the walking P-cells W onto its structured inputs, U = A ⊔_{∐Dᵢ} ∐Wᵢ. The closure rule holds in every model iff the output D_o → U extends along D_o → W. On failure, U with its tautological inputs is the countermodel. With ∀-clauses there is no walking object. A set-sized countermodel search is still exact, but it is not effective.
- **The proposed syntactic conditions are false.** "Built from t and earlier clause cells" plus "functorial in t" does not give (a), (b) or (e). The scheme P_n(t) = "an arrow from the ultimate target of t to its ultimate source" fails on 1_f in the walking arrow f : 0 → 1, while 1_{1_0} has it, and 1_f = f ◁ 1_{1_0}.
- **Uniform constructions.** In general there are none, even when closure holds semantically. A ∀-scheme that holds on every arrow has no substitution-natural recipe for whiskering, because its output must change under an inclusion of models. For **Inv's two Gray factor rules** (x ⊗ y with x or y Inv) there is a finite recipe: a dovetailed search for one whole layer (two reverses, two cancellations) in the generic presentation of Eⁿ ⊗ Dᵐ. It terminates because the collapse Dⁿ⁻¹ ⊗ Dᵐ has no non-identity cells in degree ≥ n + m. This is a search, not a Benjamin–Markakis-style closed form. Its admissibility is stated for the researcher's presheaf syntax (pasting along globe attachments, Kan fillers), not for a CaTT-style raw syntax.
- **Table** (existence of closure; property in the weak setting).

| Scheme | (a) coh | (b) whisker | (c) vertical | (d) pasting | (e) earlier / later | property |
|---|---|---|---|---|---|---|
| Inv | yes | yes | yes | yes | yes / yes | yes |
| RInv | yes | yes | yes | yes | no / no | no |
| LAdj | yes | yes | yes | yes | yes / yes | **no** |
| Idem | strict yes, weak no | yes | no | no | no / no | no |
| Ps₀ (top test only) | yes | yes | yes | yes | yes / yes | yes |
| Ps_* (with boundaries) | no | no | yes | no | no / no | yes |

- **LAdj has exactly the support of Inv.** In an LAdj tower every cell has two contractions, so its members are invertible. Conversely, every invertible cell has an adjoint-equivalence tower. So LAdj adds no new supported cells, only structure.
- **Property criterion.** A representable scheme is a property iff the fold W ⊔ʰ_D W → W is an equivalence. On clauses: the limit of the prefix spaces is subterminal. A sufficient syntactic condition is blocks of the form "a new endpoint together with a path to it".
- **LAdj is not a property** in the ω case. In K(C₂, 3) two LAdj structures on the identity differ only in their triangle witnesses, and a mod-2 cohomology class separates them. The swallowtail is missing.

**8.2 Corrections to the sections above.**
- §2 **(S-coh) [sketch] is false as stated.** P₁ has its only ∃-clause type built from t's boundary, yet the identity coherence 1_f does not carry it. The sketch's step "each clause type is again a coherence-case type" fails whenever a clause type relates boundary cells that the coherence does not identify. (S-coh) holds for Inv, LAdj and Ps₀ (table, column (a)). For a general scheme the exact condition is the free-arity test at the coherence arity, which is semantic. A repaired syntactic sufficient condition is needed (S35(c), owned by SCHEME).
- §4.3 "So is LAdj **[conj]**" is **refuted**: LAdj as written (two triangle witnesses, no swallowtail) is structure. It cannot be used proof-irrelevantly.
- §4.2 "Inv's closure rules over L can be derived rather than assumed" (open) is **answered for the two Gray factor rules**, in the researcher's syntax and by search. For CaTT-style raw syntax over L it is still open.
- §0 item 4 and §6 "until a closure criterion makes them instances of something general": no decidable criterion exists. A user scheme can gain a closure rule only through a **closure certificate** checked per scheme. One natural form is the postfixed-family proofs the researcher uses for RInv and LAdj: a finite grammar of pastes S, with a finite recipe showing that S is postfixed for the scheme. This is in-house work (§8.3).

**8.3 Follow-ups (owners in the ledger, S35).**
1. Restate (S-coh) with a sufficient syntactic condition, and prove it.
2. Define closure certificates for user schemes, and check that RInv's (a)–(d) and LAdj's support proofs are instances. This replaces "until a closure criterion".
3. Decide whether a finite coherent-adjunction scheme (LAdj with one triangle witness and a swallowtail, or a half-adjoint form) is a property with the support of Inv. Attempt in-house first, then the outbox if it stalls (standard 12).
4. Decide whether Inv's Gray factor rules are admissible in the CaTT-style syntax of L, by a uniform construction or by a search in L's own free objects. The researcher's search needs a syntax with pasting along arbitrary globe attachments.
5. Agda (standard 9): encode P₁ and the Idem composite as a negative example for the old (S-coh) sketch, and encode the corrected statement.
