# Alternatives to the marking system (S17)

*Design note, 2026-11-22. Ledger S17 (closed here), new items S21–S22, E4 extended. Thread "Compare alternatives to the marker system". Builds on `invertibility-markings.md`, `uniform-marks.md`, `ord-recovers-two-tier.md`, `icatt-and-rice-rules.md`, `pseudo-vs-gray.md` R10–R11 and spec chapter 3.*

*Markers: **[proved]** proved here; **[Agda]** machine-checked; **[paper]** checked against the source; **[proposal]**; **[conj]**.*

## 0. Summary

Anthony asked whether the marking system was thought through at the big-picture level, which alternatives were considered, and whether a theoretical result forced it.

**Short answers.**
1. *Was it compared against other forms?* No. The notes compared ways of getting pseudo behaviour back on top of the lax core (separate kernels, two kinds of 2-cell, ICaTT with β/η, laws as hypotheses) and chose property-style marks. They never compared the *form* of the marks. This note does that.
2. *Did a theorem force it?* Partly. Four results force pieces of it (§2): L's non-collapse forces some extra datum; "pseudo is a property of lax data" (Theorem 3.5.1) forces marks rather than a second kind of cell; the C1″ counterexample forces `ps*`; and E13 forces `ord` to act through the side condition, so `ord` is a mode in every design. Since the 2026-11-23 researcher answer, a fifth: pseudo-ness can never be certified from data, so `ps` has to be a declared mark (§8.2). **No result forced the choice of proof-irrelevant judgments over invertibility evidence in the syntax.** That was a choice, and the comparison shows it has a real cost.
3. *The cost, made precise.* The `inv` judgment is not **saturated**: it is not closed under ICaTT's inv-intro ("a cell with an explicitly given inverse and invertible unit cells is invertible"). An equivalence given by data is invertible in every model, but no rule can say so (§3.1, **[Agda]**). The defect propagates: the lax naturality cell of a lax transformation at such a cell is invertible in every model and not derivably so.
4. *The cost cannot be removed while keeping the judgment as it is.* **Theorem 3.3 [proved]:** no decidable judgment on raw terms is sound and closed under inv-intro. The proof reduces the unit problem of finitely presented monoids, which is undecidable (Narendran–Ó'Dúnlaing–Otto 1991). So saturation requires the evidence to be written in the syntax.
5. *Smaller repair.* The spec's (DES) never says that an inverse t⁻ˡ is itself invertible. That is a plain gap, fixed in spec §3.3 by (DES-inv) (§3.2).
6. *Verdict by the evidence (§6).*
   - Keep proof-irrelevant judgments as the decidable core.
   - Add an equation-free evidence layer: ICaTT's inv-intro and can, without equations, with the judgment as the trivial certificate. It is conservative, decidable and fixes both examples **[Agda: `Gray/MarksSaturation.agda`]**.
   - Read the object marks (`ord`, `grpd_k`) as modes. Cell-level marks cannot be modes (§4.5).
   - Reject marked arrow types and complicial thinness as kernel forms. Marked arrow types need subtyping or duplicate terms (§4.3). Complicial thinness is a different core rather than another marking, and its saturated form meets Theorem 3.3 (§4.4).
7. *Limits of any certificate system (researcher answers r2 and r3, §9 and §10).* In L, some invertible cells have no finite certificate. Invertibility in free L-models is not even recursively enumerable. So no decidably checked evidence language is complete, and `inv` in L is permanently incomplete. The evidence layer gains one sound periodic rule, (INV-clock), for the known infinite-tower pattern. In P, certificates are complete.

## 1. The current system, and the axes along which it can vary

Chapter 3 has judgments `t inv`, `t ps`, `t ps*` on terms and `C grpd_k`, `C ord` on object variables. Declarations may carry marks, and substitutions must preserve them. Propagation rules are syntax-directed on `coh`. ICaTT's destructors t⁻ˡ, t⁻ʳ, λ_t, ρ_t are term formers that depend on t only, with no equations. Marks are proof-irrelevant: a derivation of `t inv` leaves no trace in any term.

Three independent choices are bundled in this:

| Axis | Current choice | Alternatives |
|---|---|---|
| (A) Is invertibility evidence part of the syntax? | No (proof-irrelevant) | Evidence terms of a type `Inv(t)` (ICaTT) |
| (B) Where does a mark live? | On a term, as a judgment | In the type (marked arrows `u ≅ v`), or on the sort of objects/homs (modes) |
| (C) Is "being a coherence" itself a mark? | No: coherences are `coh` terms; marks are about invertibility | Yes: complicial/thin cells, where thinness *is* coherence |

Candidates compared below: (d) the current judgments; (a1) an equation-free `Inv` type; (a2) marked arrow types; (b) complicial thinness; (c) modes; plus the options already compared elsewhere, listed in §4.6.

## 2. What was forced, and by what

| Piece | Forced by | What it rules out |
|---|---|---|
| Some datum beyond L-terms is needed to recover pseudo | L's non-collapse: the reverse interchanger is not derivable (`pseudo-vs-gray.md` §3.6 Thm 1(2)) | Recovering P from L by rules alone |
| Pseudo is a *property* of lax cells, so a mark (not a second sort) suffices | Theorem 3.5.1: Fun → Fun^lax is a monomorphism on mapping spaces (Gepner–Heine Thm 4.1.9), so pseudo cells are a sub-collection of lax ones | Option C of R10 (two kinds of 2-cell) as a *necessity*; it is still possible, only redundant |
| Marks on every higher cell, i.e. `ps*` | C1″ and the counterexample B = D¹, C = D³ (a non-strong modification between strong transformations) | A mark only on transformations, inherited upward |
| `ord` acts through the side condition | E13 (researcher answer, verified 2026-11-21): the loop H vs 1_w and the outer W-strip stay unconnected after every inner letter is inverted | Any invertibility-only reading of `ord`, in *every* form of marking (judgment, evidence type, or marked type) |
| Invertibility restricts what may be substituted, not an assertion about a variable | CaTT_lim researcher answer (`catt-lim-pseudo-vs-gray.md` §5): "a syntactic implementation needs marked declarations, with substitutions required to supply equivalence certificates" | A rule asserting that an arbitrary declared cell is invertible |
| `ps` must be declared, never certified from data | Prop. 8.2 (from the verified 2026-11-23 answer): freely attaching a generic earlier cell makes the pseudo test equivalent to invertibility | Any Ps-intro rule from data or from a generic-cell binder |
| No β/η on an `Inv` type | Project standard 5, a design constraint and not a theorem | ICaTT as published |

So three things were forced: that pseudo is a mark rather than a second sort, that `ps` is declared and never derived from data (§8.2), and that `ord` is not an invertibility mark. The form of the invertibility marks themselves was not forced. The CaTT_lim answer even speaks of "certificates", which the current design implemented as "derivably `inv`".

## 3. Findings

### 3.1 The judgment is not saturated [Agda]

**Example (Γ₁, an equivalence by data).** Γ₁ = (a, b : ⋆)(x : a → b)(y : b → a)(l : y;x ⇛ 1_b)^inv(r : x;y ⇛ 1_a)^inv.
- In every model, x is invertible: y is a left and a right inverse up to invertible cells. This is ICaTT's inv-intro with t_l = t_r = y.
- `Γ₁ ⊢ x inv` is not derivable. No rule concludes `inv` for an unmarked variable except (OBJ-k), which needs hd ≥ 1.
- More strongly **[proved]**, no 1-cell a → b at all is derivably `inv` in Γ₁. The rules that conclude `inv` for a 1-cell are (mark), (COH-inv) and (OP-inv). There are no inv-marked 1-cells. (COH-inv) at dimension 1 gives identities. (OP-inv) needs every top argument to be inv, so by induction every derivably inv 1-cell is a composite of identities and has equal endpoints. Destructors need an inv premise, so they add nothing new.

**Example (Γ₂, propagation lost).** One dimension up: T, B objects, u, w : T → B, x : u ⇒ w and y : w ⇒ u, l : y;x ⇛ 1_w and r : x;y ⇛ 1_u marked inv, and a lax β : F ⇒ G : B → C. The naturality cell of β at x (the Gray cell x ⊗ β) is invertible in every model, by Lemma 2.1, because x is. It is not derivably inv. With x marked, (INV-fac) gives it.

Machine check: `src/CaTTExp/Gray/MarksSaturation.agda` evaluates the encoded rules of `Gray/Marks.agda` on both contexts. Both contexts and the naturality cell are well-typed (certified checker). l and r are inv, the inv-intro shape holds, and x and y are not inv. The naturality cell is not inv, and it is inv once x is marked.

**Why this matters in practice.**
- Equivalences in ordinary mathematics are usually given by data (functors, unit and counit). Ordinary-math developments (spec ch. 9) will meet this every time an equivalence built from data must instantiate an `inv` hypothesis.
- `uni` in CaTT_lim takes invertible comparison cells. A cone morphism whose comparison is invertible only by explicit data cannot be fed to it.

### 3.2 Inverses are not marked invertible [proved; spec repaired]

Spec §3.3 (DES) concludes `λ_t inv` and `ρ_t inv`, but not `t⁻ˡ inv` or `t⁻ʳ inv`, and no other rule gives them. So t⁻ˡ ; t⁻ˡ⁻ˡ is ill-formed, and composites involving an inverse (for example the inverse of a pseudo naturality cell whiskered by a functor) are not derivably inv by (OP-inv). In every model, t⁻ˡ is invertible with inverse t. `limits-metatheory.md` §6.1 already listed "inv, eta, eps of invertible terms (which are themselves invertible)", so the two notes disagreed.

**Repair (DES-inv):** `t inv ⇒ t⁻ˡ inv, t⁻ʳ inv`. It is sound and syntax-directed, and substitution stability is immediate (destructors commute with substitution). Spec §3.3 now includes it. Agda: blocked on destructors entering the core syntax (ledger E4, which now includes DES-inv).

### 3.3 Saturation and decidability are incompatible on raw terms [proved]

Call a judgment J ⊆ {(Γ, t)} on the kernel's raw terms *sound* if J(Γ, t) implies ⟦t⟧ invertible in every model of Γ. Call it *saturated* if it contains the marked variables and the coherence-case cohs, and is closed under (OP-inv), (INV-fac), (DES), (DES-inv) and inv-intro: if J(Γ, l) and J(Γ, r) for l : s ; t ⇛ 1, r : t ; s′ ⇛ 1, then J(Γ, t).

**Theorem 3.3.** No sound saturated judgment is decidable, uniformly in Γ. This holds already for contexts with one object, 1-cells, and inv-marked 2-cells, in two-tier L, and equally in P.

*Proof.* Take a finite monoid presentation M = ⟨A | R⟩. Build Γ_M:
- one object a;
- a 1-cell g : a → a for each g ∈ A;
- for each relation (u, v) ∈ R, a 2-cell ρ : ⌊u⌋ ⇒ ⌊v⌋ marked inv, where ⌊w⌋ is the left-bracketed composite of the word w and ⌊ε⌋ = 1_a.

*Claim: J(Γ_M, g) holds iff [g] is a unit of M.*

(⇒) Interpret Γ_M in M, read as a one-object strict ω-category with only identity higher cells. A strict ω-category is a model of P and hence of L. Send g ↦ [g] and ρ ↦ the identity, which is well-typed because [u] = [v]. Marked cells go to identities, which are invertible. By soundness ⟦g⟧ = [g] is invertible in M.

(⇐) If [g] is a unit, choose a word h with gh = 1 = hg in M. Each equation is a finite chain of elementary rewrites p u q ↔ p v q. Each rewrite step is a whiskering of ρ or of ρ⁻ˡ, with re-bracketing coherences on either side. Whiskerings are inv by (OP-inv) with (INV-fac) (one positive factor), ρ⁻ˡ is inv by (DES-inv), and coherences by (COH-inv). The vertical composite of the chain is then inv by (OP-inv). This gives J-cells l : ⌊h⌋ ; g ⇛ 1_a and r : g ; ⌊h⌋ ⇛ 1_a, and inv-intro gives J(Γ_M, g).

*Conclusion.* M is a group iff every generator is a unit. If J were decidable uniformly in Γ, group-ness of finite presentations would be decidable. It is not: Narendran, Ó'Dúnlaing and Otto, *It is undecidable whether a finite special string-rewriting system presents a group*, Discrete Math. 98 (1991) 153–159. ∎

**Consequences.**
- The current judgment is decidable *because* it is unsaturated (principle 0.6).
- Any decidable saturated system must record the certificate (s, s′, l, r) in the syntax. A checker given only raw terms would have to search for it, and the theorem says that search cannot be a decision procedure.
- This is the precise sense in which axis (A) matters: proof-irrelevance and saturation exclude each other under decidability.

*What the theorem does not say.* It does not show that the evidence form is complete, that is, that every cell invertible in the free model on Γ has a *finite* certificate. See §6.1 and the outbox prompt.

### 3.4 Proof-irrelevant destructors need models with chosen inverses [paper]

Because t⁻ˡ depends on t only, a model must interpret t⁻ˡ by a *choice* of inverse for each invertible cell, and a substitution (a morphism of models) must preserve the choice. Spec §3.3 already says this. With evidence terms (a1), linv(e) is interpreted by the data e, and no global choice is needed.

- *Strict and algebraic models:* both work, and choosing is free.
- *(∞,ω)-models:* the space of invertibility data is contractible, so a choice exists. Strictly preserving it along substitution is a coherence obligation that the evidence form avoids.

This is not a derivability difference. It is recorded because it is the one semantic simplification the evidence form offers.

## 4. The candidates

Each subsection gives the description, then what is derivable, decidability, fit with standard 5, how `ord`/(COH-ord) and `ps*` fit, and user cost.

### 4.1 (d) Proof-irrelevant judgments (current)

*Description.* As in §1.
- **Derivable.** Exactly the inductive closure of the rules: unsaturated (§3.1). With (DES-inv) the inverse gap is closed.
- **Decidable.** Yes, syntax-directed. Theorem 3.3 says this is only possible because it is unsaturated.
- **Standard 5.** Matches the inductive judgments of published variants (`⊢ps`, ICaTT's invertibility criterion as a side condition) and the marked computads of Benjamin–Champin–Markakis (arXiv 2606.30254), where marking is a designated set of generators. In BCM the marked cells are generated inductively from marked generators and the unit constructors `lunit`, `runit` (§3.2 there). That is the same shape as our judgment: marked by generation, not by any data a cell may have.
- **ord, ps\*.** `ord` and `grpd_k` are marks on object variables, and (COH-ord) changes the side condition (§4.5). `ps*` is a recursive judgment.
- **User cost.** One mark per declared pseudo structure cell (spec Q3.1, M1). An equivalence given by data cannot be used where `inv` is needed at all.

### 4.2 (a1) An equation-free invertibility type (ICaTT minus its equations)

*Description.* A type former `Inv(t)` for each arrow t, with evidence terms: variables, `inv(t, s, s′, l, r, e_l, e_r)` (inv-intro), `can(coh[γ], {e_x})`, and destructors `linv(e)`, `rinv(e)`, `lunit(e)`, `runit(e)`, `ilunit(e)`, `irunit(e)`. No β, η, can or rec equations (standard 5). Over L, every propagation rule with an `inv` premise becomes an evidence former: can over L's top generators, and factor formers for (INV-fac), (INV-obj), (PS-fac) and (OBJ-k). `ps` needs its own type `Ps(t)`.

- **Derivable.** Everything (d) derives, after erasing evidence. Plus inv-intro: x in Γ₁ and the naturality cell in Γ₂ get evidence.
  - Conversely, erasing evidence maps every (a1) typing to a (d) typing, *except* inv-intro.
  - (a1) also *loses* something. Two derivations of the same invertibility give two different terms linv(e₁), linv(e₂). These are connected only by a cell, where (d) has one term t⁻ˡ.
  - Without β, `linv(inv(t, s, …))` is not s. The inverse a user supplied is forgotten as soon as it is packaged, and every use needs a transport cell from s.
- **Decidable.** Yes: evidence is explicit, and checking is syntax-directed.
- **Standard 5.** A type former with intro and elim rules, as in ICaTT (published). Acceptable once the equations are removed.
- **ord, ps\*.** `ord` cannot be evidence (E13): it changes which cohs exist. It stays a mark on object variables, as in (d). `ps*` becomes a recursive evidence type, or a type `Ps(t)` together with Ps evidence on the boundaries.
  - **Ps-intro by data needs a binder.** `ps` quantifies over every cell y composed before t, so evidence that t is pseudo by data is a term in an extended context (a generic y), like ICaTT's rec (§6.1).
- **User cost.** Every use of an invertible cell carries its evidence term. A surface can infer evidence wherever (d) would derive the judgment, which reduces the cost to (d)'s except where inv-intro is used.

### 4.3 (a2) Marked arrow types

*Description.* Arrow types carry the mark: `u ≅_A v`, `u →^ps_A v`. A marked declaration is a variable of a marked type, which is the most direct reading of BCM's marked generators. `ps*` falls out for free: a cell is `ps*` when every arrow in its type is ps-marked, because the boundaries' types are part of the type.

**The obstruction [proved].** In CaTT a term has a unique type, read off syntactically: x has its declared type, and coh_{Γ,A}[γ] has A[γ]. Take Γ = (a, b)(x : a → b) and the unary composite c = coh_{Γ, a → b}[x]. Substitute x ↦ t with t : a ≅ b invertible. The problem already appears at the substitution itself, since t has type a ≅ b and x has type a → b. And c[γ] has type a → b (unmarked) but is invertible. Three ways out, each costly:
1. *Subsumption* `u ≅ v ≤ u → v`, needed for the substitution itself, together with a rule that upgrades the type of c[γ]. That is subtyping, which no published CaTT variant has (standard 5). The type of a term is then no longer A[γ], so the substitution lemma has to be reproved for a non-structural typing rule.
2. *Annotations everywhere*: variables declared at marked and unmarked types, and coh_{Γ, a ≅ b} as well as coh_{Γ, a → b}. Two distinct raw terms for the same composite, connected only by a cell. A 3-cell between composites then depends on which annotation was chosen.
3. *The marked type is only a lower bound* and a separate judgment finds the rest. That is (d) with a cache.

- **Derivable.** No more than (d) (or (a1), if inv-intro is added as an intro rule for `≅`).
- **Decidable.** Yes under (1) and (2).
- **ord.** Not expressible as a type mark (E13); it stays an object mark.
- **User cost.** Same as (d) at declarations. Under (2), extra transport cells between differently annotated composites.

### 4.4 (b) Complicial / thin-cell marking

*Description.* Following Verity's complicial sets (Riehl, *Complicial sets, an overture*, arXiv 1610.06801; Ozornova–Rovelli, arXiv 2007.01235), cells are simplices and some are *thin* (marked). Thin simplices witness composition, so coherence itself is a marking. Fibrancy is a lifting property against complicial horn extensions and thinness extensions. *Saturated* complicial sets also lift against saturation extensions, and the r-equivalences then satisfy 2-out-of-6 (Ozornova–Rovelli Def. 1.6 and §1.1). Saturated N-complicial sets model (∞, N)-categories (Thm. 1.7 there).

- **What it would change.** Coherences would not be `coh` terms but marked horn fillers, and the propagation rules would be the thinness extensions. That replaces CaTT's core (globular pasting schemes and the single `coh` rule) with a simplicial core. It is a different kernel, not a different marking.
  - No CaTT-style type theory for complicial sets is published. A literature search (2026-11-21) found none.
  - So it fails standard 5's "rule classes of published CaTT variants".
- **Decidability.** The saturated marking is closed under 2-out-of-6, which contains inv-intro. As a judgment on a syntax of this kind it would meet the analogue of Theorem 3.3 **[conj]**. The theorem is proved for this kernel's raw terms. The same monoid reduction is expected to go through for finitely presented marked simplicial sets, but that was not checked. Unsaturated thinness is decidable, but it is the analogue of (d), not something new.
- **What it confirms.**
  - The complicial picture separates *thinness* (coherence) from *saturation* (equivalences are thin). Our (COH-inv) is the first, and §3.1 is exactly a failure of the second.
  - Saturation is a fibrancy (lifting) condition there, never a decidable syntactic one. That matches Theorem 3.3.
- **ord, ps\*.** No counterpart for `ord`. "Strict inside an object" is uniqueness of thin fillers in complicial terms, not a mark. `ps` would be thinness of the cylinder simplices of a Gray product. Ozornova–Rovelli–Verity use Verity's tensor ⊗ (with a pretensor ⊠ in the background); whether lax and pseudo versions differ only in marking was not checked from the source here.
- **User cost.** A new core, with every construction rewritten simplicially.

### 4.5 (c) Modes, one per strictness level

*Description.* Each object (or hom) has a mode, for example lax, ordinary, or k-groupoidal. Rules depend on the modes involved, and adjunctions between modes give change-of-mode operations, as in multimodal type theory (Gratzer–Kavvos–Nuyts–Birkedal, arXiv 2011.15021).

- **Object marks are already modes.** `grpd_k` says "C lies in Cat_{k−1}". `ord` with (COH-ord) changes the coh rule for heads whose objects are `ord` (E13 forces this). Substitutions must send an object of a given mode to one of the same mode. That is a mode discipline in all but name, and the open question about heads mixing `ord` and non-`ord` objects (E15) is the usual question of how modes interact.
- **Cell marks cannot be modes on objects or 1-cells [proved].** Pseudo-ness of a transformation is not determined by its objects and functors.
  - Let C be a 2-category with an arrow p : c → d and a non-invertible 2-cell ε : p ⇒ p. Let F : D¹ → C pick p.
  - The lax transformations F ⇒ F with identity components and naturality cell 1_p, respectively ε, have the same source, target, domain and codomain. The first is pseudo, the second is not.
  - So a mode carried by objects or 1-cells cannot express `ps`. A mode on the hom or on the 2-cell's arrow type is possible, but it is (a2) (§4.3) or R10's option C (two kinds of 2-cell), already judged heavier and subsumed by marks.
- **MTT itself is excluded.** Its modal types have β/η rules (standard 5). Change-of-mode functors would be object formers (reflections τ_k, the reflection onto ordinary ω-categories): free objects, not marks.
- **Verdict.** Modes describe the object-level part of the current system exactly, and nothing more.

### 4.6 Already compared elsewhere

- **Separate kernels for lax and pseudo** (spec §0.4): rejected by principle 0.4.
- **Two kinds of 2-cell** (R10): subsumed, and §4.5 shows it is what "modes for cells" would be.
- **Full ICaTT with β/η**: excluded by standard 5.
- **Inverse data as declared hypotheses** (`design-decisions.md` §1.4(c) style: declare y, l, r as variables instead of marking x). No kernel change. It is weaker than (a1): in Γ₂ the naturality cell at x stays non-invertible, because propagation rules read marks and not hypotheses.

## 5. Worked examples across the options

### 5.1 The examples

| # | Example | (d) current | (d) + DES-inv | (a1) Inv evidence | (a2) marked types | (b) complicial | (c) modes |
|---|---|---|---|---|---|---|---|
| W1 | Pseudo naturality of α marked ps (spec Ex. 3.3(a)) | 1 mark | same | 1 evidence variable | 1 marked type | thin cylinder simplex | not expressible per cell |
| W2 | x in Γ₁ (equivalence by data) is invertible | **not derivable** | **not derivable** | `inv(x, y, y, l, r, e_l, e_r)` | not derivable without inv-intro | in the saturated form | n/a |
| W3 | Naturality of lax β at x in Γ₂ | **not derivable** | **not derivable** | `can` with the W2 evidence | as W2 | as W2 | n/a |
| W4 | t⁻ˡ is invertible | **not derivable** | rule | inv-intro with t | rule | 2-out-of-6 | n/a |
| W5 | c[x ↦ t] for c = coh_{x : a→b, a→b}[x] and invertible t | inv by (OP-inv) | same | `can` | type a → b, needs subsumption or a second term | thin filler | n/a |
| W6 | Directed EH inside an `ord` object (spec §3.6 Ex. (a)) | (ORD) via (COH-ord) | same | same (object mark) | same (object mark) | no counterpart | the mode of C |
| W7 | Ring object, `grpd_1` (spec Ex. 3.3(d)) | 1 object mark | same | 1 object mark (or evidence per witness) | object mark | 1-trivial marking | the mode of R |
| W8 | Pseudo modification between strong transformations | `ps*` on every higher cell | same | Ps evidence on cell and boundaries | automatic from the type | thinness on each cell | not expressible |

### 5.2 Summary comparison

| | (d)+DES-inv | (d)+DES-inv + evidence layer (§6) | (a1) alone | (a2) | (b) | (c) |
|---|---|---|---|---|---|---|
| Saturated (W2, W3) | no | **yes** | yes | no | only if undecidable | n/a |
| Decidable | yes | yes | yes | yes | saturated: no by the analogue of Thm 3.3 [conj] | n/a |
| Unique inverse per cell | yes | yes for derived marks; evidence-indexed for data | no | yes | n/a | n/a |
| Published rule classes (std 5) | yes | yes (ICaTT formers, no equations) | yes | needs subtyping | no | MTT needs β/η |
| `ord` | object mark, side condition | same | same | same | none | is a mode |
| `ps*` | recursive judgment | same | recursive evidence | free from types | thinness | no |
| User cost at the common case | lowest | same as (d); evidence only when using inv-intro | evidence everywhere unless inferred | (d) plus transports | new core | (d) |

## 6. Verdict and proposal

The evidence decides as follows.

1. **Keep (d) as the decidable core and add (DES-inv).** It is the only form with unique inverses, the lowest user cost and the published rule classes. Theorem 3.3 shows that its lack of saturation is the price of deciding it on raw terms, not a design slip. (DES-inv) is a plain gap and is fixed in spec §3.3.
2. **Add saturation as an evidence layer [proposal, Agda-checked on examples].** The kernel gets an evidence syntax with
   - `!` (the judgment itself, ICaTT's evidence erased),
   - `inv(t; s, s′, l, r; e_l, e_r)` (inv-intro),
   - `can(coh[γ]; {i ↦ e_i})` (arguments upgraded by evidence and fed to the existing L rules), and
   - destructors on evidence, with linv(!) printed t⁻ˡ.

   It is used only where a judgment needs a cell that is invertible by data: substituting into a marked variable, and the premises of the propagation rules. Properties:
   - *conservative*: evidence `!` is exactly the judgment, by definition (`jud-conservative` holds by refl);
   - *decidable*: structural on the evidence, with the evidence terms type-checked by the certified checker;
   - *sound*: inv-intro is the definition of invertibility, and `can` follows from the soundness of the rules it feeds;
   - *equation-free*.

   It fixes W2 and W3 in `Gray/MarksSaturation.agda`. Unlike (a1) alone, the common case keeps (d)'s unique inverses and zero evidence. This is the "equivalence certificates" the CaTT_lim answer asked substitutions to supply.
3. **Present `ord` and `grpd_k` as modes** in spec chapter 3 (naming only), with E15 as the mode-interaction question.
4. **Do not adopt (a2), (b) or modes for cells.** (a2) needs subtyping or duplicates terms. (b) is a different core, and its saturated form is undecidable. Modes on objects or 1-cells cannot carry cell marks, and modes on homs reduce to (a2) or option C.

### 6.1 Open questions behind the verdict

- **Finite certificates (S22).** Is every cell that is invertible in the free model on a finite marked context certified by finitely many applications of inv-intro and can over the judgment?
  - In **P** (and plain CaTT) yes **[proved]**. This assumes that the syntactic model is the free model (initiality, as for CaTT), so that inverse data in the free model is given by terms. Every term of dimension greater than dim Γ is derivably inv with (DES-inv). By induction on terms, a variable cannot have that dimension, (COH-inv) and (OP-inv) handle cohs (their top arguments have the same dimension), and destructors are inv by (DES)/(DES-inv). So the coinductive tower of inverse data can be cut off after finitely many levels.
  - In **L** the argument fails: above dim Γ there are directed interchangers, which are not invertible.
  - Some invertible cells of free L-models need an infinite tower (§9), and invertibility there is not even recursively enumerable (§10). So no decidably checked certificate language, including one with ICaTT's rec, is complete in L.
- **Pseudo by data (S21).** Closed negatively (§8.2): pseudo-ness cannot be certified from data, so there is no Ps-intro rule.
- **Encoding.** inv-intro is encoded for dimensions 1 and 2 only. The general rule uses the suspended composite.

## 7. Open items from this note

| Item | Ledger | Status |
|---|---|---|
| (DES-inv) in Agda | E4 (extended) | with E4 |
| Evidence layer: general-dimension inv-intro in Agda, spec text (Ps-by-data closed, §8.2) | S21 | in progress (this thread) |
| Finite certificates in free L-models | S22 | closed: finite certificates are incomplete (§9, r2), and invertibility is not r.e., so no decidably checked certificate language is complete (§10, r3) |
| (INV-clock) checking in Agda, as part of the evidence layer | S21 | in progress (this thread) |
| Mixed `ord` heads as mode interaction | E15 | unchanged owner |

## 8. After the researcher answer (2026-11-23)

The response to `invertibility-certificates.md` is filed with its verification at `conjectures/answered/invertibility-certificates-2026-11-23.md`.

### 8.1 Finite certificates (S22): the question was mis-posed, and is restated

The response proves that rules 1–6 of the prompt certify every invertible cell, in the strict and the weak Gray setting. The proof uses rule 5 as worded ("any chosen inverse of a certified cell, with its witnesses") on an identity. Any invertible contraction w : c → 1_z is a witness that c is an inverse of 1_z. So w is certified without its own tower, and rule 6 then certifies every invertible f from its contractions.

That rule is not in the kernel.
- The destructors (DES) give one fixed package per cell, and the package of an identity consists of coherences.
- Being "a witness" is a semantic condition, and the response shows that with it even rules 1–5 are undecidable.

So the result does not settle S22. The question the project needs is the same one with rule 5 restricted to the package recorded by the derivation. It is restated as `conjectures/outbox/invertibility-certificates-r2.md`.

The response's own examples confirm the restriction matters: in the group-presentation example, rules 1–5 with free choice decide the word problem. The kernel's syntax-directed rules are decidable (Theorem 3.3 only concerns closure under inv-intro).

The quotient criterion (Q3) characterizes invertibility in any model but gives no algorithm, so no rule changes. Its example `abab ⇒ 1` (ab invertible, ba not, both normal forms using each letter once) shows that no support or multiplicity test on normal forms can decide invertibility. That rules out a BM-style criterion for marked computads in general.

**In-house attempt on r2 (continuing while it is out).** The natural route is Q3 of r2 with N(C) = dim C. It reduces to one lemma, the Gray analogue of Benjamin–Markakis Prop. 37 above the dimension of the generators:

> *(Gray support lemma)* In F(C, M), a cell of dimension greater than dim C, in normal form, is invertible only if each of its top-dimensional constituents is a coherence, a recorded inverse or unit, or a Gray cell with an invertible positive factor.

If the lemma holds, the tower argument of the ordinary case goes through unchanged, and finite certificates are complete in L. The obstruction to proving it is the lack of a normal form for free Gray ω-categories with chosen inverses: the Steiner-complex normal form covers the strict, inverse-free case only. **[conj]**

### 8.2 Pseudo-ness cannot be certified from data [proved, from the verified answer]

**Fact (Q4 of the answer, verified).** Freely attach a new object s and a generic cell y : D¹ → K′(s, a) at the source a of t ∈ K(a, b). Then y ⊗ t is invertible in K′(s, b) = D¹ ⊗ K(a, b) **iff t is invertible**. Collapsing the two end copies of K(a, b) sends d₁ ⊗ t to the suspended dual of t.

**Proposition 8.2.** Let Γ be a context with no `ps`, `grpd_k` or `ord` marks, and t a term of Γ with hd(t) ≥ 1. If ⟦t⟧ is pseudo in every model of Γ, then ⟦t⟧ is invertible in every model of Γ.

*Proof.*
1. Take a model K of Γ with source object a = ⟦src t⟧, and attach a generic y at a, giving K′.
2. The inclusion K → K′ is an enriched functor, so inv-marked variables stay invertible. No other marks need to be checked, so K′ is a model of Γ.
3. In K′, ⟦t⟧ pseudo gives y ⊗ ⟦t⟧ invertible.
4. By the Fact, ⟦t⟧ is invertible in K. ∎

**Consequence.**
- Any evidence former for `ps` whose soundness rests only on invertibility data would be sound in mark-free contexts. There, by the proposition, it could only certify invertible cells, which (INV⇒PS) already covers.
- So S21(b) ("pseudo by data, with a binder over a generic earlier cell") is closed with a negative answer. The generic test is exactly invertibility, and no Ps-intro rule is needed or possible.
- Pseudo-ness enters only through declared marks, or through (PS-fac) and (OP-ps) from them.

**This answers part of Anthony's original question.** The `ps` mark is *forced*. Unlike invertibility, pseudo-ness quantifies over cells that do not exist yet. It cannot be derived from any data in a context, so it has to be a declared property. In the table of §2, this is a fifth forced piece.

The two finite examples of the answer also show the opposite gap: internal pseudo-ness (checked against existing cells) is weaker than the generic test. That is consistent with marks being declarations that a substitution must respect, rather than consequences of the data.

## 9. After the second answer (2026-11-23): finite certificates are incomplete in L

The response to `invertibility-certificates-r2.md` is filed with its verification at `conjectures/answered/invertibility-certificates-r2-2026-11-23.md`. **S22 is answered negatively.**

### 9.1 The result

**The marked computad.**
- Objects a, b; 1-cells p : a → a and x : a → b; 2-cells u : 1_a ⇒ p and v : p ⇒ 1_a; a 3-cell f : 1_x ⇛ 1_x in the hom (a, b).
- Marked: contractions of u;v, of (pu);(pv) and of (pv);(pu), and of p·f.

**What holds in the free model.**
- f is invertible.
- f has no finite certificate, even with inv-intro and recorded inverses.
- The alternating interchangers u ⊗ v ⊗ … ⊗ f give such cells in every dimension ≥ 3.

**Why.** The two cylinders Id ⇒ p· and p· ⇒ Id built from u and v have an invertible *composite* (rule 4, because u;v is certified). Their individual tiles u ⊗ q and v ⊗ q are directed interchangers that are never certified. The reversal tower of f passes through such tiles at every level.

**Why no finite rule can help.** In a two-object model whose homs are bit-labelled cells, with designated cells = identities, every finite-certificate rule holds, the marks go to identities, and f does not. So any rule that is sound in every model whose designated class is merely closed under the rules cannot certify f.

**In P this cannot happen** (§6.1): there all cells above dim Γ are certified, so every tower closes.

### 9.2 What it means for the design

1. **`inv` in L is a decidable, sound, provably incomplete criterion. The incompleteness is intrinsic.** This is already the reading of principle 0.6 ("a decidable sufficient judgment"), now with a concrete witness. The evidence layer of §6 stays as proposed. It is sound, and it adds inv-intro, which the bare judgment lacks (Theorem 3.3). But it cannot reach every invertible cell of a free L-model.
2. **Only saturated semantics can make up the gap.** The spec's intended models give every invertible cell its invertibility data (§3.3 Semantics), so they are saturated. A complete rule has to depend on that and could not be interpreted in models whose designated class is smaller. The response gives one complete rule: coinduction relative to recorded certificates, over an indexed family of reversal data. But the dimension increases along every branch, so a *finite* index family adds nothing.
3. **What users do meanwhile.** A cell like f is invertible, but the kernel cannot show it. A development that needs it declares the cell marked `inv` (a hypothesis), or works with a certified replacement.
   - This affects lax constructions in which a composite of two directed cylinders is invertible but the cylinders are not. One example is a functor P that is an equivalence only up to directed comparisons.
   - P-style developments (all mixed cells invertible) are unaffected.
4. **Settled by r3 (§10):** invertibility in free L-models is not recursively enumerable, so no decidably checked certificate language is complete, and the incompleteness is permanent.

**In-house attempt (made while r3 was out; §10 gives the finished form, the periodic clock rule).**
- For the counterexample, the tower is generated by one finite recipe applied at increasing dimension: split, rebase along ℓ, whisker. That suggests schematic certificates of the form "a recipe uniform in the based cell q, plus a proof that it maps the hypothesis 'p·q certified' to the same hypothesis one dimension up".
- Such a rule is checkable if the recipe is a term in a context with a generic based q. It is sound by the postfixed-set argument.
- Whether every invertible cell has a tower presented by finitely many such recipes is exactly the r.e. question, from the other side.

## 10. After the third answer (2026-11-23): invertibility in L is not recursively enumerable

The response to `invertibility-certificates-r3.md` is filed with its verification at `conjectures/answered/invertibility-certificates-r3-2026-11-23.md`. It is verified for strict and weak Gray ω-categories (the weak case's citations to Ozornova–Rovelli–Walde and Gepner–Heine were checked against the sources). **S22 is closed.**

### 10.1 The result

- **Not r.e. [paper, verified].** There is a computable map from (Turing machine, input) to (finite marked computad, 3-cell) such that the cell is invertible exactly when the machine runs forever. With a universal machine, one fixed computad suffices, and only the cell varies with the input.
- **How (nonhalting ⇒ invertible).** The machine is a string-rewriting system, one marked 2-cell per rule. Each simulated step emits one copy of a clock letter s, so an infinite run gives invertible comparisons w_i ⇒ w_{i+1}s for all i. Each copy of s pays for one level of the reversal tower of w_0 f, by the same split as in §9 (cylinders from u : s ⇒ t and v : t ⇒ s).
- **How (halting ⇒ not invertible).** If the run halts, every word congruent to w_0 has bounded length. A model graded by the presented monoid puts the image of w_0 f in a bit-labelled fibre of finite height. There, every coinductively invertible cell is an identity, and the image is not one.
- **Consequence.** No certificate language with decidable checking is sound in all models and complete for free L-models. The incompleteness of `inv` in L (§9.2) is permanent, not a gap in the current rules. In P, certificates remain complete (§6.1).

### 10.2 Sound extensions exist, but none is maximal

- **The periodic clock rule (INV-clock).** Its certificate is:
  - cells u : s ⇒ t and v : t ⇒ s, with certificates for u;v, (tu);(tv), (tv);(tu) and t·f;
  - finitely many prefix words, each with a successor index;
  - for each word w with successor w′, a certificate for a comparison w ⇒ w′s.

  Its conclusion is that w_0 f is invertible. Checking is decidable, and soundness (also under substitution) is the clock criterion.
- **It covers the §9 example.** Take s = 1_a, t = p and the single prefix 1_a pointing to itself. The hypotheses are the four marks.
- **There is no largest decidably checked sound fragment.** Any such fragment misses some true instance, and adding that instance as an axiom gives a larger one.
- **No decidable sound superset of Cert exists** on cells. On monoid presentations it would decide the group problem.

### 10.3 Design decision

1. **The kernel judgment `inv` stays as it is:** decidable, sound and incomplete in L. This is principle 0.6, and r3 shows nothing better exists of this form.
2. **The evidence layer (S21) gains (INV-clock) as one more evidence constructor, beside inv-intro and can.**
   - It is the finished form of the in-house schematic attempt (§9).
   - It covers the one pattern known to need an infinite tower: two directed cylinders whose composite is invertible and whose tiles become invertible after whiskering by t. That is the lax "equivalence up to directed comparisons" case of §9.2 item 3.
   - Since no fragment is maximal, further rules are added only when a construction needs them. Each needs a soundness proof of this kind.
3. **Users who meet an invertible cell outside the evidence layer** declare it marked `inv` as a hypothesis, as in §9.2 item 3. That is the "ground axiom" extension of §10.2, made locally and explicitly.
4. **Formalization (S21, this thread).** Encode (INV-clock) checking in `Gray/MarksSaturation.agda`, with the §9 example certified by it. The rule's soundness is the paper clock criterion; Agda checks only the certificate's well-typedness.
