# Pseudo ambient (P) vs Gray-style core (L)

*Design notes, 2026-11-18. Answers the decision raised in `notes/limits-representables.md` §3 (PR #2), `notes/internal-hom.md` §2–3 (PR #3) and `notes/agda-sketch-findings.md` finding 4 (PR #4). Background: `catt-survey.md` (project files). Redoing existing results is treated as free, per Anthony; only mathematical and practical upsides and downsides count.*

*Markers. **[paper]**: checked against the source this session. **[conj]**: my conjecture. **[proposal]**: a design choice being put forward. Every claim once marked **[recall]** was re-checked on 2026-11-18 (ledger G1) and now carries its source, a correction, or [conj]. Orientation conventions are fixed in `conventions.md`; long-term semantic gaps are collected in `semantics-gaps.md`.*

---

## Practical gains and losses

This section answers one question: what can a user write, construct and prove under each option, and how much bookkeeping does each force? The technical comparison starts at §0.

The three options, in one line each:
- **P:** plain CaTT. The ambient's 2-cells are pseudo transformations.
- **Two-tier L:** the ambient's 2-cells are lax transformations. Inside each object, plain CaTT.
- **Uniform L:** like two-tier L, but composition is laxly interchanged inside objects too.

A "mark" below means an annotation the user writes, such as "this cell is pseudo" or "this object is an ordinary ω-category". Under it, coh treats the relevant interchange cells as invertible.

### Example 1: a lax transformation and its naturality cell

Take F, G : B → C, an element x of B (a map ⊤ → B), and an arrow f : x ⇒ y of B.

**P.** A lax transformation is not a cell. The user declares

```
α  : B → [⟦D¹⟧, C]ₗₐₓ
e₀ : ev₀ ∘ α ≅ F        e₁ : ev₁ ∘ α ≅ G          (invertible 2-cells)
```

- **Component at x.** First take (α ∘ x)♭ : ⟦D¹⟧ → C. This is an arrow of C from ev₀(αx) to ev₁(αx). It becomes an arrow F x → G x only after composing with (e₀x)⁻¹ and e₁x.
- **Naturality at f.** First take (α ∘ f)♭ : ⟦D¹ ⊗ D¹⟧ → C, a lax square. Then extract its 2-cell generator and whisker it with e₀ and e₁ at x and y.
- So every use goes through two transport isomorphisms and the Λ/♭ rule.

**Two-tier L and uniform L.**

```
α   : F ⇒ G                                   (a context variable)
α_x := α ∘ x                                  (whiskering coh)
α_f := the interchange coh of α with f        (one term; the reverse direction is rejected)
```

**Verdict:** L is one line, P is about five steps with two isomorphisms carried through. If α is a *pseudo* transformation, P is one line (α is a variable and naturality is a coh in both directions). Two-tier L is then one line plus a "pseudo" mark on α.

### Example 2: composing lax transformations

Take α : F ⇒ G and α′ : G ⇒ G′, both from B to C, and β : H ⇒ K from C to D.

**Vertical composite α′·α.**
- **P.** Four steps:
  1. Pair α and α′ into B → [D¹, C] ×_C [D¹, C]. This is a pullback map, and it needs an isomorphism ev₁α ≅ ev₀α′ built from e₁ and e₀′.
  2. Identify the result with [D¹∨D¹, C].
  3. Restrict along the composite D¹ → D¹∨D¹.
  4. Build the new endpoint isomorphisms.

  Associativity and unit laws are restrictions along coherences, followed by comparing the endpoint data.
- **L.** α′·α is a coh. Associativity and units are coh.

**Horizontal composite of α and β.**
- **P.** Compose [D¹, β] ∘ α : B → [D¹, [D¹, D]]. Curry to [D¹⊗D¹, D], then restrict along one of the two diagonal paths of the square. The interchange between the two choices is restriction along the square's 2-cell. Endpoint isomorphisms for HF and KG are built by whiskering the e's.
- **L.** Write (βG)·(Hα) or (Kα)·(βF), one coh each. The directed interchanger between them is one more coh.
  - The user must pick one of the two. Laws such as middle-four interchange then hold in one direction only.
  - If β or α is marked pseudo, the two choices become interchangeable.

**Verdict:** for lax transformations L turns a multi-step universal-property construction into single coherences, and P never lets coh see these laws. The cost of L is choosing an order for horizontal composites.

### Example 3: comma objects and lax slices

- **All three options.** f ↓ g, the lax slice C//c, and other lax or partially lax limits are the same cone context (Mikhail's rules plus markings). Constructing them, and their 1-dimensional universal property, look the same.
- **Where they differ: the 2-dimensional universal property.**
  - Under P, the cells of Hom(X, f ↓ g) are built from pseudo transformations. The question "what does a *lax* transformation into C//c correspond to?" can be asked only through [D¹, –]ₗₐₓ again.
  - Under L it is a direct statement about native cells.

- **Correction (R11, verified).** Under P, Mikhail's rules as written force the arrows of a comma or hom object built this way to be *invertible*. P must restrict cone morphisms to pseudo ones, and still needs the Gray machinery for genuine hom objects (whose arrows are non-invertible). Under L the unrestricted lax rules are compatible, given the orientation fixed in §3.1 and the printed `ctrf` repair needed in either option.

**Verdict:** not a wash, as an earlier version said. L gets comma and hom objects directly from the limit rules. P needs modified rules plus Gray tensors for them.

### Example 4: adjunctions and monads between ω-categories

The standard notions (adjunction L ⊣ R : A ⇄ B, monad T on C) use pseudo transformations for η, ε, μ.

- **P.** Written exactly as in CaTT, with no annotations. Triangle laws and higher coherences (the swallowtail; associativity of μ at arity 4, which uses μ ⋆ μ) are cohs, and horizontal composites like μ ⋆ μ are canonical.
- **L, unmarked.** η, ε and μ are lax, so the user gets a weaker notion: a "lax adjunction" or "lax-natural monad". All of its theorems also hold for real adjunctions and monads. But some standard theorems need invertible naturality and fail for it, for example the hom-isomorphism Hom(Lx, y) ≅ Hom(x, Ry) being natural in both variables. The higher coherences involve μ ⋆ μ and η ⋆ ε, which have two non-equivalent layerings, so the user must write them in a specific orientation.
- **L, with "pseudo" marks on η, ε, μ.** Behaves like P. The cost is one mark per structure cell, plus a marking-propagation rule that makes every interchanger involving them invertible. Higher structure cells (e.g. modifications in the triangle laws) need their own marks, because pseudo-ness does not propagate upward (§2.4).
- **Gained by L:** monads and adjunctions whose structure cells are genuinely lax become statable directly. These are rare in practice.

**Verdict:** P wins on the standard notions. L matches it only with marks. L's advantage here is narrow.

### Example 5: a group or ring (ordinary math)

- **Group.** Present BG as an object from a computad with invertible marks, e.g. BZ from (x, s : x → x) with s invertible. Reasoning about elements of BG (composing, inverting, proving equations) happens *inside one object*.
  - P and two-tier L: identical, plain CaTT.
  - Uniform L: horizontal composites inside BG are directed. Every cell of BG is invertible, so with a propagation rule ("an interchanger with an invertible factor is invertible" **[conj]**) nothing changes. Without that rule the user marks BG ordinary.
- **Ring.** R with + and · : R × R → R (products are finite limits) and equation witnesses: invertible 2-cells between maps R³ → R.
  - P: those witnesses must be marked invertible anyway, since ambient 2-cells are directed in P too.
  - Two-tier L: the same marks suffice, given the propagation rule.
  - Neither option proves R discrete; that needs an h-level discipline in all three.

**Verdict:** P and two-tier L cost the same. Uniform L costs nothing extra *if* invertibility propagates automatically, and one mark per object otherwise.

### Example 6: structure inside an object (where uniform L differs)

A monoidal category M as a one-object 2-category BM: f ⊗ g is the horizontal composite of two 2-cells.

- **P and two-tier L.** f ⊗ g is a canonical coh, and Eckmann–Hilton and the braiding argument go through as in CaTT.
- **Uniform L, unmarked.** f ⊗ g has two layerings, (f⊗1)(1⊗g) and (1⊗g)(f⊗1), connected by a directed cell. So BM is a monoidal structure whose ⊗ is only laxly functorial. Ordinary monoidal reasoning needs "BM is ordinary".
- **Gained by uniform L:** objects whose own composition interchanges only laxly are first class. Examples are monoidal-like structures with a non-invertible interchanger, and ωCat_lax itself (or a lax universe) as an object. P and two-tier L can describe such things only through maps out of Gray tensors.

### What none of the three gives

**Lax functors**, meaning maps preserving composition only up to a directed cell. In all three options functors preserve composition up to invertible cells. Lax functors would need yet another rule (e.g. Gray-shaped "lax functor" contexts) in any of them. *Update 2026-11-18:* `ordinary-math.md` §7 proposes maps out of glued orientals for finite loop-free shapes (no new rule) and a directed refinement-coherence rule for lax-functor variables (`conjectures/lax-functor-refinement.md`).

### Gains and losses, side by side

| | **P** | **Two-tier L** | **Uniform L** |
|---|---|---|---|
| Lax transformations | 1-cells into [⟦D¹⟧, C]ₗₐₓ plus two endpoint isomorphisms. Every component and naturality cell is unpacked by hand. | context variables; components and naturality are cohs | same as two-tier |
| Composing lax transformations | universal-map constructions (pullback pairing, currying, restriction); laws not checked by coh | cohs; pick an order for horizontal composites | same |
| Standard notions (adjunction, monad, equivalence) | exactly as in CaTT | one "pseudo" mark per structure cell, or you get the weaker lax notion | same |
| Reasoning inside an object (elements, groups, rings) | plain CaTT | plain CaTT | plain CaTT after an "ordinary" mark or automatic propagation; otherwise directed |
| Objects with lax internal composition | not expressible as objects | not expressible as objects | expressible |
| Bookkeeping falls on | lax work (heavy) | pseudo work (one mark each) + layering choices | pseudo work + ordinary objects (one mark each) |

### The practical trade-off

- P is cheapest when most transformations are pseudo, which is the case in standard (∞,n)-category theory and ordinary math. It is clumsy wherever lax transformations are the point: lax naturality, lax colimits and Grothendieck constructions, (op)lax twists, lax slices.
- L reverses this. It moves the annotation cost from lax work to pseudo work.
- **Surface defaults are a lever.** The kernel can be uniform L while the surface syntax assumes "objects are ordinary, transformations are pseudo, unless declared lax". The user then writes P-style code for standard work and opts into laxness where it matters. The kernel cost is the marking and propagation machinery, which P also needs for marked limits.

---

## Reconciliation with the other notes

*Added 2026-11-18. This note is now the single pseudo-vs-lax comparison for the project. The comparison sections in `limits-representables.md` (PR #2 §3) and `internal-hom.md` (PR #3 Part I) point here. Below, each point on which they and this note disagreed is settled on the merits. "Option A/B" in PR #3 are P/L here.*

### R1. Can the L side condition be stated, and is it decidable?

- **Earlier claims.**
  - PR #2 §3.3: "side conditions stop being purely free-variable checks… an orientation condition, not a free-variable condition."
  - PR #3 I.4: "a new kind of side condition… its correctness is the central open problem."
  - PR #3 I.7, experiment 2, asks whether a free-variable-style test that permits CaTT minus interchange can be found.
- **Settled.** Yes, it can be stated, and it is decidable (§3.3).
  - The test is still "the sides use exactly these generators". The generators are now those of the Gray unfolding of the pasting scheme rather than its raw variables.
  - Orientation is not a separate check. The two whiskered composites of an interchange have *different* supports (∂⁻ and ∂⁺ of the unfolding), so the coherence case cannot relate them, and the operation case relates them in one direction only (§3.4).
  - On a single hom the test is expected to coincide with Finster–Mimram's Var **[conj]**, which is step 2 of the plan in §7.1.

  So experiment 2 has an answer in the CaTT aesthetic.
- **What PR #2 and PR #3 got right.** Stating the test is not the same as knowing it is *correct*. Correctness is lemma S1: in the intended models, any two parallel terms with full support over a Gray unfolding are connected by an invertible cell. When PR #2 and PR #3 were written, nobody had attempted it. §3.6 now attempts it:
  - for the strict model it is proved modulo three combinatorial lemmas;
  - for (∞,ω) models it is reduced to the scope of Campion's pasting theorem;
  - uniform L first needs a construction.

  The earlier summary of this note ("a small, decidable change") was accurate about the rule and silent about S1. The summary now says both.

### R2. Does L need a new class of context shapes?

- **Earlier claims.**
  - PR #2 §3.3: "Gray tensors of pasting schemes are not pasting schemes… the core would need a new shape class, whose well-formedness and contractibility are open for n > 1."
  - PR #3 I.6 lists "the same Gray shapes" as new machinery for both options.
- **Settled.** Not in the kernel.
  - L's contexts stay pasting schemes. The Gray tensor is computed on chain complexes, only to evaluate side conditions.
  - Every source and target needed, including the Gray cube's hexagons, is an ordinary term over pasting schemes (§3.4).
- **Where the n > 1 problem really lives.** Typing Gray-shaped *contexts* (PR #3's G1; Mikhail's open n > 1 case) is needed by **P**, for its lax function objects [Θ, C]ₗₐₓ. Under L, Gray-shaped diagrams are maps out of free objects into native lax homs. That they are derivable is a conjecture (§4.2), which replaces G1 rather than adding to it.

### R3. Is there a semantics?

- **Earlier claims.**
  - PR #3 I.4: "the intended model, ω-categories enriched over the Gray tensor, is expected to exist but is not in the literature in a usable form."
  - PR #2 §3.3: "no published weak-ω notion."
- **Settled.**
  - **∞-categorical target (two-tier L): in the literature.** Campion builds the Gray tensor on (∞,ω)-categories as a monoidal biclosed structure, and Gepner–Heine (2025) define categories enriched in it ("oriented categories") and treat ∞Cat as one (§2.1).
  - **Strict test model: in the literature** (Ara–Maltsiniotis).
  - **Algebraic, CaTT-style notion: not in the literature.** This means a coherator, i.e. what "a model of L" would be in the Grothendieck–Maltsiniotis sense. PR #2 and PR #3 are right about that. But the same gap exists for P: no one has shown that ωCat itself is a model of CaTT.
  - **Uniform L: no semantics of its own** (§2.5).

### R4. What carries over from existing CaTT metatheory?

- **Earlier claims.** PR #2: "none directly; each needs reproving." PR #3: "most existing CaTT results need to be redone."
- **Settled: partly.**
  - The single-hom fragment of two-tier L *is* CaTT (given the [conj] in R1). So the existing checker, models of hom-ω-categories, suspension, and the invertibility argument for the coherence case all carry over.
  - What needs new work is everything about composition across objects: computads, models, S1, and the interaction with markings.
  - Anthony has said redoing results is not a cost, so this matters only as a schedule question.

### R5. Dualities

- **Earlier claim.** PR #3 I.4: "Half the dualities stop being symmetries. Reversing dimension-2 cells turns lax into oplax."
- **Settled: PR #3 is right, and §5.4 of this note understated it.**
  - Under L, an opposites meta-operation that reverses the order of composition across objects sends the lax theory to the *oplax* theory, not to itself. By the Gray tensor's duality formulas (AM Props. A.20, A.22; `conventions.md` §3.3), the odd dual (X⊗Y)^op ≅ Y^op ⊗ X^op and the even dual (X⊗Y)^co ≅ Y^co ⊗ X^co swap lax and oplax, while the total dual (X⊗Y)° ≅ X° ⊗ Y° is a symmetry of the lax theory. By AM Remark A.21 no other duality gives an isomorphism of this kind.
  - Practical consequence: a lemma proved once and dualised may land in the oplax theory, so a second proof may be needed. CaTT's proof-size savings from opposites shrink accordingly.
  - Mitigation: a kernel parameterised by orientation, so proofs transfer between the lax and oplax theories. This reduces the loss but does not remove it.
  - Which reversals survive is a short computation, and it is PR #3's experiment 3. Under two-tier L, dualities used only inside one object (e.g. the Eckmann–Hilton development) are unaffected.
  - **Done (2026-11-18, `closed-structure.md` Part D, Agda `GrayDuality.agda`).**
    - Symmetries of two-tier L: J ∈ {∅, {2,3,…}, odd, {1,2,4,6,…}}.
    - Lax ↔ oplax swaps: J ∈ {{1}, all, even, {3,5,7,…}}.
    - Every other J lands in a mixed-orientation theory L_ε.
    - The orientation-parameterised kernel is the family L_ε, on which all dualities act. Implementing it costs one sign per dimension in the support computation.

### R6. "P and L coincide for functors into 1-categories" (PR #2 §3.2)

- **Semantically true.** Into a 1-category, every interchange cell is invertible.
- **Syntactically, L does not know this.** It needs either a mark ("C is a 1-category") or a propagation rule from invertibility of C's cells (Example 5 above). So for ordinary math the difference is annotation cost, not expressiveness.

### R7. Staging: "build P first, then test elaborating L into it" (PR #2 §3.4)

- **Settled: the cheap direction is the other way round.**
  - P sits inside L as the marked fragment (§2.4). Embedding is cheap.
  - Elaborating L into P would require P to have lax homs for arbitrary domains, Gray composition maps between them, and all their coherence cells via `uni`. Those are the most expensive parts of P, so this direction is costly.
- **PR #2's underlying aim survives.** Its aim was to start from existing foundations. Two-tier L does that: step 2 of §7.1 *is* the existing checker, re-expressed through supports.
- **The Agda thread agrees** (PR #4, finding 4 and suggested next steps):
  - it lists "a Gray-CaTT whose invertible fragment is CaTT" as option (c), which is this note's conclusion;
  - it proposes the same first experiment: orient the full-coherence case and check that naturality typechecks in one direction only.

### R8. Where lax transformations are actually needed

- **Earlier claim.** PR #3 I.1 and I.6 list "lax limits, lax algebras, monad morphisms" as uses of lax transformations.
- **Correction.**
  - The 2-cells in lax algebras and lax monad morphisms are ordinary non-invertible 2-cells of the ambient. Every option has those, P included, since P's 2-cells are directed and only their *naturality* is invertible.
  - Lax limits likewise need only non-invertible cone cells (Mikhail; Example 3).
  - Lax *transformations* matter when naturality itself is directed. That covers lax naturality squares, maps into lax function objects, (op)lax twists (JFS), Grothendieck-type constructions, and composing such things.

  So P covers more of the "lax" programme than PR #3's table suggests. The difference between P and L is concentrated in Examples 1–2 above.

### R9. Mimram's CCCaTT (PR #3 §5.7)

- **Neutral between P and L.** It supplies the closed structure in CaTT style. A cartesian-closed version is published (1-dimensional). The planar/linear version, which a Gray-closed (lax) hom would need, is unpublished.
  - **P** needs the cartesian one for its native hom and a planar/linear one for lax homs of arbitrary domain.
  - **L** needs the planar/linear one for currying its native (lax) hom, and gets the pseudo hom from markings plus products.

  Either way both flavours appear.
- **One connection.** L's support condition and CCCaTT's planar/linear pasting types both express the same "no duplication, no cancellation, order matters" principle, the linearity theme of survey §13. That is a reason to expect the two to fit together, not a decision criterion.

### R10. Option C (two kinds of 2-cell)

PR #3 I.5 considers a double structure with both pseudo and lax 2-cells. Agreed: it is heavier than both P and L. It is subsumed by L with markings, where pseudo 2-cells are marked lax ones.

### R11. CaTT_lim and directed interchange (verified researcher result)

**The result.** `notes/conjectures/catt-lim-pseudo-vs-gray.md` (answered and verified, PR #11) establishes three things.
- **Forced invertibility.** In a CaTT ambient, Mikhail's universal property forces the comparison cell m_f of every cone morphism to be invertible. The cell of ucone_*(β) is CaTT's invertible interchanger I_{β,λ_f}, and essential surjectivity transfers that invertibility.
- **Collapse.** With `uni` at all levels, every ambient cell of dimension ≥ 3 becomes invertible. There is a finite cartesian counterexample to the unchanged rules.
- **No oriented models.** Oriented (Gray-enriched) categories cannot model *unchanged* CaTT_lim, because unchanged CaTT already contains the invertible interchanger and its inverse.
- **Two repairs.**
  - Keep CaTT and restrict cone transfors to invertible comparison cells over positive-dimensional diagram variables. This must be done with marked declarations, not an invertibility rule.
  - Keep unrestricted lax transfors and change the base theory so that this interchanger is directed. This is option L.
- Separately, Mikhail's printed `ctrf` side condition (Def. 4.15) needs a repair under either option.

**What it means for each option.**
- **P.** It must use the restricted universal property. Its limits then classify lax cones with *pseudo* morphisms, and comma and hom objects built from limits have only invertible arrows (eq. (8) there: the cartesian arrow fibre is the core of the hom). Genuine hom objects and lax cotensors need the Gray tensor (G1), not limits.
- **Two-tier L.** Compatible with the *unrestricted* universal property, given two checks.
  - *Where the obstruction lives.* Every interchanger used in the argument composes a cell along c → L with a cell along L → (diagram), i.e. across an object. Two-tier L directs exactly those, so the forced-invertibility argument does not go through: ucone_*(β)'s comparison cell is a directed interchanger, and essential surjectivity transfers nothing invertible. The same holds for the ≥3-cell collapse argument (§4 there), which interchanges an arbitrary 3-cell along c → Y with a cell along Y → ·. Inside a hom, two-tier L's interchange stays invertible, and the argument never uses it **[checked against §§1–4 of the response; the semantic re-derivation is now done, see *Semantics* below]**.
  - *Orientation.* The direction is forced: the universal cone needs (u◁φ);(β▷v′) ⇛ (β▷v);(u′◁φ). §3.1 now fixes L's factor order so that this is the derivable direction. With the reverse order, ucone_* would be ill-typed in L.
  - *Semantics (answered, researcher result verified 2026-11-18; `notes/conjectures/oriented-lax-limits.md`).* In ∞Cat as an oriented category, the unrestricted lax universal property holds with no collapse. For an arrow F : X → Y the limit is `Fun^oplax([1], Y) ×_{ev₁,Y,F} X`, and it has cone morphisms with non-invertible m_F in every dimension. Every small diagram has such a limit, as a Gray-weighted limit. The response also locates the failed step of the cartesian argument: it needs the interchanger to be invertible. That is the line-by-line re-derivation asked for above.
  - *Marked legs.* A partially lax limit must respect its marked leg coherently: m_b invertible in every dimension. With an arbitrary m_b, a finite strict 2-category shows that no limit exists. With the coherent marking, the comma `⊤ →a C ←b ⊤` is the full `Hom_C(b, a)`.
- **Uniform L.** The same, plus the inner levels: cone transfors of higher dimension interchange laxly inside homs too, so `ctrf` shapes must use uniform Gray shapes. This depends on the construction problem of §2.5.

**Practical point.** Under L, comma objects, hom objects and lax cotensors come directly from the limit rules (with the ctrf repair). Under P they need the restricted rules plus Gray tensors.

### Settled conclusion

1. **Stating L is solved.** The coherence side condition for lax interchange can be stated in the CaTT aesthetic, as an equality-of-supports test on pasting-scheme contexts, and it is decidable. No new context shapes are needed.
2. **Correctness of L: the attempt is in §3.6.**
   - **Two-tier L, strict model.** Proved, modulo three combinatorial lemmas about Steiner complexes that are stated as a self-contained problem. This covers soundness, non-degeneracy (the reverse interchanger is not derivable) and conservativity over CaTT on a single hom.
   - **Two-tier L, (∞,ω) models.** Reduced to whether Campion's pasting theorem covers Gray tensors of pasting diagrams (a second problem).
   - **Uniform L.** Needs a definition before it can be proved: §2.5's recursive formula was wrong. Stated as a construction problem.
3. **Practical trade-off.** P is cheapest for pseudo-heavy and standard work and clumsy for lax transformations. L reverses this. Uniform L adds marks inside objects.
4. **Real losses of L that remain:**
   - fewer dualities (R5);
   - annotations for pseudo work and for 1-categorical targets (R6);
   - non-canonical horizontal composites.
5. **Recommendation.** Pursue uniform L, and work on the open problems of §3.6 in parallel rather than treating them as gates (§7).

---

## 0. Summary

1. **The target is not an ω-category.** The ω-category of ω-categories with lax transformations is a category *enriched over ωCat with the lax Gray tensor*, which Gepner–Heine call an **oriented category** ([2510.10504](https://arxiv.org/abs/2510.10504), §1.8, with ∞Cat's hom-objects being Fun^lax(S, T)) **[paper, intro level]**. A CaTT model is enriched over the *cartesian* product. So under P the ambient is a different object (ωCat with pseudo transformations), and the lax one appears only as a family of objects and maps inside it.
2. **Two versions of L.** In ωCat_lax only the outermost composition is Gray, since each hom Fun^lax(B, C) is an ordinary ω-category.
   - **Two-tier L** matches that exactly: plain CaTT inside homs, directed interchange only for composition across objects.
   - **Uniform L** makes interchange directed at every level. Its side condition needs a free "lax at every level" structure to compute supports in, and that structure still has to be constructed (§2.5).
   - Uniform L is weaker than two-tier L, which is weaker than P. Each stronger theory is the weaker one plus an invertibility marking, so every model of the stronger theory is a model of the weaker one, ωCat_lax included **[conj]**.
   - *Revised 2026-11-18 after Anthony clarified that "lax by default" means "the most general version until there is a concrete reason otherwise". The first version recommended two-tier L.*
3. **The L rule is a small syntactic change.** Contexts stay pasting schemes, and the coh rule keeps its shape. What changes is the side condition: free-variable sets are replaced by **supports in the Gray unfolding** of the pasting scheme. For Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ, that unfolding is the hom-level shape Θ₁ ⊗ … ⊗ Θₙ (factors in execution order; §3.1 explains why the order is forced). Supports are Steiner chains, so the check is integer linear algebra and decidable (§3).
   - *Stating* the rule is the small part. Its correctness for two-tier L is proved in the strict model modulo three combinatorial lemmas, and reduced to a known theorem's scope for (∞,ω) models (§3.6). The open pieces are written up as self-contained problems in `notes/conjectures/`.
4. **L absorbs the hardest open item of P.** Under P, lax homs [Θ, C]ₗₐₓ need a Gray *context former* whose generators x⊗y must be typed by composites of non-pasting molecules. PR #3 calls this "the biggest open technical point" (G1). Under L, a lax square in C is just the interchanger of a native 2-cell with an arrow of C, so lax homs are the native hom made into an object and Gray contexts become derivable (§4.2).
5. **L is the weaker theory, and P is recoverable from it.** Every cartesian-enriched model is also Gray-enriched, through the comparison map X ⊗ Y → X × Y. So **P ≈ L + "interchangers are invertible"** **[conj]**. "Pseudo = lax + marking", which PR #3 adopted for shapes, then holds for the ambient as well. Choosing L does not close off P; the reverse is false.
6. **L's real costs.**
   - The horizontal composite of 2-cells across objects no longer exists canonically. Users choose an order, and the laws carry directed interchangers.
   - Ordinary-math reasoning in low dimensions may meet interchangers that are semantically invertible but not syntactically so.
   - The metatheory (computads, models, invertibility, substitution) must be built for the new side condition.
   - Under two-tier L, a future universe object would be pseudo, not lax, so it would not match the ambient (§4.7). Uniform L removes this mismatch.

   None of these makes L ill-defined.
7. **Is there an unambiguous path?**
   - **P:** unambiguous to build, but it is the least general option.
   - **Two-tier L:** a target in the literature (oriented categories; the strict model of Ara–Maltsiniotis), a pinned-down rule change, and a finite list of lemmas.
   - **Uniform L:** the side condition needs the free strict structure with directed interchange at every level, which has not been constructed. Iterated Gray enrichment does not give it (Crans; Bourke–Lobbia). This is a construction problem, now posed in `notes/conjectures/strict-lax-interchange-at-every-level.md`. It is not a reason to drop uniform L.

**Recommendation (revised): uniform L as the kernel**, with "ordinary ω-category" (interchange invertible inside an object) and "pseudo" as markings (§2.5, §7). Both two-tier L and P remain reachable by marking. The open problems behind each version are worked on in parallel, not used as gates.

---

## 1. What the question is

Three threads found the same obstruction. CaTT's coherence side condition admits the interchange cell in both directions, so in any CaTT model the naturality cell of a 2-cell at a 1-cell is invertible (Benjamin–Markakis, all coherences are invertible, [2406.12127](https://arxiv.org/abs/2406.12127)). Lax transformations do not have this property.

- **P:** keep CaTT. The ambient's 2-cells are pseudo transformations. Lax ones come from lax function objects [⟦D¹⟧, C]ₗₐₓ, built from Gray-tensored contexts.
- **L:** change the coherence rule so interchange across objects is directed. The ambient's 2-cells are lax transformations.

The comparison should be about which *mathematical object* each theory is the internal language of, and what working in it is like.

---

## 2. Structural facts that decide most of the comparison

### 2.1 ωCat with lax transformations is Gray-enriched

- **Strict.** Strict ω-Cat with the Ara–Maltsiniotis Gray tensor is monoidal biclosed, with Hom(A ⊗ B, C) ≅ Hom(A, Hom_oplax(B, C)) ≅ Hom(B, Hom_lax(A, C)) ([1607.00668](https://arxiv.org/abs/1607.00668)) **[paper: Thm A.15, §A.18]**. AM's names agree with Bénabou's (`conventions.md` §3.1). So strict ω-Cat is enriched over (ω-Cat, ⊗) in two ways: ∞-Cat_oplax with homs Hom_oplax, and ∞-Cat_lax with homs Hom_lax, enriched in the transposed tensor **[paper: AM Ex. C.18, §C.16]**. The latter, read in execution order, is L's ambient (`conventions.md` §4).
- **(∞,ω).** Campion constructs a unique monoidal biclosed Gray structure on Cat_n for n ∈ ℕ ∪ {ω} (Theorem A of [2311.00205](https://arxiv.org/abs/2311.00205)) **[paper, abstract/intro]**. A left-closed monoidal ∞-category is enriched in itself, with hom-objects the internal homs **[paper: Gepner–Haugseng, [1312.3178](https://arxiv.org/abs/1312.3178), Cor. 7.4.10]**. So Cat_ω is Gray-enriched, with hom-objects Fun^lax(A, B).
- **Named notion.** Gepner–Heine, *Oriented category theory* ([2510.10504](https://arxiv.org/abs/2510.10504)), define oriented categories as categories enriched in ∞Cat for the lax Gray tensor. Their compositions "only commute up to a coherent (anti)oriented interchange law". They state that ∞Cat viewed as an oriented category has hom-objects Fun^lax(S, T) **[paper, intro level]**. Their companion paper on oriented colimits is the one PR #2 already cites ([2608.02592](https://arxiv.org/abs/2608.02592)).

So **L's semantic target is an established notion. P's ambient is the cartesian (∞,ω)-category Cat_ω, which is a different object.**

### 2.2 Only composition across objects is Gray

In a Gray-enriched 𝒦:

- For objects a, b, the hom 𝒦(a, b) is an ordinary ω-category. All its internal compositions, which are 𝒦's compositions in dimension ≥ 1, interchange invertibly as usual.
- Composition across objects is 𝒦(a, b) ⊗ 𝒦(b, c) → 𝒦(a, c), with factors in execution order; this order is the lax/oplax convention, fixed in §3.1 and recorded project-wide in `conventions.md` §4. On generators it sends a pair (x, y) of cells of dimensions m and k (in the homs) to a cell of dimension m + k. So:
  - an object x (k = 0) whiskers: y ⊗ x has the dimension of y;
  - two 1-cells of homs (2-cells of 𝒦, i.e. transformations α, β) give a **2-cell of the hom, i.e. a 3-cell of 𝒦: the interchanger**, between the two whiskered composites. There is no horizontal composite in dimension 2.

This is the precise content of "lax by default" for ωCat. Inside an object C, cells are an ω-category, and CaTT reasoning in C is plain CaTT. Lax transformations compose vertically by the ordinary laws of Fun^lax(B, C). Directedness lives only where transformations are composed across different objects.

### 2.3 "Directed interchange at every level" is not a settled target

One could try a theory in which *every* pair of compositions interchanges directedly, i.e. Gray structure at every level. The evidence says this is not a well-understood structure:

- Crans showed that no monoidal biclosed structure on Gray-categories captures weak transformations. Bourke–Lobbia ([2212.12358](https://arxiv.org/abs/2212.12358)) recall this and work around it with *skew* monoidal closed structures, one for lax and one for pseudo transformations **[paper, abstract/intro]**. A related obstruction is Bourke–Gurski, *A cocategorical obstruction to tensor products of Gray-categories* (TAC 30, 2015; [1412.1320](https://arxiv.org/abs/1412.1320)): any monoidal biclosed structure on Gray-categories has undesirable properties, and none makes the model category of Gray-categories a monoidal model category **[paper, abstract]**.
- Gepner–Heine introduce *bioriented* categories, related to suspension. This is the frontier, not a foundation one can build a kernel against yet **[paper, intro level]**.
- The objects of ωCat are ordinary ω-categories anyway. A uniformly directed theory would describe something *other* than ωCat_lax.

*First-version conclusion, superseded by §2.5:* "L should mean two-tier L." That conclusion assumed the target was ωCat_lax exactly. Under the generality principle it does not hold, and §2.5 replaces it.

### 2.4 Every P-model is an L-model

There is a canonical comparison X ⊗ Y → X × Y, which collapses the mixed generators. It makes the identity a lax monoidal functor (ωCat, ×) → (ωCat, ⊗), and change of base along it turns a cartesian-enriched ω-category into a Gray-enriched one whose interchangers are invertible **[paper: AM Ex. C.17 gives the lax monoidal structure, with comparison (1_X ⊗ p_Y, p_X ⊗ 1_Y) : X ⊗ Y → X × Y and identity unit constraint; the change of base is standard enriched category theory]**. Since × is symmetric, the result can be read in either factor order, in particular in L's (`conventions.md` §4). The interchanger generators β ⊗ φ map to identities.

Consequences:

- Everything L proves holds in every CaTT model. **L is a weaker theory with more models**, including both ωCat_lax and ωCat_pseudo.
- **[conj]** L plus a rule "every interchanger is invertible" is equivalent to P, in the sense of having the same models, with a conservative translation of P-terms. Horizontal composites become definable by a chosen layering, and the two layerings are related by an invertible cell.
- PR #3's principle "pseudo = lax + marking" becomes uniform. It applies to the ambient's own cells, not only to shapes.
  - **Now proved** (researcher response, verified; `notes/conjectures/gray-vs-cartesian.md`, PR #14). (A ⊗ B)[mixed⁻¹] ≃ A × B in every Cat_n and in (∞,ω). Strong transformations, and their higher cells, are exactly the lax ones whose adjunct inverts every mixed cell, *including on boundary faces*.
  - **Caveat: the marking must be recursive.** The strong internal hom is **not** a locally full sub-ω-category of the lax one. Between two strong transformations there can be lax modifications whose naturality 3-cell is not invertible (counterexample with B = D¹, C = D³).
  - So "pseudo" cannot be a mark on a 2-cell alone. It must be a mark *on every cell in every dimension*: a pseudo transformation, pseudo modifications between those, and so on, each requiring its own mixed cells to be invertible. Equivalently, P ≈ L + "every interchanger, of every dimension, is invertible". The [conj] above is meant in this recursive sense.

### 2.5 Uniform L, and where generality stops

**The rule.** The coh rule of §3.3 is unchanged. Only the structure in which supports are computed changes.
- Two-tier L computes supports in ν(Θ₁ ⊗ … ⊗ Θₙ), a strict ω-category, so composition *inside* the hom interchanges strictly.
- Uniform L needs, in its place, the **free strict structure on Γ in which every interchange is directed**. Each hom is then itself such a structure, not an ω-category.

**Correction (2026-11-18).** An earlier version of this section defined uniform L by the recursion U(ΣΘ₁ ∨ … ∨ ΣΘₙ) := U(Θₙ) ⊗ … ⊗ U(Θ₁). That formula is wrong. U(Θ) is the shape of a *single hom* of Θ's free structure, so the recursion throws away all of Θ's lower-dimensional structure. For example, it sends a vertical composable pair of 2-cells to a point.

The right object is not a Steiner complex at all, because ν always produces strict ω-categories. Constructing it is a problem in its own right. Iterated Gray enrichment does not give it (Crans; Bourke–Lobbia), and Forest–Mimram's Gray presentations do it in dimension 3 only. The problem, with the properties the rule needs, is posed in `notes/conjectures/strict-lax-interchange-at-every-level.md`.

**What it does.**
- Example: inside a single object C, take two 2-cells composable along a 1-cell, i.e. Γ = Σ(D¹ ∨ D¹) in C's own cells. This now gets a directed interchanger one dimension up, just as transformations do in two-tier L.
- So Eckmann–Hilton, horizontal composites and the like are directed everywhere, unless marked.

**Generality ordering [conj].** Uniform L ⊂ two-tier L ⊂ P, in the sense that each is the previous one plus invertibility markings:
- "interchange inside this hom is invertible" gives two-tier;
- "every interchanger is invertible" gives P.

Finer supports map onto coarser ones under the collapse X ⊗ Y → X × Y, so every pair of terms the finer rule accepts, the coarser rule accepts too. Hence every model of the stronger theory is a model of the weaker one, including ωCat_lax and every ordinary ω-category.

**What uniform L gains over two-tier L.**
- Objects need not be ordinary ω-categories. The theory also covers objects whose own compositions interchange directedly, such as Gepner–Heine's oriented categories, which are not ω-categories.
- The ambient and its objects are the same *kind* of structure again. This removes the universe mismatch of §4.7: a universe object can be lax.
- One rule at every level, with no special status for dimension 0. That is closer to the CaTT aesthetic than two-tier L.

**What has to be done, and what it costs.**
1. **No construction yet of the free structure the side condition needs** (above). This is open, not a reason against: the problem is posed and being worked on. If it is solved, the two-tier proof of §3.6 should transfer with Steiner chains replaced by the new generator sets.
   - **Constraints now known** (researcher response, verified 2026-11-18; see the end of `notes/conjectures/strict-lax-interchange-at-every-level.md`):
     - *Higher interchangers must be boundary-adjusted.* A raw cell `(a ∗ₗ b) ∗ₖ (c ∗ₗ d) → (a ∗ₖ c) ∗ₗ (b ∗ₖ d)` for cells of dimension above l+1 forces strict interchange two dimensions down, so it kills directedness. The higher instances must be naturality comparisons. Not of the joint form `L_A ∗₂ χ_{a′} ⇛ χ_a ∗₂ R_A`: a second verified response (2026-11-18, `conjectures/answered/directed-interchange-every-level-2026-11-18.md`) shows that this has no image in the Gray quotient. Instead they are tensor-shaped: one Leibniz-signed naturality cell per variable, and higher cells between routes. Uniform L's side condition must compute supports in a structure built that way. Under that corrected reading the problem is open, not refuted.
     - *Supports live in the expanded basis.* If support of a composite were the union of supports, every interchange would be forced strict. This is already how §3.2 computes supports for k = 0.
     - *Finiteness.* If F(Γ) has one finite generator set with injective support, it has only finitely many non-identity cells, so the tower of higher comparisons must stop in each F(Γ).
     - *Dimension 4.* Bourke–Lobbia's lax 4-categories (arXiv 2610.31448 §4.2.6) direct the outer interchanger but keep Gray-category homs, so they are two-tier, not uniform, in dimension 4.
2. **Usability, unless markings are cheap.** Plain CaTT reasoning inside an object (elements, the post's §Functors) now has directed interchange. The fix is a marking "C is an ordinary ω-category" that restores invertible interchange in C. The marking must be easy enough that ordinary use never notices it.
3. **Cost.** Unfoldings now multiply at every level, not only across objects. Symbolic supports should keep this polynomial **[conj]**, but it is a real constant-factor cost.

**Where generality stops.** One step further is to drop the interchanger entirely, i.e. an ω-sesquicategory: whiskering without any interchange cell (AM Appendix C define ∞-sesquicategories and use them as the underlying structure of Gray ∞-categories; Araújo studies n-sesquicategories, their computads and string diagrams, [2210.07704](https://arxiv.org/abs/2210.07704)) **[paper]**. *Correction:* an earlier version called this "the setting of Markakis's generalised signatures". Markakis's signatures ([2303.11978](https://arxiv.org/abs/2303.11978)) are about computads for operations over a direct category of sorts (weak ω-categories, semi-simplicial Kan complexes); sesquicategories are not their topic. That gives up the *existence* of naturality cells, which every lax transformation has. So there is a concrete reason to stop at directed interchange: it is the most general option that still contains the intended structure.

---

## 3. What the Gray-style coh rule looks like (two-tier L)

### 3.1 Contexts: unchanged

Pasting schemes as in Finster–Mimram. Every pasting scheme decomposes uniquely as a wedge of suspensions

```
Γ  =  ΣΘ₁ ∨ ΣΘ₂ ∨ … ∨ ΣΘₙ          (n ≥ 0; objects a₀, …, aₙ)
```

Here Θᵢ is the pasting scheme of cells in the hom from aᵢ₋₁ to aᵢ.

**Gray unfolding.** Define the hom-level shapes

```
U_{ij}(Γ)  :=  Θᵢ₊₁ ⊗ … ⊗ Θⱼ          (i < j, factors in execution order)
```

These are tensors of Steiner complexes, computed generator-wise, with generators θⱼ ⊗ … ⊗ θᵢ₊₁, dimension the sum, and boundary given by the Leibniz formula. Mikhail's `gray` judgment and PR #3 §4.1 give the same formula. The Steiner complex λ(S) of a pasting diagram is a strong Steiner complex, i.e. its basis is unital and *strongly* loop-free **[paper: AM Prop. 4.13]**, and tensors of strongly loop-free unital bases are strongly loop-free **[paper: Steiner, HHA 2004, Example 3.10]**. *Correction:* an earlier version said "loop-free"; Steiner's tensor statement is for the strong notion (which implies loop-free, Steiner Prop. 3.7). So the free strict ω-category on U_{ij} is ν of a strong Steiner complex, freely generated by its atoms (Steiner Thm 5.6), and its cells are determined by their chains.

The **order of factors** is the lax/oplax convention, and it is **forced by the limit rules**. The project-wide statement of this convention, with the Leibniz computation, is `conventions.md` §4. Mikhail's lax cones need the comparison cell of a cone morphism to go from "outer cell first" to "inner cell first". In execution order, for β : u ⇒ u′ (from c to L) and φ : v ⇒ v′ (from L to y), that is

```
(u◁φ);(β▷v′)  ⇛  (β▷v);(u′◁φ)
```

(`notes/conjectures/catt-lim-pseudo-vs-gray.md`, eq. (2), verified). With factors in execution order, the Leibniz formula gives exactly this orientation; the reverse factor order gives the opposite one. So U is Θᵢ₊₁ ⊗ … ⊗ Θⱼ.
- *Correction:* an earlier version used the reverse order, which would have made Mikhail's universal cone ill-typed under L.
- The same orientation makes the naturality cell of α : F ⇒ G at f : x → y go α_x ; Gf ⇛ Ff ; α_y (execution order), i.e. Gf ∘ α_x ⇛ α_y ∘ Ff. That is the lax convention of Bénabou and Johnson-Freyd–Scheimbauer.

### 3.2 Supports

For a term t : A in context Γ with endpoints aᵢ, aⱼ (dimension ≥ 1), define **supp(t : A)** as the graded set of generators of U_{ij}(Γ) that appear in the image of t and its iterated boundaries under the *strict* interpretation. That is, interpret t in the free strict Gray-enriched ω-category on Γ, which is computable through Steiner chains. For objects and terms of dimension 0 the support is just the variable.

**[proposal]** Read side conditions off the strict model. This is how the free-variable sets of CaTT behave too:

- **[conj]** On a single hom (n = 1), supp coincides with Finster–Mimram's Var. The intuition is that the free strict ω-category on a pasting scheme has no cancellation, so a variable used by a term stays in the support of its strict image.
- This is the same "linearity / no cancellation" principle that the survey (§13) identifies as recurring.

*Convention, as formalized (`notes/agda-gray-findings.md`).* "Its iterated boundaries" means the cells in t's type, read type-directedly like Var(t : A). Side conditions compare the *downward closures* of these sets in K(Γ), as in §3.6. The table support alone, i.e. the union of the chains of ⟦t⟧'s table, is not enough here. For example, in D¹ ⊗ D¹ the 0-cells f⊗g′ and f′⊗g occur only in boundaries of atoms, so they are absent from the table support of the total cell but present in its closure, which is all of U. The same holds for single homs: in f ⇒ g ⇒ h the middle 1-cell g is absent from the table support of the vertical composite, so supp = Var on a single hom (§3.2 [conj]) can only hold for closed supports.

### 3.3 The rule

```
Γ ⊢ps     Γ ⊢ t :A    Γ ⊢ u :A      Δ ⊢ σ : Γ        (t, u with endpoints aᵢ, aⱼ)

(operation)  supp(t:A) = ∂⁻U_{ij}(Γ)   and   supp(u:A) = ∂⁺U_{ij}(Γ)
(coherence)  supp(t:A) = U_{ij}(Γ) = supp(u:A)
──────────────────────────────────────────────────────────────────────
Δ ⊢ coh_{Γ, t →_A u}[σ] : (t →_A u)[σ]
```

- ∂^± are taken in the molecule U_{ij} at dimension dim U_{ij} − 1, with all lower boundaries.
- *As formalized:* the operation case also checks dim A = dim U_{ij} explicitly. For A = ⋆ (composites of 1-cells and identities), the condition is dim U = 0, t = a₀, u = aₙ. Both cases compare downward closures (§3.2 convention). Implemented and checked in `src/CaTTExp/Gray/`.
- Composites and coherences relate the endpoints a₀ and aₙ, so in practice (i, j) = (0, n). The general indexing is for sub-terms.
- **The dimension changes.** The operation case over Γ produces a cell of 𝒦-dimension 1 + Σᵢ dim Θᵢ, not dim Γ.

### 3.4 Worked cases

**Whiskering.** Take Γ = ΣD⁰ ∨ ΣD¹, a 1-cell f followed by a 2-cell β : g ⇒ g′. Then U = D¹ ⊗ D⁰ ≅ D¹, and the operation case gives βf. This is the same as in CaTT.

**Horizontal composite: gone.** Take Γ = ΣD¹ ∨ ΣD¹, with α : f ⇒ f′ : x → y and β : g ⇒ g′ : y → z.

- U = D¹_α ⊗ D¹_β is the lax square in 𝒦(x, z). It has four vertices f;g, f′;g, f;g′, f′;g′, four edges, and one 2-dimensional generator α⊗β.
- No term of 𝒦-dimension 2 has full support, so there is **no coherence-case or operation-case horizontal composite**. The two whiskered composites (f◁β);(α▷g′) and (α▷g);(f′◁β) are both well typed, through ordinary whiskering and vertical cohs, but they are not identified.

**The interchanger: one direction only.** In the same Γ, the Leibniz formula gives, in execution order:

```
∂⁻(α⊗β) = (f⊗β) ∪ (α⊗g′)      i.e.   (f◁β) ; (α▷g′)      β first, then α
∂⁺(α⊗β) = (α⊗g) ∪ (f′⊗β)      i.e.   (α▷g) ; (f′◁β)      α first, then β
```

- So coh_{Γ, (f◁β);(α▷g′) → (α▷g);(f′◁β)} is an operation-case 3-cell.
- The reverse fails, because the support of its source is ∂⁺U, not ∂⁻U.
- With β : F ⇒ G a transformation and α an arrow of an object (an element 2-cell), this is β's lax naturality cell at α. With α = β of a cone morphism and β = a cone cell, it is the comparison cell Mikhail's universal cone needs (§3.1).

**The Gray cube.** Take Γ = ΣD¹ ∨ ΣD¹ ∨ ΣD¹. Then U is the 3-cube, and its top generator is a 4-cell of 𝒦 between the two hexagonal composites of interchangers.

- Each hexagon is a vertical composite of whiskered interchangers, plus associators to match bracketings. Each interchanger is a coh over a sub-wedge with one point factor (e.g. ΣD¹ ∨ ΣD¹ ∨ ΣD⁰), substituted. So **the source and target are ordinary terms over pasting schemes.**
- *Checked in Agda* (`src/CaTTExp/Gray/Cube.agda`). The ∂⁻ hexagon uses faces fβγ, αg′γ, αβh; the ∂⁺ hexagon uses αβh′, αgγ, f′βγ. hex⁻ ⇛ hex⁺ is accepted as one operation-case coh, and the reverse coh's side condition is false.
- No coh over a non-pasting context is needed. The Gray molecules appear only in the side-condition computation.
- This corrects PR #3 §4.3's expectation that a Gray core forces "molecular coh" into the kernel.

**Inside a hom.** Take Γ = ΣΘ. Then U = Θ, and by the [conj] of §3.2 the rule is plain CaTT. Suspension maps L-terms to L-terms, since the image lands in the cartesian tier.

### 3.5 Which cells are invertible

| Cell | Invertible? | Why |
|---|---|---|
| Coherence case (supp t = supp u = U) | yes | The reversed coh satisfies the same condition; Benjamin–Markakis's argument goes through unchanged. |
| Anything inside a single hom | as in CaTT | §3.4, last case |
| Composites (operation case, n = 1) | no, as in CaTT | |
| Interchangers y ⊗ x with dim x, dim y ≥ 1 | **no** | The source and target supports are different halves of ∂U. |
| Interchanger where one factor is invertible | yes **[proved]** | Rule (INV-fac) of `invertibility-markings.md` §1.2, sound by Lemma 2.1 there (Dᵐ ⊗ Eᵏ ≃ Dᵐ ⊗ Dᵏ⁻¹). |
| Interchangers with a transformation marked *pseudo* (as the **later** factor; `invertibility-markings.md` §1.6c) | yes, by marking | A pseudo transformation is a 2-cell whose interchangers are all marked invertible. Modifications between pseudo transformations are *not* automatically pseudo (§2.4, verified counterexample), so higher cells carry their own marks. |

**Naturality cells at invertible 1-cells: the classical semantic fact [proved here for strict 2-categories].** (The type-theoretic rule is (INV-fac) above.) Let α : F ⇒ G be a lax transformation between 2-functors A → B, with cells α_f : Gf ∘ α_x ⇒ α_y ∘ Ff, and let f : x → y be an isomorphism in A with inverse g. Lax naturality says α_{gf} is the pasting (α_g · Ff) ∘ (Gg · α_f), and α_{1} = 1. Since gf = 1, this gives (α_g · Ff) ∘ (Gg · α_f) = 1. Whiskering by Gf on the left and using GfGg = 1: (Gf · α_g · Ff) ∘ α_f = 1. Symmetrically, fg = 1 gives (α_f · Fg) ∘ (Gf · α_g) = 1, and whiskering by Ff on the right: α_f ∘ (Gf · α_g · Ff) = 1. So β := Gf · α_g · Ff is a two-sided inverse of α_f. For an adjoint equivalence the same computation goes through with the unit and counit isomorphisms inserted, using naturality of α with respect to 2-cells. The (∞,2) statement is Haugseng's Remark 3.11. Lax transformations at equivalences are therefore pseudo there, consistent with (INV-fac).

### 3.6 Soundness: proof attempt

**Precise form of §3.2.** Fix a pasting scheme Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ with objects a₀, …, aₙ. Let **𝔉(Γ)** be the free strict Gray-enriched category on Γ: the free category enriched in (strict ω-Cat, ⊗_AM) on the chain of hom-generators ν(λΘ₁), …, ν(λΘₙ). Because the underlying graph is a chain, its homs are

```
𝔉(Γ)(aᵢ, aⱼ)  =  ν(λΘᵢ₊₁) ⊗ … ⊗ ν(λΘⱼ)  ≅  ν(Kᵢⱼ),      Kᵢⱼ := λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ
```

where λ is the Steiner complex of a pasting diagram, and the isomorphism is Ara–Maltsiniotis's ν(K ⊗ L) ≅ ν(K) ⊗ ν(L) for strong Steiner complexes **[paper: AM §A.16, with Prop. 4.13 for λ(S)]**.

- Every L-term t over Γ has a **strict interpretation** ⟦t⟧, a cell of some 𝔉(Γ)(aᵢ, aⱼ), defined by induction on derivations (coh cases below; substitutions act through the strict Gray functors they induce).
- **supp(t : A)** := Supp(⟦t⟧), the downward-closed set of basis elements of Kᵢⱼ used by ⟦t⟧ and its boundaries. Supports of objects are the objects themselves.
- The rule of §3.3 reads: operation case if supp(t) = Supp(∂⁻T) and supp(u) = Supp(∂⁺T); coherence case if supp(t) = supp(u) = all of Kᵢⱼ. Here T := ⟨Θᵢ₊₁⟩ ⊗ … ⊗ ⟨Θⱼ⟩ is the **total cell**, the Gray tensor of the composites of the pasting diagrams.
- Everything is computable: tables of finite chains, and chain maps for substitutions.

**Three combinatorial lemmas**, about any Steiner complex K, in particular Gray tensors of pasting diagrams. They are posed precisely, with proof sketches, in `notes/conjectures/steiner-support-determines-cells.md`. *Literature update (2026-11-18): (A)–(C) hold for Gray tensors of pasting diagrams. They follow from Hadzihasanovic (arXiv 2404.07273), Prop. 8.3.17 and Thm 11.2.18; see that file's "Literature status".*

- **(A) 0/1 chains.** Every chain in the table of a cell of ν(K) has coefficients in {0, 1}.
- **(B) Support determines the cell.** Two cells of ν(K) of the same dimension with the same support are equal.
- **(C) Support is functorial.** For a strict functor F : ν(K) → ν(L), Supp(Fx) = ⋃_{b ∈ Supp(x)} Supp(F⟨b⟩).

**Theorem 1 (two-tier L, strict model), assuming (A)–(C).**

1. *Soundness.* Every derivable term has a strict interpretation. So every strict Gray-enriched category models two-tier L, by mapping 𝔉(Γ) into it.
   - *Operation case.* ⟦t⟧ and ∂⁻T have the same dimension and the same support, so ⟦t⟧ = ∂⁻T by (B). Likewise ⟦u⟧ = ∂⁺T. Interpret the coh as T, which has the right source and target.
   - *Coherence case.* ⟦t⟧ and ⟦u⟧ have the same dimension and full support, so they are equal by (B). Interpret the coh as the identity on ⟦t⟧.
   - *Substitution.* ⟦coh[σ]⟧ is the image of ⟦coh⟧ under the strict functor that σ induces between free objects.
2. *Non-degeneracy.* The reverse interchanger is not derivable. Take Γ = ΣD¹ ∨ ΣD¹ and K₀₂ = λD¹ ⊗ λD¹. A 2-cell from the ∂⁺-path to the ∂⁻-path would need a top chain z with z + σ a 2-cycle. But K₀₂ has the homology of a point, and degree 2 is its top degree, so z = −σ, which is not a non-negative chain. Since every derivable term is interpreted, no derivable term has that type.
   - The same argument works for every interchanger y ⊗ x with dim x, dim y ≥ 1. So L does not collapse to P.
3. *Conservativity on one hom.* For Γ = ΣΘ, supp(t : A) = Var(t : A).
   - "⊆": ⟦t⟧ is built from the images of the variables of t.
   - "⊇": induction on t, using (C) and the fact that both coh cases interpret with full support of their own context.

   So on a single hom, the rule *is* Finster–Mimram's rule, and L restricted to one hom is CaTT. The existing Agda checker is that fragment.

**What is proved outright** (no lemma needed): the decidability of the side condition and substitution admissibility. Side conditions are checked only on the coh's own pasting-scheme context Γ, never on the context Δ substituted into, so substitution cannot invalidate them, exactly as in CaTT.

*Correction (2026-11-18, from the formalization):* an earlier version also listed the non-degeneracy argument in 2 as proved outright. Its chain computation needs no lemma, but its last step, "every derivable term is interpreted", is soundness (1), and that uses (B) in both coh cases. So 2 holds under the same hypotheses as 1. Since (A)–(C) are now known for Gray tensors of pasting diagrams (Literature update above), the conclusion stands. Without (B), what is proved is only that the reverse interchanger *coh* is underivable.

*Formalization status (`notes/agda-gray-findings.md`):*
- Machine-checked: decidability (by construction), substitution admissibility (`CaTTExp.Subst`, for every side condition), and that the reverse interchanger *coh* has no derivation.
- Machine-checked with one explicit hypothesis, (B) (a module parameter, not a postulate); (T) was a second one and is now a theorem (`Strict/Bridge.T-cell`, 2026-11-18): soundness (1) and non-degeneracy (2) for every *term*, in `src/CaTTExp/Strict/`. `Soundness.sound-tm` shows every derivable term over a pasting context is a cell of ν(K(Γ)); `ReverseInterchanger.no-reverse-interchanger` shows no term t at all has type (α▷g);(f′◁β) ⇛ (f◁β);(α▷g′). The hypotheses are (B), in the form "same dimension and same downward-closed support ⇒ equal cells", and (T) "the total cell T of a pasting context, as `chainT` computes it, is a cell". (B) is this file's lemma, proved for every Steiner complex in `conjectures/steiner-support-determines-cells.md`; (T) is Ara–Maltsiniotis's description of the Gray tensor's top cell, now proved in Agda (`Strict/Tensor`, `Strict/TotalCell`, `Strict/Pasting`, `Strict/Bridge`). (A) is not needed, because chains are kept as non-negative bags. (C) is not needed as a hypothesis: the substitution case is proved directly (`Strict/Subst.topS-sub`, `Strict/L.transport-σ`).
- Not yet formalized: the term-level half of conservativity (3), supp = Var for derivable terms. Its ⊇ step needs the invariant "a cell with empty top support has boundaries with equal closed supports", which soundness now makes available.
- Checked by evaluation: the rule-level half of (3), for all 196 pasting diagrams with ≤ 6 edges (`Gray/Bounded.agda`).

**Theorem 2 (two-tier L, (∞,ω) models), conditional.** Assume (A)–(C) and the following three statements, posed in `notes/conjectures/free-infinity-gray-of-pasting-diagrams.md`. *Literature update (2026-11-18): (D) and (E) are known (Campion, arXiv 2311.00205, Example 3.2 and Cor. 3.5; Chanavat, arXiv 2603.22242, Thm 3.29), and (F) follows. So the hypotheses (D)–(F) of Theorem 2 are discharged; see that file's "Literature status".*

- **(D)** For K = λΘ₁ ⊗ … ⊗ λΘₙ, the free (∞,n)-category on K's generators is equivalent to ν(K). This is Campion's pasting theorem, if K is torsion-free; Campion's theorem covers lax Gray cubes, and the question is whether it covers Gray tensors of pasting diagrams.
- **(E)** Campion's Gray tensor of the free (∞,n)-categories on λΘᵢ is the free one on their Steiner tensor.
- **(F)** The free oriented ∞-category on Γ has homs given by tensoring along the chain. This is the ∞-version of the formula for 𝔉(Γ). For V monoidal with ⊗ preserving colimits in each variable, the free V-∞-category on the chain graph 0 → 1 → … → n with edge objects V₁, …, Vₙ has maps from i−1 to j given by Vᵢ ⊗ … ⊗ Vⱼ **[paper: Gepner–Haugseng, [1312.3178](https://arxiv.org/abs/1312.3178), §2.5, stated in the discussion of the graphs Δ_(V₁,…,Vₙ)]**. Campion's Gray tensor is biclosed, so this applies with V = (Cat_ω, ⊗).

Then every oriented (∞,ω)-category (Gepner–Heine), in particular ∞Cat with lax transformations, interprets two-tier L:
- operation-case cohs go to lifts of T;
- coherence-case cohs go to the invertible cells that (D) provides between parallel cells with equal strict image.

*Caveat shared with CaTT.* Interpreting a dependent type theory in an (∞,ω)-category needs a strictification or coherent-choice argument. That gap is not specific to L: it is open for CaTT in (∞,ω)-categories too.

**Uniform L.** The theorem above cannot even be stated yet, because the strict structure 𝔉ᵤ(Γ) (lax interchange at every level) in which supports would be computed has not been constructed. That is the problem in `notes/conjectures/strict-lax-interchange-at-every-level.md`. Its requirements (support determines cells; reverse interchange uninhabited; substitution) are exactly what the proof of Theorem 1 uses. So a solution should give Theorem 1 for uniform L by the same argument.

**Every model of two-tier L is a model of uniform L [conj].** The uniform side condition is meant to be stricter: a uniform-admissible pair should stay admissible after collapsing the inner interchanges. Once 𝔉ᵤ is defined, this becomes a checkable statement about its collapse map to 𝔉. If it holds, Theorem 2 already shows that ∞Cat with lax transformations models uniform L.

---

## 4. How each option handles the main constructions

### 4.1 Lax and pseudo transformations

| | P | L |
|---|---|---|
| Lax transformation F ⇒ G : B → C | a 1-cell B → [⟦D¹⟧, C]ₗₐₓ over (F, G): an element of a pullback (PR #2 §6.3, PR #3 §5.2) | a native 2-cell |
| Pseudo transformation | a native 2-cell | a native 2-cell with marked (invertible) interchangers |
| Naturality "via coherence" (the post's §Functors) | pseudo naturality | **lax naturality** (§3.4) |
| Composing transformations across objects | maps [C,D]ₗₐₓ ⊗ [B,C]ₗₐₓ → [B,D]ₗₐₓ out of a Gray tensor of objects, or curried. The coherence laws come from universal-property (uni) rules, not from coh. | coh |
| Vertical composition | coh in [⟦D¹⟧, C]ₗₐₓ restricted along cohs (PR #3 §5.3) | coh |

**Why P cannot use the cartesian product here.** A map [C,D]ₗₐₓ × [B,C]ₗₐₓ → [B,D]ₗₐₓ would force (β,1)∘(1,α) = (1,α)∘(β,1) to map to isomorphic composites, i.e. an invertible interchanger. So under P the composition of lax transformations needs the Gray tensor *of objects*, or its curried form. Either way it is a new rule family whose coherences do not come from coh.

### 4.2 Gray shapes and lax homs

- **P.** [Θ, C]ₗₐₓ needs Γ ⊗ Δ as a *context former* (PR #3 §4–5.1). Its generators x⊗y must be typed by composites of molecules such as hexagons, and those composites must have syntactically matching boundaries (condition G1). Two routes are proposed:
  - layering with associator bookkeeping, which pushes CaTT_sua early;
  - molecular coh justified by Campion.

  Both are open.
- **L.** A lax square in C is the interchanger of a native 2-cell α : u ⇒ v (with u, v : ⟦D¹⟧ → C) with the generic arrow of ⟦D¹⟧, read in 𝒦(⊤, C) ≃ C. More generally, **[conj]** Δ ⊗ Θ-shaped diagrams in C are Δ-shaped families of cells of the native hom 𝒦(⟦Θ⟧, C).
  - So [⟦Θ⟧, C]ₗₐₓ is the native hom made into an object, by the same Σ ⊣ Hom-style rule PR #3 §5.4 proposes for P's pseudo hom.
  - Gray contexts become *derived* notation, and G1 disappears.
  - The Gray tensor still appears, but only as an algorithm on chain complexes inside the side condition, which is standard Steiner theory.

This is the largest concrete simplification L offers. It is also the place where the earlier threads underestimated L.

*Correction (2026-11-18, `invertibility-markings.md` §4.3).* "G1 disappears" holds for *using* lax cells (their Gray-shaped components are derivable L-terms), not for *introducing* a lax cell from component data, which still needs a Gray-shaped context with syntactically matching boundaries. That residue is Conjecture CT, `conjectures/canonical-gray-terms.md`.

### 4.3 Internal homs

| | P | L |
|---|---|---|
| Native hom made an object | [B, C]: pseudo (PR #3 §5.4) | [B, C]: lax, by the same rule |
| Currying | Hom(A, [B,C]) ≅ Hom(A × B, C), using × from finite limits: all finitary | Hom(A, [B,C]) ≅ Hom(A ⊗ B, C). Needs a Gray tensor of *objects* A ⊗ B, given by a mapping-out rule (adjunction-style β/η). This is finitary as a rule, but it is a new object former. |
| The other hom | [B, C]ₗₐₓ for all B needs Gray tensors of objects as well (§4.1) | [B, C]_pseudo = the sub-hom with marked naturality. Cartesian currying via × from limits. |

So each option makes one hom native and gets the other from an extra rule family. The difference is which one CaTT's coh handles for free.

### 4.4 Limits (CaTT_lim)

- **P.** Mikhail's cone shapes apply as published ([2412.13310](https://arxiv.org/abs/2412.13310)). Lax cones have non-invertible ambient 2-cells p_f, so they are lax limits in ωCat_pseudo. Transfors between cones are Gray-shaped *contexts* (`ctrf`), whose existence is proved only for n = 1.
- **Verified (R11).** As written, Mikhail's universal property forces cone-morphism cells to be invertible in a CaTT ambient, and all cells of dimension ≥ 3 once every level of `uni` is imposed. So P must use marked (pseudo) cone transfors, and hom and comma objects from limits have only invertible arrows.
- **L.** The cone *shapes* are the same: a cone over Γ is the same context. The universal property becomes a Gray-enriched one, quantifying over native lax cells.
  - **[conj]** The `ctrf` shapes (transfors between cones) become native cells of the hom 𝒦(c, ·), so the `ctrf`/`star` machinery may shrink. A cone transfor would be a native cell between cones, with interchangers supplying the Gray squares.
  - *Update (2026-11-18, `limits-metatheory.md` §1, §5):* semantically yes. In strict ωCat with the Gray tensor, n-transfors are exactly n-cells of 𝒦(c, lim) (Theorem A). Syntactically, `star`/`ctrf` shrink to one horn context and one `uni`, shared with P. L needs only operation-case cohs over two-factor wedges `ΣDᵃ ∨ ΣDᵇ`.
  - In dimension 2, lax limits are special Cat-weighted limits, which are standard (Street 1976, Kelly 1989; surveyed in Lack, *A 2-categories companion*, [math/0702535](https://arxiv.org/abs/math/0702535), §§6.7–6.8) **[paper: Lack]**. *Correction:* an earlier version said "Gray-enriched weighted limits"; the dimension-2 theory is Cat-enriched, and Gray-enrichment only enters one dimension up.
  - Gepner–Heine's oriented colimits are the matching (∞,ω) notion. PR #2 §2.4 already suspects CaTT_lim's limits are "oriented" in their sense. Under L that becomes the expected reading rather than a mismatch.
- **Markings** (PR #2 §4.2) are needed by both.

### 4.5 Free objects and representables

- **Both.** PR #1's construction (initial object plus one-generator cell attachment) and PR #2's R-B (⟦Γ⟧ := lax colimit of const ⊤) are colimits and work in either ambient.
- **What changes is what Hom(⟦Γ⟧, C) means.**
  - Under P it is pseudo transformations of Γ-diagrams.
  - Under L it is lax ones, which matches Johnson-Freyd–Scheimbauer's lax transformations between diagrams and the "lax by default" decision.
- **Elements** (PR #2 §5.1, PR #4 finding 3): 𝒦(⊤, C) ≃ C holds in both, since 1 ⊗ X ≅ X ≅ 1 × X. Under L, the functor action is whiskering as before, but **the naturality square of α at an element arrow f is a directed interchanger**. The post's elementwise style then yields lax naturality, which is what Anthony's 2026-11-17 answers asked for.

### 4.6 The ω-category of ω-categories itself

- **P.** The ambient is Cat_ω with pseudo transformations, a (large) ω-category, cartesian closed.
  - Lax data is present as objects [B, C]ₗₐₓ and maps between them.
  - The Gray-enriched structure of ωCat_lax is *constructed*: composition maps out of Gray tensors of objects, plus their coherences via uni-style rules.
  - **Users who want to reason in ωCat_lax do so through universal maps, not through coh.**
- **L.** The ambient *is* ωCat_lax, an oriented category. Its compositions and their coherences are CaTT-style cohs. ωCat_pseudo is the marked sub-structure.

### 4.7 Universes (not on the current plan, but they affect the long term)

- **P.** A universe U : ⋆ of small ω-categories is an ω-category whose cells are functors and pseudo transformations. That is the same *kind* as the ambient, so "ωCat : ωCat" is at least kind-correct (modulo size).
- **L.** Objects are ω-categories, but ωCat_lax is an oriented category, not an ω-category. So a universe *object* can only be the pseudo one.
  - Elementwise reasoning inside U would give pseudo naturality while the ambient gives lax: a mismatch.
  - A lax universe would need objects that are themselves oriented categories. That is the uniform/bioriented frontier of §2.3.

PR #1 recommends no universe for now, so this is a long-term cost of two-tier L, not a near-term one. **Uniform L removes it** (§2.5), because its objects may be oriented categories themselves.

---

## 5. Decidability, cost, usability

### 5.1 Decidability

- **P.** Plain CaTT is decidable: the pasting-scheme check is linear and the Var checks are set computations. The CaTT_lim side conditions are syntactic too.
- **L.** Still decidable.
  - Supports are computed in the strict Gray model through Steiner chains, i.e. integer linear algebra.
  - Gray unfoldings of pasting schemes are generated, never recognised, so no molecule recognition is needed.
  - The rule never asks for coh over a molecule (§3.4).

### 5.2 Cost

- U for a row of n horizontally composable 2-cells is the n-cube, with 3ⁿ cells. Computed naively, supports blow up exponentially in the *horizontal width* of a pasting scheme.
- ~~Computed symbolically … the cost should be polynomial in term size **[conj]**.~~ *Corrected (2026-11-18):* false for explicit supports, since the coh over n side-by-side 2-cells is a term of size O(n) with support of size 3ⁿ. The restated question (polynomial in shared term size) is E9′ in `invertibility-markings.md` §5.
- In practice horizontal width is small. Plain CaTT has no such cost.

### 5.3 Usability

- **L: no canonical horizontal composite.** A user composing transformations across objects must pick a whiskering order. Laws relating the two orders are directed interchangers, the bookkeeping familiar from Gray categories.
  - This is intrinsic to lax transformations: P's users meet it too, the moment they use lax transformations, and there coh does not help them.
  - L's users meet it even for pseudo transformations, unless they mark them.
  - Mitigation: surface syntax with a default layering, plus automatic invertibility propagation from markings.
- **L: interchangers in low-dimensional math.** For "ordinary math" objects (1-category-like, groupoid-like), interchangers are *semantically* invertible, but L only knows that from markings. A property like "C has only invertible 2-cells" would need to propagate to interchangers with cells into C. Neither option has such a property-propagation rule yet. Under P the question never arises.
- **P: two kinds of cell for one concept.** P's users handle lax transformations as 1-cells into [⟦D¹⟧, C]ₗₐₓ, a different kind of thing from the ambient's 2-cells. Laws for them come from universal properties, and coh does not apply to the outer level. This is a large ergonomic cost if lax transformations are common, and "lax by default" says they are.

### 5.4 Metatheory and semantics

| | P | L |
|---|---|---|
| Models | GM/BFM weak ω-categories; computads (Dean–Finster–Markakis–Reutter–Vicary); Benjamin–Markakis–Sarti contexts-as-computads | to build: "Gray-coherator" models. Target notion exists (Gepner–Heine). Markakis's generalised signatures ([2303.11978](https://arxiv.org/abs/2303.11978): sorts form a direct category; free algebras on computads are the cofibrant objects) may cover the computads **[conj; see `semantics-gaps.md` §5]**. |
| Strict test model | strict ω-Cat with the cartesian hom (strictly natural transformations) | strict ω-Cat with the AM Gray tensor. This model is exactly the one used to compute supports, so the side condition and the test model coincide. |
| Is ωCat itself a model? | strictly, only with strict 2-cells; (∞,ω) open (algebraic weak ω-cats vs (∞,ω)) | strictly yes: AM's ∞-Cat_lax, by Theorem 1 of §3.6; (∞,ω) open, same gap. Details in `semantics-gaps.md` §4 |
| Invertibility, Σ, opposites, naturality meta-operations | done | to redo. Σ is admissible (§3.4). Some opposites swap lax and oplax instead of being symmetries (see R5). The naturality meta-operation (BMOSV) becomes the interchange coh. |
| Biggest open lemma | G1 for Gray contexts (PR #3 §4.3). "Pseudo = marked Gray" is now proved (§2.4). | Steiner lemmas (A)–(C) and the (∞,ω) transfer (D)–(F), §3.6 |

---

## 6. Side-by-side

| | **P: pseudo ambient** | **L: two-tier Gray-CaTT** | **L: uniform** |
|---|---|---|---|
| Internal language of | Cat_ω with pseudo transformations | ωCat_lax, an oriented category (Gepner–Heine) | structures with directed interchange at every level; ωCat_lax is one model |
| Core rule | CaTT, unchanged | CaTT syntax; side conditions on Gray supports | same, with the unfolding applied recursively |
| Lax transformations | constructed (cotensor + pullback) | native | native |
| Pseudo transformations | native | lax + marking | lax + marking |
| Inside one object | plain CaTT | plain CaTT | directed, unless C is marked as an ordinary ω-category |
| Generality | strongest theory | P + nothing; P = it + marking **[conj]** | weakest; both others = it + marking **[conj]** |
| Gray tensor of contexts | primitive context former (G1 open) | algorithm inside the side condition. Gray diagrams are derived **[conj]**. | same |
| Coherence of lax composition | via universal-property rules | via coh | via coh |
| Horizontal composite | canonical | chosen across objects; laws are directed | chosen everywhere unless marked |
| Internal hom with cartesian currying | yes (pseudo) | yes for the marked pseudo hom | yes for the marked pseudo hom |
| Internal hom, lax | needs Gray tensor of objects | native; currying needs Gray tensor of objects | same |
| Limits | CaTT_lim restricted to pseudo cone transfors (marked declarations); hom objects need Gray tensors (R11) | unrestricted lax CaTT_lim over L's base, with the interchange orientation fixed by the cones (R11) | same, with uniform Gray shapes for higher transfors |
| Free objects, elements | yes | yes; naturality comes out lax | yes |
| Future universe | kind-correct (pseudo) | pseudo only (mismatch) | kind-correct (lax) |
| Established semantics | (∞,ω)-categories | oriented categories | none of its own yet; frontier (bioriented) |
| Decidable | yes | yes; cost grows with horizontal width | yes; cost grows at every level |
| Central open problems | G1 | (A)–(C), (D)–(F) | the same, plus constructing the free structure with lax interchange at every level |

---

## 7. Recommendation

**Revised recommendation: uniform L as the kernel**, with two markings:
- "C is an ordinary ω-category": interchange inside C is invertible;
- "this transformation is pseudo".

Two-tier L and P are then fragments obtained by marking. The working rule is "steer toward the most general version until there is a concrete reason otherwise", and §2.5 found no decisive reason against uniform L. The one reason found against going further, dropping interchangers altogether, is concrete: it loses naturality cells that every lax transformation has.

**How the open problems are handled.** Following the project standard, an unproved step is investigated, not used as a reason to stop short or fall back. The three open problems of §3.6 are worked on in parallel:
- the Steiner lemmas (A)–(C);
- the (∞,ω) transfer (D)–(F);
- the construction of the free strict structure with directed interchange at every level.

The implementation work (§7.1) proceeds at the same time. A refutation would change the plan. An open problem does not.

The reasons for L over P (first version, still valid):

1. **It is the internal language of the stated target.** "Internal language for the ω-category of ω-categories" with lax transformations names an oriented category, not an ω-category. Under P the target is a derived structure whose coherences coh never sees. With redoing results set aside as a cost, P's remaining advantage is mostly that it works in a different, easier ambient.
2. **It removes P's hardest open item rather than adding one.** P needs Gray contexts as a primitive, with G1 open. L gets lax squares, cubes and lax homs from native interchangers, and keeps the Gray tensor as a chain-complex computation in the side condition.
3. **It is weaker and more general.** Every CaTT model is an L-model, and P is (conjecturally) L plus one marking. So L does not foreclose anything P offers. Choosing P forecloses the lax ambient.
4. **The target and the test are concrete.**
   - The semantics is Gray-enriched (∞,ω)-categories (Campion's monoidal structure; Gepner–Heine's oriented categories).
   - The strict AM model is exactly what the side condition computes in, so every rule can be tested mechanically against it.

*The first version advised against uniform L because "it describes something other than ωCat_lax". Under the generality principle that is not a reason: ωCat_lax remains a model. The dimension-4 literature (Crans; Bourke–Lobbia) is a risk for its semantics (§2.5), not a refutation.*

**Open problems** (none of them is a reason to delay):
- the lemmas and constructions of §3.6, now posed in `notes/conjectures/`;
- the usability of directed horizontal composition, which will show up in practice in the §7.1 experiments;
- the universe question (§4.7), which uniform L addresses once its free structure exists.

### 7.1 Work plan

1. **Fix conventions.** *Done (2026-11-18): `conventions.md`.* Choose lax vs oplax, i.e. the factor order in U, once, consistently with Mikhail and with PR #3 §4.1.
2. **Supports and conservativity (Agda).**
   - Implement Steiner chains for pasting schemes and the Gray unfolding.
   - Prove that on a single hom, supp = Var. Then L restricted to one hom *is* the existing PR #4 checker.
3. **Two-object cases.**
   - Check §3.4 mechanically: D²∨D² (interchanger accepted one way, rejected the other); D¹∨D² (whiskering); D²∨D²∨D² (the cube's 4-cell typed from ps-terms only).
   - Validate against the strict AM model.
4. **Invertibility markings.** Port ICaTT's judgment, add the interchange propagation rule, and state "pseudo transformation".
5. **The §3.6 problems,** in parallel: lemmas (A)–(C), the (∞,ω) transfer (D)–(F), and the uniform construction. Each is posed in `notes/conjectures/` for external analysis, and attempted internally as well.
6. **Representables and lax homs.** Restate PR #2's R-B and PR #3's §5.4 hom rule over L. Check the [conj] in §4.2 that Gray-shaped diagrams are derivable.
7. **Uniform L,** in parallel with steps 2–6.
   - Use the construction of the free structure with lax interchange at every level (§2.5) as it develops, and add the "ordinary ω-category" marking.
   - Re-run steps 2–3 for the case Σ(D¹ ∨ D¹) *inside* an object, i.e. directed Eckmann–Hilton-type interchange.
   - Check that marking an object restores exactly plain CaTT inside it.

**If something is refuted.**
- A counterexample to (B) would mean the support rule has to be refined, e.g. to compare chains instead of supports, which is still decidable. The worked cases of §3.4 do not change.
- A refutation of (D)/(E) would mean (∞,ω) models need a different rule, while the strict theory stands.
- A negative answer to the uniform construction problem, i.e. a proof that no free structure with properties 1–3 exists, would be a genuine reason to stop at two-tier. The one no-go proved so far (2026-11-18) is for raw higher interchange cells, which uniform L does not need; it is not such a negative answer.

Each of these is a finding to act on. An open status is not.

---

## 8. Questions for Anthony

1. *(Answered 2026-11-18: "lax by default" means the most general version until there is a concrete reason otherwise. This note now recommends uniform L, reached through two-tier L.)*
2. **Marking ergonomics.** Under uniform L, plain CaTT reasoning inside an object needs the "ordinary ω-category" marking. Should objects be unmarked by default (most general), with the marking opt-in, as recommended here? Or should the surface syntax assume the marking unless told otherwise?
3. **Horizontal composition.** Is it acceptable that composing transformations across objects has no canonical result, with a surface-syntax default layering, or should the surface hide interchangers more aggressively?
