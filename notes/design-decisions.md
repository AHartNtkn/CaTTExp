# Design decisions: the lax side-condition theory and context checking

*Owner: thread "Choose lax core and context-check designs" (DSGN). Written 2026-11-20. Ledger rows E12, B25 and (§3) D7.*

## 0. How these choices are made

These two questions stopped being research questions when the latest answers came back:
- lax interchange: there is no initial theory over P, not even a weakly initial one, and there are infinitely many independent laws (r7, (K54)–(K57));
- context checking: homotopicality of finite polygraphs is undecidable, co-r.e.-complete already on positive 3-polygraphs (HPOL r4).

Neither result picks a design, so the choice is made here, under the project standards:
- every coherent option is described, with worked examples of what it derives and what it rules out;
- the options are compared on decidability of type checking, the CaTT rule aesthetic, no universes and no definitional equalities;
- proved facts decide. Where they leave a tie, the most general option wins (standard 4).
- A claim that is still open is not held against the option that needs it. It gets a proof attempt here, and an outbox question if the attempt stalls.

Each decision ends with what would overturn it.

---

## 1. Lax interchange: which theory the side condition computes in

### 1.1 What the choice actually changes in a CaTT-style kernel

Uniform L keeps CaTT's syntax and changes only the side condition of `coh`. Whether `coh(Γ, u → v)` is derivable over a pasting context Γ is read off the free object F_T(Γ) of a fixed strict theory T (`pseudo-vs-gray.md` §2.5, §7). So:
- **a law of T is never a definitional equality.** If T proves ⟦u⟧ = ⟦v⟧, the kernel gets coherences u → v and v → u, which are cells like any others. Every option below satisfies constraint 5 in the same way.
- **The rule's form does not depend on T.** Only the oracle behind the side condition changes. Every option has the same rule classes as published CaTT variants.
- **Generality is set inclusion.** If T interprets into T′ fixing P, every judgement derivable over T is derivable over T′. Fewer derivable coherences means more models.

### 1.2 Facts that constrain the choice (all proved, see `open-issues.md` E6)

- (K47)–(K50): T₁₂ satisfies requirements 1–5 in every dimension with H ≠ 1. (K52): normal forms in every degree; equality and reachability on F_T₁₂(Γ) are decidable.
- (K44), (K51): the **inner composite-crossing law** (direct crossing of A₁ ∗ A₂ past B = paste of the two crossings) is optional. A tagged model separates the two sides, and the joint theory without the law still satisfies 1–5.
- (K55): on the T₁₂ signature the **right split R** and the **prime left splits L_p** are independent of each other and of T₁₂'s other laws. Any selection of them can be omitted by taking the common laws of T₁₂ and the separating tables (r7 Response 2, "Take the common theory of the primary T coordinate and the tests for just the laws one wants to fail"). (K56): the divisibility laws D_{d,p} give a further infinite family.
- (K54), (K57): no initial and no weakly initial theory exists. In particular, no single theory is sound for every admissible theory's models. Generality can also be inflated without content: duplicating T₁₂'s upper operations gives an admissible theory with an involution (K54).

### 1.3 The options

**L1. Fix T₁₂.** The side condition is reachability in F_T₁₂(Γ).
- Derives: every coherence that T₁₂'s laws give. That includes an invertible cell between the direct inner crossing of a composite and the composite of crossings, and all the splits.
- Rules out: every model in which an inner crossing of a composite differs from the paste of crossings: the tagged model of (K44), the tables M_q of (K55), and U_N of (K56).
- Decidable: yes, by (K50) and (K52).

**L2. Fix the most general known theory J, with the catalogued laws as switches.** J is the common theory of T₁₂ and the separating algebras for each catalogued law:
- the tagged model of (K44)/(K51), which fails the inner composite-crossing law;
- the marked algebra of (K51), which fails R;
- the cyclic marked tables M_q for every prime q, which fail every L_p.

J(S) is J with the laws in S switched back on, which means dropping their separating algebras. J(all) = T₁₂.
- Derives: what holds in every one of these models, which is everything T₁₂ derives except the catalogued laws and their consequences.
- Rules out: nothing that L1 allows. Every T₁₂ model is a J model.
- Decidable: yes (Lemma J-dec, §1.5).
- Developments import upwards: a J(S) development is valid in J(S′) for S ⊆ S′, because the identity-on-letters quotient sends steps to steps (argued in prose) and the abstract lemma that such a map sends paths to paths is machine-checked (`Join/BoundedReach.agda`, `Transport.transport`).

**L3. J plus laws as hypotheses.** Keep J's side condition, and let the user declare a catalogued law as a signature cell over its generic context, marked invertible. All its instances then follow by substitution.
- Derives: the law itself, but not its higher coherences. The side condition does not see a declared cell, so two different uses of it are not related by any coherence.
- Decidable: yes. The cost falls on the user (example (c) below).

**L4. The theory-independent kernel E.** A coherence is derivable iff its type is inhabited in **every** admissible theory.
- Derives: only what all admissible theories share, so it is sound in all of their models. That is the strongest possible reading of "most general".
- Status: nobody knows whether E is the side condition of any admissible theory, or whether it is decidable. (K57) shows that E is not the image of any single weakly initial theory. It does not show that E fails requirement 3 or 4.

### 1.4 Worked examples

(a) **The strip C_{2,1}.** Inside a hom, take two composable inner cells A₁, A₂ and a cell B in interchange position. Let u = ι(A₁ ∗ A₂, B) be the direct inner crossing and v the paste of ι(A₁, B) and ι(A₂, B). Both have the same Gray image. *(Corrected 2026-11-21: this used to write W. The outer W-strip on C_{2,1}, a degree-5 lift, is a different pair. It stays distinct and unconnected after localization in every setting, including with both switches: ledger E13.)*
- L1: ⟦u⟧ = ⟦v⟧, so `coh` gives an invertible cell u ≅ v.
- L2 (law off): u and v are distinct cells with no cell between them. In the tagged model they really differ.
- L2 with the inner law switched on: same as L1.
- L3: the user declares κ : u ≅ v once, over C_{2,1}.
- L4: unknown. It depends on whether every admissible theory relates u and v by some cell, and (K57)'s U_m suggests that not all do.

(b) **A loop.** In a context with an inner endomorphism A and an adjacent B, compare W(A ∗ A, B) with W(A, B) pasted with W(A, B). Over a pasting context these terms arise only by substituting A₁, A₂ := A into example (a). So in every kernel above, L₂ for this A is decided by the strip law. The independent prime laws only become visible as separate kernel choices if F_T(Γ) of some *pasting* Γ contains an inner endomorphism they act on. F_T₁₂(Γ_{2,2r}) does contain loops (the powers of H, (K45)), so this is possible. Whether it happens is open question Q-vis (§1.6).

(c) **Three-fold composite, L3's cost.** With a declared κ, the crossing of A₁ ∗ A₂ ∗ A₃ past B can be split into single crossings in two ways (κ on the left pair first, or on the right pair first). Under L1 both routes are equal cells, so `coh` relates them. Under L3 the side condition does not know κ, so the two composites of κ instances are unrelated until the user declares a 6-cell, then a 7-cell for the next coherence, and so on. L3 cannot replace switching the law on in the side condition.

(d) **Reductions.** In every option, making inner interchangers identities gives two-tier L, and making all of them identities gives CaTT (requirement 4 for J(S) is part of the r7 Response 2 construction). So markings like `ord` behave the same under every option.

### 1.5 Lemma J-dec (decidability of every switch setting)

**Lemma.** For every finite pasting diagram Γ and every switch set S (finite, or the full prime family), reachability between two cells of F_{J(S)}(Γ) is decidable.

*Proof.*
1. Equality is decidable. A cell of F_{J(S)}(Γ) is a generated tuple (Response 2): a T₁₂ coordinate, which is decidable by (K52), plus the values in the separating algebras. The tagged and marked algebras are finite in each degree. For the whole prime family, Response 2 reduces equality of two given terms to finitely many exceptional primes plus one common answer, a finite linear-algebra computation.
2. Paths have bounded length. J(S) has the T₁₂ signature and a subset of T₁₂'s equations. So the projection to T₁₂ sends a J(S)-path to a T₁₂-path with the same letters, and the positive grading of (K45)/(K50) bounds its length by the gradings of the endpoints.
3. Steps are finite. At fixed boundaries the contextual alphabet is finite (K50).
4. Steps 1–3 make reachability decidable. This abstract step is machine-checked in `src/CaTTExp/Join/BoundedReach.agda` (`Reach.Bounded.reach?`, no postulates). ∎

*Correction 2026-11-21 (ledger S14).* Step 2 is false in general. The gradings are conserved along paths but do not bound their length: some free objects have loops, such as the loop H of V at degree 4 on Γ_{2,2} (pairwise distinct powers), and a positional self-loop at degree 5 on the 2 × 2 grid in T₁₂ (`notes/uniform-checker.md` §1.1, PR #380). The conclusion stands by another route. At fixed faces and weight the vertex set is finite (K58), and reachability in a finite closed universe is decidable with no length bound (r10 Response 3; `Uniform/FiniteGraph.agda`). The same correction applies to step 1 of Lemma V-dec below.

The cyclic tables for composite N (needed to switch off the D_{d,p} with p | d) need the same linear algebra over ℤ/N. That step is not written out, so those switches are not in the default J yet (§1.6).

### 1.6 Decision (superseded 2026-11-20 by §1.7)

**Original decision: the kernel's side condition computes in J (L2). Each catalogued law is a per-development switch, and T₁₂ is the setting with every switch on.**

Reasons:
1. **L2 against L1.** Both satisfy requirements 1–5, both are decidable, and both have the same rule form. J is strictly more general: the tagged model and the M_q are J models but not T₁₂ models. Standard 4 then picks J unless there is a concrete reason to specialize. No derivation is known yet that needs a catalogued law. The switches keep T₁₂ one setting away, and imports run upwards.
2. **L2 against L3.** Hypotheses do not reach the side condition, so a declared law brings an unbounded tower of coherence declarations (example (c)). Switches put the law into the oracle, where all its coherences come for free.
3. **L2 against L4.** L4 is the right target if it exists, but its admissibility and decidability are unknown. Per standard 1, that is a question to ask, not a reason to drop it: it is now the main question of `conjectures/outbox/lax-interchange-every-dimension-r8.md` (answered 2026-11-20, `conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`: on pasting diagrams a least admissible theory V exists and is decidable; see its Verification section). If it has a positive answer with a decidable side condition, it replaces J.
4. **Stability.** A newly discovered independent law joins the catalogue as a new switch. A development records its switch set, so later additions to the catalogue do not change what it checked against.

**What would overturn this.**
- A positive answer to the least-theory question in r8 (then use that theory).
- A proof that some catalogued law is needed for a core construction, such as cones over composites at inner levels or the directed Eckmann–Hilton of E7 (then that switch defaults to on, with the reason recorded here).
- A failure of the combined J construction under the in-house re-check (then fall back to the largest verified sub-selection).

**Open items (owner DSGN unless stated).**
- (J-chk) Re-check in-house that all separating algebras can be combined at once with exact quotients. Response 2 asserts this ("use (K51)'s argument with all the selected tests at once") and it was verified at construction level.
- (Q-vis) Which catalogued laws are visible on free objects of finite pasting diagrams? A law that is not visible does not change the kernel, so it need not be a switch.
- (ZN) Decidability for the composite-N tables (§1.5), then add the D_{d,p} switches to the default.
- Outbox: the least-theory question, merged into `outbox/lax-interchange-every-dimension-r8.md` as its main question (standard 11); answered 2026-11-20 (`answered/lax-interchange-every-dimension-r8-2026-11-20.md`), follow-up `answered/lax-interchange-every-dimension-r9-2026-11-20.md` (answered 2026-11-20), next follow-up `conjectures/answered/lax-interchange-every-dimension-r10-2026-11-20.md`.
- LCORE's uniform rule takes the switch set as a parameter (message sent to LCORE).

### 1.7 Revised decision (2026-11-20, after the r8 answers)

The r8 answers (`conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`, verified) meet overturn condition 1 in the form the kernel uses.
- **L4 exists.** Let B be the forced base and V = B + the round-5 guarded equations. Then V is admissible, F_V(Γ) = F_B(Γ), and F_V(Γ) maps generator-preservingly to F_E(Γ) for every admissible E. So on every finite pasting diagram, a directed cell or an equality exists in F_V(Γ) iff it exists in every admissible theory.
- **Q-vis.** The right split R and the inner composite-crossing law are visible on pasting diagrams. Every L_p and D_{d,p} is invisible, because every chronological 3-endomorphism in a free object on a pasting diagram is an identity.
- **Q1(a) is negative** (no least or minimal law set on arbitrary algebras). The kernel never sees those algebras, so this does not matter for the decision.

**Decision. The side condition computes in V. The switches are the visible laws: the inner composite-crossing law and R. A setting S means the side condition computes in V + S.** *(Superseded 2026-11-24 by §1.8: the switches became object marks.)*

Reasons:
- V is the most general possible choice, not just the most general known one. Every judgement it derives is derivable in every admissible theory, so a V development is sound in the models of every admissible theory. That is L4, and it removes reason 3 of §1.6.
- The catalogue shrinks to the visible laws. L_p and D_{d,p} do not change the kernel, so they are not switches, and (ZN) is moot.
- (J-chk) leaves the critical path, because J is no longer the default.
- L1 and L3 lose for the same reasons as before.

**Lemma V-dec.** For every finite pasting diagram Γ, equality and reachability in F_V(Γ) are decidable.

*Proof.* The proof follows Lemma J-dec.
1. V has the T₁₂ signature and a subset of T₁₂'s equations. So the identity on letters sends a V-path to a T₁₂-path with the same letters, and the positive gradings of (K45)/(K50) bound its length by the endpoint gradings.
2. At fixed boundaries the contextual alphabet is finite (K50).
3. Equality of two V-terms of the same weight is decidable. A derivation of the equality uses only defining pairs between terms of that same weight, since the gradings are conserved by every equation of V ⊆ T₁₂. So equality is connectivity in the finite graph whose vertices are the terms of that weight at those boundaries and whose edges are one-step applications of V's defining pairs. That graph is finite by step 2.
4. Steps 1–3 satisfy the hypotheses of `Reach.Bounded.reach?` (`src/CaTTExp/Join/BoundedReach.agda`), so reachability is decidable. ∎

*Correction 2026-11-21 (ledger S14).* Step 1's length bound fails where F_V(Γ) has loops, as in the loop H at degree 4 on Γ_{2,2}. Step 3 is unaffected, since it uses finiteness of the vertices of one weight, not path length. Reachability is decidable by breadth-first search over that finite vertex set (r10 Response 3; `Uniform/FiniteGraph.agda`), so the lemma stands.

**Switch settings V + S.** T₁₂ is admissible and contains both visible laws, so the all-on setting has T₁₂'s pasting profile. **Updated 2026-11-20 (r9 Responses 2–5, verified; K73 in `conjectures/answered/lax-interchange-every-dimension-r10-2026-11-20.md`):** every finite set of equations true in T₁₂ is admissible over V, so V + {R} and V + {inner law} are each admissible, and all four settings (none, R, inner law, both = T₁₂) are available. **Decidable (2026-11-20, r10 Response 3, verified):** equality and reachability in F_{V+S} are decidable for every S, in every dimension, uniformly in Γ, the degree and the switch bits, and the comparison maps F_{V+S}(Γ) → F_{V+S′}(Γ) are computable. Lemma V-dec therefore extends to every setting. Two caveats. First, r10 found that `SwitchLaws` enabled both binary splits under the inner-law bit, so the "inner law" and "both" settings had the same free tables. Corrected 2026-11-20 (LCORE): this was a modelling error in `SwitchLaws`. The inner composite-crossing law is the left split (§1.2: the direct crossing of A₁ ∗ A₂ past B is the paste of the two crossings), so the inner-law bit now enables only the left split, and R is the separate right-split bit. The four settings are distinct: on the suspended 2 × 3 interval, V, V + R, V + inner law and T₁₂ have 49, 14, 29 and 2 cells respectively (`scripts/e6/interchange_fibre_decorations.py`, which now selects the left split alone for the inner-law bit). r10 Response 3's algorithm covers the left split selected alone, as the response states. Second, the procedure is not polynomial on shared terms, and the problem is P-hard; polynomial time remains an implementation question under E12. Admissibility is not closed under unions in general and the pasting profiles are not a lattice, but neither caveat affects these two laws, which are both true in T₁₂. Imports still run upwards: F_V(Γ) maps generator-preservingly into F_T₁₂(Γ), and `Transport` applies.

**The degree-5 loop in T₁₂ does not contradict (K49) (settled 2026-11-21, ledger S14).** The S3 work found that on Σ(Σ[2] ∨ Σ[2]) with both splits on, the 4-paths X = χ(b₂a₁) χ(b₂a₂) χ(b₁a₁) χ(b₁a₂) and Y = χ(b₂a₁) χ(b₁a₁) χ(b₂a₂) χ(b₁a₂) are equal, both being the full crossing of b₁b₂ past a₁a₂ split in the two orders. So the positional square X ⇛ Y is a 5-loop (`Uniform/GridFiveExamples.agda`, `Square22.loop-T`). The question was whether this refutes (K49)/(K48) or whether T₁₂ lacks one of the splits. Neither.
- *T₁₂ has both splits.* r5 Response 34 ("the completed strong theory of Response 33 has the law") and r7 Response 2 ("T satisfies all of them by the two full split laws"). On a suspension the two splits are the suspended outer law (K15), which already makes the two expansions of w = χ(a₁a₂, b₁b₂) equal in T at degree 4. So the all-on setting is T₁₂'s pasting profile, as §2.3 of the spec says.
- *The loop is a whiskered square, not a (K49) rectangle.* (K49) is about the elementary four-input interchanger CDAB ⇒ CADB: there is a temporal cut of the source 3-word with the early inputs A, B on one side and the late inputs C, D on the other (r5 Response 11: "at both outside 3-boundaries all early events precede all late events"). Here the active inputs are χ(b₁a₁) and χ(b₂a₂). The source word is b₁b₂a₁a₂, and no prefix of it contains b₁ and a₁ without b₂. The outer moves χ(b₂a₁) and χ(b₁a₂) straddle the cut. So the loop is [χ(b₂a₁) | I₂(χ(b₁a₁), χ(b₂a₂)) | χ(b₁a₂)], the cut-3 whiskering of the bare square I₂ : χ(b₂a₂) χ(b₁a₁) ⇛ χ(b₁a₁) χ(b₂a₂) on b₁a₁b₂a₂ → a₁b₁a₂b₂. The bare square is directed in every setting: its two 4-paths are distinct, since no split merges crossings of different b's past different a's, and no positional square leaves a path whose left-window move is already first. This is the suspension of the loop H of (K34), which is likewise a whiskered binary interchanger in degree 4. Requirement 3 is about elementary interchangers, not their whiskerings (r6 §2 (K25), scope note: "the reverse of an inner interchanger after right whiskering by p … does not by itself contradict requirement 3"). r5 Response 14 already records the phenomenon: "an exchange can have a return in an arbitrary top context while every four-input rectangle in the theorem is directed."
- *Downstream.* Nothing changes. The four settings, their counts 49, 14, 29, 2 on the 2 × 3 interval, the admissibility of V + {R} and V + {inner law} (K73), and the breadth-first decision of S14 all stand. The only correction is wording: a loop at degree 5 must be described as a whiskered square. "A degree-5 rectangle with a reverse" would be a counterexample to (K49), and this is not one.

**What would overturn this.**
- A proof that a visible law is needed for a core construction. That law's setting then becomes the default for that construction's development.
- Answered: the intermediate settings V + {R} and V + {inner law} are admissible (K73).

**Open items.**
- (FV) An explicit description of F_V(Γ) and of what T₁₂ adds. **Answered 2026-11-20 by r9 (verified):** q : F_V(Γ) → F_T₁₂(Γ) is finite-to-one in every degree, and a V-cell is a T₁₂ normal word with decorated faces and a rank-selected word index (K65). Fibres are unbounded (2^{m−1} on suspended strips) but all those identifications come from R (K66). Visibility of pasting-diagram laws is decidable, so (Q-vis) is decidable for any proposed switch (K67). A closed-form description of the decorations is asked in r10 Q3.
- Whether F_J = F_V on pasting diagrams. This is now only of interest for comparison.
- Admissibility of V + R and of V + inner law separately. **Answered 2026-11-20 (K73): both admissible.** Uniform normal forms for V + S are asked in r10 Q2.
- LCORE: point the default setting at V (message sent).

### 1.8 Revised decision (2026-11-24): the two crossing laws are object marks, not a file setting (ledger S31)

**Decision.** There are no switch settings. The left split (inner composite-crossing law) and the right split R are **object marks**, `lsplit` and `rsplit`, written on object variables in the context like `iord` and `ord`. A coherence over a pasting context Δ with objects a₀, …, aₙ computes its side condition in V + S(Δ), where S(Δ) is the set of splits carried by every one of a₁, …, aₙ (`ord` carries both). With no marked object, that is V. A substitution may send an `lsplit` (`rsplit`) variable only to an `lsplit` (`rsplit`) or `ord` variable. (COH-ord) is unchanged. Spec §2.3 and §3.6 state the rule.

**Why the file setting goes.**
- *It chose a class of models.* §1.6–1.7 justified the switches by "some models with directed inner crossings satisfy these laws and some do not", and let a development declare which kind it was about. The project has no intended model and no mechanism for choosing a class of models (spec §0.1 after ledger S32). That justification is gone.
- *It was the only assumption outside the context.* Every other hypothesis a judgment uses (a mark, a declared variable) is in the context and is discharged by substitution. The setting was a per-file global, so the library split four ways with one-way imports, and nothing in a judgment showed which laws it used.
- *Under the generality ordering it only added cells.* V with no laws is the least admissible theory (§1.7). A setting S ≠ ∅ only adds derivable cells, everywhere in the file at once.

**Why the laws are not simply deleted.** A split is a property of particular objects: it says how crossings in the homs into one object behave. The kernel already states properties of this kind as object marks: `iord` (inner letters invertible) and `ord` (inner letters trivial). `ord` is strictly stronger than either split: both sides of each split are pure inner terms (below), so they are equal wherever inner letters are trivial. Deleting the splits but keeping `ord` would make the only way to use a split to assume much more. A concrete case is directed Eckmann–Hilton inside an object C (spec §3.6 Example (a)). With `(C : ⋆)^lsplit` and a `inv`, (INN-fac) makes EH₁ invertible. With no marks it is not invertible. With `ord` it is invertible, but `ord` assumes inner letters into C are trivial, and with (COH-ord) it also joins the loop H to 1_w and the outer W-strip (E13), which the split alone does not. A mark constrains only the objects it is placed on, so an unmarked object is still checked in V and no generality is lost.

**E12's original reasons, re-examined.**
- *The separating models* (the tagged model of (K44)/(K51), the marked algebras) show that each split is independent of V and of the other split. That makes each mark a non-redundant hypothesis. It does not say that the hypothesis belongs at file level.
- *The unbounded coherence tower* (§1.4(c)) is an argument against a law as a declared cell κ, which the side condition cannot see. A mark acts through the side condition, as (COH-ord) does, so every higher coherence of the law comes from the oracle. The argument therefore supports marks as much as it supported switches.

**What is lost and what is gained.** Nothing expressible before is lost: marking every object with S gives exactly the old setting S (`Uniform/SplitMarks.uniform-recovers`). What is gained is per-object precision. A development can assume the left split for one object and nothing for another, and a lemma proved over unmarked objects applies to marked ones by substitution, since stronger marks only enlarge S(Δ) (`meet-mono`, `invM-mono`).

**Check: both laws are pure-inner in every degree.** S31 asked for this first. In T₁₂'s signature the splits of an **outer** interchanger (along a 0-cell) are axioms of the base, (7) `χ-∘ˡ`, `χ-∘ʳ` in `Join/SepAlgebra.agda`, so they are already in V. The two visible laws are the splits of an interchanger along a k-cell with k ≥ 1. Each side is built from that interchanger, identities, composition and whiskering only. At degree 4 this is **Agda-checked** (`Join/SwitchLaws.law-inner`; `Uniform/SplitMarks.Degree4.law-trivial`: any predicate closed under those constructors holds of both sides). In higher degrees the law schema is the same at each level k ≥ 1, ι(F ⨾ F′, G) = paste of ι(F, G), ι(F′, G) and its mirror (`closed-structure.md` §D.4.3), with inner letters only, so the statement holds by the same induction (paper). Consequence: `ord` ⇒ `lsplit`, `rsplit`. Both sides of each law are parallel (they are the two sides of one equation of T₁₂), and in a model with trivial inner letters into C both are identities, so they are equal. The parallelism step is by the typing of T and is not mechanized.

**Soundness (paper).** Fix a model, an algebra of an admissible theory, and an assignment γ that respects marks: each γ(aᵢ) satisfies the splits marked on aᵢ in every hom 𝒦(X, γ(aᵢ)). Every hom of F(Δ) runs from some aᵢ to some aⱼ with j ≥ 1, so it lands in an object carrying every law of S(Δ) (`SplitMarks.meet-lb`). So γ sends each generating instance of the S(Δ) congruence to an equality, and the model's map out of F_V(Δ) factors through F_{V+S(Δ)}(Δ). The designated lift of an accepted coherence is interpreted through that factorization. This is the (COH-ord) argument with the S(Δ) congruence in place of "inner letters killed".

**Decidability.** S(Δ) is one of the four law sets, each decidable by r10 Response 3 (§1.7). Nothing new is needed.

**Duality.** D_all exchanges the left split and R (`closed-structure.md` §D.4.3), so on marks it exchanges `lsplit` and `rsplit`.

**Open (owner DSGN, folded into E15).** For a mixed head, the meet S(Δ) can be weaker than necessary. The left split could be imposed only on inner crossings landing in the objects that carry it, giving a theory between V + S(Δ) and V + (the union of the objects' splits). Whether that per-object quotient is admissible and decidable is the split-mark analogue of E15(a). The meet is sound and decidable now, so the rule does not wait on it.

**What would overturn this.** A construction whose correctness needs a split law to hold on an object that the construction itself introduces, not on an object variable of the context. A mark could not express that. None is known.

---

## 2. Context checking: homotopicality of bases

### 2.1 Where homotopicality entered

The weighted-limit line concluded that "the right hypothesis of the weighted-limit rule is homotopical (Free(Γ) ≃ F_n(Γ))" (`limits-metatheory.md` §9.3). The finite-presentation theorems for totals (B14: `conjectures/outbox/fibration-presentations-characterization-r4.md` items 3–5, 10, 12, 13, 16) assume a homotopical base. The evidence for the hypothesis was item 8: over the bubble σ : 1_x ⇒ 1_x the strict base is F(σ) = B²ℕ, which groupoidifies to K(ℤ,2), so even the terminal weight has no finite presentation.

### 2.2 Facts

- Bubble-free is necessary in every dimension (Theorem N). In dimension 2 it is also sufficient, but **bubble-freeness is itself undecidable for 2-polygraphs** (`answered/homotopy-polygraphs-2026-11-19.md` item 3). So "bubble-free 2-skeleton" is an exact criterion but not a decidable one.
- In dimension 3 bubble-freeness is not sufficient: the positive 3-polygraph A : α₀g ⇛ α₁g, B : gβ₀ ⇛ gβ₁ has a circle fibre.
- Homotopicality is co-r.e.-complete on positive 3-polygraphs (HPOL r4). So **no sound and complete r.e. certificate system for homotopicality exists**. Any witness system certifies a strictly smaller r.e. class, and no extension of it can close the gap.
- Decidable sufficient classes are known: pasting contexts and their Gray tensors; graphs (all 1-polygraphs, loops allowed); positive 2-polygraphs (Chanavat Cor. 3.39); the partition test; positive-to-one polygraphs and their duals; positive 3-polygraphs without matching idle overlaps (RC r6 Response 5); orientals of finite semisimplicial sets (Chanavat Thm 3.35); typing into a fixed finite catalogue of certified templates. All of these except the catalogue are closed under suspension.

### 2.3 The options

**C1. Pasting contexts only.** Decidable and homotopical.
- Rules out: equalizers (the parallel pair x ⇉ y is not a pasting context), pullbacks (the cospan x → z ← y), loops, and every 2-dimensional base that is not a pasting diagram. Too narrow for ordinary mathematics.

**C2. A fixed decidable class.** Take the union of the §2.2 classes.
- Derives: limits over graphs (equalizers, pullbacks, loops), over positive 2-computads such as μ : a·a ⇒ a, and over orientals.
- Rules out: correctly, the bubble and the RC r6 3-polygraph. Wrongly, every homotopical base outside the class. By the co-r.e.-completeness result, no decidable class can avoid this.
- Pitfall: an "exact" test such as bubble-freeness is undecidable in dimension 2 and unsound in dimension 3. The RC r6 polygraph is positive and bubble-free but not homotopical, so a bubble-freeness test would accept it.

**C3. Explicit witnesses.** An inductive judgement Γ ⊢hpol in the style of ⊢ps. Its base rules are the §2.2 classes and its closure rules are proved closure theorems: suspension; adjoining 1-generators in dimension 2; adjoining fresh globes along two vertices (fibration r2, vertex-attachment lemma).
- Checking is decidable when the derivation is given or syntax-directed. The rules fit the CaTT aesthetic.
- Necessarily incomplete (§2.2), but extensible as closure theorems arrive.

**C4. Read bases weakly, and check nothing.** A CaTT diagram over Γ is a context morphism out of Γ, which is a functor out of the free *weak* ω-category Free(Γ), never out of F(Γ). Interpret every base as Free(Γ). Homotopicality is then not a premise of any kernel rule.
- Derives: limits over every finite context, including the bubble and the RC r6 polygraph, with their weak meaning. Over a homotopical base this meaning agrees with the strict one.
- Rules out: nothing a CaTT diagram can express. A functor out of the strict F(σ) = B²ℕ is not expressible in CaTT anyway.
- Decidable: there is no check to decide. Weight presentations still carry their certificates (B14), and those are checked as before.
- Item 8 does not apply: over Free(σ) the total of the terminal weight is Free(σ) itself, presented by σ.

### 2.4 Worked examples

| Base | C1 | C2 | C3 | C4 |
|---|---|---|---|---|
| parallel pair x ⇉ y (equalizers) | rejected | accepted (graph) | accepted (graph axiom) | accepted; fast path |
| μ : a·a ⇒ a on a loop a | rejected | accepted (positive 2-polygraph) | accepted | accepted; fast path |
| bubble σ : 1_x ⇒ 1_x | rejected | rejected | rejected | accepted; weak meaning, over a resolution |
| RC r6: A : α₀g ⇛ α₁g, B : gβ₀ ⇛ gβ₁ | rejected | rejected by the no-matching test (the overlap on g matches); a bubble-freeness test would wrongly accept | rejected unless some closure rule covers it | accepted, over a resolution |
| HPOL r4 semi-Thue family G(T,w,v) | rejected | rejected | homotopical members are accepted only by a lucky closure derivation, and no r.e. system accepts all of them | accepted, over a resolution |

### 2.5 Proposition W (finite presentations over arbitrary bases)

C4 needs the B14 theorems for bases Free(Γ) with Γ arbitrary.

**Proposition W.** Let Γ be any finite n-polygraph, and T : Free(Γ) → ω a coherent weight with values Free(Π_b)[W_b⁻¹], dim Π_b ≤ m. Then ∫T has a finite marked presentation of dimension ≤ n + m.

*Proof attempt.*
1. **Resolution of the base.** Free(Γ) is an iterated homotopy pushout of globes along their boundaries. That holds by definition of Free, not by homotopicality. Run the bounded-model calculus of `answered/fibration-presentations-characterization-r2-2026-11-19.md` §2 on it: homotopy pushouts give dimension max{b, c, a+1}, and globe attachments keep dimension. This gives a finite complicial model K of dimension ≤ n. The conversion L_n (same answer, §2.3) gives a finite polygraph Γ′ that is **homotopical** (oriental of a semisimplicial set, Chanavat Thm 3.35), of dimension ≤ n, and a finite set W′ of its generators with Free(Γ′)[W′⁻¹] ≃ Free(Γ).
2. **Pull back and present.** Let ℓ : F(Γ′) → Free(Γ) be the localisation. Then T∘ℓ is a coherent weight over the homotopical base Γ′. Item 13 (the uniform presentation Ω) gives (Ω′, S′) with Free(Ω′)[S′⁻¹] ≃ ∫(T∘ℓ) and dim Ω′ ≤ n + m.
3. **Localise the total.** Let Ŵ be the cartesian-marked generators z_{w,x} of Ω′ for w ∈ W′ and x a source-fibre vertex. These are the lifts of W′. By Lemma Loc-total below, ∫T ≃ ∫(T∘ℓ)[Ŵ⁻¹] = Free(Ω′)[(S′ ∪ Ŵ)⁻¹]. Localising does not add generators, so the dimension stays ≤ n + m. ∎ (modulo Lemma Loc-total)

**Lemma Loc-total** (remaining step). For B an (∞,ω)-category, S a set of cells, ℓ : B → B[S⁻¹] and T : B[S⁻¹] → ω, the map ∫(T∘ℓ) → ∫T exhibits ∫T as the localisation of ∫(T∘ℓ) at the cartesian lifts of S.

*Attempt.*
- B[S⁻¹] is the pushout of B along marked trivialisations ∐ D_{k+1}^t → ∐ D_k^♭ (Loubaton Def. 3.2.1.6, Prop. 3.2.1.7; (Loc), `limits-metatheory.md` §9.2).
- Pullback along the left cartesian fibration ∫T → B[S⁻¹]^♯ preserves colimits (Loubaton Thm 3.2.3.15, as in item 3). This must be used in its marked form, for the marked trivialisation; that check in Loubaton is still to be done.
- So ∫T is the pushout of ∫(T∘ℓ) along the totals over the trivialisations, and it remains to show that the total over D_{k+1}^t → D_k^♭ is the localisation at the lifts of the top cell.
- Over a globe, the weight is determined by a k-cell of ω whose top part is invertible. Its total over D_{k+1} is a Gray cylinder on the fibre, and inverting the lifted top cell gives the total over D_k^♭ by item 2 (tensor-localisation). Item 2 is stated for X[S⁻¹] ⊗ I. The globe case needs it for D_k ⊗ fibre, which is the same lemma with the factors exchanged.

This last step was posed as Question 3 of the fibration-presentations r4 prompt. **Proved 2026-11-20** (`conjectures/answered/fibration-presentations-characterization-r4-2026-11-20.md`, Response 1, verified). The globe case D_k → D_{k−1} follows from the suspension classification and the tensor-localisation lemma, and the general case from a homotopy pushout of globe trivialisations with Loubaton's pullback–colimit theorem. Steps 1–3 are confirmed, so Proposition W holds unconditionally.

**Effectiveness.** The resolution (Γ′, W′) is found by a terminating search, because a resolution always exists. A finite equivalence certificate (item 15) is checkable. So the kernel can accept any finite base. The certificate becomes trivial (Γ′ = Γ, W′ = ∅) exactly when Γ carries a ⊢hpol derivation. That is C3's role under C4: an optimisation that keeps presentations small, never a gate.

### 2.6 Machine check: what the encoded rules actually require

`src/CaTTExp/Lim/WeakBase.agda` (type-checked locally, Agda 2.6.3, no postulates):
- Mikhail's cone recognition rules, with both the printed and the strict linearity test, **accept the lax cone over the bubble** σ : 1_x ⇒ 1_x. Its projection over σ is p_σ : ρ⁻¹_q ⇛ ρ⁻¹_q ; (q ▷ σ), where ρ⁻¹_q is the cone cell over the coherence 1_x. So the encoded rules accept a cone over a non-homotopical base, and nothing in them requires homotopicality. That is one instance, not a general theorem, and these rules are known to be permissive (Defects D5). An independent reviewer checked that the recognisers reject the reversed orientation and the σ-free cell.
- The **specified** cone construction `coneC` (the repaired rule, `Repaired.agda`) is undefined on the bubble. It is also undefined on the well-formed positive base μ : a·a ⇒ a, which is homotopical by Chanavat Cor. 3.39 (a prose citation, not machine-checked). The reason is that `projTy` (Repaired.agda) only handles generators of dimension ≤ 2 whose boundaries are variables. So the restriction in the encoded repaired rule is "variable boundaries and dimension ≤ 2", not homotopicality. The Agda checks the two instances; the general statement is read off `projTy`.
- Extending `coneC` to term boundaries is the cone-over-coherences problem N^cone (B5, CONE). That problem, not homotopicality, is what the limit rules depend on. It is dimension 1 proved, dimension 2 from RC(2). This finding goes to CONE and LIM-F.

### 2.7 Decision

**Bases are read weakly (C4). No kernel rule checks homotopicality. Homotopicality enters only as the optional certified judgement ⊢hpol (C3, with the decidable §2.2 classes as base rules). Its only effect is to let a weight presentation use the base itself instead of a resolution.**

Reasons:
1. **It removes an unfixable incompleteness.** Every option that checks homotopicality (C1–C3) rejects homotopical bases, and the co-r.e.-completeness result shows that no extension can close that gap. C4 accepts every base.
2. **It matches what CaTT diagrams mean.** Diagrams are maps out of Free(Γ). The strict-base reading behind §9.3 came from the bubble example read through F(σ), which CaTT cannot express.
3. **It is the most general option** (standard 4), it is decidable (nothing to decide), and it adds no rule forms. ⊢hpol is an inductive judgement in the style of ⊢ps, and it sits off the critical path.
4. **What it needs is already owned or posed.** Lemma Loc-total (§2.5) is posed. N^cone (§2.6) is owned by CONE and the RC line.

**What would overturn this.** A counterexample to Proposition W, meaning a weight over a non-homotopical base with no finite presentation. Then the fallback is C3 as a gate for presentation-based weights only, with C4 kept for everything else.

**Open items.**
- ~~Lemma Loc-total.~~ Proved 2026-11-20 (fibration r4 Response 1, verified); Proposition W is unconditional.
- Extend `coneC` to term boundaries (N^cone). Owner CONE/LIM-F, notified.
- Encode ⊢hpol with the §2.2 base classes. Owner DSGN (Loc-total is now proved). **Started 2026-11-20:** `src/CaTTExp/Lim/Hpol.agda` decides the first base rule, positive path 2-polygraphs: objects, 1-cells between objects, and 2-cells between nonempty composites of 1-cell variables. Their homotopicality is cited from Chanavat Cor. 3.39, not formalised. It accepts the parallel pair and μ : a·a ⇒ a, and rejects the bubble. Still to add: pasting contexts, orientals, positive-to-one, the no-matching positive 3-polygraphs, top weight ≤ 2, and closure under suspension. The homotopy-polygraphs r5 answer adds decidable classes: finite strict cells with abelian tests, top weight ≤ 2 in any dimension, and one-resource semaphores.
- B24 (HPOL) is no longer on the critical path of any kernel rule. It remains a research item, and its decidable classes (r5 Q3) feed ⊢hpol.

---

## 3. Closed structure: which rules the kernel takes

*Added 2026-11-20 by the thread "Add Gray biclosed rules to the core" (GBIC), after the verified r3 answer (`conjectures/answered/gray-biclosed-coherence-r3-2026-11-20.md`). Ledger row D7.*

### 3.1 The options

**G1. Representable factors only.** Keep (lhom) of `internal-hom.md` §5.1 and the B ⊗ Θ rule of `closed-structure.md` E.2 as primitives.
- Derives: B ⊗ ⟦Θ⟧ and [Θ, C] for representable Θ, lax transformations between arbitrary functors (E.4).
- Rules out: B ⊗ C and Fun^lax(C, D) for arbitrary C. Lax-functor-category currying with both factors arbitrary is not expressible.

**G2. The r3 templates.** ⊗, \ and / are type formers. Pairing, the two evaluations, probe pairing and the point are corollas. Currying c and its comparison ε are cut templates at every ball dimension, and there is a directed-cut template (`closed-structure.md` F.7.4).
- Derives: everything G1 derives (as derived rules, F.7.4 item 5), plus B ⊗ C, C\D = Fun^lax(C, D) and D/C = Fun^oplax(C, D) for arbitrary objects, with every currying equivalence and probe absorption.
- Rules out: reverse cells (orientation is inherited from hypotheses), and the unsound all-levels bijection of E.1 (time slots never move past a bound object).
- Decidable: yes (Lemma GB-dec). Exact: initial over the lax-grid model (Response 2). The kernel's extensions (element generators, probe bound arguments, the L core as probe base) are covered by the in-house Lemma GB-ext, whose independent check is D7c.

**G3. A uniform contractibility test on Gray pasting types,** in Mimram's CCCaTT style. Here every sequent passing one structural test would get a coherence.
- Status: no such test is known. Response 1 of r3 shows that a test justified by inhabitation in every model is unsound for the free theory: a goal can hold in every ambient model and still have no map in the free theory. Per standard 1 that only rules out tests of that kind. A uniform test that is generative, not modelwise, is not excluded. Any such test would have to derive exactly G2's cells, since G2 is exact.

### 3.2 Worked examples

(a) **Fun^lax(C, D) for C = the walking span.** G1 has no object for it. G2 gives C\D, with evaluation (C, C\D ▸ D). A lax transformation α between F, G : B → C\D is (B, ⟦D¹⟧ ▸ C\D), which corresponds by the left row to (C, B, ⟦D¹⟧ ▸ D).

(b) **The walking square.** In context (h : (Q, X ▸ Z)), G2 admits no template whose goal is the reverse of a square at a time slot. Specializing X = ⟦D⁰⟧, Z = Q and h = the unit would give a reverse square in Q, which does not exist. G1 and G2 agree here.

(c) **The naive bijection.** (B ⊗ C, ⟦D¹⟧ ▸ D) against (B, ⟦D¹⟧ ▸ C\D)? G2 does not relate them, because the left row keeps the time slot after C, which is (C, B, ⟦D¹⟧ ▸ D). This matches E.1's counterexample at B = C = D¹.

### 3.3 Decision

**The kernel takes G2. (lhom) and the B ⊗ Θ rule become derived rules.**

Reasons:
1. G2 strictly extends G1, and everything G1 derives is a derived rule of G2.
2. G2 is decidable and exact, and its rule classes are those of `coh`: generic contexts, template recognition and invertible witnesses. There are no universes and no definitional equations (standard 5).
3. G3 has no candidate test. Any candidate must reproduce G2, so G2 is the reference it would be measured against.

**What would overturn this.**
- A counterexample to Lemma GB-ext. The kernel would then keep G2 for data-sorted signatures and treat element variables through G1's rules.
- A uniform generative test (G3) that is decidable. It would replace the template list, with G2 as its specification.

**Open items.** D7c (an independent check of Lemma GB-ext), and D7d (Agda, `src/CaTTExp/Gray/Biclosed/`), owned by GBIC.

---

## 4. Free objects and probes: rule GB-shape

*Added 2026-11-21 by the thread "Write the consolidated system spec" (SPEC), at the coordinator's request after `ordinary-math.md` §6.5.2 (FSET, PR #361). Ledger rows S13 and F8a.*

### 4.1 The gap

The kernel has two kinds of "shape object", and no rule relates them.
- **Free objects** (chapter 7, `free-objects.md`; written ⟦Θ⟧♭ here and in `ordinary-math.md` §6.5.2, ⟦Θ⟧ in `spec/07`). They are data objects. Maps ⟦Θ⟧♭ → C are Θ-shaped diagrams of elements of C, by LIFT. ⊤ ≃ ⟦D⁰⟧♭, and an element of C is a map ⊤ → C (chapter 6).
- **Probes** (chapter 8, `closed-structure.md` F.7.4; written ⟦Θ⟧). They are the probe sort of the multimap judgment. A point of C is a nullary multimap ( ▸ C), and (⟦Θ⟧ ▸ C) is a probe diagram. The unit row makes (L, ⟦D⁰⟧, R ▸ Z) ≃ (L, R ▸ Z), so a point is also (⟦D⁰⟧ ▸ C).

The graded countermodel 𝒢 of `ordinary-math.md` Theorem 6.4 (a) satisfies every current rule. In 𝒢, elements ⊤ → C are families of points of every component C_n, while points ( ▸ C) are points of C₀ alone. So no comparison between elements and points is derivable, in either direction.

### 4.2 Audit: where the notes and spec identify the two silently

Each place below is true with GB-shape. Without it, the statement is unsupported.

| Place | What it identifies | Effect without GB-shape |
|---|---|---|
| `internal-hom.md` §5.1, "Status 2026-11-20: derived" | (lhom) is stated for Δ ⊳ C = maps out of the free object ⟦Δ⟧♭. The derived rule C/⟦Θ⟧ is about probe multimaps (⟦Δ⟧ ▸ –). "Nothing in this section changes meaning" equates the two. | The derived rule gives (lhom-Λ/♭) for probe Δ only. The data form, including the D⁰ check "points of [Θ, C] are Θ-diagrams", is not derived. The same applies to §5.2–5.6, which use Δ ⊳ –. |
| `closed-structure.md` E.2, "Status 2026-11-20"; `spec/08` §8.4 (B ⊗ ⟦Θ⟧) | E.2's B ⊗ Θ took Θ as a shape of data diagrams. F.7.4 item 5 reads it as B ⊗ ⟦Θ⟧ with a probe. | E.2's rule is derived for the probe reading only. Its consistency clause (B = ⟦Δ⟧) holds inside the probe sort only. |
| `spec/06` §6.5 table, "lax cotensor [⟦Θ⟧, C]: lim over Θ of the constant diagram"; `spec/08` §8.4, "[Θ, C] := C/⟦Θ⟧" | Two definitions of the lax cotensor: a limit whose maps in are data diagrams, and a residual whose maps in are probe multimaps. | Two objects, with no derivable comparison between them. |
| `spec/07` §7.3, "Why A1 is the primitive"; ledger S10; `free-objects.md` §4.4 update | It says chapter 8's probes ⟦Δ⟧ "use A1's form", i.e. that they are free objects. | False as stated. The A1 choice still stands on the pushout argument alone, which does not use probes. |
| `spec/08` §8.1, "(⟦Δ⟧ ▸ C) is a Δ-shaped diagram in C" | Probe diagrams and chapter 7's diagrams Diag(Δ, C). | Probe diagrams only. Globular probes ⟦Dᵏ⟧ in a time slot are ambient k-cells (the time-slot reading of §8.1), but a time slot needs a data input beside it, so this does not reach the nullary case. |
| `spec/09` §9.6 | Presents GB-shape and L-× as "added". | They are proposals (ledger F8a, F8b). |

Places checked and found consistent: chapter 6's elements, hom objects and T-hom (all about ⊤ → C); chapter 9's G, DJ, dcoh_S (elements ⊤ → –); chapter 8's rows, conservativity and dualities (probe sort only); `design-decisions.md` §3.2 (b) (probe sort only); the Agda `Gray/Biclosed` modules (probe sort only, plus the weakening row in `FunSets.agda`, which assumes GB-shape at D⁰).

### 4.3 The options

**K0. Status quo.** Two notions of element and of shape diagram, related by nothing.
- Derives: what the current rules derive, read with the corrections of §4.2.
- Rules out: projections out of ⊗, weakening, and every bridge in §4.2 (Theorem 6.4 (a)).

**K1. GB-shape at D⁰ only (weakening).** The corolla ι_{D⁰} : (⟦D⁰⟧ ▸ ⊤) and the row "⊤ at slot i": H = (L, ⊤, R ▸ Z), B = (L, ⟦D⁰⟧, R ▸ Z), r(x) = x ∘ᵢ ι_{D⁰}.
- Derives: elements = points, since (⊤ ▸ C) ≃ (⟦D⁰⟧ ▸ C) ≃ ( ▸ C). Projections out of ⊗ and the comparison κ (`ordinary-math.md` §6.5.2 (ii)).
- Derives at globes: an ambient k-cell between elements e, e′ : ⊤ → C is (⊤, ⟦Dᵏ⟧ ▸ C) by the time-slot reading. The ⊤ row followed by the unit row turns it into (⟦Dᵏ⟧ ▸ C). So probe globes are cells between elements.
- Not known: whether (⟦Θ⟧ ▸ C) ≃ maps ⟦Θ⟧♭ → C for non-globular Θ. That would need probes to decompose along the pasting of Θ, and no current rule glues probes (§4.5).

**K2. GB-shape at every pasting shape Θ** (`ordinary-math.md` §6.5.2 (ii)). The corolla ι_Θ : (⟦Θ⟧ ▸ ⟦Θ⟧♭) and the row "shape at slot i": H = (L, ⟦Θ⟧♭, R ▸ Z), B = (L, ⟦Θ⟧, R ▸ Z), r(x) = x ∘ᵢ ι_Θ.
- Derives: everything K1 derives, and maps ⟦Θ⟧♭ → C ≃ (⟦Θ⟧ ▸ C) for every Θ. So every bridge of §4.2 holds.

**K3. One sort: identify ⟦Θ⟧♭ with ⟦Θ⟧ as a single object.**
- Rejected. The sort discipline (`spec/08` §8.1) is what makes the biclosed rules conservative over L (§8.5, GB-ext step 4). If probes are data objects, an object variable in an output position can be a probe. A row's output can then feed a pure judgment, and conservativity over L is lost.

### 4.4 Worked examples

1. **An element as a point.** For e : ⊤ → C, its point ( ▸ C).
   - K0: no term.
   - K1, K2: the c of the ⊤ row applied to e, then the unit row.
2. **An arrow between elements as a probe 1-cell.** A 2-cell θ : e ⇒ e′ between elements, as (⟦D¹⟧ ▸ C).
   - K0: no term.
   - K1, K2: θ is (⊤, ⟦D¹⟧ ▸ C) by the time-slot reading. The ⊤ row at slot 0 gives (⟦D⁰⟧, ⟦D¹⟧ ▸ C), and the unit row gives (⟦D¹⟧ ▸ C).
3. **A composable pair.** Θ = (x → y → z), i.e. D¹ ∨ D¹. A pair of composable arrows of elements is a map ⟦Θ⟧♭ → C (chapter 7). The lax cotensor C/⟦Θ⟧ of chapter 8 classifies probe diagrams (⟦Θ⟧ ▸ C).
   - K2: the shape row at Θ identifies the two.
   - K1: each arrow transfers by example 2. Gluing the two at y as a probe diagram needs a pasting rule for probes, which the kernel does not have.
   - K0: no transfer.
4. **The two lax cotensors** (§4.2, third row). lim_Θ(const C) represents maps ⟦Θ⟧♭ → –. C/⟦Θ⟧ represents (⟦Θ⟧ ▸ –) at the probe slot.
   - K2: both represent the same functor through the shape row, so they are equivalent by the uniqueness of representing objects (GB-cut at n = 1).
   - K0, K1: no derivable comparison, except at globes in K1.
5. **Projections out of ⊗.** (A, W ▸ A).
   - K1, K2: w₁(1_A) ∘₁ !_W (`ordinary-math.md` §6.5.2 (ii)).
   - K0: not derivable (𝒢).

### 4.5 Comparison

| | K0 | K1 | K2 | K3 |
|---|---|---|---|---|
| Rules added | none | one corolla, one row | one corolla and one row per Θ | sort merge |
| Sound in Cat_ω | yes | yes (⟦D⁰⟧ and ⊤ are both the point) | yes (ι_Θ is the identity of Θ) | yes |
| Conservative over L (`spec/08` §8.5) | yes | yes: data output | yes: data output | **no** |
| Decidable (Lemma GB-dec) | yes | yes: one more template family | yes: one more family, indexed by Θ, bounded by the goal as for the probe-pair row | — |
| Elements = points | no | yes | yes | yes |
| Shape diagrams = probe diagrams | no | globes only (others unknown) | yes | yes |
| Bridges of §4.2 | none | globular instances | all | all |

### 4.6 Verdict (by the evidence)

**K2**, on the evidence so far. Adoption waits on an independent check of the exactness argument for the shape row (GB-ext step 1 with ι_Θ as an element generator; F8a, FSET). Soundness in Cat_ω is proved, and the countermodels 𝒢 and 𝒬 passed their independent check.
- It is the most general option that keeps conservativity (standard 4). K3 loses conservativity, and K0 and K1 derive strictly less.
- Every claim in §4.2 then becomes true as written, so the notes need pointers, not rewrites.
- Its cost over K1 is one template family indexed by Θ, decided by the same matching as the probe-pair row.
- Its soundness is immediate in Cat_ω. Its exactness is at argument level (GB-ext step 1, `ordinary-math.md` §6.5.2 (ii)).

**What would overturn this.**
- That exactness check failing for Θ ≠ D⁰. K1 would then be the choice.
- A proof that K1 derives the shape row at every Θ, for example from a pasting rule for probes. K1 and K2 would then coincide, and K1 is the smaller statement.

### 4.7 Decision (2026-11-21)

**K2 is adopted.** The independent check of the exactness argument passed at argument level (ledger S13).
- By the left and right rows, O(L, ⟦Θ⟧♭, R; Z) ≃ Map(⟦Θ⟧♭, L\Z/R) and O(L, ⟦Θ⟧, R; Z) ≃ O(⟦Θ⟧; L\Z/R). This uses probes as bound arguments (GB-ext (ii)). So the row family is a single locality condition: ⟦Θ⟧♭ represents O(⟦Θ⟧; –) on data through ι_Θ. GB-ext step 1 applies, and Cat_ω is local because ι_Θ = id.
- Steps 3–5 are unchanged. ι_Θ is an element generator, and no profile has a data input with a pure output.

Precisions recorded:
- (a) The check treats ⟦Θ⟧♭ as a data atom. Its identification with chapter 7's free object is sound in Cat_ω. Exactness of the combination with LIFT is outside GB-ext, as for every non-biclosed chapter.
- (b) GB-dcut for this row puts the time slot at a fixed gap of L or R, as for the pair row. The row adds no slot of its own (`spec/08` §8.8).
- (c) Derived: ⟦Δ⟧♭ ⊗ ⟦Θ⟧♭ ≃ ⟦Δ ⊗ Θ⟧♭, by the pair and probe-pair rows. This is true in Cat_ω.

The corrections in §4.2 stand as statements of what needs GB-shape. With K2 adopted, each place there now holds as originally written.
