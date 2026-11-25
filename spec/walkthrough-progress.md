# Spec walkthrough: progress

Anthony's piece-by-piece walkthrough of `spec/`, run in the project thread *Walk me through the system spec*. One piece per message; the next piece starts only when Anthony says to continue. `[x]` covered, `[ ]` not yet. Questions he raised, and decisions he made on open surface questions, are logged under each piece (decisions are also recorded in the chapter and in `notes/open-issues.md` S6).

Spec version at start: main @ 2d75c32 (2026-11-21).

## Chapter 0. Principles

- [x] 0.1 What the system is about
  - Q (Anthony): is "lax transformations as 2-cells" a truncation at dimension 2, like (∞,2) ⊂ (∞,ω)? Answered: no; laxness is an orientation axis, not a dimension axis, and every level of Fun^lax is lax (maps A ⊗ Dⁱ → B). The more general direction is uniform L (directed interchange inside objects too), which the kernel takes. Worked picture of D¹ × D¹ vs D¹ ⊗ D¹ and of a lax modification given.
- [x] 0.2 No universes
  - Q (Anthony): what are the practical limitations, beyond rephrasings? Answered: no large recursion (families by recursion), no encode–decode (EX had to be a rule), no power objects, no categories of structures as objects (Set, Grp, presheaves), object-indexed diagrams as fibrations, quantification over objects only outermost.
  - Q (Anthony): System F has impredicative ∀ without a universe; could (co)end calculus be adapted? Answered: yes in principle, as a binding end former; corrected my earlier "no impredicative definitions". Sub-findings: S15 (§0.1 vs §0.2 contradiction), F10(c) (which ends are sound).
  - Finding (Anthony): the resulting growing list of extra rules is unacceptable. Logged as ledger F10.
- [x] 0.3 Universal properties are witnessed by cells
- [x] 0.4 Lax by default, the most general version first
  - Correction sent: my first message said one `ord` mark per object recovers plain behaviour. After E13 (PR #398) it recovers invertibility only for operand-pure heads and none of two-tier L's extra coherences. Finding S16, resolved the same morning by PR #404 (`ord` = inner letters trivial, rule (COH-ord)); told Anthony. Pending for chapter 3 surface questions: whether to keep the invertible-only `ord` as a weaker mark (Anthony's choice); E15 (mixed heads) open.
  - Q (Anthony): was the marker system thought through; what alternatives, or was it forced? Answered: partly forced (pseudo is a property of lax cells, recursive; no definitional equality), alternatives for getting pseudo back were compared, alternative forms of marking were not. Finding S17.
- [x] 0.5 The kernel and the surface are kept apart
- [x] 0.6 Decidability of checking
- [x] Q0.1 (surface question): Which composition order does the user write?
  - **Decided:** Option A, diagrammatic only; principle: align surface with kernel, ignore historical convention. Application written `x ; F`.
- [x] Q0.2 (surface question): Are objects written as types or as terms?
  - **Decided:** Option A, kernel form `x : ⊤ → C` (also settles Q6.1). Users define abbreviations like `El(C) := ⊤ → C` themselves; surface must support user-defined abbreviations.

## Chapter 1. Core syntax

- [x] 1.1 Raw syntax
- [x] 1.2 Judgments
- [x] 1.3 Pasting contexts
- [x] 1.4 The coherence rule
- [x] 1.5 Metatheorems
- [x] 1.6 Signatures (presented with heads, after S27(a) landed; Agda S27(b)–(c) still open)
- [x] Q1.1 (surface question): Names or positions. Decided: A, distinct names, no shadowing.
- [x] Q1.2 (surface question): How much of a coherence the user writes. Decided: B (top-dimensional arguments), names as abbreviations.
- [x] Q1.3 (surface question): How pasting contexts are presented. Decided: A′, ordinary context in any order, canonicalised.

## Chapter 2. The lax core L

- [ ] 2.1 Notation
- [ ] 2.2 The side condition, in one form for every row
- [ ] 2.3 The kernel: the side condition computed in V + S
- [ ] 2.4 Which coherences are invertible
- [ ] 2.5 The two-tier fragment and the implemented checker
- [ ] 2.6 The generality ordering
- [ ] 2.7 Dualities
- [ ] Q2.1 (surface question): Which setting a development starts in.
- [ ] Q2.2 (surface question): How a horizontal composite across objects is written.
- [ ] Q2.3 (surface question): How a failed side condition is reported.

## Chapter 3. Invertibility markings

- [ ] 3.1 Notation
- [ ] 3.2 Judgments and marked declarations
- [ ] 3.3 Rules
- [ ] 3.4 Recursive pseudo
- [ ] 3.5 Pseudo = L + marks
- [ ] 3.6 Marks over the uniform core
- [ ] 3.7 The form of the marks, and saturation (added 2026-11-22, S17)
- [ ] Q3.1 (surface question): Where marks are written.
- [ ] Q3.2 (surface question): Whether `ps` and `ps*` are both visible.
- [ ] Q3.3 (surface question): How object marks are supplied.

## Chapter 4. Context checking

- [ ] 4.1 Coherence contexts
- [ ] 4.2 Bases are read weakly
- [ ] 4.3 Finite presentations over every base
- [ ] 4.4 Above the kernel: the fast path ⊢hpol
- [ ] 4.5 What the limit rules actually need from a base
- [ ] Q4.1 (surface question): Whether the user sees ⊢hpol.
- [ ] Q4.2 (surface question): How bases are written.

## Chapter 5. Derived constructions

- [ ] 5.0 Which core the constructions are valid in
- [ ] 5.1 Relative coherence (RC)
- [ ] 5.2 Naturality of coherences (N)
- [ ] 5.3 Cylinders and the Gray tensor of contexts
- [ ] 5.4 Cones, cocones and transfor shapes
- [ ] 5.5 Canonical Gray terms (introducing a lax cell from components)
- [ ] Q5.1 (surface question): Whether derived constructions are visible as names or only as elaborator output.
- [ ] Q5.2 (surface question): How much of the generated term the user sees.

## Chapter 6. Limits and representables

- [ ] 6.1 The limit object and its universal cone
- [ ] 6.2 The universal filler (horn form)
- [ ] 6.3 Colimits
- [ ] 6.4 Weighted limits
- [ ] 6.5 Derived objects
- [ ] 6.6 Elements and representables
- [ ] Q6.1 (surface question): Element notation.
- [ ] Q6.2 (surface question): How diagrams are given to `lim`.
- [ ] Q6.3 (surface question): Whether lax is the default marking.

## Chapter 7. Free objects

- [ ] 7.1 How a universal property is stated
- [ ] 7.2 The free object on a context (A1 = R-A)
- [ ] 7.3 Attaching a cell (A2), derived
- [ ] 7.4 Free object as a lax colimit of the point
- [ ] Q7.1 (surface question): How free objects are named.
- [ ] Q7.2 (surface question): How lifts are written.

## Chapter 8. Closed structure: the Gray biclosed rules

- [ ] 8.1 Judgments
- [ ] 8.2 Corollas
- [ ] 8.3 Rows, cuts and directed cuts
- [ ] 8.4 Derived rules
- [ ] 8.5 Conservativity over L
- [ ] 8.6 What the closed structure does not change
- [ ] Q8.1 (surface question): How multimaps are written.
- [ ] Q8.2 (surface question): Which residual names the user sees.
- [ ] Q8.3 (surface question): Whether currying is explicit.

## Chapter 9. Ordinary mathematics

- [ ] 9.1 h-levels
- [ ] 9.2 Descent (DESC)
- [ ] 9.3 Initial models (INIT)
- [ ] 9.4 Families, induction and the natural numbers
- [ ] 9.5 Quotients and the integers
- [ ] 9.6 Function sets
- [ ] 9.7 Colimits indexed by objects
- [ ] 9.8 Lax functors
- [ ] 9.9 Filler tactics (admissible, no rule)
- [ ] Q9.1 (surface question): Whether `trunc n` is written or inferred.
- [ ] Q9.2 (surface question): How INIT instances are introduced.
- [ ] Q9.3 (surface question): How descent data are supplied.
- [ ] Q9.4 (surface question): Whether the filler tactics run automatically.

## Findings raised during the walkthrough

- S36 (2.6): object marks (ord, grpd_k) could not reach defined objects; fixed by the markings thread.
- S32 (2.3): a development must not choose its class of models (models stay a justification tool).
- S31 (2.3): per-file switch settings may be unjustified; proposal to drop them.
- S30 (2.2): completeness of the lax side condition is unstated.
- S29 (2.2): §2.2 frames SC as computed in a strict theory; should present it as a combinatorial test with soundness alongside.
- S28 (1.6): user postulates removed; the signature is closed to users, and assumptions are context variables.
- S27 (1.5): how kernel extensions enter (closed constants vs substitution-applied heads) is under-specified; metatheory doesn't cover limit formers.
- S26 (1.1): §1.6 forbids the binders §0.2 allows.
- S24 (0.6): `⊢hpol` is an optimisation but sits in the kernel; move it to the conservative-extension layer.
- S19 (0.5): Anthony's decisions: surface may strictify 2 of 3 by rewrite rules; surface layers trusted by Agda-proved conservativity, no kernel re-check; everything formalized.
- S18 (0.5): the spec carries history ("an earlier version of this section").
- S17 (0.4): alternatives to the form of the marking system never compared.
- S16 (0.4): marks no longer recovered two-tier L from uniform L. Resolved by PR #404 / #406.
- S15 (0.2): chapter 0 contradicts itself on internal quantifiers.
- F10 (0.2): the universe-free rule list keeps growing; seek a small general set of principles that closes it.
