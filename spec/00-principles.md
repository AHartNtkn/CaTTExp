# Chapter 0. Principles

These are the constraints every later chapter satisfies. They are design commitments, not theorems, so they have no proof status; each one names where it was decided.

## 0.1 What the system is about

The system is a type theory in the style of CaTT (Finster–Mimram) whose intended model is **the ω-category of ω-categories with lax transformations**. That object is not an ω-category: it is an *oriented category*, a category enriched in ω-categories for the lax Gray tensor (Gepner–Heine, arXiv 2510.10504; strictly, Ara–Maltsiniotis's ∞-Cat_lax, arXiv 1607.00668, Ex. C.18). Write 𝒦 for it.

- A term of type ⋆ is an object of 𝒦, that is, an ω-category.
- A term of type `a → b` between objects is a 1-cell of 𝒦, a functor. A term between 1-cells is a lax transformation, and so on up.
- Inside one hom 𝒦(a, b), cells compose as in an ω-category. Composition **across** objects, 𝒦(a, b) ⊗ 𝒦(b, c) → 𝒦(a, c), is Gray: it has a directed interchanger and no horizontal composite.

The ambient 𝒦 stays **external**: it is the model the judgments are about, not a term inside the theory. Internal quantifiers in Lawvere's style (a rule that binds an object variable and has a universal property witnessed by cells) are allowed where the rules below support them.

*Source:* `notes/pseudo-vs-gray.md` §0, §2.1–2.2; `notes/conventions.md` §4.

## 0.2 No universes

There is no type of types, no type of small ω-categories, and no rule that turns a judgment into a term. ⋆ is a sort, not a universe: nothing has type "the collection of objects".

What this excludes:
- any object or term that classifies objects, families of objects or presented structures. "The ω-category of ω-categories" is never an object of the theory, and its structure appears only through rules about 𝒦 (limits, free objects, the closed structure);
- any rule that reflects a judgment into a term, including ⋆ itself or Γ ⊢ C : ⋆.

What it does not exclude:
- **Binding formers in Lawvere's style** (§0.1). A rule may bind an object variable in a premise and form an object or a cell from it. Examples are an end ∫_X F(X, X) or a System F-style ∀X. T(X).
- Such a rule must state its universal property as the existence of cells (§0.3), and it must not make ⋆ or a judgment into a term.
- A binder of this kind ranges over the sort ⋆, as a context variable does. It needs no type of objects, so it is not a universe.
- The kernel has one such former: INIT (chapter 9, §9.3), the initial model μΔ of a positive context Δ, read impredicatively as ∀Δ. X with naturality. It is sound in 𝒦 for its class of contexts. The dual, final models of copositive contexts, is unsound in general and is not a rule.

*Source:* project standard 5; `notes/pseudo-vs-gray.md` §4.7 records why universes are off the plan.

## 0.3 Universal properties are witnessed by cells

The kernel has **no definitional equality** beyond syntactic identity of terms after substitution, as in CaTT. In particular:
- no β or η rules for any type former or term former;
- no computation rules for limits, free objects, internal homs or tensors;
- a law of a strict theory used in a side condition (chapter 2) never becomes a definitional equality. It only makes certain cells derivable.

Every universal property is stated as the existence of cells: a structure map, a comparison cell, and a witness that the comparison is invertible where invertibility is meant. In the kernel, an equation is proved by exhibiting a cell, never by a conversion check.

**This is a property of the kernel only.** The surface may add computation rules (§0.5). For example, rewrite rules may strictify two of associators, unitors and interchange. Each such rule is justified by a formalized conservativity proof, not by a definitional equality in the kernel.

Rule classes are those of the published CaTT variants: context formation, type formation, the `coh` rule with a side condition computed on its own pasting context, substitution, signature constants with decidable validity, and inductive judgments in the style of `⊢ps` (for example `inv`, `ps`).

*Source:* project standard 5; `notes/design-decisions.md` §1.1 (laws of T are never definitional); Anthony, spec walkthrough 2026-11-22 (surface computation rules; ledger S6, S19).

## 0.4 Lax by default, the most general version first

Where a construction has lax, pseudo and strict versions, the kernel takes the **most general** one. It recovers the others by marking (chapter 3). Concretely:
- the core is the uniform lax core L (chapter 2): interchange is directed at every level, not only across objects;
- the side condition computes in the **least** admissible theory V, so every derivable judgment holds in every admissible theory's models (chapter 2, §2.3);
- pseudo transformations, ordinary ω-categories and groupoids are marks on top of L (`inv`, `ps`, `ord`, `grpd_k`), never separate kernels (see below for how far each goes).

**The generality ordering**, from most to least general, is uniform L ⊂ two-tier L ⊂ P (plain CaTT with pseudo transformations). It is an ordering by derivability. Every uniform-L derivation projects to a two-tier derivation, and every two-tier derivation collapses to a P derivation (chapter 2, §2.6). "More general" means fewer derivable cells and more models.

**How far marks go back down the ordering.**
- *From two-tier L to P:* by marks. P is two-tier L with every interchanger invertible, and the relative coherence lemma for 𝔉 → ν holds (ledger E5).
- *From uniform L to two-tier L:* by marks, with `ord` read as "the inner letters into this object are trivial".
  - The rule (COH-ord) accepts a head all of whose objects are `ord` on the two-tier side condition. With every object marked `ord`, uniform L then derives exactly two-tier L: the same terms, types and marks (chapter 3, §3.6; ledger S16(b)).
  - The mark has to act through the side condition. A mark that only makes inner letters invertible does **not** give two-tier coherences, in any setting. The loop H and 1_w, and the outer W-strip, share a Gray image and stay unconnected after every inner letter is inverted (ledger E13).
  - Heads that mix `ord` and non-`ord` objects use the uniform rule (ledger E15).

Specialisation happens only for a concrete, recorded reason. The one recorded stop is at directed interchange: dropping the interchanger altogether (ω-sesquicategories) would lose the naturality cells that every lax transformation has.

*Source:* project standard 4; `notes/pseudo-vs-gray.md` §2.5, §7; `notes/design-decisions.md` §1.7.

## 0.5 The kernel and the surface are kept apart

The **kernel** is an explicit, decidable system. It has:
- no defaults (every mark, every switch setting, every bracketing is written out);
- no implicit arguments, no notation, no overloading, no computation rules;
- a checker that decides every judgment.

The **surface** is the language a person writes.
- It may infer marks, choose default bracketings or layerings, and offer notation and implicit arguments.
- It may have **computation rules** the kernel lacks. Rewrite rules may strictify two of associators, unitors and interchange, and similar rules may be added for other structure (ledger S6, S19).
- It may not change what is derivable. Every surface layer (elaborator, rewrite system, tactic) is **proved conservative** over the kernel: every surface derivation corresponds to a kernel derivation of the corresponding judgment, and the surface derives nothing the kernel does not.

**Trust comes from proof, not from re-checking.** Each conservativity proof is formalized once. The layer's output is then trusted on the strength of that proof and is not sent back through the kernel term by term, which would make checking slow and memory-hungry. **Everything is formalized**: the kernel, its checker, and every layer above it. The kernel is kept separate because it is the reference theory that the conservativity proofs target, not because it is the only formalized part.

This spec fixes the kernel and leaves every surface choice open. Each chapter lists its open surface questions, with options and a practical comparison.

*Source:* Anthony, in this project's chat (2026-11-21): keeping the kernel and surface apart is essential. Anthony, spec walkthrough (2026-11-22): surface computation rules, and trust by formalized conservativity (ledger S6, S19). The conservativity proof for strictified associators and unitors is ledger S19 (b)–(c).

## 0.6 Decidability of checking

Every kernel judgment is decidable. Where a property of interest is undecidable (homotopicality of polygraphs, chapter 4), the kernel does not check it: it reads the construct in a way that does not need it. A decidable sufficient test that only speeds checking up (`⊢hpol`, chapter 4, §4.4) is not part of the kernel. It lives in the layer above it and is proved conservative like every other layer (§0.5).

Decidability is not the same as efficiency. Several side conditions are decidable but expensive (chapter 2, §2.6). Efficiency is an implementation question and never changes the rules.

*Source:* `notes/design-decisions.md` §0, §1.5, §1.7, §2.7.

## 0.7 Open surface questions

**Q0.1. Which composition order does the user write?** The kernel uses diagrammatic order (`f ; g`, first f).
- *Option A: diagrammatic only.* Matches the kernel, Mikhail's rules and the Gray tensor's execution order, so the factor order in a Gray cell reads left to right. Users coming from classical category theory reverse every composite in their head.
- *Option B: classical only* (`g ∘ f`). Familiar, but every Gray cell's factor order is then read right to left, and the lax/oplax naming hazard of `conventions.md` §3.2 becomes a daily hazard.
- *Option C: both, with distinct symbols.* Cheap to support (it is pure notation) but doubles what a reader must recognise.
- *Worked example.* The lax naturality cell of α : F ⇒ G at f : x → y is `α_x ; Gf ⇛ Ff ; α_y` in A and `Gf ∘ α_x ⇛ α_y ∘ Ff` in B.

**Q0.2. Are objects written as types or as terms?** The kernel has objects as terms of sort ⋆ and elements of C as 1-cells ⊤ → C (chapter 6).
- *Option A: as in the kernel* (`x : ⊤ → C`). Nothing to elaborate; every element is visibly a functor, so lax naturality at elements is visible.
- *Option B: elements as variables of type C* (`x : C`), elaborated to `⊤ → C`. Reads like ordinary mathematics; the elaborator must insert ⊤ and whiskerings everywhere, and error messages must translate back.
