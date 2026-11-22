# The system specification

This folder states the system as it currently stands: one file per chapter, each chapter depending only on earlier ones. It records the **current answer** only. Superseded designs, rejected options and the history of how a decision was reached stay in `notes/`, which is the research record; every rule here links to the note that justifies it. **Change history** is not written into the spec: it lives in git and in the ledger (`notes/open-issues.md`), whose rows record what was corrected and why. A spec passage may explain why a rule has its current form, for example by a counterexample to a simpler rule, but it does not narrate earlier versions.

If the spec and a note disagree, that is a bug in one of them. It is recorded in `notes/open-issues.md` (section S) with an owner, and neither document is silently preferred.

## Chapters

| # | File | Contents | Layer |
|---|---|---|---|
| 0 | [`00-principles.md`](00-principles.md) | No universes; universal properties witnessed by cells; lax by default; the kernel/surface split | both |
| 1 | [`01-core-syntax.md`](01-core-syntax.md) | Pasting shapes, contexts, types, terms, substitution, the coherence rule | kernel |
| 2 | [`02-lax-core.md`](02-lax-core.md) | The lax core L: directed coherence, the side condition computed in V, the four switch settings | kernel |
| 3 | [`03-invertibility-markings.md`](03-invertibility-markings.md) | Marks `inv`, `ps`, `ps*`, `grpd_k`, `ord`; pseudo = L + marks | kernel |
| 4 | [`04-context-checking.md`](04-context-checking.md) | Pasting contexts for `coh`; arbitrary bases read weakly; the optional `⊢hpol` fast path | kernel |
| 5 | [`05-derived-constructions.md`](05-derived-constructions.md) | Gray tensor of contexts, cylinders, naturality, cones, as algorithms | derived |
| 6 | [`06-limits-representables.md`](06-limits-representables.md) | Limits and representables | kernel extension |
| 7 | [`07-free-objects.md`](07-free-objects.md) | Free objects | kernel extension |
| 8 | [`08-closed-structure.md`](08-closed-structure.md) | Gray biclosed rules | kernel extension |
| 9 | [`09-ordinary-math.md`](09-ordinary-math.md) | Ordinary mathematics: descent (DESC) and initial models (INIT), h-levels, and what they derive | kernel extension |

## The two layers

- The **kernel** is the set of judgments and rules that a checker must implement and that the semantics interprets. It has no defaults, no implicit arguments, no notation and no elaboration. Everything in a kernel chapter is stated so that it can be decided mechanically.
- The **surface** is what a person writes. Besides notation, defaults and implicit arguments, it may have computation rules the kernel lacks. An example is rewrite rules that strictify two of associators, unitors and interchange (§0.5).
  - Every surface feature, and every other extension of the kernel, comes with a proof that it is **conservative** over the kernel, and that proof is formalized. Its output is then trusted on the strength of that proof, not re-checked by the kernel term by term.
  - Everything is formalized: the kernel, its checker, and every extension.
  - This spec makes **no** surface decisions. Each chapter ends with a section *Open surface questions*, which lists the choices a surface language must make, with the options and a practical comparison, and leaves the choice open.

A kernel rule never depends on a surface choice. A surface choice may change what the user writes and how fast it is checked, never what is derivable.

## Format of a rule

Every rule is given in the same six parts.

1. **Rule.** The inference rule, in the notation of the chapter.
2. **Side condition and decision procedure.** What has to be checked, and how it is decided.
3. **Example.** A small worked instance, accepted or rejected.
4. **Semantics.** What the rule means in the intended models.
5. **Status.** One of the labels below, with ledger IDs (`notes/open-issues.md`) for anything open.
6. **Source.** The notes and code the rule comes from.

## Status labels

| Label | Meaning |
|---|---|
| **Agda-checked** | Stated and proved in `src/` under `--safe` with no postulates. The module is named. |
| **proved** | Proved on paper in a note, or a verified researcher answer, but not machine-checked. |
| **paper only** | Stated in a note, with an argument that is a sketch or with a step still open. The open step has a ledger ID. |
| **stated here** | The notes support the rule but do not state it in this form. The spec's formulation is new, and its agreement with the notes is a ledger item. |
| **open** | Not settled. Ledger ID given. |

## Conventions

Orientation conventions (composition order, Gray tensor, lax and oplax) are fixed in `notes/conventions.md`, and the spec uses them without restating them. In particular `f ; g` is diagrammatic order, and composition across objects is `𝒦(a, b) ⊗ 𝒦(b, c) → 𝒦(a, c)` with factors in execution order.
