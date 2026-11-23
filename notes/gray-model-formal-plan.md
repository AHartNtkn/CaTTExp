# Formal plan: the strict Gray model 𝔖 in Agda (C5b, D7g instances)

*Started 2026-11-21, thread "Formalize the strict Gray model in Agda". Ledger: C5 (C5b) and D7g. This file holds the plan; status lives in `open-issues.md`.*

**Goal.** Give an instance of `Gray/Biclosed/Model` that carries Theorem S over to 𝔖 (`free-objects-proofs.md` §5.4). Then add the strictly-invertible reading of inv, and state the D7g instance criterion.

## The obstacle in the literal route

The literal route would interpret every formula as a strict ω-category and ⊗ as the Gray tensor of arbitrary strict ω-categories. That route has two problems.

**Quotients.** The Gray tensor is a colimit, presented by generators and relations, and `--safe` Agda has no quotients. So it needs setoid ω-categories and a term model.

**The core theorem.** `Model` requires `unC` for the corolla m in every context: (P, U ⊗ W, Q ▸ Z) ≅ (P, U, W, Q ▸ Z). That is representability of lax multilinear maps by the term model inside a multilinear context, which is the associativity theorem for the Gray tensor (Crans 1995; Ara–Maltsiniotis 1607.00668 App. A).
- To prove it, a functor ν(M) → U ⊗ W from a Steiner complex has to be pushed through other tensor factors.
- Its atoms land on formal composites of charts, and (a ⊗ (t # t′) ⊗ b) is not a composite of a ⊗ t ⊗ b and a ⊗ t′ ⊗ b.

The setoid ω-categories were written (2026-11-21) and then dropped for the route below; this obstacle is why. The literal version stays open as ledger item C5c.

## The route: Day convolution over Steiner complexes (𝔖̂)

Let 𝒮 be a small category of finite strong Steiner complexes, with all maps of augmented directed complexes between them. It is monoidal under Steiner's tensor, with the Leibniz rule of `conventions.md` §2. 𝔖̂ is the multicategory of presheaves on 𝒮 with Day convolution:
- **Objects** are presheaves of setoids on 𝒮.
- **Multimaps** (F₁, …, Fₙ ▸ G) are families F₁(K₁) × … × Fₙ(Kₙ) → G(K₁ ⊗ … ⊗ Kₙ), natural in each Kᵢ.
- **⊗** is Day convolution, a coend. A coend is a setoid with the generated equivalence, so it needs no ω-category word problem. The corolla m is the coend injection, and `unC` is the coend's universal property.
- **\ and /** are ends: (A\C)(K) is the natural families A(L) → C(L ⊗ K). Evaluation and currying are immediate.
- **rep Θ and shp Θ** are the representables y(λΘ), and the probe pair is Δ ⊠ Θ ↦ λΔ ⊗ λΘ. By Yoneda, y K ⊗ y L ≅ y(K ⊗ L), which gives p and ι. pt is the unit y(λD⁰). δ and σ are the face and collapse maps of globes, and σδ = 1 is a computation in 𝒮.
- **obj i** is valued as any presheaf. Valued as a nerve N A = Hom(ν −, A), it is the ω-category A.

**Relation to 𝔖.** These are citation-level facts (Steiner 2004; Ara–Maltsiniotis App. A). They need every code to be a strong Steiner complex. Globes and their tensors are. The named bases (the parameter `nmFB`) are arbitrary in the Agda, which does not assert loop-freeness or unitality, so the transfer to 𝔖 applies only when every named basis is strong Steiner (ledger C5d). `Steiner/StrongSteiner` gives a sound check for a given finite basis (certificate ⇒ strong Steiner; completeness not proved), so a concrete named basis that passes is certified by `tt`:
- *Nerves.* ν is fully faithful on strong Steiner complexes and 𝒮 is dense in strict ω-categories. So ω-categories form a full reflective sub-multicategory of 𝔖̂ by nerves.
- *Closures.* Hom(|N A ⊗ N B|, Z) = Hom(A ⊗ B, Z), so (N A, N B ▸ N Z) in 𝔖̂ is exactly 𝔖's multimap set. Closures of nerves are nerves: [N A, N Z] ≅ N(A\Z).
- *Tensors.* 𝔖̂ differs from 𝔖 only in maps *into* a tensor. There the Day convolution is not a nerve.

**Consequences.** Theorem S in 𝔖̂ gives Theorem S in 𝔖 for judgements whose output is not a tensor:
- *C5b and D7g.* Canonical rows output an object variable or a closure into one, which is what C5b and D7g use.
- *The instance criterion.* On representables 𝔖̂ and 𝔖 agree exactly: y K ⊗ y L = y(K ⊗ L), and (y K ▸ y L) = 𝒮(K, L) ≅ Hom(νK, νL) by full faithfulness. So the criterion's computations (walking square, four-cube) take place in 𝒮.

## Milestones

- **S1. Codes for 𝒮.** Codes are globe n, named i (a parameter family of finite bases), ⊗ and the unit. Each code gets its basis elements, degrees and ∂^±, with the Leibniz rule for ⊗.
- **S2. Maps of ADCs.** A map is a chain map that preserves degree and augmentation, with ℕ coefficients. This step defines identity and composition, the pointwise ≈, and the category laws.
- **S3. ⊗ on maps.** This covers functoriality, the n-ary tensor of a list, and the flattening isomorphisms ⊗(K⃗, ⊗L⃗, M⃗) ≅ ⊗(K⃗, L⃗, M⃗), with their naturality and coherence.
- **S4. Day multicategory.** This covers presheaves of setoids, multimaps, substitution (restriction along flattening), and the laws `seq`, `par`, `unit-l` and `unit-r`.
- **S5. Structure.** This covers the coend ⊗ with `unC` for m; the ends \ and / with `curL` and `curR`; Yoneda for rep, shp, p, pt and ι; and globes with σδ = 1. The result is `dayModel : Model`.
- **S6. inv as strictly invertible**, and the D7g instance criterion stated over 𝒮.

## Status (2026-11-22)

**S1–S5 are done in Agda** (`src/CaTTExp/Gray/Biclosed/Steiner/`, `--safe`, no postulates). `DayModel.dayModel ob : Model` is the instance 𝔖̂, for any family `ob` of presheaves valuing the object variables. So `Soundness.soundness` (Theorem S, generic part) holds in 𝔖̂.
- *Codes and maps* (`Codes`, `Globe`, `Maps`, `Tensor`, `Assoc`). Codes are lists of atomic bases (globes and named bases), read as their Steiner tensor. Maps are degree- and augmentation-preserving ℕ-chain maps. Steiner's loop-freeness and unitality are not stated; the instance does not need them.
- *Day multicategory* (`Psh`, `DayMult`). Setoid presheaves, multimaps as natural families, one-place composition with Markl's laws.
- *Structure* (`PshOps`, `Sem`, `Rep`, `Corollas`, `GlobeMaps`, `DayModel`). ⊗ is the coend, presented by generators with the generated equivalence; m is the coend injection, and its universal property is proved by induction on that equivalence. \ and / are ends, with evaluation and currying. rep Θ and shp Θ are representables y(λΘ). p_{Δ,Θ}, ι_Θ and pt are Yoneda corollas, through y(λΔ ++ λΘ) ≅ y(λΔ) ⊗ y(λΘ) at the level of multimaps. δ^± and σ are postcomposition with the face and collapse maps of globes, and σδ = 1 (= pt at n = 0) is the chain-map identity `GlobeMaps.σδ`.

**What 𝔖̂ establishes, and what it does not.** Theorem S holds in 𝔖̂ in Agda. Carrying it to the literal 𝔖 uses the nerve facts listed above, which are citation level. Tensors of 𝔖̂ match S only *as inputs*: a multimap out of U ⊗ W is a multimap out of (U, W), as in 𝔖. A judgement whose output is a tensor is about Day convolution, which on nerves is not the nerve of the Gray tensor. C5b and D7g only use outputs that are object variables or closures into them, so they are covered. The literal version, with every formula a strict ω-category and ⊗ the Gray tensor, is ledger item C5c.

**S6, partly done.**
- *Instance criterion.* `Soundness.no-term` states it in every model: if one valuation satisfying Γ has no element of ⟦A⟧, then no term has type A over Γ. Taking A to be the reversed goal of a directed instance gives the criterion of `free-objects-proofs.md` §5.5.
- *The two examples, computed in 𝒮.* `Steiner/WalkingSquare.no-reverse-face`: no map λD² → λD¹⊗λD¹ has the reverse interchanger's faces. `Steiner/FourCube.no-uv`, `no-vu`: no map λD³ → (λD¹)^⊗4 has faces with top chains [212321] and [123212], in either order. Each reads a few coordinates of the chain condition. `FourCube.uCell`/`vCell` build u and v as chain maps λD² → (λD¹)^⊗4 from the path 4321 to 1234, checked by computation (`CheckMap`), and `no-u⇒v`/`no-v⇒u` state the result with them as faces. What is not formalized is the step from these to a syntactic instance: building a Γ and a kernel instance σ whose valuation in 𝔖̂ gives these maps, and computing ⟦σ(u^±)⟧ there. *2026-11-23:* the semantic half of that step is done for the walking square (`Steiner/CellRep`). Operations of 𝔖̂ out of a globe into a representable represent maps of 𝒮 (`rep-ext`), and their faces represent the composites with δ^± (`rep-face`). `ws-no-term` rules out a term of type s ⇒ t whenever a valuation satisfying Γ makes s and t represent paths that differ at n₀. The concrete Γ, σ and valuation remain (ledger D7g-link, parts 1–2).
- *inv as strictly invertible.* Not done. Soundness still reads inv as flat.

## D7g-link, parts 1–2: design (2026-11-23)

**Question.** Parts 1–2 ask for an instance σ : Γ ⊢ ctx t whose images σ(u⁻), σ(u⁺) are the two paths of the walking square (resp. u and v of the four-cube pair), and for a valuation of Γ in 𝔖̂.

**The kernel cannot name a path as a single term.** The term formers (`Typing.infer`) are:
- variables, the structural operations, `idt` and `comp`;
- `glue`, which adjoins invertible collars;
- `here`, which instantiates a template.

`comp` is planar substitution, or whiskering when exactly one argument is a higher cell. Nothing composes two directed cells vertically. So a 1-cell term at the top of a whiskering is one generator (a variable or a `here` cell) whiskered by operations. That is one edge of the square, never the two-edge composite (f◁β);(α▷g′). The same holds for the 6-edge paths of the four-cube pair.

**What is left once vertical composites are excluded.** σ(u±₁) can only be variables, or single edges. With variables, the instance with the most structure is Γ = ctx t, σ = identity. Its reverse goal is excluded already by the generic theorem `D7g.d7g` (proved in the poset model, so in every model). Valuing it in 𝔖̂ with the walking square gives no new syntactic statement. `DirEnv` (any model) would supply that valuation from a tower of H-cells, and the CellRep extraction would finish it, but this only re-proves a case of `d7g`.

**Decision.** Parts 1–2 are not expressible in the current kernel. The examples are formal at the semantic level:
- the computations in 𝒮 (`WalkingSquare`, `FourCube`);
- the extraction of maps from cells of 𝔖̂ (`CellRep.rep-ext`, `rep-face`);
- the syntax-facing criterion `CellRep.ws-no-term`, which applies to any Γ and valuation.

If the kernel gains vertical composition of directed cells, σ(u±) become the composite paths. Part 1 is then a term, and part 2 is `DirEnv`'s valuation built from a tower in 𝔖̂. Until then the ledger row records parts 1–2 as not applicable.
