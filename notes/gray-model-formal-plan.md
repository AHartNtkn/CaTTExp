# Formal plan: the strict Gray model 𝔖 in Agda (C5b, D7g instances)

*Started 2026-11-21, thread "Formalize the strict Gray model in Agda". Ledger: C5 (C5b) and D7g. This file holds the plan; status lives in `open-issues.md`.*

**Goal.** Give an instance of `Gray/Biclosed/Model` that carries Theorem S over to 𝔖 (`free-objects-proofs.md` §5.4). Then add the strictly-invertible reading of inv, and state the D7g instance criterion.

## The obstacle in the literal route

The literal route would interpret every formula as a strict ω-category and ⊗ as the Gray tensor of arbitrary strict ω-categories. That route has two problems.

**Quotients.** The Gray tensor is a colimit, presented by generators and relations, and `--safe` Agda has no quotients. So it needs setoid ω-categories and a term model.

**The core theorem.** `Model` requires `unC` for the corolla m in every context: (P, U ⊗ W, Q ▸ Z) ≅ (P, U, W, Q ▸ Z). That is representability of lax multilinear maps by the term model inside a multilinear context, which is the associativity theorem for the Gray tensor (Crans 1995; Ara–Maltsiniotis 1607.00668 App. A).
- To prove it, a functor ν(M) → U ⊗ W from a Steiner complex has to be pushed through other tensor factors.
- Its atoms land on formal composites of charts, and (a ⊗ (t # t′) ⊗ b) is not a composite of a ⊗ t ⊗ b and a ⊗ t′ ⊗ b.

The setoid ω-categories were written (2026-11-21) and then dropped for the route below; this obstacle is why.

## The route: Day convolution over Steiner complexes (𝔖̂)

Let 𝒮 be a small category of finite strong Steiner complexes, with all maps of augmented directed complexes between them. It is monoidal under Steiner's tensor, with the Leibniz rule of `conventions.md` §2. 𝔖̂ is the multicategory of presheaves on 𝒮 with Day convolution:
- **Objects** are presheaves of setoids on 𝒮.
- **Multimaps** (F₁, …, Fₙ ▸ G) are families F₁(K₁) × … × Fₙ(Kₙ) → G(K₁ ⊗ … ⊗ Kₙ), natural in each Kᵢ.
- **⊗** is Day convolution, a coend. A coend is a setoid with the generated equivalence, so it needs no ω-category word problem. The corolla m is the coend injection, and `unC` is the coend's universal property.
- **\ and /** are ends: (A\C)(K) is the natural families A(L) → C(L ⊗ K). Evaluation and currying are immediate.
- **rep Θ and shp Θ** are the representables y(λΘ), and the probe pair is Δ ⊠ Θ ↦ λΔ ⊗ λΘ. By Yoneda, y K ⊗ y L ≅ y(K ⊗ L), which gives p and ι. pt is the unit y(λD⁰). δ and σ are the face and collapse maps of globes, and σδ = 1 is a computation in 𝒮.
- **obj i** is valued as any presheaf. Valued as a nerve N A = Hom(ν −, A), it is the ω-category A.

**Relation to 𝔖.** These are citation-level facts (Steiner 2004; Ara–Maltsiniotis App. A):
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
