# Formal plan: the strict Gray model 𝔖 in Agda (C5b, D7g instances)

*Started 2026-11-21, thread "Formalize the strict Gray model in Agda". Ledger: C5 (C5b) and D7g. This file holds the plan; status lives in `open-issues.md`.*

**Goal.** Give an instance of `Gray/Biclosed/Model` whose formulas denote strict ω-categories. In it:
- ⊗ is the Gray tensor;
- \ and / are its closures;
- representables are ν(λΘ).

Then add the strictly-invertible reading of inv and κ_Θ (`free-objects-proofs.md` §5.4).

**Why setoids.** `Strict/Omega.ωCat` uses ≡ on cells. The Gray tensor and the closures of *arbitrary* strict ω-categories are presented by generators and relations, and `--safe` Agda has no quotients. So the instance works with `Strict/OmegaS.ωCatS`, which has cells up to an equivalence ≈ and composition invariant under ≈. Every `ωCat` embeds (`fromωCat`). `Model` already allows this, because its ≈ is an arbitrary equivalence and V is a single `Set`. The atoms' values are a module parameter, so the multimap sets are small.

## Milestones

- **M1 (done 2026-11-21).** `Strict/OmegaS`: setoid strict ω-categories, strict functors, and pointwise equality, with the category laws.
- **M2. Lax multilinear maps and the tensor.**
  - *Multimaps.* A multimap (A₁, …, Aₙ ▸ Z) assigns a cell f(x₁, …, xₙ) of Z to each tuple of cells. For each tuple, the values on the faces must satisfy the attaching words of the top atom of λDᵖ¹ ⊗ … ⊗ λDᵖⁿ. They must also be compatible with identities and with composition in each variable.
  - *Attaching words.* These are the boundaries of the atoms of λS ⊗ λT, written as composition-only expressions. `Strict/Generation.generation` gives them, applied to the atom's source and target cells, because `Strict/TensorBasis` shows the tensor basis is ordered unital.
  - *Uniqueness.* `Strict/Lift` makes the extension to ν(λS ⊗ λT) unique.
  - *The tensor object.* A ⊗ B is the term model. Pre-terms are generators x ⊠ y and formal composites. Well-formedness and ≈ are defined as mutual inductive families. ≈ is the least congruence containing the ω-category axioms and the generator relations above.
  - *Representability.* corolla m : (A, B ▸ A ⊗ B) is the inclusion of generators. Its inverse `unC` is the extension along the term model. That extension is unique up to ≈ by induction on terms.
- **M3. Closures.**
  - *Definition.* (A\C)ₙ consists of the multimaps (A, Dⁿ ▸ C), and (C/A)ₙ of the multimaps (Dⁿ, A ▸ C).
  - *Structure.* The ω-category structure comes from the co-ω-category structure of the globes, so A ⊗ – must preserve the gluings Dⁿ ∐_{Dᵏ} Dⁿ. This is the step that is long on paper (Crans 1995; Ara–Maltsiniotis 1607.00668 App. A) and the main risk.
  - *Evaluation.* Evaluation and currying are restriction and transposition of multimaps.
- **M4. Model fields.**
  - The multicategory laws `seq`, `par` and the units hold pointwise, because multimaps compose by substitution.
  - `unC` covers m, p, pt and ι.
  - `curL` and `curR` come from M3, and σδ = 1 is checked on globes.
- **M5. Representables and probes.**
  - ⟦Θ⟧ = ν(λΘ), via `fromωCat` and `Strict/PsGlob`.
  - p_{Δ,Θ} is the comparison ν(λΔ) ⊗ ν(λΘ) ≅ ν(λΔ ⊗ λΘ). It comes from `Strict/Lift` and the universal property of M2.
  - κ_Θ.
- **M6. inv as strictly invertible.** Generalize `Gray/Biclosed/Sem` and `Soundness` from flat to strictly invertible inv cells. This needs r⁻¹ to preserve invertibility (Lemma S1, the reviewer's point (c)).

After M4 the instance exists. After M5 and M6 it is 𝔖 as §5.4 states it, and the D7g instance criterion can be stated in Agda.
