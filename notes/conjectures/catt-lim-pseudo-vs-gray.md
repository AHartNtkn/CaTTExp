# Does CaTT_lim force cone morphisms to be pseudo?

## Background

**CaTT** (Finster–Mimram, [arXiv 1706.02866](https://arxiv.org/abs/1706.02866)) is a dependent type theory whose models are Grothendieck–Maltsiniotis weak ω-categories (Benjamin–Finster–Mimram, [2106.04475](https://arxiv.org/abs/2106.04475)).
- Its types are `⋆` and `t →_A u`.
- Its only term former is `coh_{Γ, t→u}[σ]` over a pasting-scheme context Γ, with a free-variable side condition.
- Because that side condition is symmetric in t and u, every coherence has an inverse coherence. Benjamin–Markakis ([2406.12127](https://arxiv.org/abs/2406.12127)) show coherences are coinductively invertible, and that coinductive equivalences are closed under composition.

**CaTT_lim** (T. J. Mikhail, *A type-theoretic definition of lax (∞,∞)-limits*, [arXiv 2412.13310](https://arxiv.org/abs/2412.13310), Def. 4.15) extends CaTT with:
- a judgment `K cone(Γ; c)` that generates the context of lax cones with apex c over a diagram context Γ;
- a universal cone `ucone_{Γ,x}`;
- judgments `ctrf` generating "conical (n+1)-transfors", which are morphisms of cones, morphisms between those, and so on. Their shapes follow a Gray tensor `M ⊗ Dⁿ`: each cone variable is duplicated and joined to its copy by a connecting cell. **These connecting cells are not required to be invertible.**
- a filler schema `uni`, which states that `ucone_* : Hom(c, lim_Γ) → Cones(Γ; c)` is essentially surjective on cells of every dimension. "Essentially" is witnessed by invertible cells in a judgment `⊨`.

## Statement

Let Γ = `(x:⋆, y:⋆, f : x → y)` and let `L = lim_Γ`. Take two 1-cells `u, u' : c → L` and a 2-cell `β : u → u'`.

1. The cone morphism `ucone_*(β)` has a connecting cell at f. It relates the two composites of `ucone_f` (a 2-cell along `L → ·`) and β (a 2-cell along `c → L`). **Show that this cell is an interchange coherence, and hence invertible in every model of CaTT_lim.**
2. Deduce from the 2-dimensional instance of `uni` that for *every* cone morphism `m` (a `ctrf` context with n = 1), the connecting cell `m_f` is invertible. That is, an inverse for the variable `m_f` is derivable in CaTT_lim.
3. Conclude, or refute: in the (∞,ω)-category of (∞,ω)-categories with *cartesian* hom-objects, where 2-cells are pseudo-natural transformations and non-invertible modifications exist, the lax limit of a non-trivial arrow does **not** satisfy CaTT_lim's universal property as written.
4. Determine the corrected universal property in that setting. The conjecture is: the same rules with every `ctrf` connecting cell over a positive-dimensional cone variable placed in `⊨`. Also determine what the original rules *do* model. The conjecture is: (∞,ω)-categories enriched over the **Gray** tensor, i.e. "oriented" categories in the sense of Gepner–Heine ([2608.02592](https://arxiv.org/abs/2608.02592)).

## A consequence to check

If (1)–(3) hold, take the cartesian setting and the partially lax limit of `⊤ →a C ←b ⊤` with the b-leg invertible. Its points are arrows `b → a` of C, but its arrows are only the **invertible** 2-cells of C. The genuine hom-object `Hom_C(b, a)` is instead the fibre of the *oplax arrow object*, which is characterised through the Gray tensor. This matches the (∞,2) fact that mapping categories are fibres of `Ar^oplax(C) → C × C`, not of `Fun([1], C)` (Gagna–Harpaz–Lanari, [2012.04537](https://arxiv.org/abs/2012.04537)) **[recalled, please verify]**.

## What is known

- Step 1 seems to need only that `ucone_*` is computed by whiskering, which is how Mikhail defines it (§4.3–4.4).
- Step 2 uses invertibility of `⊨` cells and closure of coinductive equivalences under composition (Benjamin–Markakis).
- The worry is whether the paper's `ctrf` connecting cells are oriented so that the cell in step 1 is literally the one in the `ctrf` context. Rules KE and pctrf of Def. 4.15 fix this through σCond/τCond.

## Why it matters

A type theory for higher categories with limits has to decide whether its ambient's 2-cells are pseudo or lax transformations. If CaTT_lim's universal property already forces one choice, that decides which semantics the rules can have and which constructions (hom objects, lax functor objects) they can produce.

## What would count as a solution

One of:
- a derivation of (2) in CaTT_lim;
- an identification of where the argument fails, with the correct orientation of `ctrf` cells;
- a precise statement of which enriched setting CaTT_lim's rules are sound for.
