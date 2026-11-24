# Which semistrict definitional equalities are conservative over CaTT-style theories? (round 2)

*A self-contained problem. Standard higher category theory is the only background assumed. This is the second round. The first round's prompt and its 267 responses are reproduced in the repository file `notes/conjectures/answered/semistrict-surface-conservativity-2026-11-24.md` ("Response n" below refers to them). §2 summarises what they settled. Those results are taken as known and are not re-asked.*

**What we are asking for.** For a CaTT-style theory T, whose coherence side condition is read off a family of strict free structures, and for a set S of strict laws, is T with the laws of S added as definitional equalities conservative over T for inhabitation, in every finite context and every dimension? Round 1 settled this for every S over the Gray variant CaTT_G, and for every S without interchange over CaTT. Three cases remain. We want them settled as instances of one general statement, not one context or dimension at a time:

- **(a)** associativity and units (S = {A, U}) over the theories whose side condition reads off free structures with **directed interchange at every level** (§1.3). These are the theories CaTT_E for admissible E, the least one CaTT_V included;
- **(b)** the four subsets containing interchange, {I}, {A, I}, {U, I} and {A, U, I}, over ordinary CaTT;
- **(c)** insertion (Catt_sua) over ordinary CaTT in arbitrary contexts.

## 1. Setting

### 1.1 CaTT and its strict images

**CaTT** is Finster–Mimram's type theory for weak ω-categories (arXiv 1706.02866).
- Contexts are finite computads, written as lists of typed variables.
- Types are ⋆ or `t →_A u`.
- Terms are variables or `coh_{Δ, A}[σ]`. Here Δ is a pasting context (`Δ ⊢ps`), A = `t →_B u` is a type over Δ, and σ : Γ → Δ is a substitution.
- The rule for `coh` has a side condition on (Δ, A) alone.
- There is no definitional equality: types are compared syntactically.

**Kernels.** A *kernel* 𝕋 assigns to each finite computad Γ a strict higher-categorical structure F_𝕋(Γ), free on Γ. It is functorial for substitutions of cells for generators, and it comes with a projection π : F_𝕋(Γ) → ν(λΓ) to the free strict ω-category on Γ, read as a polygraph (Steiner, *Omega-categories and chain complexes*, HHA 2004). In every kernel below, composition is strictly associative and strictly unital. Every well-typed term t over Γ has a strict image ⟦t⟧ ∈ F_𝕋(Γ):
- a variable goes to its generator;
- `coh_{Δ, A}[σ]` goes to σ_*(c), where c is the cell of F_𝕋(Δ) supplied by the side condition (below).

The theory **CaTT_𝕋** has the syntax and rules of CaTT. Its `coh` side condition is:

```
SC_𝕋(Δ, t →_A u)  :⟺  F_𝕋(Δ) has a cell c : ⟦t⟧ → ⟦u⟧ (an identity allowed)
                       whose projection has full support.
```

Support is measured in the Steiner bases of the relevant Gray-enriched or strict quotient (below). The coherence is in the *coherence case* if ⟦t⟧ = ⟦u⟧, and in the *operation case* otherwise. Three kernels are in play:

| Kernel | F(Γ) | Interchange |
|---|---|---|
| ν (ordinary **CaTT**) | ν(λΓ), the free strict ω-category | strict at every level |
| 𝔉 (the **Gray variant CaTT_G**) | the free category enriched in strict ω-categories with the lax Gray tensor | strict inside each hom; directed across objects |
| E (**CaTT_E**), for admissible E (§1.3) | F_E(Γ) | directed at every level |

For ν and 𝔉, c is unique when it exists. The operation case is then exactly "⟦t⟧ = ∂⁻τ_Δ and ⟦u⟧ = ∂⁺τ_Δ" for the total cell τ_Δ, and the coherence case is exactly "⟦t⟧ = ⟦u⟧ with full support".

### 1.2 The Gray kernel

Every pasting context decomposes uniquely as Δ = ΣΘ₁ ∨ … ∨ ΣΘₙ, with objects a₀, …, aₙ. The homs of 𝔉(Δ) are

```
𝔉(Δ)(aᵢ, aⱼ) = ν(λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ),
```

with ⊗ the Steiner–Ara–Maltsiniotis tensor and factors in execution order. For a general finite computad Γ, 𝔉(Γ) is the free such enriched category on Γ. The total cell τ_Δ is the tensor of the composites of the Θᵢ. Support is measured in the Steiner bases.

Example: over Δ = ΣD¹ ∨ ΣD¹, with α : f ⇒ f′ and β : g ⇒ g′, the coherence of type (f ◁ β) ; (α ▷ g′) → (α ▷ g) ; (f′ ◁ β) is accepted. Its reverse is not, and no term at all has the reverse type.

### 1.3 Kernels with directed interchange at every level

These kernels direct interchange along k-cells for every k, including inside homs. They are strict theories on the following signature:
- strictly associative and unital composition ∗ₖ in every dimension;
- an elementary interchanger χ for every pair of levels k < l;
- one naturality cell per varying argument, with Leibniz-signed orientation;
- higher cells between routes.

Such a theory E is **admissible** if its free objects on finite pasting diagrams satisfy five requirements:

1. They have an explicit combinatorial description by generators with explicit boundaries.
2. Two cells of the same dimension that use the same generators, counted in the expanded basis, are equal.
3. Every elementary interchanger exists, and its reverse does not.
4. Making every interchanger along a k-cell with k ≥ 1 an identity gives 𝔉(Γ). Making every interchanger an identity gives ν(λΓ).
5. They are closed under substitution of cells for generators.

The projection of §1.1 is the composite of requirement 4. For E, π denotes the first map, to 𝔉(Γ), and support is measured there. The expanded basis of F_E(Γ) is infinite already on Σ[2] ∨ Σ[2].

**Known facts about these theories** (proved elsewhere; full constructions in the repository files `notes/conjectures/answered/lax-interchange-every-dimension-r8-2026-11-20.md`, `-r9-2026-11-20.md` and `-r10-2026-11-20.md`):
- **The least theory V.** On finite pasting diagrams there is a least admissible theory V: F_V(Γ) maps generator-preservingly into F_E(Γ) for every admissible E.
- **Settings.** Two further laws change free objects on pasting diagrams: the *inner law* (crossing a composite A₁ ∗ A₂ past B equals the paste of the two crossings) and its mirror *R*. All four of V, V + R, V + inner law and V + both are admissible and pairwise distinct.
- **Decidability.** Equality and reachability in F_{V+S′}(Γ) are decidable for each of the four settings S′, in every dimension.
- **Loops.** Some free objects have non-identity endo-paths, for example a degree-4 loop H on the 2 × 2 grid with pairwise distinct powers. So c in SC_E need not be unique. The image of an operation-case coherence is a chosen lift: the first shortest witnessing path in a fixed enumeration.
- **Comparison with CaTT_G.** Every CaTT_E derivation projects to a CaTT_G derivation.
- **Interchange inside a hom.** Inside a hom, for 2-cells a, b of one object composable along a 1-cell, there are directed interchangers b ∗ a ⇛ a ∗ b and a ∗ b ⇛ b ∗ a. They are not inverse to each other. The Eckmann–Hilton cells are therefore non-invertible.

The question in (a) concerns only inhabitation. It does not depend on the choice of lift, since ≈_S below is syntactic.

### 1.4 Semistrict equalities

Write A, U and I for the associativity, unit and interchange laws:
- A: (x ∗ₖ y) ∗ₖ z = x ∗ₖ (y ∗ₖ z);
- U: 1 ∗ₖ x = x = x ∗ₖ 1, and 1_{a ∗ⱼ b} = 1_a ∗ⱼ 1_b;
- I, in whiskering form: for j-composable cells a, b of dimension > j, (a ∗ⱼ s b) ∘ (t a ∗ⱼ b) = (s a ∗ⱼ b) ∘ (a ∗ⱼ t b), together with the analogous laws for cells of unequal dimension. Here s and t are the source and target one dimension below the cells, and ∘ is composition along them. With U this is equivalent to Godement's law.

For a kernel 𝕋:
- **Words** over a pasting context Δ are terms built from variables, identities, and the binary composites that exist in CaTT_𝕋. In CaTT these are all ∗ₖ. In CaTT_G and CaTT_E they are vertical composites and whiskerings, since a horizontal composite of positive-dimensional cells across a directed interchange does not exist.
- For S ⊆ {A, U, I}, **≈_S** is the smallest congruence on terms, stable under substitution, that contains:
  - (i) w ≈ w′ for all raw-parallel words w, w′ over a pasting context that are equal in the free algebra satisfying exactly the laws in S;
  - (ii) coh_{Δ, w → w′}[σ] ≈ 1_{w[σ]} for every such pair whose coherence exists in CaTT_𝕋.
- **Published closed forms.**
  - ≡_su is Catt_su (Finster–Reutter–Rice–Vicary, arXiv 2007.08307: disc removal, endo-coherence removal, pruning).
  - ≡_sua is Catt_sua (Finster–Rice–Vicary, arXiv 2302.05303: the same with insertion).
  - They contain ≈_{U} and ≈_{A,U} respectively.

**Conservativity.** T_≈ is T plus the conversion rule: from Γ ⊢ t : A and A ≈ B, conclude Γ ⊢ t : B. T_≈ is **conservative over T in Γ** if every T-type over Γ that is inhabited in T_≈ is inhabited in T. This is the inhabitation form. We do **not** ask for T-terms ≈-equal to the given ones (see §2, item 2).

## 2. What is known (all proved or checked; not re-asked)

**1. A sufficient condition and an obstruction.**
- *Sufficient condition.* Write EL(k) at Γ for: parallel T-terms u, u′ of dimension k over Γ with u ≈ u′ are joined by T-terms e : u → u′ and e′ : u′ → u with e ≈ 1 and e′ ≈ 1. If EL(k) holds at Γ for all k < n, then T_≈ is conservative in Γ for types of dimension ≤ n. The proof is induction on derivations, whiskering level by level.
- *Obstruction.* If u ≈ u′ and some T-cell u → u′ exists but no T-term has type u′ → u, then T_≈ is not conservative in Γ.

**2. EL fails for every binary surface (Response 43).** In every nonempty finite context, in both CaTT and CaTT_G, EL_S(k) holds iff any two raw-parallel, ≈_S-equal k-terms are literally equal. So EL_S fails from rank 1 if A or U ∈ S, and from rank 2 otherwise (S = ∅ included). The sufficient condition of item 1 therefore cannot prove any positive case here. The round-1 prompt's claimed converse ("conservativity implies EL") holds only for the elaboration form, where the inhabitant must be ≈-equal to the given one. The positive results below are model-theoretic.

**3. Over CaTT_G, the classification is complete: conservative in every finite context and dimension iff I ∉ S.**
- *Subsets without I.*
  - ∅ is conservative (Response 3).
  - {A} is conservative (Response 16).
  - {U} is conservative (Response 51).
  - {A, U} is conservative (Response 222). The proof builds a model with strictly associative and unital temporal products and Kan fibrations at globular boundaries: simplicial presheaves on a site of arities with free temporal composition, then a Reedy/injective comparison and fixed-object rigidification. It uses Response 170: with strict units, top associativity generates the whole {A, U} surface.
- *Subsets with I.* Any S ∋ I fails already at ΣD¹ ∨ ΣD¹ in dimension 3, by the obstruction of item 1.
- *Context-level results for S ∋ I.*
  - Through dimension 3, the exact per-context test is that every exchange edge has a directed return path, and this test is undecidable (Response 2).
  - On globular pasting contexts, in all dimensions, conservativity holds iff I ∉ S or at most one column is active (Response 2).
  - Per-context conservativity is Π⁰₂-complete in general (Responses 13, 29, 105, 185, 218).
- *Full image equality.* Taking equality in 𝔉 as the definitional equality is **not** conservative (Response 1). In Σ(x, a : 1ₓ → 1ₓ), the suspended diagonal Eckmann–Hilton braid ΣE(a, a) and Σ1_{a∗a} have equal 𝔉-images, but no CaTT_G 5-cell joins them in either direction.

**4. Over CaTT, every S without I is conservative in every finite context and dimension.**
- ∅ (Response 3), {A} (Response 16), Catt_su and hence {U} (Response 50), and {A, U} (Response 222) are conservative.
- {A, U} is also conservative when joined with all three published strict-unit rules (Responses 170, 183, 222).

**5. Over CaTT with S ∋ I, the known results are partial, and no counterexample is known.**
- *Low dimensions.* Every S, and ≡_sua, is conservative through dimension 4 in every finite context (Response 6).
- *Restricted contexts.* All eight binary surfaces and ≡_sua (also ≡_su) are conservative:
  - on every finite 2-computad, in all dimensions (Response 10);
  - on every finite 3-computad in which no two generators of dimension ≥ 2 are spatially composable (Response 14; extended to bubble-free 2-bases with arbitrary 3-generators in Response 229);
  - through degree h + 1 when the first generator above the 2-skeleton has degree h ≥ 4 (Response 31);
  - through dimension 5 in every finite context without 1- or 2-generators (Response 33).
- *Equations on 2-dimensional data.* All ordinary binary equations on 2-dimensional data are conservative in arbitrary higher extensions. So are all ≡_sua equations on 2-dimensional data, taken separately. Their union fails on the scalar (Response 26).
- *The Eckmann–Hilton pair is not identified* (Responses 1 and 4). Let E(a, b) : a ∗₁ b → b ∗₁ a be any two-variable term for scalars a, b : 1ₓ → 1ₓ, possibly itself using conversion by ≈_{A,U,I}. Then E(a, a) and 1_{a∗a} are not ≈_{A,U,I}-equal, and no surface 4-term joins them in either direction. One proof uses a weight model: 3-cells are interpreted in (ℕ, +), the five-disc string arity has weight 1, the braid has weight ≥ 1 and the identity has weight 0. They are also not ≡_sua-equal (they have distinct Catt_sua normal forms). Even a ∗₁ b and b ∗₁ a stay distinct on the full binary surface. So Simpson's Eckmann–Hilton obstruction does **not** by itself refute any S ∋ I over CaTT. In contrast, full strict-image equality (equality in ν) fails already in dimension 4 at (x, a : 1ₓ → 1ₓ), and in dimension 5 on a single scalar 3-generator (Response 33).
- *Decidability.* Conversion for ≈_{A,U,I} is decidable on well-typed terms over every finite computad (Response 44). So is conversion for every finite insertion width (Response 202), and for strict units with binary {A, U} (Response 217).

**6. Over CaTT_E (directed interchange at every level).**
- Every S ∋ I fails, by item 1: requirement 3 leaves the reverse interchanger type empty.
- Nothing is known about {A, U}, {A} or {U} in arbitrary contexts.
- A CaTT_E-type that becomes inhabited after conversion is in particular a CaTT_G-type inhabited after conversion, hence inhabited in CaTT_G (item 3). This says nothing about inhabitation in CaTT_E, because CaTT_E has fewer terms.

**7. Semantic background.**
- Gordon–Power–Street: every tricategory is triequivalent to a Gray-category (strict associativity and units, weak interchange).
- Simpson (*Homotopy types of strict 3-groupoids*, 1998): strict units together with strict interchange cannot model all homotopy 3-types. He conjectures that strict associativity and interchange with weak units suffice.
- Joyal–Kock prove that conjecture semantically for 3-types with one object and one arrow.

## 3. Questions

**Q1 (main).** Give a uniform classification. For which kernels 𝕋 and which S ⊆ {A, U, I} is CaTT_𝕋 with ≈_S conservative over CaTT_𝕋 in every finite context and every dimension? The same question applies to ≡_sua over CaTT. By §2 this comes down to three statements, and a single argument covering several of them is preferred:

- **(a)** For every admissible E, in particular V and the three other settings, ≈_{A,U} is conservative over CaTT_E. The most general form wanted is this: ≈_{A,U} is conservative over CaTT_𝕋 for **every** kernel 𝕋 whose free structures are strictly associative and unital, are closed under substitution, and reflect the side condition through a projection as in §1.1. Does the construction of Response 222 extend? It needs a site of arities with free temporal composition. In F_E the temporal composites inside a hom also carry directed exchanges, and c need not be unique.
- **(b)** Over CaTT, decide conservativity for {I}, {A, I}, {U, I} and {A, U, I}. By downward closure it suffices to settle {A, U, I}, and {A, I} and {U, I} if it fails. {A, I} is Simpson's case. No conjecture is offered, because the expected Eckmann–Hilton counterexample is ruled out (§2, item 5).
- **(c)** Over CaTT, is Catt_sua (≡_sua) conservative in every finite context? Is the join of ≡_sua with ≈_{A,U,I} non-conservative in some context, given that it fails on the scalar on 2-dimensional data (Response 26)?

**Q2.** Where any part of Q1 fails, determine exactly which contexts it holds in, and give a minimal counterexample (context, dimension and type). Say whether conservativity in an individual context is decidable for that surface, and if not, its complexity.

**Q3 (fallback, only if Q1 is out of reach).** For (b) and (c), settle conservativity through dimension 6 in every finite context. Dimension 4 is known (Response 6), and dimension 5 is known in the restricted classes of §2, item 5. For (a), settle it on all pasting contexts in every dimension, and through dimension 4 in every finite context.

## 4. What counts as a solution

For each of (a), (b) and (c): a proof valid in every finite context and every dimension, or a counterexample, meaning a context Γ and a CaTT_𝕋-type over Γ that is inhabited after conversion but not before. A counterexample's non-inhabitation should come with an invariant (a model of CaTT_𝕋, as in Responses 1 and 4) that can be checked by hand or by a short program. A proof for (a) may be stated for a class of kernels containing every admissible E. In that case, say which of the five requirements it uses.

## 5. Literature (searched 2026-11-22 and 2026-11-24)

- Finster–Reutter–Rice–Vicary (arXiv 2007.08307) prove Catt_su conservative over Catt for terms over pasting diagrams. Finster–Rice–Vicary (arXiv 2302.05303) define Catt_sua. Rice's thesis (arXiv 2502.17068, Ch. 4) gives partial rehydration over pasting contexts and discusses obstructions in generic contexts. None of these proves or conjectures conservativity in arbitrary contexts.
- Chanavat–Hadzihasanovic (arXiv 2507.00146) use top associativity in globular operations (cited in Response 16).
- No published treatment of CaTT-style theories with directed interchange at every level was found. For directed interchange inside homs, Gepner–Heine's oriented categories are the closest semantic setting.

## Researcher Response 1

**The join in Q1(c) is conservative on a finite ordinary 2-computad exactly when its free strict 2-category has no nonidentity cell from an empty path to itself.** This decides the mathematical criterion simultaneously in all output dimensions. On these inputs Q2 recognition for the join is $\Pi^0_1$-complete under computable many-one reductions, even on one object with no generating scalar. In every failing 2-computad there is a failure in output dimension four, the least possible by round-1 Response 26. The same criterion applies to strict units alone joined with the single elementary binary interchange square (including its head equation), and to every intermediate surface up to the join in Q1(c).

**From a bubble to a raw boundary.** Write a positive empty-to-empty history at $x$ as a succession of $m>0$ positioned 2-generator events. Every nonidentity strict 2-bubble has such a spelling by planar serialization. Realize it by a raw term $b:1_x\to1_x$. Whisker the indicated generator by the words on either side of each step. Fit its raw 1-source and 1-target to chosen bracketings of the two edge words by composing with rebracketing and unit comparisons in their line arities, in the required directions. Use the literal $1_x$ at both ends. These comparisons have zero generating 2-events, so the composite still has $m$. This construction also works when the given raw attachment of a 2-generator uses unbiased 1-heads: compare its spelling to the chosen path by the raw line-arity lifting of round-1 Responses 2 and 4, then substitute the edges.

Let $E$ be Rice’s raw two-variable Eckmann–Hilton term. The old type
\[
               E(b,b)\longrightarrow 1_{b *_1 b}
\]
is inhabited in the join by converting an identity. Indeed the square calculation of round-1 Response 26 is a judgement with a free scalar variable, so substitute the raw term $b$ into that judgement. For raw non-inhabitation, use the list model of round-1 Response 1. Give each generating 2-cell one bead, all of the same colour, and send every 1-cell to the unique arrow. Both sides of each 2-attachment have that arrow as value. The evaluation of $b$ is a list of length $m$: a whiskered event contributes one and the path comparisons contribute zero. To calculate the generic $E$ on two such lists, first use distinct colours for the $2m$ positions. The only colour-preserving bijection to the list in the other block order exchanges the blocks, preserving the internal orders. Recolouring them all alike leaves the permutation of positions unchanged. The identity fixes all positions and the model has only identity 4-cells. This excludes a raw filler in either direction. In particular no assumption on connectedness of the chosen history or on distinct generator labels is necessary. [List model and raw braid](../answered/semistrict-surface-conservativity-2026-11-24.md#researcher-response-1) · [Generic joined calculation](../answered/semistrict-surface-conservativity-2026-11-24.md#researcher-response-26)

**Converse.** On a bubble-free finite 2-polygraph the comparison from its free weak realization to its free strict realization is an equivalence by the repository’s dimension-two homotopy-polygraph theorem. Passing from raw attaching 1-terms to their edge words preserves the free realization by the path comparison before each 2-attachment, as in round-1 Response 10. Thus the raw comparison is a weak equivalence. At *specified parallel raw faces* a strict filler lifts: local essential surjectivity in the iterated hom at those faces gives a raw filler with equivalent strict value. The target is gaunt (edge length and 2-event count are additive and it has only identities above two), so that value equals the given value. Objects are the declared vertices. Every derivation in the join evaluates in the strict target, since each of its equations holds there, so this lifts a filler at every old type inhabited in the join. This direction applies to any strict-sound conversion. It uses the repository’s verified dimension-two comparison, including the mesh-model inputs identified in its verification. [Dimension-two comparison](../answered/homotopy-polygraphs-2026-11-19.md#followup-2) · [Application to raw computads](../answered/semistrict-surface-conservativity-2026-11-24.md#researcher-response-10)

**Complexity.** Enumerating finite positioned rewrite histories semidecides failure. For hardness, take a positive semi-Thue reachability instance $u\Rightarrow^*v$. On one object use the letters as edges, add two fresh edges $L,R$, and adjoin $\epsilon\to LuR$ and $LvR\to\epsilon$ to the original rules. A successful derivation between the given words yields a positive bubble. Conversely take the first death in any positive closed history. The matched pair of markers it consumes was created by one birth: before that first death births insert balanced pairs and interior rules cannot touch markers. No surviving nested birth is possible between the two adjacent-in-marker-order letters of this pair at death. Thus its interior changed from $u$ to $v$ by ordinary rules alone. The hardness input is the effective halting reduction to positive word reachability, not merely undecidability: one may use nonempty configuration words containing endmarkers and a state, rules simulating one tape step, and a halting-state cleanup that absorbs adjacent letters one at a time down to a fresh singleton. These rules have nonempty sides. This proves the claimed completeness and makes recognition undecidable on arbitrary finite contexts as well. In arbitrary rank enumerability of raw and joined derivations gives the general $\Pi^0_2$ upper bound; the exact unrestricted complexity does not follow here. [Guarded reduction, item 3](../answered/homotopy-polygraphs-2026-11-19.md) · [Halting reduction, Theorem 23.4](https://www.cs.utexas.edu/~ear/cs341/automatabook/AutomataTheoryBook.pdf)

**Reproduce.** Run `python3 tools/semistrict_surface_join_bubbles.py`. The solver compares bounded empty-to-empty search against an independent finite transitive closure for 128 guarded word problems, including nested and adjacent guarded blocks in the search space. It replays the 79 positive histories and computes their block permutations by adjacent exchanges. With `--rice-dir /path/to/catt-strict` and a release build, Rice also checks the raw diagonal at $b=(1_x\xrightarrow{u}f\xrightarrow{d}1_x)$ and its strict-unit conversion to the specialized square. The additional elementary square equation is the mathematical step above. With `--input data.json --width N` the solver searches a supplied 2-computad and returns a history and a separating permutation. A negative bounded result excludes histories only up to that width. The two surfaces individually remain conservative on all these inputs by round-1 Response 10. [Solver](../../../tools/semistrict_surface_join_bubbles.py) · [Rice’s raw term](https://github.com/alexarice/catt-strict/blob/577993375ec7491b1b50c07dc58a0595c5fd58fc/examples/eh.catt)

## Researcher Response 2

Every admissible kernel inherits Gray conservativity for the interchange-free binary surfaces through degree three in arbitrary finite contexts. On a pasting context with at most one active outer column, including the suspension of an arbitrary tree, conservativity holds in every degree and raw inhabitation at a pair of faces is exactly strict reachability.

### Transport from a quotient that first identifies parallel cells in degree three

Write $q_P:F_E(P)\to\mathfrak F(P)$ for the first quotient in requirement 4. An elementary interchanger along a $k$-cell first exchanges two $(k+2)$-cells and has dimension $k+3$. Killing those for $k\ge1$ therefore does two things in dimensions at most three. It preserves the entire 2-truncation and induces a surjection on 3-cells at **every prescribed pair of 2-faces**. Indeed its first relations identify parallel 3-cells. Such a quotient neither identifies lower cells nor makes new tuples of 3-cells composable since their incidence data have dimension at most two. Relations from higher cells have parallel lower boundaries. This argument only concerns the quotient presentation. It needs neither normal forms for paths nor uniqueness of a 3-cell with given faces.

Consequently the two *raw* languages have identical typing through degree three on common declarations. Induct on a Gray typing derivation in this range. For a degree-three head, lift its generic Gray witness by the surjection. Its 2-faces are the required interpreted generic terms by the 2-truncation isomorphism. Its projection is the original Gray witness, so it passes exactly the stipulated support test. For a lower head use the isomorphism itself. Then use the same raw substitution. Choices between different lifts in degree three cannot affect this induction, since the head test only compares faces through degree two. Variables use their declared types. The converse is projection. Higher declarations in the ambient context can be ignored here since a raw term of degree at most three uses only declarations through that degree. This follows from fullness after ordinary projection, which bounds the height of each head arity by its output degree. The zero-dimensional judgment returns a vertex directly.

Given an old $E$-type of degree at most three inhabited after interchange-free binary conversion, project its derivation to the corresponding Gray surface as in §1.3. Gray conservativity gives a raw Gray term at that very type, and the raw typing comparison returns the term at the original $E$-type. Degree three is the last degree for which this argument needs only the isomorphism below the first quotient relations. In degree four the boundary can prescribe a particular representative of a quotient 3-cell. This transfer uses requirement 4, the dimensions of the interchangers and the projected head test.

### An all-degree test on the support of the strict witness

Write $p$ for ordinary strict projection from Gray. Use the strict interpretation of the interchange-free surface in $F_E$. For clarity, the binary operations in this interpretation are the stipulated compositions, whiskerings and identities on words. An $A,U$ word equation therefore has equal strict values. For clause (ii) the identity on this value is the coherence-case witness. Indeed a Gray endomorphism on a pasting arity is an identity by strong loop-freeness of its Steiner homs, so if a loop passes the projected fullness test then its identity has the same projection and passes too. For an operation-case head make the given choice on its bound arity at the interpreted strict boundary, and evaluate a head application by substituting into that chosen cell. In particular one need not choose a shortest path anew after substitution. Induction on formation and conversion gives soundness: equal interpreted boundaries give the same choice on the same bound arity, and evaluating a substituted application composes the two substitutions. This argument uses the interpretation of the word constructors as the named strict operations in §1, and requirement 5.

Let $P$ be any pasting context, let $u,v$ be literal parallel $E$-terms there, and suppose $c:\llbracket u\rrbracket\to\llbracket v\rrbracket$ in $F_E(P)$. Take the positional support $K\subseteq P$ of $p q_P c$, including the faces of its generators. It is a pasting tree, possibly a point. Take the raw retraction $r:P\to K$ which clamps the outer spine to its occupied interval and does the same recursively in the traversed columns. Off the interval it uses iterated identities. If $q_K(r_*c)$ has full Gray support on $K$, there is a raw term $u\to v$ in $P$.

To prove this, every generic $E$-head uses every position of its ordinary strict arity. In fact its Gray projection has full support by the head test. In each traversed Gray tensor, augmenting all factors but one sends a basis element in that factor tensored with stationary vertices to the specified basis element. Full closed tensor support gives full closed support in every factor projection, by the image-of-support lemma. The single-column and point cases are immediate. Under an ordinary strict labelling the support of the resulting paste is the union of the closed supports of the labels it uses. Thus raw term induction shows that all generating variables of either old face, including their dependencies, lie in $K$. Both faces restrict literally to $K$; equivalently, clamping acts there as the identity. Apply the $E$-head test over $K$ at these restricted raw faces, with witness $r_*c$, and weaken its head along $K\subseteq P$. The resulting term has the prescribed raw type. Its selected strict value need not be $c$. [Positional support and the tensor projections](../answered/semistrict-surface-conservativity-2026-11-24.md#researcher-response-4) · [Raw clamping substitution](../answered/semistrict-surface-conservativity-2026-11-24.md#researcher-response-27)

In particular the test succeeds if at most one outer column of $K$ contains a generator of dimension at least two in global degree. On each occupied hom all other tensor factors are units. The Gray-to-ordinary projection there is the unit isomorphism, including for closed support. Since $p q_K(r_*c)$ uses exactly $K$, its Gray lift has full support. If $P$ itself has at most one active outer column this holds for every $K$. Strict interpretation of any proposed surface inhabitant now gives the required $c$, establishing conservativity on $P$ in all degrees. More precisely, at any old pair of faces on such a $P$, **both** inhabitation questions are exactly strict reachability in $F_E(P)$. The four decidable settings of §1.3 hence give a decision at those faces. There is no bound on the number of active columns *inside* the one outer column. Requirements 1–3 are not used by the support argument. The argument uses the given Gray quotient and substitution, and the stated special-case decision uses the reachability theorem.

**Validation.** The raw clamping substitutions above depend only on variables and iterated identities. The arity-retraction checker constructs and verifies them for all 258 distinct strict-cell supports on trees through four edges. Its generated Gray substitutions typecheck in Agda with `--safe`. This checks the literal source and target types of the retractions. The quotient and support arguments above establish the conclusions for arbitrary admissible kernels. [Arity-retraction checker](../../../tools/semistrict_surface_exact_boundary.py)
