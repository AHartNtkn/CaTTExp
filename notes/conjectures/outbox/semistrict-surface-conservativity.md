# Which semistrict definitional equalities are conservative over CaTT and over its Gray variant?

## Setting

**CaTT** is Finster–Mimram's type theory for weak ω-categories (arXiv 1706.02866).
- Contexts are finite computads, written as lists of typed variables.
- Types are ⋆ or `t →_A u`.
- Terms are variables or `coh_{Δ, A}[σ]`. Here Δ is a pasting context (`Δ ⊢ps`), A = `t →_B u` is a type over Δ, and σ : Γ → Δ is a substitution.
- The rule for `coh` has a side condition on (Δ, A) alone.
- There is no definitional equality: types are compared syntactically.

**Strict images.** For a context Γ, let F(Γ) be the free strict ω-category on Γ, read as a polygraph. Every well-typed term t has an image ⟦t⟧ ∈ F(Γ):
- a variable goes to its generator;
- `coh_{Δ,A}[σ]` goes to σ_*(c), where c ∈ F(Δ) is:
  - the top cell of F(Δ), if A is full and of dimension dim Δ (an "operation");
  - the identity on ⟦t⟧, if ⟦t⟧ = ⟦u⟧ with full support (a "coherence").

In F(Δ), a pasting diagram, c is unique.

**The Gray variant CaTT_G.**
- Every pasting context decomposes uniquely as Δ = ΣΘ₁ ∨ … ∨ ΣΘₙ, with objects a₀, …, aₙ.
- Let 𝔉(Δ) be the free category on Δ enriched in strict ω-categories with the lax Gray tensor. Its homs are
  `𝔉(Δ)(aᵢ, aⱼ) = ν(λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ)`,
  with ν and λ as in Steiner (*Omega-categories and chain complexes*, HHA 2004) and ⊗ the Steiner–Ara–Maltsiniotis tensor.
- For a general finite computad Γ, 𝔉(Γ) is the free such enriched category on Γ.
- CaTT_G has the syntax and rules of CaTT, except that the `coh` side condition is read off 𝔉(Δ). The head (Δ, t → u) is accepted iff one of the following holds:
  - ⟦t⟧ = ∂⁻τ_Δ and ⟦u⟧ = ∂⁺τ_Δ, where the total cell τ_Δ is the tensor of the composites of the Θᵢ;
  - ⟦t⟧ = ⟦u⟧, and its support in the Steiner bases is everything.
- In 𝔉, composition is strictly associative and unital. Interchange inside one hom is strict. The interchanger of two cells in adjacent homs is a non-invertible generator.
- Example: over Δ = ΣD¹ ∨ ΣD¹, with α : f ⇒ f′ and β : g ⇒ g′, the coherence of type (f ◁ β) ; (α ▷ g′) → (α ▷ g) ; (f′ ◁ β) is accepted, and its reverse is not. No term at all has the reverse type.
- Strict images ⟦t⟧ ∈ 𝔉(Γ) are defined as for CaTT.

**Semistrict equalities.** Write A, U and I for the associativity, unit and interchange laws of ω-categories:
- A: (x ∗ₖ y) ∗ₖ z = x ∗ₖ (y ∗ₖ z);
- U: 1 ∗ₖ x = x = x ∗ₖ 1, and 1_{a ∗ⱼ b} = 1_a ∗ⱼ 1_b;
- I, in whiskering form: for j-composable cells a, b of dimension > j, (a ∗ⱼ s b) ∘ (t a ∗ⱼ b) = (s a ∗ⱼ b) ∘ (a ∗ⱼ t b), where s, t are the source and target one dimension below the cells and ∘ is composition along them, together with the analogous laws for cells of unequal dimension. In the presence of U this is equivalent to Godement's law (a ∗ⱼ b) ∗ₖ (c ∗ⱼ d) = (a ∗ₖ c) ∗ⱼ (b ∗ₖ d); unlike Godement's law it can be stated in CaTT_G, which has no horizontal composite.

For a theory T ∈ {CaTT, CaTT_G}:
- *Words* over a pasting context Δ are terms built from variables, T's binary composites and identities. In CaTT these are all ∗ₖ. In CaTT_G they are vertical composition and whiskering, since no horizontal composite of two positive-dimensional cells in adjacent homs exists.
- For S ⊆ {A, U, I}, let **≈_S** be the smallest congruence on terms, stable under substitution, that contains (i) w ≈ w′ for all parallel words w, w′ over a pasting context that are equal in the free algebra (globular set with composites and identities) satisfying exactly the laws in S, and (ii) coh_{Δ, w → w′}[σ] ≈ 1_{w[σ]} for every such pair whose coherence exists in T (a coherence between S-equal words is an identity).
- Two published closed forms:
  - ≡_su: Catt_su, Finster–Reutter–Rice–Vicary, arXiv 2007.08307 (disc removal, endo-coherence removal, pruning);
  - ≡_sua: Catt_sua, Finster–Rice–Vicary, arXiv 2302.05303 (disc removal, endo-coherence removal, insertion).

  They contain ≈_{U} and ≈_{A,U} respectively.

**T_≈ and conservativity.** Let T_≈ be T plus the conversion rule: from Γ ⊢ t : A and A ≈ B, conclude Γ ⊢ t : B. T_≈ is *conservative over T in Γ* if every T-type over Γ that is inhabited in T_≈ is inhabited in T.

## Known

**1. Reduction to relative coherence.**

Let ≈ satisfy the following:
- it is an equivalence on terms and types;
- it is a congruence for the term formers, and stable under substitution;
- it does not change the side condition;
- it is invertible on arrow types: arr A t u ≈ arr A′ t′ u′ implies A ≈ A′, t ≈ t′ and u ≈ u′;
- it preserves dimension;
- it is compatible with whiskering: if p ≈ 1 and q ≈ 1, then p ∗ⱼ x ∗ⱼ q ≈ x.

Let **EL(k) at Γ** be the statement: for all parallel T-terms u, u′ of dimension k over Γ with u ≈ u′, there are T-terms e : u → u′ and e′ : u′ → u with e ≈ 1_u and e′ ≈ 1_{u′}.

Then the following are equivalent, provided EL(< n) also holds at every pasting context of dimension ≤ n:
- (a) T_≈ is conservative over T in Γ for types of dimension ≤ n;
- (b) EL(k) holds at Γ for all k < n.

Proof sketch:
- (b) ⇒ (a): induction on T_≈-derivations. The only nontrivial step moves a term to a ≈-equal type. It does so by whiskering with the cells given by (b), level by level, starting from the lowest boundary where the types differ.
- (a) ⇒ (b): convert the identity 1_u : u → u to the type u → u′.

The same argument shows the following. If u ≈ u′ and some T-cell u → u′ exists, but no T-term has type u′ → u, then T_≈ is not conservative in Γ.

**2. Relative coherence for full strictness in CaTT.** These results are unpublished; proofs are available. Here ≈ is equality in F(Γ).
- EL(1) and EL(2) hold in every context. EL(0) is trivial.
- EL(n) holds for every n in every finite strong-Steiner (strongly loop-free) context, pasting contexts included.
- EL(3) **fails** in the context (x, a : 1ₓ → 1ₓ). The obstruction is Eckmann–Hilton.

So for every S, CaTT_{≈_S} is conservative in strong-Steiner contexts, and in every context through dimension 3, since ≈_S is contained in equality in F(Γ). CaTT with full image equality is not conservative in (x, a : 1ₓ → 1ₓ) at dimension 4. Whether ≈_{A,U,I} and ≈_{U,I} identify the obstructing pair is part of Q2.

**3. Interchange over CaTT_G.** Let ≈ identify the two layerings (f ◁ β) ; (α ▷ g′) and (α ▷ g) ; (f′ ◁ β) over ΣD¹ ∨ ΣD¹. Then CaTT_G with ≈ is not conservative, by the last sentence of item 1. The whiskering form of I contains this identification, so every S containing I fails over CaTT_G, already in a pasting context and in dimension 3.

**4. Literature on ≡_su and ≡_sua.**
- Catt_su is conservative over Catt for terms over pasting diagrams (Finster–Reutter–Rice–Vicary).
- For Catt_sua, "partial rehydration" over pasting contexts is in Rice's thesis (arXiv 2502.17068, Ch. 4). The thesis also discusses obstructions to rehydration in a generic context.
- Neither source proves or conjectures conservativity in arbitrary contexts.

**5. Pasting contexts for CaTT_G** (argued, not yet independently checked). For ≈ equal to equality in 𝔉, EL holds in every pasting context. A coherence-case coherence over the variables of u connects u and u′. This needs the variables of a term over a pasting context to form a pasting sub-context on which the term has full support.

**6. Semantic background.**
- Gordon–Power–Street: every tricategory is triequivalent to a Gray-category, which has strict associativity and units and weak interchange.
- Simpson (*Homotopy types of strict 3-groupoids*, 1998) shows that strict units together with strict interchange cannot model all homotopy 3-types, by an Eckmann–Hilton argument. He conjectures that strict associativity and interchange with weak units suffice.
- Joyal–Kock prove the semantic form of that conjecture for 3-types with one object and one arrow.

## Questions

**Q1 (main): the classification.** For each T ∈ {CaTT, CaTT_G} and each S ⊆ {A, U, I}, decide whether T_{≈_S} is conservative over T in every finite context and every dimension.

Conservativity is downward closed in S, so it suffices to settle the maximal cases. After Known 2 and 3, the conjectured answer is:
- (i) over CaTT_G: conservative iff I ∉ S. Equivalently, ≈_{A,U} is conservative in every context. A sharper form: parallel CaTT_G-terms with equal images in 𝔉(Γ) are connected, in both directions, by terms whose images are identities, in every context.
- (ii) over CaTT: conservative iff S ⊉ {U, I}. Equivalently, both ≈_{A,U} and ≈_{A,I} are conservative in every context, and ≈_{U,I} is not (the last is expected from Eckmann–Hilton but not yet established; see Q2).

Prove these, or give counterexamples. A uniform proof is preferred to separate ones, for example one covering every CaTT-style theory whose side condition is read off a family of strict free structures. A proof of the stronger form for ≡_sua (Catt_sua conservative over Catt in every context) is also wanted.

**Q2.** Where any part of Q1 fails, determine exactly which contexts it holds in. Candidate classes: loop-free contexts, homotopical polygraphs, or contexts with no generator from an identity to an identity. Give the minimal counterexample. In particular:
- In (x, a : 1ₓ → 1ₓ), are the Eckmann–Hilton braid of a with itself and the identity on a ∗ a (suitably whiskered so that they are parallel) ≈_{U,I}-equal?
- Are they ≈_{A,U}-equal, or ≡_sua-equal?
- In CaTT, is there any 4-term between them?

**Q3 (fallback, only if Q1 and Q2 are out of reach).** Settle Q1 for terms of dimension ≤ 4 in every context.

## Researcher Response 1

The sharper Gray conjecture in Q1(i) fails. Its counterexample lives entirely in one hom, one dimension above the CaTT scalar counterexample. For Q2, the choice of a raw braid matters. For Rice's explicitly typed diagonal braid, the answers to the three equality questions are **no** for `≈_{U,I}`, **no** for `≈_{A,U}`, and **no** for `≡_sua`. There is no CaTT 4-cell in either direction. The first answer uses the restriction to **binary** words in the definition above.

### The diagonal calculation

Fix the raw term $E(a,b)$ defined as `eh` in [Rice's implementation](https://github.com/alexarice/catt-strict/blob/577993375ec7491b1b50c07dc58a0595c5fd58fc/examples/eh.catt). It has type $(a *_1 b)\to(b *_1 a)$ in CaTT itself. Put $B=E(a,a)$ and $J=1_{a *_1 a}$. The outer constructor of $B$ is the unbiased composite of a string of **five** 3-cells. This is a single CaTT operation. Its arity survives substitution of the second scalar by the first.

**Lemma.** For the congruences generated by (i) and (ii), $B\not\approx_{A,U,I} J$.

**Proof.** Give each 3-variable a weight in the additive monoid of natural numbers. Evaluate a 3-dimensional head applied to a substitution by summing the weights of the arguments at the 3-variables of its arity. Add one more if the arity is the vertical string of five 3-discs. This definition ignores the head type except for dimension. At dimensions below three take a singleton, and above three take a unique cell for every parallel pair of boundaries. Thus equations at higher dimensions can be checked at their boundaries. Equivalently one can evaluate just the 3-dimensional expressions at every assignment of weights. The substitution lemma follows by induction, since evaluating a substituted argument gives its value at the induced assignment. Changing a head type by congruence preserves its arity and dimension.

On the signature of words this evaluation is the strict globular algebra with one lower cell, 3-cells in the commutative monoid, and the indicated unique higher fillers. In dimension three each binary composite adds the contributions of its 3-dimensional slots, a whiskering carries its one such slot, and an identity contributes zero. Hence every equation (i) holds, including all the interchange equations. For (ii) in dimension three the endpoints are 2-words with the same strict image. A coherence-case head on such endpoints has no 3-variable in its arity, by fullness. An operation-case head on a three-dimensional pasting diagram cannot have these endpoints. Its total 3-cell has distinct strict 2-faces. Indeed its nonzero top chain has nonzero boundary in the loop-free basis (a first negative face cannot cancel). Thus the left side of (ii) has weight zero, as does the identity. In lower dimensions both values are forced, and in higher dimensions the already verified boundary equations give equality by uniqueness. This proves soundness for the generated congruence.

The value of $B$ is at least one, whereas $J$ has value zero. Downward closure gives the two claimed word-congruence inequalities. This invariant concerns **definitional equality**. An ordinary CaTT 4-cell can relate terms of different weight, since the weight interpretation admits a 4-cell between any parallel weights. ∎

For the published insertion theory there is a separate normal-form proof. Normalize the two terms *after* diagonal substitution. The normal form of $B$ is the swap head over two adjacent 2-discs applied to the two arguments $a,a$. Its generic source and target still perform the two steps in opposite orders. The normal form of $J$ is the identity on the binary vertical composite. These distinct normal forms decide the inequality by confluence and termination. The calculation can be reproduced by importing `eh` and running the following two commands with `catt_strict --sua` at the revision linked above. The weak checker also accepts both terms at the common type before normalization. [Rice, §§4.4.4 and 4.5](https://arxiv.org/pdf/2502.17068)

```text
normalise eh(x,a,a) in (x : *) (a : id(x) -> id(x))
normalise id(comp[a,a]) in (x : *) (a : id(x) -> id(x))
```

For the 4-cell question, evaluate first with two different singleton colours in the list model of [relative coherence, §3, item 20](../answered/relative-coherence-all-dimensions-r10-2026-11-21.md). Choose the ordinary input order for binary vertical composition. Any interpretation of the typed term $E(a,b)$ must take the list $[r,b]$ to $[b,r]$ by a colour-preserving bijection. There is exactly one, the transposition. Recolour both letters alike. Naturality in recolourings leaves the permutation of positions unchanged. The identity has the identity permutation, and the model has only identity cells above permutations. This excludes both orientations of a CaTT 4-cell. This argument applies to every uniform two-variable braid of this type, independently of its outer constructor.

### A single-hom counterexample to the sharper Gray statement

There is a boundary-preserving interpretation of **kernel** Gray terms in kernel CaTT that can be chosen to fix suspensions of CaTT terms. Here is the construction, including the action on heads whose arguments subsequently land in a single hom.

On a globular pasting arity $P$, there is a projection $p_P:\mathfrak F(P)\to F(P)$. Read the strict target as Gray-enriched via the canonical tensor-to-cartesian map, and extend the identity assignment of generators by freeness. In particular the projection sends cross-hom interchangers to identities. Suppose the generic endpoints $u,v$ of a Gray head have already been interpreted as parallel CaTT terms with the projected strict images. The projected generic cell has precisely those images as faces. The globular boundary-lifting property of $\mathrm{Free}_{\mathrm{CaTT}}(P)\to F(P)$ gives a CaTT term with the *prescribed weak endpoints* and that strict image. This invokes lifting only over a globular pasting arity. Fix one such term for each head. Interpret a head application by substituting the translated arguments into its fixed term. Induction then gives typing, commutation with substitution, and the strict-image assertion, since both composites on strict images are the maps induced by the same assignment on generators. [Pasting-arity lifting, §3, item 2](../answered/relative-coherence-all-dimensions-r10-2026-11-21.md)

For a suspended CaTT head over $P=ΣΘ$, there is just one tensor factor. Its hom and its projected hom are both the free strict ω-category on $Θ$. The CaTT operation condition and full-support identity condition there admit the suspended head in the Gray kernel. In the construction above choose that very suspended CaTT head as its lift. Induction from variables now fixes every suspended CaTT term. In particular a Gray filler between two such terms, even one using heads with several tensor factors, would give a CaTT filler between them.

Take the suspension of the scalar context, with objects $s,t$, arrow $f:s\to t$, and 3-generator $z:1_f\to1_f$. The terms $ΣB,ΣJ$ are parallel 4-terms. Their Gray images are equal because the hom from $s$ to $t$ is free strict on the scalar computad, where both are the identity on the square of the scalar. Explicitly there are no generating cells above that scalar in this hom. But the two terms admit no Gray 5-cell in either direction. Such a cell would translate as above, and the same two-colour proof in the list model with lists in dimension three excludes the translated CaTT 5-cell. This also gives an old type newly inhabited by conversion for **full Gray-image equality**, by converting an identity. The argument does not give that conversion for the smaller $≈_{A,U}$.

### Scope of the obstruction

The generic swap itself *does* collapse by (ii) for $I$, already before any specialization. Rice's weak braid and its strictly unital normal form therefore cannot be interchanged freely in a proof about $≈_{U,I}$. The weight lemma isolates a specific step where that argument fails. Even a proof using only binary padding would need to check parallelism. Over the generic 2-disc $d:f\Rightarrow g$, the right whiskering of $d$ by an identity has endpoints $f *_0 1,g *_0 1$, while $d$ has endpoints $f,g$. They cannot be used directly as a pair of parallel CaTT words in (i).

There is also a dimension bound on the Gray obstruction. For **every** $S$ and finite $\Gamma$, conversion is conservative over the Gray kernel for types of dimension at most two. Interpret the surface in the free *ordinary strict* ω-category on the declarations of $\Gamma$, interpreting each attaching term before adjoining its generator. Every allowed Gray head has its projected generic cell there, and the strict interpretation respects (i) and (ii). For (ii) the projected generic cell is an endomorphism over an ordinary globular pasting arity, hence an identity by loop-freeness. This interpretation also works at a converted head boundary: its source and target have their prescribed strict images. It follows that a new inhabitant would give a strict cell between the original boundaries.

In dimension zero an object is a vertex. In dimension one any strict path lifts by composing its generating edges, using the identity for an empty path. In dimension two write the strict cell as a vertical string of generating 2-cells whiskered by paths of edges. This presentation follows by induction on strict compositions, expanding a horizontal composite by interchange. Whisker each corresponding Gray variable by chosen path terms. To join successive steps, or meet either prescribed boundary, one must connect two weak 1-terms with the same edge path. A weak 1-term parses as a tree of path composites and identities, including unbiased path operations and unary disc operations. It factors through the linear pasting context of its flattened path by assigning a separate position to each occurrence of an edge, including positions at vertices for empty subpaths. This follows by concatenating the positional lifts of the arguments at each path operation. Both lifted terms traverse the whole line, so the full-support Gray coherence connects them in either direction, including on the point for an empty path. Substitute back and compose the steps. This proves the bound even for a strict identity 2-cell, in which case only the boundary comparison is needed. Thus three is the least possible type dimension of the Gray failures for $I\in S$.

The classification for the binary congruences still lacks the arbitrary-context positive cases and a CaTT counterexample for $\{U,I\}$ or $\{A,U,I\}$. The Gray cases containing $I$ have the dimension-three counterexample of Known 3. The exact classes of contexts, arbitrary-context conservativity for insertion, and the remaining dimension-four cases of Q3 are unresolved here.
