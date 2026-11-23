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

## Researcher Response 2

Through dimension three, the Gray surface is conservative in every finite context iff $I\notin S$. For an **individual** context and $I\in S$, the exact test through dimension three is whether every elementary exchange has a directed return path in the graph defined below. This property is undecidable on finite contexts. On **globular pasting contexts** there is a simpler classification in **all** dimensions.

### Ordered 2-paths and prescribed boundaries

In the following, an edge path is a word in the 1-generators of the context, including its initial vertex. A step is a triple $(l,a,r)$ of a left edge path, a 2-generator and a right edge path. It replaces $l\,s(a)\,r$ by $l\,t(a)\,r$, using the flattened attaching paths. An ordered 2-path is a composable list of steps with a specified starting path. Empty whiskers, empty attaching paths, repeated variables and empty lists are allowed. The two whisker lengths distinguish different positions even in a path with repeated edges.

Fix two exterior edge paths. Form a directed graph on the ordered 2-paths between them. Its elementary edges are the following replacements, closed under adding edge paths on the left and right and adding unchanged lists of steps before and after.

1. Apply a declared 3-generator to its ordered source list to obtain its ordered target list.
2. Exchange two steps acting on horizontally separate factors, in the direction of the Gray square in the Setting. The middle edge path between the factors may be empty. Two scalar steps at the same cut are allowed as consecutive factors with empty attaching paths.

These are the endpoints of the generating 3-cells of the free lax Gray structure. One way to see the presentation is to build its homs in increasing dimension. In hom dimension one the tensor supplies a step in one factor with objects in the other factors. This gives whiskering and concatenation, so the ordered lists are the actual 2-cells. In hom dimension two a generator either comes from one factor or from a pair of hom arrows in different factors. The latter has the two boundary walks of the directed square. Subdividing either arrow factors its exchange into elementary squares. Whiskering and pasting generate the edges in context and their paths. Equations between parallel pastes do not affect reachability. For the ordinary strict image, quotient the lists by exchanges in both directions. Thus reachability of ordinary strict 3-cells between two represented lists is precisely reachability in the same graph with both orientations of exchange. Indeed, any two representatives of a strict 2-cell differ by elementary exchanges, which can be inserted at each interface of a paste. [Forest–Mimram, §2.3](https://members.loria.fr/SForest/articles/forest-rewriting-2021.pdf) · [Ara et al., §4.1](https://arxiv.org/abs/2312.00429)

**Lifting lemma.** Given parallel raw Gray 2-terms $T,U$, a kernel 3-term $T\to U$ exists iff there is a directed path from the list of $T$ to that of $U$. In particular an empty directed path lifts at *any* such pair of boundaries with the same list, in both directions, with identity strict image.

*Proof.* Strict interpretation gives necessity. For the empty-path assertion use the following normalization, keeping the raw exterior 1-terms fixed. A structural 2-term is one containing no 2-variable. Each such term lies over a single walked edge path $w$ and pulls back from the linear pasting context with one edge per position of $w$. To see this, lift the arguments of its outer head by induction. The 1-arguments in each column occupy the same subinterval because any intervening structural 2-argument has identity strict image. Consecutive columns concatenate their subintervals. This also specifies positions for empty subpaths. It lifts the substitution with common faces, including when the original path revisits a vertex. Both faces traverse the entire lifted path. Consequently any two parallel structural 2-terms have identity-image comparisons in both directions over that line. Write $K(p,q)$ for the structural 2-cell between any two writings of $w$ obtained by substituting into the line coherence. These constructions include the point when $w$ is empty.

Up to identity-image 3-cells in both directions, every raw 2-term is a vertical string of structural factors and 2-variables individually whiskered by 1-terms. Here the Gray head condition is important. A 2-dimensional operation has total hom degree one, so precisely one column is a vertical string of 2-discs and all other columns are single arrows. A coherence-case 2-head has an arity of dimension at most one, since its full image is a 1-cell. For the operation, whisker the successive generic 2-variables by the outside arrows with fixed bracketing. At the two ends use structural comparisons $K$ to the declared endpoints. This expression and the generic head are parallel with the same full Gray image, so the arity gives both comparisons. Substitute and apply induction to the arguments. Distribute each remaining 1-whisker over a vertical product using the same comparison on a whiskered vertical pair of discs. Comparisons can be pasted inside these expressions by whiskering a 3-cell. Vertical rebracketings have the two identity-image comparisons over a vertical string. This proves the assertion by induction and retains the **order** of all steps.

For each $w$ fix a bracketing $b(w)$. For one step $(l,a,r)$, take the line of $l$, a fresh 2-disc $Z$, and the line of $r$ in succession. On this arity choose the canonical bracketed whiskering of $Z$, then substitute $a$ for $Z$ and the actual edges for the line variables. Pad at both ends by $K$ to obtain a factor between $b(l\,s(a)\,r)$ and $b(l\,t(a)\,r)$. Every iterated whiskering of $a$ with these path labels is comparable to that chosen factor with exterior padding. Indeed, before substituting $a$, lift its whiskers positionally to the two lines, treating the entire source and target of $a$ as the two formal edges of the disc. Compare the two whiskerings with matched endpoints on this arity, where their ordered image uses every position. After substitution any two ways of joining the resulting structural end factors are comparable over the expanded edge paths by the structural case above. This argument also handles a scalar, because the two formal edges of its disc remain distinct until substitution.

Joining the chosen factors in list order, with $K$ at the exterior endpoints, now gives a single writing for any list at prescribed raw 1-boundaries. Replace each individual factor by its comparison and combine adjacent structural factors over their common path. This joins every raw writing to the chosen one in both directions. These are the positional and single-generator steps of the ordinary two-dimensional normalization. The arities just checked ensure that each comparison used here has identity **Gray** image. [Positional lifting and normalization, Steps 1–3](../../relative-coherence.md#2-theorem-a-rc2-in-every-context)

For a graph edge use the declared variable or the generic directed square, whiskering by the indicated paths. A middle path in an exchange can be absorbed into the whisker of the first step. To extend an edge by a prefix or suffix of steps, choose their writings at matching raw 1-boundaries and whisker the 3-cell vertically by those 2-terms. At an interface where 1-writings differ, pad source and target of the 3-cell together by the same structural $K$'s along cut one. This gives representatives of the required two lists at any prescribed common exterior 1-boundaries. Join equal lists by the empty-path assertion, both between consecutive edges and at $T,U$. Composition gives the required kernel term. ∎

### Consequences for the classification

If $I\notin S$, the free Gray image interprets the surface. The binary word laws in $S$ hold there, and a head between such equal words has identity image over its pasting arity. A surface inhabitant of an old 3-type therefore supplies directed reachability, and the lifting lemma supplies a kernel inhabitant. Together with Response 1 and Known 3, this gives the universal classification through dimension three.

If $I\in S$, **conservativity through dimension three at $\Gamma$ holds iff every exchange edge has a directed return path**. For necessity choose the raw lifted endpoints of an elementary square. Conversion supplies its reverse in the surface by (i). Whisker this reverse for an exchange in context and use the equal-list comparisons to meet any prescribed original boundaries. Kernel inhabitation of this old type implies a directed return path. For sufficiency interpret the surface in the ordinary strict image as in Response 1. A resulting strict 3-cell gives a graph path with exchanges in either direction. Replace each backward exchange with a directed return path and apply the lifting lemma. Dimensions below three are covered by Response 1.

**Undecidability of the individual-context test.** Take a finite string rewriting system with nonempty rule sides and two nonempty words $u,v$. Start with the path $x\xrightarrow f y\xrightarrow g z$ and two 2-generators $a:f\to f$, $b:g\to g$. In the hom across the path denote the whiskered letters by $L=a\mathbin{▷}g$ and $R=f\mathbin{◁}b$. The basic directed square is $RL\to LR$. On the single raw 1-term $k=f *_0 g$, adjoin 2-endomorphisms for the alphabet and two fresh marker letters $m,n$. For each string rule adjoin one 3-generator between bracketed vertical spellings on $k$. Finally adjoin the 3-generators

$$
 LR\longrightarrow m u n,\qquad m v n\longrightarrow RL .
$$

All these endpoints are literally parallel on $k$.

There are no nonidentity exterior 1-whiskers on a letter from $x$ to $z$. The only basic exchange of generating steps is $RL\to LR$. All its contextual instances have return paths exactly when this basic one does. From the word $LR$, the only possible first move toward $RL$ is the start rule. Inside the two markers only the string rules can act before the finish rule. The finish rule requires the *entire* intervening word to be $v$, and its application reaches $RL$. Thus the test answers yes exactly when $u\to^* v$. Taking both orientations of the relations of a finitely presented semigroup gives the undecidable word problem. This concerns even signatures with an acyclic generating 1-graph and no generator with identity source or target. [Post, *Recursive Unsolvability of a Problem of Thue*](https://doi.org/10.2307/2267170)

### Exact answer on globular pasting contexts, in all dimensions

Call column $i$ of $P=ΣΘ_1\vee\cdots\veeΣΘ_k$ active if $Θ_i$ has positive dimension. The Gray surface is conservative in $P$ **iff $I\notin S$ or at most one column is active**.

For the positive direction use the globular boundary-lifting theorem for the Gray kernel over a pasting arity. It lifts a strict cell at any prescribed parallel raw faces, without assuming a support-factorization lemma for arbitrary substitutions. For $I\notin S$, interpret the inhabitant in the Gray image and lift it at the original boundary. For at most one active column, the map from that Gray image to the ordinary strict image is an isomorphism. On each forward hom the tensor-to-product comparison has only tensor-unit factors apart from possibly one factor. It is the identity under the unit isomorphisms. Endomorphism homs are points and backward homs are empty in both structures. Interpret now in the ordinary strict image for any $S$, use the inverse isomorphism, and lift at the original boundary. [Pasting-arity lifting theorem and its proof](../answered/relative-coherence-all-dimensions-r9-2026-11-20.md#a-directed-interchange-theory)

For the negative direction choose a generating 2-cell in each of two active columns. Whisker across the intervening columns by one chosen 1-edge per column so that the two cells are horizontally composable. Substitute them in the square of Known 3. To exclude a reverse, send $P$ into the **strict** free Gray square. In either selected factor $Θ_i$, cut the ordered vertices across the chosen generating arrow. Map vertices before the cut to 0, the remaining vertices to 1, and each edge to its unique possible image in the interval. Every higher generator maps to an iterated identity since its parallel faces have the same image. The chosen arrow maps to the nonidentity interval arrow. Collapse all other columns to identity 1-cells at the appropriate square vertex. Freeness gives a strict enriched map. It sends the specialized boundary to the original two walks of the square, whose reverse is impossible in its Steiner complex. Conversion by $I$ inhabits that reverse. The least failing pasting context by number of declarations is therefore $ΣD^1\vee ΣD^1$, with three objects, four arrows and two 2-cells. Each active column requires at least the two arrows and one 2-cell of a suspended interval. [Square orientation and coefficient obstruction](../../../src/CaTTExp/Strict/ReverseInterchanger.agda)

**Validation.** On every ordered pasting tree through eight edges, the tensor-chain test checked the cut projections on generators against the signed boundary, including inactive columns between the selected factors. All 1,597 choices of column pair and cuts hit all nine basis elements of the square, with 55,395 generator checks. The reachability reduction agreed with direct string rewriting on 3,600 pairs of words in four finite length-preserving systems. Rice's weak checker accepted the literal return type and the composite of a start cell, a marker-whiskered rewrite, and a finish cell in the one-rule instance. The unbounded assertions follow from the lifting and reduction proofs above.

The outstanding arbitrary-context cases include dimension four for CaTT and for interchange-free Gray surfaces. The pasting-context theorem and the dimension-three test do not decide those cases or arbitrary-context conservativity for insertion.

## Researcher Response 3

**For both kernels, $S=\varnothing$ is conservative in every finite context and every dimension.** Clause (ii) is present even for this subset. The proof gives a sufficient condition for adding equations to a cellular theory of this form. It uses the repository's model-structure theorem for the two kernels and boundary lifting **on pasting arities**. There is no strict-image lifting assumption on the context where conservativity is asserted.

### Comparing two interpretations of the heads

Write $H_P$ for the kernel model freely generated by the globular arity $P$, and $C_P$ for its strict image regarded as a kernel model. Write $D_n$ for the free globe model and $B_n$ for its boundary. The model-category inputs are as follows.

- The maps $B_n\to D_n$ generate the cofibrations. Every kernel model is fibrant.
- $H_P\to C_P$ is a globular trivial fibration. A weak equivalence into $C_P$ is a trivial fibration provided it is surjective on objects. Indeed the target has only identity coinductive equivalences, so the equifibration tests extend by identity data on the given lift. In the directed case use the same test in each fixed hom and lift the global identity equivalences at objects. The forward strict homs are strong Steiner and the endomorphism homs are terminal.

These inputs are results about the original kernels. [Model structures and their generating maps](../answered/catt-models-unit-condition-r5-2026-11-20.md#researcher-response-1) · [Ordinary arity lifting, §3(2)](../answered/relative-coherence-all-dimensions-r10-2026-11-21.md) · [Directed arity lifting](../answered/relative-coherence-all-dimensions-r9-2026-11-20.md#a-directed-interchange-theory)

Suppose a surface has an interpretation on the objects $H_P$ that fixes globes and globular inclusions, preserves globular sums, and sends substitutions to composition. This means its generic terms are interpreted as actual kernel terms over their arities, with translated faces, and its equations hold literally under the interpretation. Suppose further that on the kernel each generic head has its original strict image. Call this second action on the kernel $e$, and write $e^*Y$ for a kernel model $Y$ with its operations interpreted by $e$. Its underlying globular set is the same. The assumed interpretation gives $e^*Y$ a surface action. Under these conditions the surface is conservative.

To prove the criterion, build cylinders on the *representing globes*. Inductively let $J_{B_n}$ be the union of the cylinders already chosen for the faces of $D_n$, with $J_{B_0}$ initial. Factor the fold to $D_n$ as

$$
 L_n= J_{B_n}\amalg_{B_n\amalg B_n}(D_n\amalg D_n)
       \ \lhook\joinrel\longrightarrow J_n
       \ \overset{\sim}{\twoheadrightarrow} D_n
$$

by a cofibration and a trivial fibration. On a globular arity or boundary $P$, glue these objects along its generating globes to obtain $J_P$, with two endpoint maps $H_P\to J_P$ and fold $J_P\to H_P$. The fold is a weak equivalence. In detail, the globe diagrams for $J$ and $H$ have latching maps that are cofibrations. For $J$ factor the latching inclusion through $L_n$, adjoining two globes at their boundaries before the indicated cofibration. Both colimits along the finite cellular filtration therefore compute homotopy colimits, and the globe folds are weak equivalences. The same argument applies to $B_n$. In particular each one-ended inclusion

$$
 J_{B_n}\amalg_{B_n}D_n\longrightarrow J_n
$$

is a trivial cofibration. It is a cofibration by adjoining the other end and using $L_n\to J_n$. The map from $D_n$ into its domain is a pushout of the corresponding endpoint $B_n\to J_{B_n}$, a trivial cofibration by the fold equivalence and the two-end cofibration construction. Its composite into $J_n$ is also a weak equivalence by the globe fold. This proves the one-ended assertion, including $n=0$.

The composite $J_P\to H_P\to C_P$ is a weak equivalence surjective on objects, hence a trivial fibration by the inputs above. Give $J$ an action of the *raw* kernel theory with the original interpretation at one end and $e$ at the other. For a generic $n$-head over $P$, its previously interpreted faces specify a map from $J_{B_n}$ to $J_P$. The original and translated head at the two ends extend this to $L_n\to J_P$. Below this map use $J_n\to D_n\to C_P$, where the second arrow classifies the strict head. The lifting square commutes on the ends by strict-image agreement and on the faces by induction. Lift against $J_P\to C_P$ along $L_n\to J_n$. Choose once per generic head, in the cellular order. Application to a substitution is then composition of maps. This makes both endpoints natural for all kernel substitutions and preserves the strict projection, which is the inductive assertion needed for later faces.

For any kernel model $Y$, the sets of maps $J_n\to Y$ now form a kernel model $M(Y)$. A label on a pasting arity is a map from its globular sum $J_P$, and the chosen head maps act by precomposition. Restriction to the ends gives strict kernel maps

$$
                    Y\ \longleftarrow\ M(Y)\ \longrightarrow\ e^*Y .
$$

**Both maps lift cells at prescribed boundaries.** Such a lifting problem is precisely an extension from $J_{B_n}\amalg_{B_n}D_n$ to $J_n$ into the fibrant object $Y$.

Take $Y$ free on the original context. Lift its tautological variable assignment into $M(Y)$ along the left projection, one declaration at a time. The right projection gives an assignment of the context in the surface model. Evaluate a proposed surface inhabitant there. For an old type its exact boundary already has a lift in $M(Y)$, given by the lifted variable assignment and the old kernel term operations. Lift the inhabitant along the right projection **at that boundary**, then apply the left projection. The resulting cell in $Y$ is a kernel term of the original type. This proves the criterion without normalizing the declarations of the context.

### Applying the criterion to the empty set of word laws

Strict evaluation interprets this surface. On each pasting arity, define its second interpretation recursively. Given the already interpreted generic boundary $p,q$ and the designated strict cell $c$, choose a lift in $H_P$ along $H_P\to C_P$, using the same choice for the same arity, interpreted boundary and strict value. When $p=q$ and $c$ is an identity, prescribe the actual kernel identity $1_p$ as the lift. This prescription handles the identity constructor itself. On globular variables use the generators. For an application, first use the chosen generic lift and then substitute the interpreted arguments. The recursion is on the head's boundary expressions and its arguments, so also applies to heads whose boundaries were typed using conversion. Strict evaluation of the interpreted expression is the original designated value, by the substitution lemma.

In the free word algebra with no laws, equal words have identical constructor trees with identical variable labels. Thus (i) holds. For (ii) the two interpreted generic endpoints agree, and the designated strict cell between them is an identity. The prescribed lift followed by substitution gives exactly the interpreted identity on the substituted word. Equality is preserved under congruence because the choices depend only on the interpreted generic data, and under substitution because applications use composition. Induction on formation and conversion now validates the whole interpretation, including conversion inside arguments. It meets the criterion for either kernel. ∎
