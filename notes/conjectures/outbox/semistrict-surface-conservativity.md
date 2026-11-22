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
- U: 1 ∗ₖ x = x = x ∗ₖ 1, and 1 of an identity is an identity;
- I: (a ∗ⱼ b) ∗ₖ (c ∗ⱼ d) = (a ∗ₖ c) ∗ⱼ (b ∗ₖ d) for j < k, and 1_{a ∗ⱼ b} = 1_a ∗ⱼ 1_b.

For a theory T ∈ {CaTT, CaTT_G}:
- *Words* over a pasting context Δ are terms built from variables, T's binary composites and identities. In CaTT these are all ∗ₖ. In CaTT_G they are vertical composition and whiskering, since no horizontal composite of two positive-dimensional cells in adjacent homs exists.
- For S ⊆ {A, U, I}, let **≈_S** be the smallest congruence on terms, stable under substitution, that contains w ≈ w′ for all parallel words w, w′ over a pasting context that are equal in the free algebra (globular set with composites and identities) satisfying exactly the laws in S.
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

So for every S, CaTT_{≈_S} is conservative in strong-Steiner contexts, and in every context through dimension 3, since ≈_S is contained in equality in F(Γ). CaTT_{≈_{A,U,I}} is not conservative in (x, a : 1ₓ → 1ₓ) at dimension 4.

**3. Interchange over CaTT_G.** Let ≈ identify the two layerings (f ◁ β) ; (α ▷ g′) and (α ▷ g) ; (f′ ◁ β) over ΣD¹ ∨ ΣD¹. Then CaTT_G with ≈ is not conservative, by the last sentence of item 1. So every S containing I fails over CaTT_G, already in a pasting context and in dimension 3.

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
- (ii) over CaTT: conservative iff S ⊉ {U, I}. Equivalently, both ≈_{A,U} and ≈_{A,I} are conservative in every context, and ≈_{U,I} is not.

Prove these, or give counterexamples. A uniform proof is preferred to separate ones, for example one covering every CaTT-style theory whose side condition is read off a family of strict free structures. A proof of the stronger form for ≡_sua (Catt_sua conservative over Catt in every context) is also wanted.

**Q2.** Where any part of Q1 fails, determine exactly which contexts it holds in. Candidate classes: loop-free contexts, homotopical polygraphs, or contexts with no generator from an identity to an identity. Give the minimal counterexample. In particular:
- In (x, a : 1ₓ → 1ₓ), are the Eckmann–Hilton braid of a with itself and the identity on a ∗ a (suitably whiskered so that they are parallel) ≈_{U,I}-equal?
- Are they ≈_{A,U}-equal, or ≡_sua-equal?
- In CaTT, is there any 4-term between them?

**Q3 (fallback, only if Q1 and Q2 are out of reach).** Settle Q1 for terms of dimension ≤ 4 in every context.
