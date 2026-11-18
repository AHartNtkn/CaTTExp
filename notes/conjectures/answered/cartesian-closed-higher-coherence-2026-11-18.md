# Are free cartesian closed (∞,1)-categories 1-categories? Soundness of Mimram's higher pasting criteria

*A self-contained problem. No knowledge of the project that posed it is assumed. The cleanest question is Question 1. Questions 2–3 are the concrete type-theoretic statements it would settle.*

## Background

**Pasting types.** Mimram (*An unbiased simply typed combinatory logic*, CSL 2026) singles out a decidable class of simple types (with →, ×, 1), the **pasting types**, each with exactly one inhabitant up to βη (his Theorem 15).

A type is first normalized by the type isomorphisms of Bruce–Di Cosmo–Longo to A₁ × … × Aₙ with each Aᵢ implicational. Each Aᵢ must then be derivable as Θ \ ∅ | ∅ ⊢ Aᵢ by:

```
Θ \ (Θ′, tgt A) | Γ, A ⊢ B   (tgt A ∉ Θ′)         Θ \ Θ′ | Γ, Δ ⊢ A₁  …  Θ \ Θ′ | Γ, Δ ⊢ Aₙ
────────────────────────────────────────         ───────────────────────────────────────────
Θ \ Θ′ | Γ ⊢ A → B                                Θ \ Θ′ | Γ, (A₁→…→Aₙ→X), Δ ⊢ X
```

Here tgt A is the rightmost variable of A. A type theory with a constant for each pasting type and an equality rule identifying all terms of a pasting type is equivalent to the simply typed λ-calculus with products modulo βη (his Theorems 19 and 21).

**Higher dimensions.** The paper says an "easy variant", with dependent and identity types, should axiomatize cartesian closed ∞-categories, meaning (∞,1). It also says the corresponding criterion is implemented in the tool cccatt but left for future work.

A context may contain:
- objects;
- 1-cells f : A → B between types;
- higher cells α : s → t between parallel terms one dimension down.

A goal is a type of some dimension.

## The two criteria in the tool

Source: github.com/smimram/cccatt, `src/pasting.ml`, commit 69bb11af, 2026-11-15.

**(Rev), for (∞,1).**
1. While possible, pick a hypothesis α of dimension ≥ 2 with a variable endpoint x and other endpoint t, such that:
   - x ∉ FV(t);
   - x occurs in no other hypothesis's type;
   - x has not been rewritten before.

   Delete α and substitute x := t.
2. Then strip the goal's higher layers and require its underlying 1-type to be pasting in the remaining 1-dimensional context.

If this succeeds, every goal of every dimension over these data is accepted, in both directions.

**(Dir), directed.** For a goal of dimension n:
1. The n-dimensional hypotheses must be cells x → y between variables, with:
   - no loops;
   - distinct sources and distinct targets;
   - an acyclic relation.
2. Let the source context be the context without the targets of these cells, and the target context the context without their sources. Check both, recursively, against the goal's (n−1)-type.
3. The goal's source term must avoid targets, and its target term must avoid sources.

There is no fullness condition. With no n-dimensional hypotheses, every parallel pair of terms of a pasting (n−1)-type gets an n-cell in both directions.

## Questions

1. **(Discreteness.)** Let S be a set, or more generally a directed graph. Is the free cartesian closed (∞,1)-category on S equivalent to the free cartesian closed 1-category on S? Equivalently, are its mapping spaces discrete?
   - For comparison, the free symmetric monoidal (∞,1)-category on a set is ⊔ₙ Sⁿ_{hΣₙ}, whose mapping spaces are discrete. So the analogous statement holds there for formal reasons.
   - The analogous statement for weak ω-categories on a graph is also known to hold: the free weak ω-category on a graph is the free category.
   - For cartesian closed structure no formula of that kind is available.
2. **(Soundness of Rev.)** Assuming a positive answer to 1: is every goal accepted by (Rev) uniquely fillable, up to a contractible space, in the free cartesian closed (∞,1)-category on the context?
   - The contraction step adjoins a cell together with its free endpoint, which should be a trivial extension in any (∞,1)-setting. So 2 should reduce to 1 together with Mimram's Theorem 15. Is this reduction correct?
3. **(Soundness of Dir.)** Let 𝒞 be the free cartesian closed (∞,ω)-category, with pseudo exponentials (Map(A × B, C) ≃ Map(A, C^B) as mapping (∞,ω)-categories), on a finite computad of the shape above. Does every goal accepted by (Dir) have a contractible space of fillers, invertible when the goal has no top-dimensional hypotheses?
   - **Smallest open case:** dimension 3 over a graph (no hypotheses of dimension ≥ 2). Are any two parallel 2-cells between βη-equal 1-terms connected by a unique invertible 3-cell? This is coherence for free cartesian closed tricategories.

## What is known

- **Dimension 1:** Mimram, Theorems 15, 19 and 21. His Agda proof postulates Theorem 15.
- **Dimension 2 over a graph:** Fiore–Saville, *Coherence for bicategorical cartesian closed structure* (MSCS 31(7), 2021; LICS 2020). In the free cartesian closed bicategory on a graph there is at most one 2-cell between parallel 1-cells, and every cartesian closed bicategory is biequivalent to a 2-category with 2-categorical cartesian closed structure. This settles (Dir) in dimension 2 without 2-dimensional hypotheses: terms of a pasting 1-type are βη-equal, hence related by a unique invertible 2-cell. See also Saville's thesis (arXiv 2007.00624).
- **No coherence result is known** for cartesian closed tricategories, cartesian closed (∞,1)-categories, or cartesian closed (∞,ω)-categories.

## What counts as a solution

- A proof or a counterexample for Question 1: for instance, a non-trivial loop in a mapping space of the free cartesian closed (∞,1)-category on one object.
- A proof of 2 or 3, or a counterexample: an accepted goal with two inequivalent fillers, or with none.
- A reference proving coherence for cartesian closed tricategories, or the discreteness in 1.

# Researcher Response

**Question 1 has a positive answer for a set or an ordinary directed graph.** A proof follows from simplicial presheaf models and a retract argument. It also proves **Rev as stated**, and settles the **graph-generated case of Question 3**, including its three-dimensional case, for cartesian closed higher categories defined by the stated pseudo universal properties.

The general abstract Dir criterion with higher-dimensional generators is not settled by this argument. **The unordered implementation at the cited commit has a separate, executable counterexample.**

I did not find the exact discreteness statement presented as a theorem in the literature. The argument below is a deduction from the cited results.

## 1. Discreteness of the free cartesian closed \((\infty,1)\)-category

Write \(\mathbf{CCC}_\infty\) for the \(\infty\)-category of small cartesian closed \(\infty\)-categories and functors preserving finite products and exponentials. Mapping spaces in \(\mathbf{CCC}_\infty\) use natural equivalences between such functors.

For a directed graph \(G\), let \(\operatorname{Int}_G(\mathcal C)\) be the space of interpretations of its vertices and edges in \(\mathcal C\). Thus the intended freeness condition is
\[
\operatorname{Map}_{\mathbf{CCC}_\infty}(F_\infty(G),\mathcal C)
\simeq
\operatorname{Int}_G(\mathcal C).
\tag{1}
\]

### 1.1. A strict simplicial model lemma

**Lemma.** Every small cartesian closed \(\infty\)-category \(\mathcal C\) admits a cartesian closed equivalence
\[
e:\mathcal C\simeq N_{\mathrm{hc}}\mathcal D,
\]
where \(\mathcal D\) is a small simplicial category with Kan mapping simplicial sets and enriched terminal object, products, and exponentials satisfying their universal properties by **isomorphisms of simplicial sets**.

In particular, the ordinary category \(\mathcal D_0\), whose morphisms are the \(0\)-simplices of the enriched homs, is cartesian closed.

**Proof.** First, the Yoneda embedding
\[
y:\mathcal C\longrightarrow\mathcal P(\mathcal C)
\]
preserves finite products and exponentials. For exponentials, evaluate at \(X\in\mathcal C\):
\[
\begin{aligned}
\bigl((yB)^{yA}\bigr)(X)
&\simeq
\operatorname{Map}_{\mathcal P(\mathcal C)}
       (yX\times yA,yB)\\
&\simeq
\operatorname{Map}_{\mathcal C}(X\times A,B)\\
&\simeq
\operatorname{Map}_{\mathcal C}(X,B^A)\\
&=y(B^A)(X).
\end{aligned}
\]
These equivalences are natural in \(X\), so the canonical comparison
\[
y(B^A)\longrightarrow (yB)^{yA}
\]
is an equivalence.

Choose a small simplicial category \(\mathcal A\) presenting \(\mathcal C\), and put
\[
\mathcal M=[\mathcal A^{\mathrm{op}},\mathbf{sSet}],
\]
using enriched functors. Equip \(\mathcal M\) with the injective model structure. Its weak equivalences are objectwise weak homotopy equivalences; its cofibrations are monomorphisms. Consequently, every presheaf is cofibrant. This is a simplicial model category. These statements are HTT Proposition A.3.3.2 and Remark A.3.3.4; the presheaf case is also stated explicitly by Kapulkin–Szumiło, Theorem 5.1. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HTT.pdf?utm_source=chatgpt.com)

The enriched presheaf category is simplicially cartesian closed. One reference covering this exact enriched setting is Shulman’s Corollary 8.29, together with Definition 6.1. [arxiv.org](https://arxiv.org/pdf/1904.07004?utm_source=chatgpt.com)

Its injective model structure is cartesian: pushout products are computed objectwise, where the required cofibration and weak-equivalence assertions hold in simplicial sets. Therefore exponentiation by any presheaf is right Quillen. It follows that:

- the terminal presheaf is fibrant;
- products of fibrant presheaves are fibrant;
- \(Q^P\) is fibrant whenever \(Q\) is fibrant.

Thus the full simplicial category \(\mathcal M^{\mathrm f}\) of fibrant presheaves has Kan homs and actual enriched products and exponentials.

Moreover,
\[
N_{\mathrm{hc}}(\mathcal M^{\mathrm f})
\simeq
\mathcal P(\mathcal C).
\]
The comparison between enriched diagram categories and \(\infty\)-categorical functor categories is HTT Proposition 4.2.4.4; Remark 4.2.4.5 explicitly permits the injective model structure. [math.ias.edu](https://www.math.ias.edu/~lurie/papers/HTT.pdf?utm_source=chatgpt.com)

Compose Yoneda with this equivalence. Take the full simplicial subcategory \(\mathcal D\subseteq\mathcal M^{\mathrm f}\) on the images of all objects of \(\mathcal C\), together with their closure under chosen terminal object, binary products, and exponentials.

This is a small simplicial category. Every presheaf added during closure is equivalent to a representable presheaf, by the Yoneda calculation above. Hence
\[
\mathcal C\longrightarrow N_{\mathrm{hc}}\mathcal D
\]
is fully faithful, essentially surjective, and cartesian closed. This proves the lemma. \(\square\)

### 1.2. The retract argument

Let
\[
F=F_\infty(G),
\qquad
C=F_1(G),
\]
where \(C\) is the ordinary free cartesian closed category.

Freeness of \(F\) supplies a cartesian closed comparison
\[
q:F\longrightarrow NC
\]
extending the generating graph.

Apply the lemma to \(F\):
\[
e:F\simeq N_{\mathrm{hc}}\mathcal D.
\]

The images of the generating vertices and edges define an ordinary graph interpretation in \(\mathcal D_0\): an edge of \(N_{\mathrm{hc}}\mathcal D\) is a \(0\)-simplex of the corresponding enriched hom. Ordinary freeness therefore gives a cartesian closed functor
\[
s_0:C\longrightarrow\mathcal D_0.
\]

Regard \(C\) as a simplicial category with discrete homs. Then \(s_0\) gives a simplicial functor and hence a cartesian closed \(\infty\)-functor
\[
s:NC\longrightarrow N_{\mathrm{hc}}\mathcal D.
\]
It preserves the \(\infty\)-categorical products and exponentials because the enriched universal properties in \(\mathcal D\) are actual isomorphisms.

Now \(e\) and \(sq\) have equivalent restrictions to \(G\). Applying **the full freeness condition (1)** gives
\[
sq\simeq e.
\]
Consequently, with
\[
r=e^{-1}s:NC\longrightarrow F,
\]
we have
\[
rq\simeq\operatorname{id}_F.
\tag{2}
\]

For each \(A,B\in F\), equation (2) makes
\[
\operatorname{Map}_F(A,B)
\]
a homotopy retract of the discrete space
\[
\operatorname{Hom}_C(qA,qB),
\]
with endpoints transported along the equivalence \(rq\simeq\operatorname{id}_F\).

A homotopy retract of a \(0\)-truncated space is \(0\)-truncated: on every positive homotopy group, the identity factors through zero. Therefore
\[
\boxed{\operatorname{Map}_F(A,B)\text{ is }0\text{-truncated for all }A,B.}
\]

One can also identify the comparison itself. The composite
\[
qr:NC\longrightarrow NC
\]
is an ordinary cartesian closed endofunctor, and its restriction to \(G\) is isomorphic to the identity interpretation. Ordinary free-CCC uniqueness gives
\[
qr\simeq\operatorname{id}_{NC}.
\tag{3}
\]
Here uniqueness is used up to natural isomorphism: the isomorphism on generators extends recursively over \(1\), products, and exponential types; naturality then follows by induction on the generating terms.

Equations (2) and (3) prove
\[
\boxed{F_\infty(G)\simeq N F_1(G).}
\]

This applies to a set of generating objects by taking \(G\) to have no edges.

### 1.3. Existence does not need to be an additional assumption

The preceding proof can be supplemented with an existence argument.

The \(\infty\)-category of cartesian closed \(\infty\)-categories equipped with an interpretation of \(G\) is locally small and complete. Limits are created in \(\mathbf{Cat}_\infty\): products and exponentials of compatible families are computed pointwise. For example, their universal property follows by taking the limit of
\[
\operatorname{Map}(X_i,B_i^{A_i})
\simeq
\operatorname{Map}(X_i\times A_i,B_i).
\]

The object \(NF_1(G)\) is **weakly initial** in this category. Given an interpretation \(G\to\mathcal C\), replace \(\mathcal C\) by the strict simplicial model from the lemma, interpret the ordinary free syntax in its underlying ordinary category, and transport back. This proves existence of an extension without assuming uniqueness.

Nguyen–Raptis–Schrade, Proposition 2.3.2, says that a locally small complete \(\infty\)-category with a small weakly initial set has an initial object. Apply it to the singleton consisting of \(NF_1(G)\). The resulting initial object is \(F_\infty(G)\), and the retract argument identifies it with \(NF_1(G)\). [arxiv.org](https://arxiv.org/pdf/1803.01664?utm_source=chatgpt.com)

### 1.4. The extension needed for Rev

The same argument applies to a **simply typed signature**: generating types together with generating arrows whose domains and codomains are expressions built using \(1,\times,\Rightarrow\), with no imposed equations.

In the strict simplicial model, evaluate those type expressions using the chosen operations and interpret the generating arrows between the resulting types. The ordinary term model then supplies \(s_0\), and the rest of the proof is unchanged. The canonical product and exponential comparison equivalences identify this interpretation with the given one on the signature.

Thus the remaining one-dimensional context in Rev need not have only atomic domains and codomains.

## 2. Rev as stated is sound

There are two steps: eliminating each contractible extension, then using discreteness.

### 2.1. Eliminating a free endpoint is an equivalence

Suppose a contraction removes
\[
x:T,\qquad \alpha:x\longrightarrow t,
\]
where \(t:T\) is independent of \(x\), and the remaining declarations satisfy the independence condition in your formulation.

Fix an interpretation of the remaining context in a cartesian closed \(\infty\)-category. Let \(X\) be the space of possible interpretations of \(x\), with its lower boundary fixed. The space of extensions by \(x,\alpha\) is
\[
\sum_{x\in X}\operatorname{Path}_X(x,t).
\tag{4}
\]
This space is contractible, with distinguished point \((t,\operatorname{refl}_t)\). Reversing the orientation gives the equally contractible space
\[
\sum_{x\in X}\operatorname{Path}_X(t,x).
\]

Hence restriction along the contraction induces an equivalence on interpretation spaces in every target. By the universal property of the free constructions, the free cartesian closed \(\infty\)-categories before and after contraction are equivalent.

Repeating the contractions gives
\[
F_\infty(\Gamma)\simeq F_\infty(\Gamma_{\mathrm{red}}),
\]
where \(\Gamma_{\mathrm{red}}\) is the remaining one-dimensional signature.

This establishes the proposed reduction semantically. It does not require choosing a preferred inverse for \(\alpha\).

### 2.2. Pasting uniqueness becomes contractibility

Write the remaining term context and underlying one-dimensional goal as
\[
z_1:T_1,\ldots,z_m:T_m\vdash T.
\]
The one-dimensional pasting test applies, after the stated normalization, to the curried type
\[
T_1\Rightarrow\cdots\Rightarrow T_m\Rightarrow T.
\]

Mimram’s Theorem 15 gives exactly one \(\beta\eta\)-class of inhabitants. Equivalently, the corresponding goal in the ordinary free cartesian closed category on the remaining signature has exactly one inhabitant. [lix.polytechnique.fr](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_cccatt.pdf?utm_source=chatgpt.com)

By Section 1, the corresponding space of inhabitants in the free cartesian closed \(\infty\)-category is \(0\)-truncated. Its set of connected components is a singleton, so that space is contractible.

Every higher goal over it specifies an iterated path space with fixed endpoints. Iterated path spaces of a contractible space are contractible. Transporting through the contraction equivalence proves:
\[
\boxed{\text{Every goal accepted by the stated Rev criterion has a contractible filler space.}}
\]

This proves your proposed reduction, including existence and higher uniqueness.

**Source qualification.** The implementation is not literally the Rev algorithm in the question. In [`pasting.ml` at `69bb11af`](https://github.com/smimram/cccatt/blob/69bb11af/src/pasting.ml), the relevant check is
```ocaml
not (List.exists (fun (_,a) -> has_fv r a) l)
```
where `r` names the higher hypothesis being eliminated, rather than its endpoint `x`. It also accumulates substitutions without rewriting the remaining hypothesis types at each step. The proof above establishes the mathematical criterion you stated; certification of that exact implementation additionally requires accounting for transport of declarations whose types mention the eliminated endpoint.

## 3. The graph-generated case of Dir follows too

Here use the usual weak higher-categorical interpretation of cartesian closed structure: products and exponentials have universal properties given by equivalences of mapping higher categories.

For such a higher category \(\mathcal C\), let \(R_1\mathcal C\) retain all objects and \(1\)-cells and retain only invertible cells above dimension \(1\). Its mapping spaces are
\[
\operatorname{Map}_{R_1\mathcal C}(A,B)
=
\bigl(\mathcal C(A,B)\bigr)^{\simeq}.
\]

The inclusion of \((\infty,1)\)-categories into \((\infty,n)\)-categories has this \(1\)-core as right adjoint. A precise reference is Ozornova–Rovelli–Walde, Theorem 2.20, with the description of its arrows in Lemma 2.23 and Remark 2.24. [arxiv.org](https://arxiv.org/pdf/2603.11005?utm_source=chatgpt.com)

### 3.1. The core inherits cartesian closed structure

Apply maximal groupoid to the exponential equivalence:
\[
\mathcal C(X\times A,B)\simeq\mathcal C(X,B^A).
\]
This gives
\[
\operatorname{Map}_{R_1\mathcal C}(X\times A,B)
\simeq
\operatorname{Map}_{R_1\mathcal C}(X,B^A).
\]
The product and terminal universal properties pass to the core in the same way.

Thus \(R_1\mathcal C\) is cartesian closed, with the same chosen product and exponential objects. The inclusion
\[
R_1\mathcal C\longrightarrow\mathcal C
\]
preserves those structures.

The core adjunction therefore restricts to cartesian closed functors. To check this restriction, observe that the comparison maps for products and exponentials are the same \(1\)-cells on either side, and \(R_1\) preserves and reflects their being equivalences.

### 3.2. Freeness on a graph transfers across the core adjunction

Let \(I\) denote the inclusion of \((\infty,1)\)-categories into higher categories. For a higher cartesian closed \(\mathcal C\),
\[
\begin{aligned}
\operatorname{Map}_{\mathbf{CCC}_{\mathrm{higher}}}
   (I F_\infty(G),\mathcal C)
&\simeq
\operatorname{Map}_{\mathbf{CCC}_\infty}
   (F_\infty(G),R_1\mathcal C)\\
&\simeq
\operatorname{Int}_G(R_1\mathcal C)\\
&\simeq
\operatorname{Int}_G(\mathcal C).
\end{aligned}
\]
The last equivalence holds because \(G\) specifies only objects and \(1\)-cells.

Therefore \(IF_\infty(G)\) is already the free higher cartesian closed category on \(G\). Section 1 identifies it with the ordinary free cartesian closed category.

In particular, for the three-dimensional case you singled out:

\[
\boxed{\text{Any two parallel \(2\)-cells between \(\beta\eta\)-equal \(1\)-terms
have a contractible space of invertible \(3\)-cells between them.}}
\]

Indeed, over a graph the same statement holds in every higher dimension.

For \((\infty,\omega)\), this argument uses a model with the stated \(1\)-core adjunction and actual equivalences in the pseudo universal properties. The finite-dimensional conclusion, including the tricategorical case, does not depend on a choice between infinite-dimensional completion conventions.

### 3.3. What remains for abstract Dir

A context with specified noninvertible higher generators need not factor through \(R_1\mathcal C\). Consequently, the core argument does not prove the general Dir assertion.

What remains is a relative coherence theorem for those higher generating diagrams: the recursive source/target conditions must imply existence and contractibility of the directed comparison spaces. I have not proved that theorem or found a counterexample satisfying the abstract distinct-source and distinct-target conditions.

## 4. The cited unordered implementation of Dir is unsound

This is separate from the abstract criterion: the implementation fails to enforce its distinctness condition.

### 4.1. Complete accepted input

The following file is accepted at commit `69bb11af`:

```text
#-# mode: cartesian closed
#-# dimension: 3
#-# ordered: false
coh bad (a b : .) (f g : a -> b)
  (alpha : f -> g) (beta : f -> g) : alpha -> beta
```

I compiled the unchanged source from that revision and ran this through the actual parser and checker. It exited with status \(0\), reporting:

```text
defined bad : (a : .) (b : .) (f : a → b) (g : a → b)
  (alpha : f → g) (beta : f → g) ⤳ alpha → beta
```

### 4.2. Why no such filler exists

Interpret the context in the strict cartesian closed \(2\)-category \(\mathbf{Cat}\), regarded as a higher category with only identity cells above dimension \(2\).

Let \(P\) be the category with two objects \(0,1\) and exactly two nonidentity arrows
\[
p,q:0\longrightarrow1,\qquad p\ne q.
\]
Interpret:

| Declaration | Interpretation |
|---|---|
| \(a\) | The terminal category \(\mathbf1\) |
| \(b\) | \(P\) |
| \(f,g:\mathbf1\to P\) | The functors selecting \(0\) and \(1\) |
| \(\alpha,\beta:f\Rightarrow g\) | The natural transformations with respective components \(p\) and \(q\) |

There is no \(3\)-cell \(\alpha\Rightarrow\beta\), because such a cell would require equality of these distinct natural transformations.

This target satisfies the requested exponential condition: currying gives an isomorphism of categories
\[
\mathbf{Cat}(X\times A,B)
\cong
\mathbf{Cat}(X,[A,B]),
\]
including natural transformations. Thus the counterexample satisfies even the strict version of the pseudo universal property.

If the accepted coherence existed in the free cartesian closed higher category on this context, its image under this interpretation would supply the nonexistent \(3\)-cell. Hence its filler space is empty.

### 4.3. The implementation error

The unordered branch of [`pasting.ml`](https://github.com/smimram/cccatt/blob/69bb11af/src/pasting.ml) compares endpoints before converting them to variable names:

```ocaml
let x, y = arr a in
let x', y' = arr a' in
if x = x' then error ...;
if y = y' then error ...;
```

Those endpoints are `Term.t` records. The record definition in [`term.ml`](https://github.com/smimram/cccatt/blob/69bb11af/src/term.ml) includes the source position `pos`, so structural equality compares positions as well as variable names.

The separately written `f` terms in the two declarations have different source positions. The same holds for the separately written `g` terms. The duplicate checks therefore fail to detect either duplication.

Afterward, conversion to names produces
\[
[("f","g");("f","g")].
\]
This relation is acyclic. Removing targets leaves only \(f\); removing sources leaves only \(g\). Both recursive one-dimensional checks pass. At dimension \(3\), the absence of top-dimensional hypotheses then permits `alpha -> beta`.

The abstract Dir criterion in your question rejects this example because the two \(2\)-generators have the same source and target. The executable counterexample therefore refutes **the unordered checker at this revision**, while leaving the general mathematical Dir question described in Section 3.3 unresolved.

## Verification of the researcher response (2026-11-18)

I checked every step. I also read the cited cccatt source at commit 69bb11af (`src/pasting.ml`, `src/term.ml`). I did not run the checker. I did not re-read HTT A.3.3.2, Shulman Cor. 8.29, Nguyen–Raptis–Schrade Prop. 2.3.2 or Ozornova–Rovelli–Walde Thm 2.20; they are standard facts and used as the response states them.

**Verdict: correct.**
- Question 1 is solved positively for sets, graphs and simply typed signatures.
- Question 2 (Rev, as stated) is proved.
- Question 3 is solved for graph-generated contexts in all dimensions, including the tricategory case. The abstract Dir with higher generators stays open.
- The cccatt implementation of Dir (unordered mode) at the cited commit is unsound (reproduced). The response's second implementation remark, about Rev, is not a bug (V2).

### V1. Discreteness (§1): correct

- *Strict model lemma.* Yoneda preserves products and exponentials. Injective simplicial presheaves are simplicial, cartesian (the pushout-product of monomorphisms is computed objectwise) and have every object cofibrant. So fibrant objects are closed under products and exponentials, and `M^f` has strict enriched cartesian closed structure presenting `P(C)`. Closing the representables under the chosen operations gives a small D with `C ≃ N_hc D`. Checked.
- *Retract.*
  - q comes from the freeness of F, and s from the 1-categorical freeness of C into `D₀`. s preserves the ∞-structure because D's universal properties are isomorphisms of simplicial sets.
  - Freeness gives `sq ≃ e`, so `rq ≃ id`, and `Map_F(A,B)` is a retract of a set, hence 0-truncated.
  - `qr ≃ id` follows from bi-initiality of the free CCC.
  - So `F_∞(G) ≃ N F_1(G)`. Checked.
- *Existence (1.3):* weak initiality of `N F_1(G)` plus a solution-set argument. Fine.
- *Signatures (1.4):* domains built from 1, ×, ⇒. Fine.

### V2. Rev (§2): correct

- The space of (x, α : x → t) is a based path space, hence contractible. This uses the side conditions that x is not free in t and occurs in no other type. So contraction does not change the free CCC.
- The remaining 1-dimensional goal has exactly one βη-class (Mimram Thm 15). By V1 its filler space is a point, and higher goals are iterated path spaces of a point.
- *Code remark, confirmed in the source:* `pasting.ml`, l. 474 checks `not (List.exists (fun (_,a) -> has_fv r a) l)`, with r the hypothesis's name, not its endpoint x. So the implemented Rev differs from the stated one. *Correction (2026-11-18, cccatt filing thread):* this is **not a bug**. Substitution rejects every cycle, and any higher hypothesis left over fails the final 1-dimensional check, so no wrong acceptance is possible. It is a valid variant of the rule.

### V3. Graph-generated Dir (§3): correct

- The 1-core `R₁` is right adjoint to the inclusion of (∞,1)- into (∞,n)-categories. It inherits the cartesian closed structure, since taking cores of an equivalence of mapping categories gives an equivalence of mapping spaces, and the adjunction restricts to cartesian closed functors. A graph only sees objects and 1-cells.
- So the free higher CCC on G is `N F_1(G)`, viewed with identity cells only above dimension 1. **Any two parallel cells over βη-equal 1-terms are joined by a contractible space of invertible cells, in every dimension.** This settles the "smallest open case" of Question 3: coherence for free cartesian closed tricategories over a graph, in the (∞,n) sense with pseudo universal properties.

### V4. The unordered Dir implementation is unsound (§4): the code analysis is confirmed; the semantic counterexample is correct

- *Code.* `pasting.ml`, ll. 597–602 compare `x = x'` and `y = y'`, where these are `Term.t` records, before mapping them to `var x`. `term.ml`, l. 10 shows that the record contains `pos : Pos.t`. So structural equality distinguishes separately written occurrences of the same variable, and duplicate sources or targets are missed.
- *Semantics.* In Cat, take `𝟙 ⇉ P` with distinct parallel arrows p and q. The transformations α and β with components p and q are distinct, so there is no 3-cell `α → β`. Cat is cartesian closed with an isomorphism of hom-categories, so the empty filler space transfers to the free object.
- I did not run the binary. The response reports exit status 0 and the printed output.

### V5. Comparison with the internal sketch `closed-structure.md` C.4 (CLOSED thread)

- **Theorem C1** (discreteness, by normalisation by gluing) and the response's §1 (strict simplicial model plus retract) **reach the same theorem by different routes.**
  - C.4 glues into presheaves of spaces on renamings and builds reflect/reify in the ∞-topos.
  - The response strictifies and uses ordinary freeness.
  - The response's proof is shorter and uses no normalisation. C.4's proof is more constructive and is the one that might extend to (∞,ω) (C.4's own "What remains").
  - Both establish the retract onto a set. **I found no error in C.4 steps 1–7 at the level of a sketch.**
  - One point in C.4 step 3 needs an argument: "the space of such functors is contractible". This is freeness of F(Σ), the same assumption the response makes explicit in (1) and justifies in §1.3.
- **Corollary C2** (Rev) matches the response's §2. C.4 phrases contraction as a pushout along an equivalence `D^{k−1} → J`, and the response as a contractible extension space. These are equivalent.
- **What C.4 does not have, and the response adds:**
  - the graph case of Question 3 via the 1-core, which C.4 lists as open and which is now settled;
  - the two implementation defects.
- **What remains of D12:** abstract Dir with non-invertible higher hypotheses. It needs a relative coherence theorem (§3.3), of the same shape as RC.

### V6. Consequences

1. **D12 Questions 1–2 are closed**, by the response and independently by C.4. **Question 3 is closed over graphs.** Open: Dir with higher generators.
2. **cccatt bugs to report upstream** (if Anthony wants): the unordered Dir duplicate check compares positioned terms (**real**, reproduced at 69bb11a by the cccatt filing thread). The second item the response raises, that the Rev side condition checks the hypothesis name, is a valid variant and not a bug (see V2).
3. A next prompt for Dir with higher generators (relative coherence) is owed by the CLOSED thread, if wanted.
