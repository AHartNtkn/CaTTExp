# Source-only joining completions: formalisation and a substitution-natural rule

*2026-11-18, LCORE. Ledger row E6. Source: `conjectures/answered/directed-interchange-every-level-r7-2026-11-18.md` §1–2 (r7). Code: `src/CaTTExp/Join/`. Everything marked "proved" type-checks under `--safe` with no postulates (`src/Everything.agda`). All dimensions are hom dimensions.*

## 1. r7's completion theorem, formalised

Setting: a quiver with vertices V, inner arrows E and positive ("seed") arrows P. For α : s → t in P and an inner path R : u → t, r7 adjoins j α R : s → u with j α [] = α and imposes (1) j α (e ∷ R) ; e = j α R.

The Agda version (`Join/Completion.agda`) proves more than r7 states, because most claims need none of r7's hypotheses.

| r7 claim | Agda | Hypotheses actually used |
|---|---|---|
| generators indexed by (α, R), count (2) | `Gen.jn`; `Finite.Paths.Count.count-J` | count: V and each E a b finite, decidable equality on V, E acyclic |
| finite, independent of saturation order | `Finite.enumPath`, `count-unique` | as above; the count is the same for every repetition-free enumeration |
| confluence | `diamond`, `confluent`, `church-rosser` | none: left-hand sides never overlap, so ⇒ has the diamond property and no termination argument is needed |
| termination | `⇒-len` (each step shortens) | none |
| unique normal forms | `nf-unique` | none |
| normal forms exist | `Normalise.nf`, `nf-red`, `nf-normal` | decidable equality of inner arrows out of each vertex |
| equality decided by normal forms | `nf-sound`, `nf-complete` | as above |
| equations form a congruence | `inst`, `~-++` | none |
| Path(Q) embeds | `ι-normal`, `embed` | none |
| contractions keep the seed list | `seeds-~` | none |
| completed quiver acyclic | `Rank.acyclic` | E acyclic and a rank φ into any strict order (r7 uses ℤ) |
| injective supports | `Quiver.Acyclic.supp-inj`, `Rank.nf-supp` | acyclicity only; holds for every acyclic quiver, with proof-relevant membership, no decidable equality |
| (5) C(Q)/(E=1) ≅ Path(Q)/(E=1) | `Collapse.restrict`, `extend`, `extend-unique` | none; stated as the universal property against any category (E-killing functors out of C(Q) correspond to those out of Path(Q)) |
| restricted naturality (seeds to seeds, inner to inner paths) | `Join/Natural.agda`: `map-~`, `map-++`, `map-ι`, `map-seeds` | none |
| §2 counterexample | `Join/NotNatural.agda`: `no-extension` | the five-word quiver of r7 §2 |

## 2. A uniform rule natural under substitution: the cospan completion

**Diagnosis.** r7 divides a seed α by inner paths. A map that sends a seed τ to a composite α ; I must send j τ R to a division of α ; I by F R, and r7 has divisions of α only. So divide every composite "seed, then inner path".

**Definition (`Join/Cospan.agda`).** For α : s → t in P, an inner path I : t → m and an inner path R : u → m, adjoin

  j α I R : s → u      (read: α ; I ; R⁻¹),

with j α [] [] = α and the equations

  (C1) j α I (e ∷ R) ; e = j α I R,       (C0) j α I [] = α ; I.

r7's generators are the case I = []. Rewriting uses (C1) left to right as a contraction and (C0) left to right as an expansion for I ≠ []. The left-hand sides are (j with R ≠ [], then an inner arrow) and (j with R = [] and I ≠ []), so they never overlap.

**Theorem 2.1 (proved, `Join/Cospan.agda`).** For any quiver (V, E, P):
1. the rewriting has the diamond property, so it is confluent and Church–Rosser (`diamond`, `confluent`, `church-rosser`), and normal forms are unique (`nf-unique`);
2. with decidable inner-arrow equality, normal forms exist and decide equality (`Normalise`);
3. original paths are normal and Path(Q) embeds (`embed`);
4. seed lists are invariant (`seeds-~`);
5. with E acyclic and a rank φ, every j α I R raises φ, since φ u = φ m = φ t > φ s. So the completed quiver is acyclic and supports of normal forms are injective (`Rank.acyclic`, `Rank.nf-supp`);
6. (5) holds: E-killing functors out of the cospan completion correspond to those out of Path(Q), with F(j α I R) equal to F α transported (`Collapse`);
7. with V and E finite, E acyclic and P finite, the generators are finite, counted by `Finite...count-J⁺`.

**Theorem 2.2 (naturality, proved, `Join/CospanNatural.agda`).** Let F : Path(Q) → Path(Q′) send each inner arrow to an inner path and each seed to a word containing a seed. Such a word is uniquely pre ; β ; post, with β its last seed and post inner. Then

  j α I R ↦ pre ; j β (post ; F I) (F R)

respects the equations (`map-~`) and composition (`map-++`), and it agrees with F on original paths up to the equations (`map-ι`). The class of such F is closed under composition. The r7 §2 map τ ↦ h_z ; f is in the class: j τ [] (e) goes to j h_z (f) (e). Not formalised: that the extension of a composite is the composite of extensions. This is routine bookkeeping with `map-ι` and associativity.

**Theorem 2.3 (the new generators are forced, proved, `Join/Forced.agda`).** In r7's completion, if I and R are nonempty inner paths with different last arrows, then no H satisfies H ; R = α ; I (`no-division`). The proof needs no finiteness, decidability or acyclicity. Seed lists are invariant, so H = P₀ ; j α S ; L. A leading inner arrow is never rewritten, so P₀ = []. Contractions only cancel a common prefix of S and L ; R, so L ; R = S ; I as inner paths, and their last arrows would agree.

So any completion that contains r7's generators and is natural for the maps of Theorem 2.2 needs a division of α ; I by R for every such cospan. Take the map that sends a fresh seed τ : s → m to α ; I and fixes everything else: it sends j τ R to that division. When I and R end in the same arrow, a smaller cospan gives the division. r7 §2 (`NotNatural`) is the instance I = f, R = e.

**Minimal form.** The Agda construction indexes j by all cospans (I, R). The forced ones are those with R ≠ [] and either I = [] or last(I) ≠ last(R). The others are parallel to a forced one: j α (I ; S) (R ; S) and j α I R have the same boundary. The minimal presentation identifies them, indexing by reduced cospans (common suffix cancelled). Reduction commutes with (C1), and naturality then reduces F's image cospan. This needs decidable equality of inner arrows and is not formalised. I recommend the reduced form as the uniform rule. The unreduced form is the one proved, and its extra generators are redundant but harmless: supports stay injective because the quiver stays acyclic.

**On K14** (`scripts/e6/cospan_count.py`, 240-word interval): 264 seeds; r7 has 877 positive generators; the unreduced cospan completion 11,004 cospans (some with R = [], which are composites); the reduced one 4,549 joining generators beyond the 264 seeds (r7's 613 included). The rank of r7 (values 0…7) is re-verified, so the completion is acyclic.

## 3. The degenerate obstruction

**Proposition 3.1 (proved, `Join/Degenerate.agda`).** In the cospan completion, a nonempty inner path R : u → a has no H : a → u with H ; R = 1 (`no-unit-division`). The reason is that equations keep seed lists, so H is inner, and inner words are normal.

So if a map sends a seed α to an identity but sends some inner path R into t α, which carries a generator j α R, to a nonempty path, then no source-joining completion containing r7's generators extends it. That includes r7's completion and the cospan completion. More generally, a seed sent to an inner path I₀ requires F R to be a suffix of I₀ ; F I for every cospan (I, R) at α.

**What remains for requirement 5.**
- (a) Check that the maps of comparison categories induced by substituting cells for generators of Γ are in the class of Theorem 2.2. That means each tensor arrow goes to a word with a tensor arrow, and inner interchangers go to inner paths. The second part is the (K15) convention.
- (b) For degenerating substitutions (a variable sent to an identity), check the suffix condition of §3. In r4's example (Ω ↦ 1_A) the joining arrow K goes to W, not to an identity. This suggests degeneracies kill the inner arrows into a degenerated seed's target together with the seed. That is unproved.
- (c) Lift from comparison categories (one hom dimension) to the tower: the higher cells of (K21)–(K22) must also be natural.

## 4. The dimension-4 theory T: machine-checked parts

*Source: `conjectures/answered/lax-interchange-construction-or-impossibility-2026-11-19.md` (the Followup's theory T, verified on paper 2026-11-19). Standard 9 asked for three items. All three are proved; the scope of each is stated with it.*

**Support equations are closed under substitution, (38)** (`Join/SupportSubst.agda`). This holds for any quiver of contextual edges, loops and repeated edges included. A substitution sends each edge to a path, which may be empty for an edge sent to an identity.
- `edges-σ⁻`, `edges-σ⁺`: the edges of σ p are exactly the union of the edges of σ e over the edges e of p.
- `same-σ`: equal edge sets map to equal edge sets.
- `≈-σ`: the congruence generated by the support equations, with contexts, maps into the target's support congruence. So the support equations form one theory closed under every substitution, degenerate ones included.

**Cut-inversion invariant, §6.3** (`Join/CutInvariant.agda`). Model a 3-path that respects a cut as a word of steps on the L or R side; inv counts pairs where an R step comes before an L step (47).
- `block`, `inv-move`: an inner move V;U → U;V that never pairs an L step of V with an R step of U lowers inv by exactly D(V, U), the number of (R step of V, L step of U) pairs (48)–(49).
- `inv-moves`: so inv never increases along inner moves.
- `proper`, `no-reverse`: a proper elementary instance (U on the L side, V on the R side) lowers inv by at least 1, so no sequence of inner moves undoes it (50).
- `precedes→ok`: with steps as nonempty integer intervals, "U's interval precedes V's" gives that side condition at every cut each step of U respects. This is the step the response states as L_h(V)R_h(U) = 0.

Not formalised, and taken from the response:
- that inv is invariant under the 3-equations (argued from "ba and ab share no interior state");
- that a reverse cell has identity Gray image and so consists of inner moves only.

**Separating algebra M and (63)** (`Join/SepAlgebra.agda`).
- **Terms.** Raw terms for 2-, 3- and 4-cells over any signature, with 2-whiskering, 1-whiskering and contexts [p | Θ | q].
- **Equations.** The relations ≈3 and ≈ encode T's equations through dimension 4 as schemas on raw terms:
  - the sesquicategory laws for composition, whiskering and units;
  - (7) and (8) for χ, r, t, and 1-whiskering preserving ι;
  - the balancing laws (9);
  - (10)–(17), (18), and the restricted laws (20)–(21) with the literal χ argument;
  - the identity normalisations, and the support equations (same edge set ⇒ equal paths).
- **Soundness in M.** M's 4-cell for Θ is (value of its source, weight Θ). Equations relate parallel cells, so M satisfies an equation exactly when the weights agree. `val3-≈` and `weight-≈` prove that every schema instance preserves values and weights, ill-typed raw instances included.
- **The diagram of §7.2.** With A, B, C ↦ 1, ι(A, B;C) has weight {(1,2)} and the pairwise composite has weight {(1,1)}. So `composite-crossing-fails : ¬ (D ≈ P)`, which is (63).
- **Scope.** 5-cells add no 4-dimensional equations and are not modelled. Godement horizontal composites are derived from whiskering and vertical composition by (2), so they are not separate primitives.

## 5. Toward dimension 5: T lacks the binary repair

*Script: `scripts/e6/t_binary_interval.py`. The prompt `conjectures/outbox/lax-interchange-every-dimension-r2.md` (K30), (K32) and Q1(A) is updated with this.*

**T on ΣD² ∨ ΣD² is the (K8) skeleton.** Take 3-cells A : α ⇛ α′ and B : β ⇛ β′ side by side along a 0-cell, and C = χ. The 3-paths in the maximal interval are the six orderings of A, B and C:
- S = BCA, V₀ = CBA, V₁ = CAB, T = ACB, U₀ = ABC, U₁ = BAC.

T's 4-generators there are:
- t̄₀ : S → V₀, ι(A, B) : V₀ → V₁, r̄₀ : V₁ → T;
- r̄₁ : S → U₁, ι(B, A) : U₀ → U₁, t̄₁ : U₀ → T.

The factorization equations (15)–(16) need a varying argument whiskered by a nontrivial 2-cell a₁, so they are vacuous here. The only route S → T is t̄₀ · ι(A, B) · r̄₀, and U₁ is a sink. So no 5-cell has A ⊗ B as its Gray image. Extending T to dimension 5 needs **new dimension-4 data**, not only 5-cells. The answered note's claim that (15)–(16) are the uniform (K10) repair is wrong, and has an erratum.

**Candidate uniform repair.** Adjoin, for A : α ⇛ α′ and B : β ⇛ β′,

  h(A, B) : Bα ; χ(α, β′) ; Aβ′ ⇛ βA ; Bα′ ; χ(α′, β′),   [Bα | r(A, β′) | ε] = h(A, B) · [ε | ι(B, A) | χ(α′, β′)].

- The degeneracies agree with T: h(A, 1) = r(A, β) and h(1, B) = identity.
- A 5-generator W(A, B) : t̄₀ · ι(A, B) · r̄₀ ⇛ h(A, B) · t̄₁ then has Gray image A ⊗ B.
- A mirror repair through t is equally possible.

Open: whether the h-extension is directed with injective supports, and closed under substitution, on the triple tensor, given the degeneration obstruction (K24)–(K25).

## 6. 4-endomorphisms after (C)

*Script: `scripts/e6/t_endomorphisms.py`. Source: the r2 response, `conjectures/answered/lax-interchange-every-dimension-r2-2026-11-19.md`. Recorded in the r3 prompt as (K37).*

The script computes, exactly, the 4-endomorphisms of F_T(Σ[m] ∨ Σ[n]) through global dimension 4.
- 3-cells: crossing paths modulo the composite-crossing laws.
- 4-cells: ι-paths modulo three things: the restricted composition laws, the support equations, and optionally (C) or (C⁺) in every context and substitution instance.
- It works one strongly connected component at a time, with a congruence closure over (3-cell, edge-set) states. A state cap leaves the largest component of Σ[3] ∨ Σ[3] and of Σ[2] ∨ Σ[5] undecided.

| Γ | T: endos / pairs | T/(C): endos / pairs | T/(C⁺): endos / pairs |
|---|---|---|---|
| Σ[1] ∨ Σ[n], n ≤ 3 | 0 / 0 | 0 / 0 | 0 / 0 |
| Σ[2] ∨ Σ[2] | 1 / 0 | 0 / 0 | 0 / 0 |
| Σ[2] ∨ Σ[3] | 6 / 0 | 1 / 0 | 0 / 0 |
| Σ[2] ∨ Σ[4] | 27 / 1 (r2's X, Y) | 11 / 0 | 7 / 0 |
| Σ[3] ∨ Σ[3] (21 undecided) | 82 / 0 | 12 / 0 | 0 / 0 |
| Σ[2] ∨ Σ[5] (25 undecided) | 86 / 9 | 40 / 0 | 28 / 0 |

"Endos" counts 3-cells carrying a nonidentity endomorphism. "Pairs" counts pairs of such 3-cells composable along a 2-cell. (C⁺) is (C) together with every rotation of every H instance.

**Findings.**
- No composable pair survives (C) where the computation decides.
- Endomorphisms do survive (C). On Σ[2] ∨ Σ[3], H(a₁, a₂; b₁, b₂b₃) = e₁ · e₂ is a loop of two ι-edges, and its rotation e₂ · e₁ is not identified with 1.
- **Doubling (proved):** a nonidentity endomorphism E on a 3-cell from BA to AB gives the composable pair b₁…bₙ E(a; bₙ₊₁…b₂ₙ), E(a; b₁…bₙ) bₙ₊₁…b₂ₙ on Σ[2] ∨ Σ[2n]. The degenerating substitutions of r2 §5 show both are nonidentity.
- So (C) leaves an obstruction pair on Σ[2] ∨ Σ[6]. (C⁺) still leaves endomorphisms on the extreme 3-cell of Σ[2] ∨ Σ[4], hence an obstruction on Σ[2] ∨ Σ[8].
- The forced repair is therefore not a finite list of loop equations. The candidate is (C∞), every 4-endomorphism an identity. Given T's support equations, this is equivalent to every 4-edge on a 4-cycle being invertible. Its consistency through dimension 4 is plausible by the (K36) argument (4-cycles consist of cut-neutral ι-moves, and inverting an edge on a cycle adds no new homs), but this has not been checked.

**Scope.** These are computations for two-factor chains only. Three factors, where τ appears, and Γ with generating 3-cells are not covered. The model's 4-equations are T's for this Γ, as listed in (K30) and instantiated by hand in the script. The zero-pair results do not depend on that list, since a missed equation could only remove endomorphisms. The positive claim does depend on it: that the rotation R survives (C), and with it the Σ[2] ∨ Σ[6] obstruction. Nothing certifies that the list is complete, and no separating invariant for R is given, so that claim is computed, not proved.

## 7. The 3-equation repair (R) of the r3 response

*Script options `--R`, `--Rall`, `--thin` of `scripts/e6/t_endomorphisms.py`. Source: `conjectures/answered/lax-interchange-every-dimension-r3-2026-11-19.md`; summarised as (K39) of the r4 prompt.*

- **Guillotine expansions.** Call the expansions of χ(A, B) that T's outer laws produce "guillotine". The crossing paths from BA to AB that are not guillotine are exactly the response's V on 3×2, and its mirror (13)(12)(23)(11)(22)(21) on 2×3. The mirror is the base 3-cell of the rotation R of §6.
- **T + (R) + (C)**, with (R) taken in all substitution instances, both orientations and in context. Σ[2] ∨ Σ[≤3] and Σ[3] ∨ Σ[2] are clean. Σ[3] ∨ Σ[3] is clean on its decided part (13 cells undecided). But Σ[2] ∨ Σ[4] keeps 2 endomorphisms on the extreme 3-cell, which doubles to an obstruction on Σ[2] ∨ Σ[8].
- **(R) does not merge all extreme paths.** Classes of crossing paths BA → AB, without and then with (R):
  - 2×4 (14 paths): 7, then 2;
  - 3×3 (42 paths): 21, then 13;
  - 2×5 (42 paths): 25, then 10.

  So the 3-level repair must be R∞: every crossing path BA → AB equals χ(A, B).
- **T + R∞ + (C)** still keeps 1 extreme endomorphism on Σ[2] ∨ Σ[4]. It is made of ι-loops at w in contexts that are not H instances.
- **T + R∞ + (C) + "every single-edge 4-loop is 1"** is clean on Σ[2] ∨ Σ[3] and Σ[2] ∨ Σ[4], and on Σ[2] ∨ Σ[5] except for 1 undecided cell.
- **Expanded-basis requirement 2 does not force (R).** Take contextual 3-edges to be (word, crossing). V's edge set lies inside the union of the four W representatives' sets, but equals none of them, and those four differ pairwise.

**A single statement (proposed, unchecked):** thin blocks. The interchanger-only cells between the two extreme composites L(u⃗), R(u⃗) of an interchanger of composites form a contractible hom. It must be restricted in two ways:
- to extreme words, because between intermediate words the 2-whiskered elementary ι must stay non-identity (requirement 3);
- to interchanger cells, because otherwise the A ⊗ B atom between r/t routes would collapse.

As with §6, every survival claim here is computed, not proved. Each depends on the script's equation list being complete.

## 8. The uniform rule in every law setting (E12)

*Code: `src/CaTTExp/Join/SwitchCospan.agda`. Source: `design-decisions.md` §1.7.*

Since the revision of 2026-11-20 (§1.7), the side condition computes in V + S, where V is the least pasting profile and the switch set S ranges over the laws visible on pasting diagrams: the inner composite-crossing law and R. All four settings are offered, since every finite set of T₁₂-true equations is admissible over V (lax r9, K73): `vS` (no switch on, the default, V), `iccS` (V + the inner composite-crossing law), `rspS` (V + R) and `allS` (both on, T₁₂'s pasting profile). L_p and D_{d,p} are invisible on pasting diagrams, so they are not switches.

The cospan completion of §2 is stated for an arbitrary quiver, so nothing in it is fixed to T₁₂. `SwitchCospan` makes the switch parameter explicit.
- **Settings.** A `Setting` presents a law setting's comparison graph by step lists, as `BoundedReach` does: cells, inner steps and seed steps. `Setting.Completion` is its cospan completion.
- **Switch maps.** A `Switch S S′` is a switch-on map: the identity on letters, so inner steps go to inner steps and seed steps go to seed steps. This is the shape of `BoundedReach.Transport`'s step map.
- **Extension (proved).** `Ext` extends a switch map to the completions by j α I R ↦ j (σα) (σI) (σR):
  - `ext-inn`, `ext-jn`: the extension acts letterwise;
  - `ext-~`: it respects the completion equations;
  - `ext-++`: it respects composition;
  - `ext-ι`: it agrees with the switch map on original paths;
  - `ext-seeds`, `seedsMap-~`: seed lists map letterwise and stay invariant.
- **Functoriality (proved).** Switching on in two stages is switching on at once (`ext-∘`), and the identity switch extends to the identity (`ext-id`).
- **The catalogued laws keep seed lists (machine-checked 2026-11-20 for raw T-syntax and for inner-word equations in the completion, `Join/SwitchLaws.agda`; the link between the two is by inspection).** The inner composite-crossing law and the right split R are split equations for ι. Each equates a direct ι of a composite with a paste of ι's of the pieces. In the comparison quiver ι-instances are inner arrows, and the 3-cell arguments and whiskers are only contexts. So both sides are inner words with empty seed lists, under every substitution too. Switching any of these laws on therefore keeps the seed-list invariance that the extension uses.

**What is mechanized.** `SwitchCospan` proves its statements for any `Switch`. `SwitchLaws` adds three parts.
- **Part A (raw syntax of T, as in `SepAlgebra`).** The switched laws are written as schemas: the binary split of a composite left operand (the inner composite-crossing law) and the binary split of a composite right operand (R). Until 2026-11-20 the inner-law bit also enabled the right split, which made the inner-law and both-on settings coincide; that was a modelling error, now fixed, and the four settings are distinct (49, 14, 29 and 2 cells on the suspended 2 × 3 interval for V, V + R, V + inner law and T₁₂ respectively, i.e. `vS`, `rspS`, `iccS`, `allS`; `scripts/e6/interchange_fibre_decorations.py`). Each is available when its switch is on. The four offered settings are ordered `vS ≤ iccS, rspS ≤ allS` (`vS≤iccS`, `vS≤rspS`, `iccS≤allS`, `rspS≤allS`).
  - `law-inner`: both sides of every switched law are pure-ι terms.
  - `seeds4-≈`: the congruence generated by any switched laws keeps the seed list, meaning the r, t and generator letters in order.
  - `≈-mono`: switching more laws on only enlarges that congruence.
- **Part B (cospan completion).** Adding any family of equations between inner words to ~ keeps seed lists (`seeds-~L`).
- **Part C (3-cell level; definitional, not a proof).** With 3-cells as vertices, T's 3-equations carry no switch and every law relates 4-terms, so a setting should not depend on its switches and the switch map should be `idS`. That argument is on paper. The module defines the setting to be constant, so `switch3 = idS` holds by definition.

**Still open (owner LCORE).**
- **Link A–B.** Nothing formal connects Parts A and B. There is no map from pure-ι 4-terms to inner words, and no proof that the switched laws instantiate the equations of Part B. This is by inspection.
- **3-cell switch-independence.** Part C assumes it (see above).
- **4-cell level.** One level up, the vertices are 4-cells, and the laws enter through the quotient on cells. That this switch map is a `Switch` (5-letters keep their inner or seed kind) is argued on paper only. There is no raw 5-dimensional syntax to state it in.
