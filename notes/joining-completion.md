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
