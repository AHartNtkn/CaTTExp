# The uniform checker (coh_S) in Agda

*2026-11-21. Code: `src/CaTTExp/Uniform/`. Ledger S3. Rule: `spec/02-lax-core.md` §2.2–2.3. Decision procedure on paper: lax r10 Response 3 (`conjectures/answered/lax-interchange-every-dimension-r10-2026-11-20.md`), with the normal forms (K65) of r9.*

Everything called "checked" below is verified when `src/Everything.agda` type-checks (`--safe`, no postulates). Checked locally with Agda 2.7.0.1.

## 1. What is checked

The work has two parts. The first is the kernel checker relative to the free objects, for every family of layers that has a grading bound (`Graded`; see §2 item 5 for layers with loops). The second is one concrete free-object layer: the one where the switches act.

### 1.1 The rule and its decision, for any free-object layer (`Rule.agda`)

A `Layer` is the data that r10 Response 3 step 3 reads:
- the cells of one dimension in normal form, with decidable equality;
- the finite contextual alphabet of letters one dimension up out of each cell (K50), with their targets;
- supports, their union, and a test "this support is full".

A cell one dimension up is a chronological path of letters. Its support is the union of the supports of its two faces and its letters. The side condition is

```
SC x z  =  Σ (p : Path x z) . T (full (suppP p))
```

which is the spec's SC_𝕋: a cell x → z of full support.

- **`Decide.sc?`**: SC is decidable once every path from x to z has length at most `bound x z` (`Graded`, the positive gradings (K45)/(K50)). The proof enumerates all paths up to the bound and filters them by support. This matches "filtering by support is a finite check on each path" in spec §2.3.
- **`coherence`**: the identity on a cell of full support is a witness (the coherence case).
- **`Transport.sc-map`**: suppose a map of layers sends letters to letters, commutes with supports through a union-preserving map, and sends full supports to full supports. Then it sends SC to SC. This is "imports run upwards" (spec §2.3), stated for any such map.

The fullness test is a parameter, so this part does not depend on how ledger S1 settles the support of V + S (see §3).

**Caveat (2026-11-21, from the S3a–S3c thread).** `Graded` holds only for layers without loops. Some layers Kernel must be instantiated with do have loops. In V at degree 4 on Γ_{2,2}, the loop H has pairwise distinct powers. On suspended grids at degree 5 in setting T₁₂, the positional square is a self-loop on the 2 × 2 grid. So spec §2.3's "paths have bounded length" is not true in general. r10 Response 3 decides reachability by breadth-first search over a finite vertex list instead. A decision that needs no `Graded` (search over pairs of a cell and an accumulated support, in a finite closed universe) is `RuleFin` (§1.5). `sc?` stays correct where `Graded` holds.

### 1.2 The kernel's judgments and checker (`Kernel.agda`)

The module is parameterised by, for each pasting context Δ and type A:
- a layer;
- its grading bound;
- a partial interpretation ⟦_⟧ of terms into the layer's cells.

It defines `side Δ A t u`. Then:
- **`side-sound`, `side-complete`**: `side Δ A t u` holds iff ⟦t⟧ = x, ⟦u⟧ = y and SC x y.
- **The judgments** are `CaTTExp.TypingWith` at this side condition. So the coh rule is exactly (coh_S), and `coh-S` / `coh-S⁻¹` state it in the spec's form.
- **The checker** is `CaTTExp.CheckWith` at this side condition. It is sound by construction and complete by `CaTTExp.Completeness`, which already holds for every side condition.

Completeness (`CheckerComplete`) takes the two hypotheses of `CaTTExp.Completeness` on the signature of constants: `==K-refl` (the equality test on constants is reflexive) and `valid?-complete` (`valid?` succeeds on valid constants). Pure CaTT satisfies both vacuously.

`KernelToy.agda` instantiates `Kernel` with a one-cell layer, so its parameters can be supplied. The resulting checker accepts coh_{(x : ⋆), x → x}[x]. This is not a model of V + S; it only shows the hypotheses are satisfiable.

Substitution, weakening and the rest of `CaTTExp.Subst` hold for these judgments too, since they are proved for every side condition.

### 1.3 Reachability in a finite graph (`FiniteGraph.agda`)

Reachability from a vertex of a finite universe closed under steps is decidable. The proof cuts loops, then applies the pigeonhole lemma `Join.Finite.pigeon`. Unlike `Join/BoundedReach.agda`, it needs no length bound as a hypothesis. `reachSet` computes the reachable set by breadth-first saturation with an early stop, and is proved to be exactly that set. This is the form the computation uses.

### 1.4 The switch layer: 4-cells on suspended grids (`Grid.agda`, `GridExamples.agda`)

**Model.** This is the model of r10 Response 3 ("Which equations the switches add") and of `check_switch_settings` in `scripts/e6/interchange_fibre_decorations.py`. Fix an m × n grid of inner cells a₁ … a_m and b₁ … b_n in interchange position.
- **Words** are the shuffles.
- **Edges** are the generating 3-advances: the block crossing ⟨i, p, q⟩ of a b-run of length p+1 past the a-run of length q+1 that follows it.
- **Raw paths** run from b…b a…a to a…a b…b.
- **Equations** are the enabled split laws, in every chronological context:
  - the left split (inner law, `icc`): ⟨i,p,a+1+b⟩ = ⟨i,p,a⟩ ; ⟨i+a+1,p,b⟩;
  - the right split (R, `rsp`): ⟨i,a+1+b,q⟩ = ⟨i+a+1,b,q⟩ ; ⟨i,a,q⟩.

V adds no equation between raw paths here. The 4-cells of setting S are therefore the classes of valid raw paths under the equivalence relation `S ⊢ p ≈ q` generated by typed one-step applications (both sides valid).

**Checked, for every m, n and every setting:**
- **`eq?`**: equality of 4-cells is decidable. It is connectivity in the finite graph of one-step applications, both directions. The universe is the valid paths of one charge, the grading Σ(p+1)(q+1), which every law preserves and which bounds path length.
- **`nf`**: normal forms, the first path of its class in a fixed enumeration (the rank selection "first word in each component"). They satisfy `nf-≈` (nf p ≈ p), `nf-cong` (p ≈ q ⇒ nf p = nf q) and `nf-complete` (the converse).
- **`≈-mono`, `nf-compare`**: for S ⊆ S′, equality in S implies equality in S′. Renormalizing the S-normal form in S′ gives the S′-normal form of the original path. So the comparison maps F_{V+S} → F_{V+S′} are well defined and computable on normal forms.
- **`Classes`**: suppose there is no run of more than K edges and the path list has no repetition (both checked by evaluation per grid). Then the paths that are their own normal form are a repetition-free system of representatives of all 4-cells: `reps-cover`, `reps-apart`, `reps-nodup`.

**Computed (by `refl`):**

| Grid | V | V + R | V + inner law | T₁₂ |
|---|---|---|---|---|
| 1 × 2 | 2 | 1 | 2 | 1 |
| 2 × 1 (the strip) | 2 | 2 | 1 | 1 |
| 2 × 3 (49 raw paths) | 49 | 14 | 29 | 2 |

These agree with the Python checker as it stands after the 2026-11-20 fix of the inner-law bit. The 2 × 3 row takes about two minutes to check.

**Example (b) of spec §2.3** is checked as an equality statement (`ExampleB`). On the strip, the direct crossing u = W(a₁a₂, b) and the paste v of the two crossings are equal 4-cells in V + inner law and in T₁₂, and different in V and in V + R. The mirror statement for R on the 1 × 2 grid is `ExampleR`.

### 1.5 Without a length bound, and degree five on grids (`RuleFin.agda`, `KernelDec.agda`, `GridFive.agda`, `GridFiveExamples.agda`; 2026-11-21, ledger S3b, S3e)

**Why a second decision.** `Rule.Decide` needs `Graded`: a bound on the length of every path between two cells. Layers with loops have none. Examples: the loop H of V at degree 4 on Σ[2] ∨ Σ[2] ((K45): its powers are pairwise distinct), and the degree-5 loop on the 2 × 2 grid below.

- **`RuleFin.DecideFin.sc?`**: SC x z is decidable, for every z, given finite lists of cells and supports that contain x and supp x and are closed under steps. The search is breadth-first over states (cell, support accumulated so far). The only algebraic hypothesis is associativity of the union of supports. This is r10 Response 3's search, with the support filter of spec §2.3 folded into the state.
- **`KernelDec`**: `Kernel` with the grading parameter replaced by any decision of SC per layer. `Rule.Decide` (from a bound) and `RuleFin.DecideFin` both supply one. `Kernel` is now `KernelDec` at `Rule.Decide.sc?`, so its interface is unchanged and the toy instance (`KernelToy`) still checks; instances with loops use `KernelDec` directly.

**The 5-letters on suspended grids (`GridFive`).** On Σ(Σ[m] ∨ Σ[n]) the only proper 5-letter is the positional square I₂(A, B) of two positive 4-cells on consecutive 3-intervals, from (u₀B)(Av₁) to (Av₀)(u₁B). This is a paper argument, not derived from raw syntax: r10 Response 1 (the paragraph on the suspended strip, around its line 490) and r9 Response 2 ("5- and 6-cells"). Every positive 4-cell uses both short spans, so no cut-1 variation or join has an active partner. A suspension has one outer span, so there is no cut-0 operation. The diagram has no 5-globe. Cut-3 squares need 5-cell inputs. And r10 Response 3 says the switches add no letter above degree four.
- **Raw letters** (`Sq`): swap adjacent edges e′ ; e into e ; e′ when e's window lies wholly left of e′'s. A letter out of a 4-cell applies to any representative of its class and lands in the class of the result.
- **Composite operands.** A square with composite operands has the same endpoints as the paste of atomic squares that moves A's edges one by one before B's. So atomic squares give the same 5-reachability. This is argued here, not checked.
- **Supports.** Under the S1 reading SC asks for full support of π(c). π kills every interchanger along a k-cell with k ≥ 1, so every cell and letter here maps to an identity on the composite of all a- and b-cells, which has full Gray support. The layer therefore has every support full, and SC between 4-cells is exactly 5-reachability.

**Checked, for every m, n and every setting:**
- `reach5?`: 5-reachability `_⇛_` (the closure of switch equality and typed squares) is decidable, by breadth-first search on the valid raw paths of one charge.
- `layer`: the 4-cells in normal form, with the squares as letters, form a `Layer`.
- `path→⇛`, `⇛→path`, `sc→⇛`, `⇛→sc`: paths of letters in the layer are exactly 5-reachability, and SC is exactly 5-reachability.
- `sc?`: SC on the layer is decidable, through `RuleFin`.

**Computed (`GridFiveExamples`, about 40 s):**
- **Example (b)** on the strip, for u = W(a₁a₂, b) and v the paste of the two crossings:
  - The strip has no 5-letter at all, since every edge moves the single b.
  - In V and in V + R, SC fails from u to v and from v to u (`noSC-V-uv`, `noSC-V-vu`, `noSC-R-uv`, `noSC-R-vu`).
  - In V + inner law and in T₁₂, u and v are the same cell and SC holds both ways.
  - `sc?` returns false, false, true, true in the four settings.
- **The 2 × 2 grid.** Let X = χ(b₂a₁) χ(b₂a₂) χ(b₁a₁) χ(b₁a₂) and Y = χ(b₂a₁) χ(b₁a₁) χ(b₂a₂) χ(b₁a₂). The positional square of χ(b₁a₁) and χ(b₂a₂) goes X ⇛ Y.
  - In V it is directed: X ≠ Y, SC holds from X to Y and fails from Y to X.
  - In T₁₂, X = Y, since they are the two split orders of the full crossing. So the square is a letter from the single 4-cell to itself (`loop-T`), the suspension of H. A Python run of the same model finds self-loops only with both switches on: 1 on 2 × 2, 1 on 2 × 3, 9 on 3 × 3. This loop is why `RuleFin` is needed. It is a whiskered square (the suspension of H) that is a 5-loop: the cut-3 whiskering [χ(b₂a₁) | I₂(χ(b₁a₁), χ(b₂a₂)) | χ(b₁a₂)] of a bare square that is directed in every setting. It is not a (K49) four-input rectangle, since no temporal cut of b₁b₂a₁a₂ separates the two active inputs (ledger S14, settled by DSGN).

### 1.6 The grid in raw T-syntax (`GridLink.agda`, `GridSep.agda`; 2026-11-21, ledger S3c)

`GridLink` translates grid paths into raw terms of the theory T of `Join/SepAlgebra.agda` and proves that equal grid paths have equal translations. `GridSep` proves the converse, so on valid paths Grid's equality is exactly T-equality of the translations (`GridSep.Converse.link-iff`).

- **The signature.** The suspended grid has 2-cells u₀ … u_m and v₀ … v_n and 3-cells aᵢ : uᵢ ⇛ uᵢ₊₁ and bⱼ : vⱼ ⇛ vⱼ₊₁. A word read from stage (i, j) is the 3-composite whose a-letter is `wr aᵢ vⱼ` and whose b-letter is `wl uᵢ bⱼ` (`w3`).
- **The translation.** A block crossing ⟨k, p, q⟩ at word w becomes `ctx P (ι F G) Q`. Here P is the first k letters, F and G are the a-run and the b-run as raw composites of generators, and Q is the rest (`trE`). A path becomes the composite of its edges' translations, ending in an identity (`tr`). Every translation is a pure-ι 4-term (`tr-inner`).
- **The relation ≈S.** It contains every equation of T except the raw support equations, together with the switched laws `SwitchLaws.Law sw`, closed under composition and context. The support equations are dropped because they identify parallel paths with the same edge set. V and the theory P of (K45) do not have them.
- **What is proved.**
  - `flat-≈3`: a normalizer for 3-terms built from ⨾, identities and 2-whiskering. Two such terms with the same nonempty list of whiskered letters are ≈3-equal.
  - `cross-sound` and `cross-complete`: the shape of a block crossing.
  - `core-left` and `core-right`: one left (right) split of a block crossing is an instance of `splitL` (`splitR`) up to T's structural equations.
  - `tr-step`: a split anywhere in a path that runs.
  - `Link.link`: if `sw ⊢ p ≈ q` in `Grid.OnGrid m n` (typed split steps between valid paths), then `sw ⊢ tr start p ≈S tr start q`.
- **The converse (`GridSep`).** It uses a model of T that reads a 3-term as its word of letters (junk when it has a χ with two non-identity arguments) and a 4-term as a raw path or junk. ι(F, G) becomes the block crossing ⟨0, |G| − 1, |F| − 1⟩ when F is all a's and G all b's, and the empty path when either side is empty. r and t become empty paths or junk, and ctx shifts by the length of its left whisker. Paths are compared up to Grid's split steps without the validity side condition.
  - `sem3-≈` and `sem-≈`: every equation of T in dimensions 3 and 4 holds on the nose, except the support equations.
  - `sem-law`: each switched law holds up to one split step.
  - `sem-tr`: the translation of a running path evaluates to that path.
  - `split-run`, `≈U→≈`: split steps keep a path running from the same word to the same word, in both directions. So the untyped split class of a valid path stays among valid paths and is Grid's typed equality.
  - `Converse.converse`: if p and q are valid and `sw ⊢ tr start p ≈S tr start q`, then `sw ⊢ p ≈ q`. So the raw presentation ≈S adds no equation on suspended grids beyond the splits; that V + S adds none follows under the by-inspection identification of ≈S with V + S (§2 item 2). In particular ≈S is not trivial there, although raw ≈ identifies all identity 4-terms (ι(id3 u, G) ≈ id4 F for every F).

### 1.7 Normal forms for any finite presentation (`Present.agda`, `GridPresent.agda`; 2026-11-22, ledger S3a, S20 (iii))

r10 Response 3 builds every layer of F_{V+S}(Γ) the same way: list the finitely many raw words over a value with fixed faces and weight, join two words when one rewrites to the other by one equation, and take the first word of each connected component. `Present` proves that construction correct once, for any carrier, so each degree only has to supply its presentation.

- **Input (`Presentation A`).** Raw words A with decidable equality, a one-step relation `Step`, a neighbour list `nb` that is sound and complete for steps in both directions, and a finite universe `U x` that contains x, is closed under steps, and is unchanged along a step (it depends only on conserved data such as faces and weight).
- **What is proved.** ≈, the equivalence generated by `Step`, is decidable (`eq?`, by search in `U x`). `nf x`, the first word of `U x` connected to x, satisfies `nf-≈`, `nf-cong`, `nf-complete` and `nf-idem`, so normal forms are exactly the classes. `Cell` is the type of normal forms, with decidable equality and `cellOf` a bijection with classes.
- **Comparison maps (`Compare`, `Compose`).** For a second presentation on the same words whose steps include the first's (a richer setting S ⊆ S′), `compare = nf′ ∘ nf` equals nf′, so it is well defined on classes, and successive comparisons compose.
- **Layers (`layerOf`).** Given letters on raw words with sources, targets and supports, it builds the `Rule.Layer` whose cells are the normal forms, ready for `RuleFin` and `KernelDec`. `LayerData` requires the outgoing letters and the support of a word to be invariant under ≈ (`out₀-cong`, `supp₀-cong`), so `layer-out` and `layer-supp` show that the layer's data at `cellOf x` is the raw data at x for every word x, not only at the representative.
- **The grid as an instance (`GridPresent`).** The degree-4 grid layer of §1.4 is a `Presentation` on valid raw paths in every setting, and the generic ≈ is exactly Grid's typed equality (`equiv-to`, `equiv-from`). So Grid's equality is the generic one, and `nf-agree` shows the generic normal form picks the same representative as Grid's own `nf`.

What this leaves for S3a is the input in every degree: the raw T₁₂ syntax, B's defining pairs, the guarded equations, and their finite grounding (that each `U x` is finite and closed). Once those give a `Presentation` and letters per degree, `layerOf`, `RuleFin` and `KernelDec` give the kernel checker, but three obligations remain per degree:

- (a) The ≈-invariance of `out₀` and `supp₀`, now fields of `LayerData` (2026-11-22), must be proved for each degree's letters. If a degree names letters by position in the word, equal lists may be too strong; equality up to ∈-equivalence would still suffice for `Rule`'s SC, and the field can be weakened then.
- (b) `RuleFin` still needs finite universes of cells and supports, closed under the letters one dimension up and under accumulating supports. These are still per degree.
- (b′) `Present`'s universe `U` (finiteness of each ≈-class) is discharged generically by `WordPresent` (2026-11-22). Over a finite alphabet with positive letter weights, a weight-preserving one-step relation gives a `Presentation` whose `U x` is the finite list of words of x's weight. Each degree still supplies its finite alphabet of contextual letters, the weights, and the steps.
- (c) The presentation must actually be F_{V+S} in that degree. For the grid this is still by inspection (§2 item 2).

### 1.8 The raw signature of P through degree four, on any pasting diagram (`SigP.agda`; 2026-11-22, ledger S3a)

The first piece of S3a's raw syntax that is not specific to grids. `scripts/e6/reachability_theory.py` states the support-free presentation P of (K45) as operations with guards and boundaries, equation schemas, and the directed 5-cell schemas. `scripts/e6/interchange_free.py` grounds that presentation on any finite pasting tree. `SigP` transcribes it as data.

- **Terms.** Variables and operations are untyped (`Tm`), with dimensions computed (`dim`). Typing conditions are guards, that is, equations between faces (`adjacent`), because the theory is essentially algebraic. The helpers `paste`, `face`, `ctx` and `vertical`, and the `Block` machinery for outer spans with stationary 1-whiskers, follow the Python.
- **Content.**
  - `sesquiOps n` and `sesqui n` give the sesquicategory structure in dimension n: faces, units, composition, the left and right actions of k-cells for k < n, and their laws. They are defined for every n ≥ 1. The Python stops at 4, and nothing in the schemas depends on that.
  - `compOps` and `comparisons` give χ, r, t, ι and h, with their boundaries, degeneracies and whiskering laws.
  - `outerEqs` gives (7a)–(21) and the binary join factorization.
  - `rules` gives W, δ, N_L, N_R, U_r and U_t.
- **Checked against the Python.** `scripts/sigp_check/check.sh` compiles a small dump harness. The harness is outside the `--safe` library, because it needs a GHC binding to print. The script compares the dump with the Python's output line by line. All 165 operations, equations and rules agree exactly, including the s_n and t_n entries, whose unstated boundaries both sides print as `?`. The check covers dimensions up to 4. `sesqui n` and `sesquiOps n` for n > 4 are the same schemas extended past the Python's bound, unchecked there.
- **The free algebra, as a specification (`FreeP.agda`).** The free algebra of a presentation in this format on a set of generators is given by two mutually inductive judgments on raw terms. `Typed x` says x is a defined cell: an operation applies when its arguments are typed with the declared dimensions and its guards are derivable. `x ≐ y` is the least congruence containing every instance of an equation schema whose guards hold, the boundary of every operation, and the generators' faces. It is parametric in the operations, schemas and generators. `FreeP gens` is P through degree four, and `Example` checks a composite and its source on a two-arrow diagram.
- **Not yet done.**
  - A computation of `FreeP` on a pasting tree, proved sound and complete for `Typed` and `≐`: ground the operations dimension by dimension on cells already quotiented, and take the congruence, as `interchange_free.py` does.
  - Its normal forms through `Present`.
  - The proof that it agrees with (K45) and with `Grid` on suspended grids.
  - The T₁₂ extensions of (K47) above degree four.

## 2. What this does not check (the trust boundary)

1. **The free objects F_{V+S}(Γ) are not constructed in Agda in general.** `Kernel` is the kernel checker relative to the layers. That suitable layers exist for V + S in every dimension, with finite alphabets and grading bounds, is the paper result: r9 (K65) and r10 Response 3, verified at the argument level. Constructing them needs the raw syntax of the T₁₂ signature in every degree, B's defining pairs, and the guarded equations. Only degree four exists in Agda (`Join/SepAlgebra.agda`), and `Join/SwitchLaws.agda` notes that there is no raw 5-dimensional syntax.
2. **The grid model is a model by inspection.** That these words, edges and split equations are the degree-4 layer of F_{V+S} on a suspended grid is taken from r10 Response 3 and the checker it cites. Since 2026-11-21 the link to raw T-syntax is checked in both directions (§1.6): on valid paths, grid equality is exactly equality of raw T-translations under T without the support equations plus the switched laws. What stays by inspection is that this raw presentation (SepAlgebra's T, with the support equations dropped) is V + S on these diagrams, and the paper claims behind it. This is the grid case of the "Link A–B" of `joining-completion.md` §8.
3. **5-letters by inspection.** `GridFive` takes the degree-5 alphabet on suspended grids (positional squares only) from the paper argument of §1.5, and treats composite-operand squares through their atomic pastes. Neither is derived from raw syntax. *(Until 2026-11-21 there were no 5-letters at all, and example (b) was checked only as u ≠ v.)*
4. **Supports of V + S.** The fullness test is a parameter. How it reads for V + S is ledger S1. The spec's 2.1 takes supports in the expanded basis, but (K45)/(K50) say that basis is infinite on some pasting diagrams, so "supp(c) = all generators" needs a reading. The point has been passed to the S1 check.
5. **`Graded` fails on layers with loops** (ledger S14): the loop H of V at degree 4 on Γ_{2,2}, and the positional self-loop at degree 5 on the 2 × 2 grid in T₁₂. *Resolved 2026-11-21 (S3e):* `RuleFin` decides SC by search over (cell, accumulated support) pairs with no length bound, and `Kernel` now uses it in place of `Graded`.

## 3. Open items

- **S3a**: construct the layers of F_{V+S} in every degree in Agda and instantiate `Kernel`. This means formalizing the raw syntax of the T₁₂ signature, B and the guarded equations, then the (K65) rank normal forms and the switch extension of r10 Response 3. The normal-form construction itself is proved for any finite presentation (§1.7), so what remains is supplying the presentation in each degree.
- **S3b**: done (§1.5).
- **S3e**: done (§1.5, `RuleFin`, `KernelDec`). The (K49) question raised by the T₁₂ loop is settled in ledger S14: the loop is a whiskered square, not a (K49) rectangle.
- **S3c**: done (§1.6, `GridLink`, `GridSep`).
- **S3d**: fix the support reading. The S1 reviewer (2026-11-21, ledger PR #350) recommends this reading: SC_{V+S} holds iff some cell c : ⟦t⟧ → ⟦u⟧ (identity allowed) has full support after the requirement-4 projection to 𝔉(Γ), meaning every Gray tuple generator. `Rule` already covers it: take `Supp` to be supports in 𝔉(Γ), `supp` and `suppL` to be the projected supports, and `full` the Gray fullness test. The reviewer also says which lift interprets a coherence is open. Distinct V-cells can share a Gray image, as u and v of example (b) do. That choice stays a parameter of `Kernel` (⟦_⟧).

Owners are recorded in the ledger (S3).
