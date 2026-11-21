# The uniform checker (coh_S) in Agda

*2026-11-21. Code: `src/CaTTExp/Uniform/`. Ledger S3. Rule: `spec/02-lax-core.md` §2.2–2.3. Decision procedure on paper: lax r10 Response 3 (`conjectures/answered/lax-interchange-every-dimension-r10-2026-11-20.md`), with the normal forms (K65) of r9.*

Everything called "checked" below is verified when `src/Everything.agda` type-checks (`--safe`, no postulates). Checked locally with Agda 2.7.0.1.

## 1. What is checked

The work has two parts. The first is the kernel checker for every theory, relative to the free objects. The second is one concrete free-object layer: the one where the switches act.

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

**Caveat (2026-11-21, from the S3a–S3c thread).** `Graded` holds only for layers without loops. Some layers Kernel must be instantiated with do have loops. In V at degree 4 on Γ_{2,2}, the loop H has pairwise distinct powers. On suspended grids at degree 5 in setting T₁₂, the positional square is a self-loop on the 2 × 2 grid. So spec §2.3's "paths have bounded length" is not true in general. r10 Response 3 decides reachability by breadth-first search over a finite vertex list instead. A decision that needs no `Graded` (search over pairs of a cell and an accumulated support, in a finite closed universe) is being added by the thread "Formalize the V + S free objects in every degree". `sc?` stays correct where `Graded` holds.

### 1.2 The kernel's judgments and checker (`Kernel.agda`)

The module is parameterised by, for each pasting context Δ and type A:
- a layer;
- its grading bound;
- a partial interpretation ⟦_⟧ of terms into the layer's cells.

It defines `side Δ A t u`. Then:
- **`side-sound`, `side-complete`**: `side Δ A t u` holds iff ⟦t⟧ = x, ⟦u⟧ = y and SC x y.
- **The judgments** are `CaTTExp.TypingWith` at this side condition. So the coh rule is exactly (coh_S), and `coh-S` / `coh-S⁻¹` state it in the spec's form.
- **The checker** is `CaTTExp.CheckWith` at this side condition. It is sound by construction and complete by `CaTTExp.Completeness`, which already holds for every side condition.

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
- **`KernelDec`**: `Kernel` with the grading parameter replaced by any decision of SC per layer. `Rule.Decide` (from a bound) and `RuleFin.DecideFin` both supply one. Everything else is as in `Kernel`.

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
  - In T₁₂, X = Y, since they are the two split orders of the full crossing. So the square is a letter from the single 4-cell to itself (`loop-T`), the suspension of H. A Python run of the same model finds self-loops only with both switches on: 1 on 2 × 2, 1 on 2 × 3, 9 on 3 × 3. This loop is why `RuleFin` is needed. It is also in tension with (K49), which is ledger S15 (owner DSGN).

## 2. What this does not check (the trust boundary)

1. **The free objects F_{V+S}(Γ) are not constructed in Agda in general.** `Kernel` is the kernel checker relative to the layers. That suitable layers exist for V + S in every dimension, with finite alphabets and grading bounds, is the paper result: r9 (K65) and r10 Response 3, verified at the argument level. Constructing them needs the raw syntax of the T₁₂ signature in every degree, B's defining pairs, and the guarded equations. Only degree four exists in Agda (`Join/SepAlgebra.agda`), and `Join/SwitchLaws.agda` notes that there is no raw 5-dimensional syntax.
2. **The grid model is a model by inspection.** That these words, edges and split equations are the degree-4 layer of F_{V+S} on a suspended grid is taken from r10 Response 3 and the checker it cites. So is the claim that V adds no equation there. Nothing in Agda links `Grid` to `Join/SepAlgebra`'s raw T-syntax. This is the same gap as the "Link A–B" of `joining-completion.md` §8.
3. **5-letters by inspection.** `GridFive` takes the degree-5 alphabet on suspended grids (positional squares only) from the paper argument of §1.5, and treats composite-operand squares through their atomic pastes. Neither is derived from raw syntax. *(Until 2026-11-21 there were no 5-letters at all, and example (b) was checked only as u ≠ v.)*
4. **Supports of V + S.** The fullness test is a parameter. How it reads for V + S is ledger S1. The spec's 2.1 takes supports in the expanded basis, but (K45)/(K50) say that basis is infinite on some pasting diagrams, so "supp(c) = all generators" needs a reading. The point has been passed to the S1 check.

## 3. Open items

- **S3a**: construct the layers of F_{V+S} in every degree in Agda and instantiate `Kernel`. This means formalizing the raw syntax of the T₁₂ signature, B and the guarded equations, then the (K65) rank normal forms and the switch extension of r10 Response 3.
- **S3b**: done (§1.5).
- **S3e**: done (§1.5, `RuleFin`, `KernelDec`). The (K49) question raised by the T₁₂ loop is ledger S15.
- **S3c**: link `Grid` to raw T-syntax (`Join/SepAlgebra`), closing item 2 above. It shares the missing map from pure-ι 4-terms to words with "Link A–B" (E12).
- **S3d**: fix the support reading. The S1 reviewer (2026-11-21, ledger PR #350) recommends this reading: SC_{V+S} holds iff some cell c : ⟦t⟧ → ⟦u⟧ (identity allowed) has full support after the requirement-4 projection to 𝔉(Γ), meaning every Gray tuple generator. `Rule` already covers it: take `Supp` to be supports in 𝔉(Γ), `supp` and `suppL` to be the projected supports, and `full` the Gray fullness test. The reviewer also says which lift interprets a coherence is open. Distinct V-cells can share a Gray image, as u and v of example (b) do. That choice stays a parameter of `Kernel` (⟦_⟧).

Owners are recorded in the ledger (S3).
