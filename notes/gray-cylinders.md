# Gray cylinders, G3, vertical composition and the Gray cube in Agda

*2026-11-18. Ledger items D5 and D6. Code in `src/CaTTExp/GrayCtx/`; every result below marked **checked** is a theorem of `CaTTExp.GrayCtx.Checks`, obtained by running the certified checker of `CaTTExp.Check` at typechecking time, so it comes with a typing derivation. Targets are those of `internal-hom.md` §7.*

## Summary

| Target (`internal-hom.md` §7) | Result |
|---|---|
| 1. Γ ⊗ D¹ for Γ a pasting scheme, as a function on syntax, well formed | **Done for both orientations** (Γ ⊗ D¹, lax, and D¹ ⊗ Γ, oplax), for every *globular* context Γ (pasting schemes and more). Well-formedness **checked** for D¹–D⁵, the horizontal pair, the 1-sphere, and **every pasting scheme with at most 4 edges** (all 23). A general proof for all Γ is not done (see "Open"). **Cross-checked:** D¹ ⊗ Γ agrees syntactically, up to renaming, with the independent `CaTTExp.Free.Cylinder` (free-objects thread) on D¹–D⁴, the vertical and horizontal pairs, the 1-sphere, the loop and the 2-loop. **D13 proved up to dimension 5**: for *every* well-formed globular Γ of dimension ≤ 5, in particular every pasting scheme of dimension ≤ 5, `cyl sd 1 Γ` is well formed (`Checks.Natural.cyl-wf`, both orientations). The proof is a general Agda theorem (`NaturalWF.cylN-wf-all`) that reduces every dimension to the disk cylinders D^n ⊗ D¹. The disks are certified for n ≤ 5. **The disk statement for all n is open** (D13, §1a). |
| 2. G3: Γ ⊗ (D¹ ∨ D¹) ≅ (Γ ⊗ D¹) ∨ (Γ ⊗ D¹) | **Holds on the nose.** The two inclusions are well-typed renamings, so every generator of Γ ⊗ (D¹ ∨ D¹) has literally the renamed type of the corresponding generator of Γ ⊗ D¹. **Checked** for every pasting scheme with at most 3 edges, both orientations; that the two images cover all 5N variables and meet exactly in copy 1 is **checked** for N ≤ 12 (`G3-cover-meet`, `G3-length`). A general proof for all Γ is not done (D13). |
| 3. Vertical composition of lax transformations as a substitution Γ ⊗ (D¹ ∨ D¹) ⊢ comp : Γ ⊗ D¹ | **Defined** for every globular Γ of dimension ≤ 2, both orientations. A general proof that it is well typed for all such Γ is **not done** (the disk reduction of §1a would apply but is not carried out, D13; dimension ≥ 3 is D15). **Checked** only on D¹, D² and the composable pair (both orientations) and the horizontal pair of 2-cells (lax orientation). **No non-pasting-scheme composite is needed**: everything is a substituted coherence over a pasting scheme (list below). |
| 4. D¹ ⊗ D¹ ⊗ D¹ under both orientations, G4 syntactically | Both bracketings ((a⊗b)⊗c via the right cylinder, a⊗(b⊗c) via the left cylinder) are **checked** well formed. **G4 fails on the nose, exactly at the cube cell**: 26 of the 27 generators have syntactically equal types under the renaming; the cube cell's types differ. **G4 holds up to coherence**: substitutions in both directions, the renaming on the 26 lower generators, are **checked**. |
| D6 (pruning, insertion, rehydration for molecules) | Analysis below. Under layering (option (i) of `internal-hom.md` §4.3) nothing needs re-examination; under molecular coh (option (ii)) pruning must be restricted to factor-wise collapses. First datum **checked**: the cylinder of an identity is coherently an identity. |

## 1. The construction

**Layout.** For Γ with N variables and the path Pₚ = (0 → 1 → … → p), `cyl sd p Γ` lists p+1 copies of Γ (copy c of x at level c·N + x), then one block of cylinder generators per edge (generator of x over edge e at (p+1)·N + e·N + x). `sd = right` gives Γ ⊗ Pₚ (generators x⊗e) and `sd = left` gives Pₚ ⊗ Γ (generators e⊗x), both in the Steiner / Ara–Maltsiniotis orientation, ∂^α(x⊗y) = (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^{dim x} α} y). `Γ ⊗D¹ = cyl right 1 Γ`, `D¹⊗ Γ = cyl left 1 Γ`. By `conventions.md` §3, maps out of Γ ⊗ D¹ are **lax** transformations (f⊗e : xₑ ; f_b ⇒ fₐ ; yₑ is the lax row α_x ; Gf ⇒ Ff ; α_y) and maps out of D¹ ⊗ Γ are **oplax** ones. Mikhail's "Γ ⊗ D¹" is `cyl left 1 Γ` (`conventions.md` §5).

**Types.** Write xₐ, x_b for the copies of x at the ends of edge e and x⊗e for its cylinder generator. For a 0-cell, x⊗e : xₐ → x_b. For x of dimension m ≥ 1 with x : s → t, writing ";" for composition along dimension m−1:

- right (Γ ⊗ D¹): x⊗e : (s⊗e) ; L(x_ε) ⇒ R(x_ε′) ; (t⊗e), where ε = b, ε′ = a for m odd and ε = a, ε′ = b for m even;
- left (D¹ ⊗ Γ): e⊗x : L′(xₐ) ; (e⊗t) ⇒ (e⊗s) ; R′(x_b).

The whiskerings are defined by recursion on m, for y of dimension m and c an m-cell parallel to a copy of y, with ▹ / ◃ whiskering along dimension m−2:

```
right:  L_m^y c = R_{m−1}^{sy} c ▹ (t s y)⊗e        R_m^y c = (s s y)⊗e ◃ L_{m−1}^{sy} c
left:   L′_m^y c = L′_{m−1}^{sy} c ▹ (t s y)⊗e      R′_m^y c = (s s y)⊗e ◃ R′_{m−1}^{sy} c
L_1 = R_1 = L′_1 = R′_1 = identity
```

So in Γ ⊗ D¹ the end copy used and the side of each whiskering **alternate with dimension**, while in D¹ ⊗ Γ they do not. In low dimensions:

```
right:  f⊗e : xₑ ; f_b ⇒ fₐ ; yₑ
        α⊗e : fₑ ; (αₐ ▹ yₑ) ⇛ (xₑ ◃ α_b) ; gₑ
        Θ⊗e : αₑ ; ((xₑ ◃ Θ_b) ▹ gₑ) ⇛ (fₑ ◃ (Θₐ ▹ yₑ)) ; βₑ
left:   e⊗f : fₐ ; yₑ ⇒ xₑ ; f_b
        e⊗α : (αₐ ▹ yₑ) ; gₑ ⇛ fₑ ; (xₑ ◃ α_b)
```

Each ";", "▹", "◃" is one coh over a pasting scheme (a glued pair of disks), built by `rw`, `lw`, `vcomp` in `GrayCtx.Elab`. Binary composition along k is the k-whiskering of two (k+1)-cells, so a single canonical term is used for each composite and boundaries match syntactically; no associator or unitor is needed for globular Γ, in any dimension tested.

**Composite boundaries.** If a generator of Γ has a boundary that is a binary composite of 1-cells u ; v (recursively), the cylinder of that boundary is the layering

```
right:  (u;v)⊗e = assoc⁻ ; (u⊗e ▹ v_b) ; assoc ; (uₐ ◃ v⊗e) ; assoc⁻     (5-fold vertical composite)
left:   e⊗(u;v) = assoc ; (uₐ ◃ e⊗v) ; assoc⁻ ; (e⊗u ▹ v_b) ; assoc
```

This is the G(2) existence construction of `conjectures/gray-contexts-in-catt.md` §3.2, specialised. It is exactly what the Gray cube needs. Other composite boundaries are not handled (`cyl` returns `nothing`); that general case is the naturality construction of Conjecture N (ledger C1).

**What the checker establishes.** That the output context is well formed (G1 for these instances). It does *not* establish that the output presents the Steiner Gray tensor (that is `gray-contexts-in-catt.md` §6.2(2)). The orientations were derived by hand from Steiner's formula. Evidence that they are right:

- `Checks.CrossFree`: `cyl left 1 Γ` agrees syntactically, up to the renaming of variables, with `CaTTExp.Free.Cylinder.cyl Γ`, which another thread wrote independently from Lemma 1 of `conjectures/naturality-arbitrary-depth.md`, on D¹, D², D³, D⁴, the vertical and horizontal pairs, the 1-sphere, the loop and the 2-loop. As a non-vacuity check, `cyl right 1 D¹` does not agree with it.
- `Checks.Cube`: `cyl right 1 D¹` and `cyl left 1 D¹` are the same square A ⊗ B up to renaming (as they must be: the first has factors D¹ ⊗ e, the second e ⊗ D¹).
- G3, vertical composition and the cube below all typecheck, which constrains the orientations: for instance, using the same end copy in every dimension of Γ ⊗ D¹ (no alternation) does not give well-typed generators from dimension 2 on, since the boundary of α⊗e would not be parallel.

## 1a. D13: well-formedness for every globular Γ

**Construction** (`GrayCtx.Natural`, used by `cyl sd 1` on globular Γ). For x of dimension m in Γ, the classifying map χ_x : D^m → Γ sends the generic m-cell to x (levels 2k, 2k+1 of D^m go to the k-dimensional source and target of x). The generator x⊗e is given the type T_m of the top generator of D^m ⊗ D¹, renamed along χ_x ⊗ D¹. The elaborator (`CylGen.cylGen`) runs only on the disks, once per dimension. On every globular context tested (D⁰–D⁵, all 23 pasting schemes with ≤ 4 edges, the 1-sphere, the loop and 2-loop, the vertical and horizontal pairs, both orientations), this is **syntactically equal** to the elaborator run on Γ itself (`Checks.NaturalAgree`). The disk types have the expected dimensions, so no failure is hidden behind a default.

**Theorem** (`NaturalWF.cylN-wf`, no postulates, `--safe`). Let Ts be any family of types such that each T_j is well typed in D^j ⊗ D¹ minus its top generator, for j ≤ k. Then the cylinder built from Ts is well formed for every well-formed globular Γ of dimension ≤ k. Proof:

- copies of Γ are renamings of Γ;
- renaming along a type-respecting map of levels is admissible (`rn-ty`, by the same induction as `CaTTExp.Subst`);
- **(CL)** χ_x respects types, Γ(χ_x d) = χ_x(D^m(d)), and sends the boundary of D^m below x;
- **(CC)** χ_x ∘ χ^{D^m}_d = χ_{χ_x d}. So χ_x ⊗ D¹ sends the generator of each boundary cell d of D^m to the generator of χ_x d, whose type is T_{dim d} renamed along χ_{χ_x d} ⊗ D¹. This is literally the image of its type in D^m ⊗ D¹. Parallel cells s, t of a globular context have the same classifying map below the top, which is where globularity is used.

`Checks.Natural` certifies the disk hypothesis for k = 5 in both orientations. This gives **`cyl-wf`: Γ ⊗ D¹ and D¹ ⊗ Γ are well formed for every well-formed globular Γ of dimension ≤ 5**. `cylN-wf-all` gives all dimensions from the disk statement for all n.

**Open: the disks uniformly in n.** That D^n ⊗ D¹ is well formed for every n is not proved. It is a statement about the elaborator's output on one context per dimension. Two remarks for whoever proves it. The elaborator uses fixed fuel (`F = 16`), so as written it is guaranteed to produce the intended types only up to a bounded dimension. An all-n proof needs a fuel-free, explicit T_n: the whiskered binary composite with the alternating whiskerings of §1, written as coh over explicit trees. Its typing must then be proved by induction on n, which means the ps-ness and side conditions of the whiskering trees for all n. **Done towards this:** the whiskering trees for all n. `CaTTExp.Derived` defines, with no fuel, the right and left whiskers c ▹ₖ h and h ◃ₖ c of an n-cell by a (k+1)-cell along k (and so the composite of two (k+1)-cells along k) as coh over explicit pasting contexts `BK k j`, `LK k j` (n = j+k+1), and proves for all k and j that they are well-typed operations: the contexts are ps, the whisker type is well formed, and the side condition holds (source on exactly ∂⁻, target on exactly ∂⁺). `Checks.WhiskerAgree` checks that these are literally the elaborator's `rw`/`lw` terms for all k + j ≤ 5. `CaTTExp.DerivedBoundary` adds the rules for given cells: c ▹ₖ h and h ◃ₖ c are well typed whenever c and h are (`rwT-wf`, `lwT-wf`), and their types are computed from the boundary of c: for c : s → t of dimension ≥ k+2, c ▹ₖ h : (s ▹ₖ h) → (t ▹ₖ h) and h ◃ₖ c : (h ◃ₖ s) → (h ◃ₖ t); for c of dimension k+1 the composite goes from s_k c to z (`rwT-ty`, `lwT-ty`, `rwT-ty0`, `lwT-ty0`). Remaining: T_n and its typing by induction on n.

## 2. G3

Γ ⊗ (D¹ ∨ D¹) = `cyl sd 2 Γ` has copies 0, 1, 2 and edge blocks i, j. The inclusions ι₁ (copies 0, 1, block i) and ι₂ (copies 1, 2, block j) of Γ ⊗ D¹ are renamings; their images cover every variable and meet exactly in copy 1 (`G3-cover-meet` checks this for every N ≤ 12, and `G3-length` that `cyl sd 2 Γ` has 5N variables on the trees of `G3-≤3`). A renaming is well typed exactly when each target variable's type is the renamed source type, syntactically. So G3 holds **on the nose**, not up to coherence: the cylinder generator's type depends only on the two copies and the edge, and the construction commutes with renaming them.

## 3. Vertical composition

`compSub sd Γ` is defined for every globular Γ of dimension ≤ 2. Well-typedness is **checked** only on D¹, D², the composable pair (both orientations) and the horizontal pair of 2-cells (right); a proof for all such Γ is open (D13), and Γ of dimension ≥ 3 is D15. It sends copy 0 to copy 0, copy 1 to copy 2, and the cylinder generator of x to a composite "x⊗(i;j)":

- **x a 0-cell:** xᵢ ; xⱼ.
- **f : x → y (right):** (xᵢ;xⱼ);f₂ ⇒ xᵢ;(xⱼ;f₂) ⇒ xᵢ;(f₁;yⱼ) ⇒ (xᵢ;f₁);yⱼ ⇒ (f₀;yᵢ);yⱼ ⇒ f₀;(yᵢ;yⱼ): associator, xᵢ ◃ fⱼ, associator, fᵢ ▹ yⱼ, associator. Left is the mirror image.
- **α : f ⇒ g (right):** a 3-cell from (fᵢ;ⱼ) ; (α₀ ▹ (yᵢ;yⱼ)) to ((xᵢ;xⱼ) ◃ α₂) ; (gᵢ;ⱼ), as a vertical composite of eleven 3-cells acting on the flattened chain of 2-cells:
  1. regroup (flatten);
  2. naturality of the associator in its first argument (moves α₀ past it);
  3. functoriality of right whiskering: (fᵢ ▹ yⱼ);((α₀ ▹ yᵢ) ▹ yⱼ) ⇛ (fᵢ;(α₀ ▹ yᵢ)) ▹ yⱼ;
  4. **αᵢ ▹ yⱼ**;
  5. functoriality back;
  6. naturality of the inverse associator in its middle argument;
  7. functoriality of left whiskering;
  8. **xᵢ ◃ αⱼ**;
  9. functoriality back;
  10. naturality of the associator in its last argument;
  11. regroup.

  Each non-generator step is a coherence over a pasting scheme, substituted and whiskered into the chain ("regroup ; whisker ; regroup", `stepAt` in `GrayCtx.Elab`). Left is the mirror image (steps in the opposite order).

**Answer to `internal-hom.md` §7 item 3.** For Γ = D¹ and D², and in fact every globular Γ of dimension ≤ 2, plain coh provides every needed term. The list of coherences used is: associator and inverse; naturality of the associator in each argument; functoriality of whiskering on each side; identities and unitors (only in the D6 datum). **No non-pasting-scheme composite is needed** at this level, so these targets give no case for molecular coh. The non-ps shapes appear only as *types of generators* (the hexagon boundary of the Gray cube), and those are handled by layering with associators.

## 4. The Gray cube and G4

Factors a, b, c; generators are triples over {0, 1, e}.

- CubeR = (a ⊗ b) ⊗ c = `cyl right 1 (a ⊗ b)`;
- CubeL = a ⊗ (b ⊗ c) = `cyl left 1 (b ⊗ c)`;

with the squares a ⊗ b and b ⊗ c both `cyl right 1 D¹`. Both orientations of the cylinder are used. **Checked:** both are well formed.

**G4 on the nose fails, only at the cube cell.** Under the renaming (a,b,c) ↦ (a,b,c), all 26 generators below the cube cell have syntactically equal types (`G4-mismatches`). The cube cell's types differ (`G4-cube-differs`). The difference, read off the terms (P = 0ee, Q = e1e, R = ee0 and P′ = 1ee, Q′ = e0e, R′ = ee1 are the six squares, A… associators):

```
CubeR:  [[A, P▹, A, ◃Q, A], R▹]   ⇛   [◃R′, [A, Q′▹, A, ◃P′, A]]
        from 00e;(0e1;e11)  to  (e00;1e0);11e
CubeL:  [P▹, [A, ◃Q, A, R▹, A]]   ⇛   [[A, ◃R′, A, Q′▹, A], ◃P′]
        from (00e;0e1);e11  to  e00;(1e0;11e)
```

The same three squares are pasted in the same order on each side, but the boundary 3-paths are bracketed differently and the associators sit at the other end. This is the "layering choices bite" of `internal-hom.md` §7 item 4, located precisely: it is the choice of **composite of the 1-dimensional boundary path**, which the two bracketings of the tensor make differently. Over CaTT_sua (strict associativity and units) both sides would become [P▹, ◃Q, R▹] ⇛ [◃R′, Q′▹, ◃P′] [conj: not machine-checked, no CaTT_sua here].

**G4 up to coherence holds.** `toL : CubeR ⊢ toL : CubeL` and `toR : CubeL ⊢ toR : CubeR` are **checked**. Each is the renaming on the 26 lower generators and sends the cube cell to the other cube cell conjugated by coherences: insert an associator and its inverse with a unitor, regroup, whisker the cube cell, regroup, cancel an associator pair with a unitor, regroup. Not checked: that toL and toR are mutually inverse up to higher cells (the composite's image of the cube cell is related to the cube cell by a 4-cell). That is a uniqueness statement for 3-dimensional composites containing a generator, the shape reduced to RC(3) in `relative-coherence.md` (ledger D2, D4).

## 5. D6: pruning, insertion and rehydration for Gray shapes

`internal-hom.md` §4.3(ii) says that if coh is extended from pasting schemes to molecules, the strict-unit / strict-associativity machinery (pruning, insertion, rehydration, from CaTT_su and CaTT_sua) must be re-examined. Findings:

**(a) Under layering (option (i)) nothing needs re-examining.** Every term produced in `GrayCtx` is an ordinary CaTT term: a coh over a pasting scheme applied to a substitution. The Gray shapes appear only as *contexts*. Pruning, insertion and rehydration act on coh terms and their pasting schemes, so they apply unchanged to these contexts' terms, and their published metatheory carries over as is. What changes is only how much the reductions simplify Gray boundaries. The first datum below shows they simplify the expected things.

**(b) Datum, checked: the cylinder of an identity is coherently an identity.** Prune D² at α ↦ id f, giving D¹ ⊢ π : D². Then π ⊗ D¹ : D² ⊗ D¹ → D¹ ⊗ D¹ needs an image for α⊗e, a 3-cell fₑ ; (id f₀ ▹ yₑ) ⇛ (xₑ ◃ id f₁) ; fₑ (right; mirror for left). `GrayCtx.Prune` builds it from the coherences "a whiskered identity is an identity" and unitors, and the substitution is **checked** in both orientations. In CaTT_su, pruning would reduce both sides to fₑ and this cell to id(fₑ). So for this case pruning commutes with ⊗ D¹ on the nose in CaTT_su and up to coherence in CaTT.

**(c) Under molecular coh (option (ii)) pruning must be restricted.** Pruning a coh over a pasting scheme P at a locally maximal variable x with σ(x) = id(t) removes x and its target and gives a pasting scheme again. For a molecule U, an atom x ⊗ y with σ(x ⊗ y) an identity forces its two boundary *molecules* to have syntactically equal images. That can happen in two ways:

- **Factor-wise:** the identity comes from a codegeneracy of a factor, e.g. σ sends x ↦ id in P and so x ⊗ y ↦ id for every y. Then U//(x ⊗ –) = (P//x) ⊗ Q is again a Gray product, and pruning is defined. The datum in (b) is this case.
- **Diagonal:** e.g. the square f⊗e with σ(xₑ) = u, σ(f₁) = v, σ(f₀) = u, σ(yₑ) = v sends both boundaries to u;v, so σ(f⊗e) = id(u;v) is allowed, but no factor degenerates. Collapsing that atom identifies two different 2-paths of the square, and the quotient is not a Gray product, and [conj] not a molecule in Hadzihasanovic's sense.

So the proposal is: **pruning for molecular coh fires only for factor-wise identities**, where it is pruning in a factor followed by ⊗. Insertion is analogous: insert into a branch of one factor. Rehydration (turning a normal form back into a CaTT term) needs composites of molecules, which is G(n) itself (ledger D2). D6 is therefore reduced to two concrete checks:

1. **[conj] Factor-wise pruning commutes with ⊗ in CaTT_su on the nose**, for P ⊗ D¹ with P a pasting scheme. (b) is the case P = D², x = α. The next case to check is a pruning that removes a 1-cell (P = Comp₂, g ↦ id), where the cylinder of a composite boundary appears.
2. **[conj] The class 𝓜 (Gray products of pasting schemes, closed under pasting) is closed under factor-wise pruning and insertion.** Factor-wise this is immediate for a single product. For pastings of products it needs checking.

Both are encodable with the code here once there is an Agda CaTT_su (no thread has one yet; see "Open").

## 6. Implementation notes

- `GrayCtx.Elab` is an **uncertified** elaborator: raw type inference, the whiskerings `rw`/`lw`, unbiased composites `vcomp`, associators, identities, unitors, `cohT` (a coh over a tree from a source/target builder and the images of the tree's locally maximal variables), and `stepAt` (rewrite a segment of a vertical chain by a higher cell). Nothing it produces is trusted; `Checks` re-checks everything with the certified checker.
- `Checks` returns typing derivations (`WF`, `WFSub`). The exhaustive results quantify over an explicit enumeration of plane trees, `trees≤ n`, with a refl-checked Catalan count. **Completeness of that enumeration is not proved in Agda**, so the theorems say "every tree in the list", and the count is the evidence that the list is all trees of that size.
- `Checks.Natural` certifies each disk in its own definition. A single function with twelve certified clauses, matching on numerals, makes Agda normalise the certified types and exhausts the heap.
- Typechecking `Everything.agda` runs all of this; the GrayCtx checks take about four minutes in total (most of it the exhaustive cylinder check and G3). An exhaustive vertical-composition check over small pasting schemes was dropped because it took over ten minutes.

## Open (recorded in `open-issues.md`)

1. **D13. The disk cylinders D^n ⊗ D¹ for every n.** Everything else is proved: well-formedness for every globular Γ reduces to the disks (`NaturalWF.cylN-wf-all`), and the disks are certified for n ≤ 5 (§1a). Remaining: an explicit, fuel-free T_n and a proof by induction on n that it is well typed. The analogous disk reduction for vertical composition (dimension ≤ 2, all Γ) is not done either.
2. **Cylinder of arbitrary composite boundaries** (Γ ⊗ D¹ for non-globular Γ). Only binary 1-composites are handled here; the general case is Conjecture N (C1) and the explicit construction of D3, both owned by NGC.
3. **D14. toL and toR mutually inverse up to higher cells.**
4. **D15. Vertical composition for Γ of dimension ≥ 3**, and associativity and unit laws for it as coherences between substitutions (`internal-hom.md` §5.3).
5. **D16. An Agda CaTT_su**, to run the two D6 checks of §5.
6. **Cross-check with the cone thread's `CylOf.cyl`** (branch `claude/project-thread-b03ys3`, not yet on main): for globular Γ it should agree with `cyl left 1 Γ` up to renaming, as `Free.Cylinder` does. Part of D5's follow-up, owned here.
