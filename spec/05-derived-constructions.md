# Chapter 5. Derived constructions

This chapter adds **no rules**. Every construction here is an algorithm that takes kernel syntax (contexts, terms, substitutions) and produces kernel syntax, which the kernel then checks like any other input. The algorithms are the Gray tensor of contexts, cylinders, naturality cells and cones. All of them rest on one construction, **relative coherence** (§5.1), which supplies the cells that connect two terms with the same strict meaning.

Each section gives the algorithm's input, its output, the steps, a worked example, the semantics, and its status.

## 5.0 Which core the constructions are valid in

The algorithms build plain CaTT terms: their correctness proofs use the reference side condition of chapter 1 (equality in the free strict ω-category). How they transfer to the kernel:
- **Inside a single hom, two-tier L.** L restricted to one hom is plain CaTT (chapter 2, §2.2: the 𝔉 instance on a single hom is Finster–Mimram's rule). So every construction whose context lives inside one hom 𝒦(X, C) is valid verbatim in two-tier L. That covers the cases the notes use: elements and their cells live in 𝒦(⊤, C) by suspension.
- **Across objects, or in uniform L.** A construction is valid verbatim in a core exactly when every coherence head it emits is accepted there. Classify the emitted heads by their pasting context Q (`notes/uniform-marks.md` §6):
  - **(H1) interchange-free.** At most one hom of Q has cells of hd ≥ 1, and that hom's diagram is a globe or a vertical chain of globes. Examples are chain contexts of 1-cells, whiskerings, vertical composites, and unitors and associators of 1-cells. Here ν = 𝔉 = F_{V+S}. **No marks, in every core.**
  - **(H2) interchange inside one hom.** Two-tier L needs nothing (E1). V + S needs `ord` on the hom's target object, and the head is accepted iff its V-fibre is connected. There is no general relative coherence of V + S over 𝔉 (it fails in every setting, ledger E13), so this is decided head by head. Inner-strip heads fail when the inner law is off. Heads like the loop H against 1_w, or the outer W-strip, fail in every setting.
  - **(H3) across objects.** Two-tier L needs `ps*` on the later factor, or `inv` on a factor, of every mixed Gray cell the head inverts, plus E5's relative coherence lemma, which is now proved (ledger E5). The step left is realizing the strict comparison cell as an L⁺ term. V + S also needs `ord` on the targets, and fibre connectivity as in (H2).
- **With every object of the emitted heads marked `ord`**, V + S accepts each head by (COH-ord) exactly when two-tier L does, so the two-tier column of the table applies verbatim (chapter 3, §3.6; ledger S16(b)). The uniform column is for heads with a non-`ord` object.
- **Native naturality needs no construction.** For a native lax transformation α in 𝒦(B, C) and any cell c of 𝒦(X, B), the naturality cell is the Gray cell G(c, α): one operation-case coherence, with no marks in any core. §5.2 is needed only for transformations given as cylinder data.

| Construction | Two-tier L | Uniform V + S |
|---|---|---|
| RC(1) | no marks | no marks |
| RC(n ≥ 2), inside one hom | no marks | `ord` on the target + fibre connectivity, head by head |
| RC(n ≥ 2), across objects | `ps*`/`inv` on the inverted mixed cells + E5 | the same, plus `ord` and fibre connectivity |
| N, Y without objects, inside one hom | no marks | as RC inside one hom |
| N with objects in Y (cylinder data) | `ps*` on the squares + E5; native transformations: G(c, α), no marks | the same, plus `ord`; G(c, α): no marks |
| Explicit cylinders (5.3.1); specified cone (5.4.1) | no marks (contexts only) | no marks |
| M ⊗ Dⁿ templates (5.3.2) | as RC (inside one hom / across objects) | as RC |
| Cones over arbitrary Γ (5.4.2) | hd-0 boundaries: no marks; higher: as RC across objects | the same, plus `ord` for higher boundaries |
| Canonical Gray terms (5.5) | no marks | `ord` on the target when lifts have inner letters |

**Status.** The "no marks" entries are **proved** (H1 heads, or contexts only). The two-tier entries are proved up to the L⁺ term-realization step of E5, since the lemma itself is proved. The uniform entries beyond "no marks" are case-by-case: relative coherence of V + S over 𝔉 is false in every setting (ledger E13, `conjectures/answered/invertibility-in-directed-interchange-2026-11-21.md`). Ledger S8 is done. Source: `notes/uniform-marks.md` §6.

## 5.1 Relative coherence (RC)

**Input.** A finite strong-Steiner context Γ (every pasting context, every Gray tensor and join of pasting contexts, and every cylinder below is one), and two parallel n-terms T, T′ over Γ with the same strict image π(T) = π(T′) in F(Γ).

**Output.** An (n+1)-term K(T, T′) : T → T′ over Γ, built from substituted coherences. It is invertible (Benjamin–Markakis–Sarti).

**Algorithm (descent over strict subdivisions; RC r9 Response 15).** Lexicographic recursion on (n, n − l, h, |S|), where n is the input rank, l the current level of the literal face condition G_l, S the dependency-closed support of the common value, and h its generating height. Start at l = 0.
1. **h ≤ l:** globular contraction (Response 2).
2. **h = n:** compare intrinsic events (Response 3); the old caps have height ≤ n − 1 and inherit G_l.
3. **l < h < n:** write the common value as 1^{n−h} c with c intrinsic of rank h. Decompose c along Campion's decomposition poset Sd(c): every non-base generator x of the marked pullback has a least carrier p_x ∈ Sd(c), and the pieces V_p = base ∪ {x | p_x ≤ p} are closed under faces.
   - In each piece, lift with prescribed boundary, interpreting back and forth between the piece and the free weak algebra of its globular arity. Bridges JR ⇒ id come from recursive calls of smaller support or lower height; inverses are computed inside the piece.
   - Glue the local lifts along Sd(c) with three rules: a zigzag of comparable monotone maps from the identity to a constant; grouping along a monotone map; the cocartesian variant over a bottom element. Campion's proof of his Theorem 4.21 supplies the zigzags and the cocartesian projections (U_{k−2}, then the bottom fibre), with Sd_{{k−1}}(µ) ≅ Lin(At_k(µ)) and Arone's coreflection I ↦ I ∩ Min.
4. Variables below the current level stay literal; above it, the two staircases of Response 6 act on expressions, raising l when a lower mark is met.

Every recursive call decreases the measure (checked call by call, `notes/relative-coherence.md` §7.14 point 1). The algorithm never searches: generator assignments are computed on demand in increasing face rank.

**Example (RC(1), any context).** Two 1-terms with the same endpoints and the same flattened path w are both full parallel terms over the chain context C(w), pulled back along ι_w : C(w) → Γ. One coherence κ_w : a → b over C(w) connects them. In dimension 2, Theorem A gives K for every context, with a term generator `tools/rc2.py` whose output the certified checker accepts.

**Semantics.** RC for all n on Γ is equivalent, for finite torsion-free computads, to the unit condition η ∈ W, so it is what makes CaTT's free objects on Γ agree with the weak ones (`notes/conjectures/answered/catt-models-unit-condition-2026-11-19.md`).

**Status.**
- RC in every dimension for every finite strong-Steiner context: **proved** (verified researcher answer, `notes/conjectures/answered/relative-coherence-all-dimensions-r9-2026-11-20.md` Response 15; independent second check `notes/relative-coherence.md` §7.14). The one citation gap (cocartesianness of U_{k−2}) is closed at argument level in Campion's setting (§7.15, independently checked). It rests on Campion's §4 at the same level as his own Theorem 4.21.
- The gluing bookkeeping and the poset zigzags: **Agda-checked** (`CaTTExp.CarrierGluing`); the poset counts: computed (`tools/rc_lin_ideals.py`).
- RC(2) in every context: **proved** (`notes/relative-coherence.md` §2), generated terms **Agda-checked** on instances (§9 there).
- RC fails for contexts with loops in dimension 3 (Eckmann–Hilton; the acyclic context (x, a : 1_x → 1_x)): counterexamples.
- Open: an elementary size bound (ledger C1), and a polynomial recognizer for shared canonical forms (E9′); both owned by RCX. These are cost questions.

**Source.** `notes/relative-coherence.md` §0, §2, §7.14–7.15; ledger C1, D2.

## 5.2 Naturality of coherences (N)

**Input.** A pasting context Q, a coherence term c over Q, and an up-closed set Y of variables of Q (the variables that move).

**Output.** The naturality cell of c over the cylinder context Q↑Y, which has two copies of Q, identified outside Y, and a cylinder generator for each variable of Y. When Y is everything, this is c's component in Q ⊗ D¹.

**Algorithm (N ⇐ RC, `notes/relative-coherence.md` §4.1).** By recursion on terms, in the order fixed by the verified ladder theorem: lower-dimensional lifts first, then the filler, then same-dimension structural recursion.
1. For a variable y ∈ Y, its lift is the cylinder generator y↑. For a variable outside Y, it is the identity.
2. For a coherence coh_{P,B}[γ], the lifts of the boundary of B are already built. They give two parallel terms over the cylinder context P↑(γ⁻¹Y) with the same strict image. RC (§5.1) on that cylinder connects them, which is the filler.
3. Substitute γ's lifts into the filler.

**Example (the associator, depth 2).** Over the full chain x → y → z → w, the associator's naturality 3-cell is generated by `tools/ladder.py` and accepted at exactly its stated type by the certified checker (`src/CaTTExp/Generated/AssociatorNaturality.agda`).

**Semantics.** The cell is the component of the lax transformation obtained by evaluating c on a cylinder, i.e. c's coherent naturality.

**Status.** N ⇐ RC: **proved**. With §5.1 this gives N at every depth for every cylinder Q↑Y that is strong Steiner, which includes every pasting Q. N for every term of dimension ≤ 2 and every up-closed Y: **proved** independently (§4.2 there). Ladder instance: **Agda-checked** (ledger C1b, closed). The ledger rows C1, D2 and B19 still describe RC(n ≥ 3) as open; ledger S9 propagates Response 15 to them.

## 5.3 Cylinders and the Gray tensor of contexts

### 5.3.1 Explicit cylinders over globular contexts

**Input.** A globular context Γ (every variable's boundary is a variable), a side (right: Γ ⊗ Pₚ, lax; left: Pₚ ⊗ Γ, oplax) and a path length p.

**Output.** The context `cyl sd p Γ`: p + 1 copies of Γ, then a cylinder generator per variable and edge.

**Algorithm.** Write xₐ, x_b for the copies at the ends of an edge e and x⊗e for the cylinder generator. For an object x, x⊗e : xₐ → x_b. For x : s → t of dimension m ≥ 1, writing ";" for composition along dimension m − 1:
- right: x⊗e : (s⊗e) ; L(x_ε) ⇒ R(x_ε′) ; (t⊗e), with ε = b, ε′ = a for m odd and ε = a, ε′ = b for m even;
- left: e⊗x : L′(xₐ) ; (e⊗t) ⇒ (e⊗s) ; R′(x_b).

The whiskerings are defined by recursion on m (▹, ◃ whisker along dimension m − 2):
```
right:  L_m^y c = R_{m−1}^{sy} c ▹ (t s y)⊗e        R_m^y c = (s s y)⊗e ◃ L_{m−1}^{sy} c
left:   L′_m^y c = L′_{m−1}^{sy} c ▹ (t s y)⊗e      R′_m^y c = (s s y)⊗e ◃ R′_{m−1}^{sy} c
L_1 = R_1 = L′_1 = R′_1 = identity
```

**Example.** Right side, low dimensions:
```
f⊗e : xₑ ; f_b ⇒ fₐ ; yₑ
α⊗e : fₑ ; (αₐ ▹ yₑ) ⇛ (xₑ ◃ α_b) ; gₑ
```
The first line is the lax naturality square α_x ; Gf ⇒ Ff ; α_y of `notes/conventions.md` §3.1.

**Semantics.** Maps out of Γ ⊗ D¹ are lax transformations; maps out of D¹ ⊗ Γ are oplax ones.

**Status.** Well-formedness for every globular Γ of dimension ≤ 5, both sides: **Agda-checked** (`NaturalWF.cylN-wf-all`). Cross-checked against the independent `CaTTExp.Free.Cylinder`. G3 (Γ ⊗ (D¹ ∨ D¹) is two glued cylinders) holds on the nose, checked for small Γ. **Source:** `notes/gray-cylinders.md` §1, §1a, §2.

### 5.3.2 The Gray tensor M ⊗ Dⁿ for every Steiner context (the repaired rule)

**Input.** A context M with a strong Steiner basis and n ≥ 1.

**Output.** A context T_n M with F(T_n M) ≅ F(M) ⊗ Dⁿ, and a translation of terms over M into terms over T_n M.

**Algorithm.** For each generator x of M and each cell y of Dⁿ, a variable x_y : B[Θ_{x,y}], where B is the **boundary template** for the pair of shapes. Terms translate structurally: ⟦coh[σ], y⟧ = C[σ̂_y], where C is the **coherence template**. Templates are checked by signed, dimension-indexed free-variable sets.
- Boundary templates exist once strict d-cells lift with prescribed boundary, which RC in dimension ≤ d − 1 gives (Lemma 2 of the answer). With §5.1, templates exist in every dimension.

**Example.** M = the walking arrow, n = 1: T₁M is the lax square. M = the composable pair: T₁M is the cylinder of 5.3.1.

**Semantics.** Sound and canonical for every Steiner M and every n, and literally functorial in substitutions.

**Status.** The rule: **proved** (verified researcher answer, `notes/conjectures/answered/gray-tensor-of-contexts-rule-2026-11-18.md`); existence of templates in every dimension follows from §5.1. Agda (ledger D3, GCTX): templates (B) and (C) and the translation for M ⊗ D¹ and D¹ ⊗ M, (B) certified for p ≤ 4 in both orders, T₁M certified for the walking arrow, triangle and lax square. **Open in Agda:** q ≥ 2, more C-templates, (B) for all p, typing of T₁M for every M (D3). Associativity of iterated tensors up to coherence (G4) reduces to RC, hence holds; the Gray cube's two bracketings agree on 26 of 27 generators on the nose (`GrayCtx/Cube.agda`, D4).

## 5.4 Cones, cocones and transfor shapes

### 5.4.1 The specified cone over a globular context

**Input.** A globular context Γ and a fresh apex name c.

**Output.** Cone(Γ; c): Γ, then c : ⋆, then for each variable t of Γ in order a variable p_t.

**Algorithm (Mikhail's Thm 3.3 formula).**
```
p_x : c → x                                                   (dim x = 0)
p_t : p_{τt}  →  p_{σt} ∗_{m−1} (p_{σ²t} ∗_{m−2} ( … (p_{σᵐt} ∗₀ t)))      (dim t = m ≥ 1)
```

**Example.**
```
f : x → y      p_f : p_y ⇒ p_x ∗₀ f
α : f ⇒ g      p_α : p_g ⇛ p_f ∗₁ (p_x ∗₀ α)
```

**Semantics.** For Steiner Γ, the free strict ω-category of Cone(Γ; c) is the Ara–Maltsiniotis join c ⋆ Γ (Prop. 2.5 there; the join's sign convention is cited, not re-checked). The cone is lax at the vertices, in Mikhail's orientation.

**Status.** Well-typedness: **proved** (Lemma 2.2), **Agda-checked** on 12 shapes up to dimension 4 (`CaTTExp.Cones`, `ConesExamples`); a general Agda typing proof is open (B22). It is one of the cones Mikhail's (KE) admits: **proved** and machine-checked. **Source:** `notes/specified-cones.md` §2.

### 5.4.2 Cones over arbitrary contexts

**Input.** Any finite context Γ (boundaries may be coherence terms).

**Algorithm.** Extend p to all terms by recursion (lower lifts, then filler, then structural):
```
P(x)              := p_x
P(coh_{Q,B}[γ])   := Π(Q, B)[Cone(γ)]
```
where Cone(γ) sends q ↦ γ(q), c ↦ c, p_q ↦ P(γ(q)), and Π(Q, B) is a cell of Cone(Q; c) of type P(τc₀) → T_{c₀}, for c₀ = coh_{Q,B}[id]. Π(Q, B) is obtained by RC (§5.1) on the join context Cone(Q; c), through the cut translation that lowers RC by one dimension (cone-over-coherences r2).

**Example.** τ : f ∗₀ g ⇒ h: the cone needs P(f ∗₀ g), which is Π(composite) applied to p_f, p_g. Machine-checked.

**Status.** Existence for every finite context follows from RC on join contexts: dimension ≤ 2 **proved** (verified), dimension ≥ 3 by §5.1 (ledger B19; S9 propagates). Agda: `ConeT.cone` and `coconeT` build cones and cocones whenever boundary terms are variables, object identities, or composites of 1-cells (checked on the bubble, μ : a ∗₀ a ⇒ a, τ, and a mixed case); 2-dimensional boundaries return `nothing` (open, CONE).

### 5.4.3 Cocones and transfor shapes

- **Cocone(Γ; c) := O(Cone(OΓ; c))**, where O reverses odd dimensions. The closed formula equals the dual syntactically (Agda, by `refl`).
- **Transfor shapes Tr_k(Γ; c):** iterated cylinder of the cone in the projection direction, transfor index first (Dᵏ ⊗ Dᵐ). Cocone transfors put the diagram index first.
  - dim Γ ≤ 1, all k: **proved** with plain coherences only, checked k ≤ 3.
  - dim Γ = 2, k = 1: **proved**, checked on 3 shapes; k ≥ 2 sketched (B18).
  - dim Γ ≥ 3: needs N at depth dim Γ − 1, which §5.2 supplies.
- **Horns are cones, reoriented:** Tr₁(Γ) ≃ Cone((D¹)^op ⊗ Γ)[π], worked out for the arrow up to unitors (B23, open in general).

**Source.** `notes/specified-cones.md` §3–5; ledger B5, B18, B19, B22, B23.

## 5.5 Canonical Gray terms (introducing a lax cell from components)

Under L, reading Gray-shaped components off a native lax cell needs no construction. **Introducing** a lax cell from component data needs a Gray-shaped context and a canonical way to fill it.

**Input.** A finite family of pasting diagrams P₁, …, P_k and their Gray tensor.

**Output.** A section: for every cell of ν(P₁ ⊗ … ⊗ P_k), a canonical term over the Gray context, functorial up to comparison.

**Status.** CT for all finite families: **proved** (r8 Response 13, verified); functoriality up to comparison and a padded recognizer (r9); coherent functoriality, an exact strict-class criterion, a superpolynomial lower bound on raw size with polynomial tableau forms, and computable comparisons (r10). Instances machine-checked: I ⊗ Dⁿ for n ≤ 4 (536 cells), D² ⊗ D² by transfer. **Source:** `notes/invertibility-markings.md` §4, §8; ledger E8.

## 5.6 Open surface questions

**Q5.1. Whether derived constructions are visible as names or only as elaborator output.**
- *Option A: named operations* (`nat c Y`, `cone Γ`, `cyl Γ`), elaborated to the algorithms' output. Readable; the user must know which construction exists for which context class.
- *Option B: invisible.* The elaborator fills a missing naturality cell or comparison whenever the user writes a hole whose type it can solve with RC. Least writing; error messages must explain a failed RC call (for example, a context with a loop).
- *Option C: both.*

**Q5.2. How much of the generated term the user sees.** RC terms have no elementary size bound and raw canonical Gray terms are superpolynomial.
- *Option A: show the term.* Honest, but unreadable beyond dimension 3.
- *Option B: show only its type, and store the term* behind a name, as a proof assistant stores a tactic's proof term. Readable; requires the checker to accept stored terms by reference, which is a surface feature (sharing), not a kernel one.
