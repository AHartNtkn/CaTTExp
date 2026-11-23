# Is invertibility in free Gray-enriched ω-categories recursively enumerable?

## Setting

**Gray ω-categories.** Let ω-Cat be the category of strict ω-categories with the lax Gray tensor product ⊗ of Ara–Maltsiniotis (arXiv:1607.00668). A *Gray ω-category* is a category enriched in (ω-Cat, ⊗).
- Inside a hom, cells compose strictly.
- Composition across objects sends the top cell of x ⊗ y (x, y of positive dimension) to a directed interchanger, which in general is not invertible.

The weak analogue is an oriented (∞,ω)-category (Gepner–Heine, arXiv:2510.10504). Write f ; g for composition along the (n−1)-boundary in diagrammatic order.

**Invertibility (coinductive).** A cell f : x → y of dimension n ≥ 1 is *invertible* if there are cells g, g′ : y → x and invertible cells l : g ; f → 1_y and r : f ; g′ → 1_x. Equivalently, f is invertible if it lies in a set S of cells such that every member has candidates g, g′ and cancellations l, r with l, r ∈ S.

**Free models.** A *marked computad* (C, M) is a finite computad C with a set M of positive-dimensional generators. F(C, M) is the free Gray ω-category on C in which every marked generator is invertible: for each marked m, adjoin m⁻ˡ, m⁻ʳ, λ_m : m⁻ˡ ; m → 1 and ρ_m : m ; m⁻ʳ → 1, mark λ_m and ρ_m, and repeat. Its cells are presented by finite terms, and equality of terms is decidable in the strict case (Steiner/Ara–Maltsiniotis normal forms for Gray tensors of free objects). The weak version is defined in the same way among oriented (∞,ω)-categories.

**Inductive certificates.** Let Cert(C, M) be the least class of cells closed under the following rules:
1. marked generators and their adjoined inverses and units;
2. identities, and in the weak case coherence cells;
3. pasting composites inside a hom whose top constituents are in Cert;
4. images of the top cell of x₁ ⊗ … ⊗ x_k with some positive-dimensional xᵢ in Cert;
5. the recorded inverse package of a member;
6. inv-intro: f, if there are g, g′ and l : g ; f → 1, r : f ; g′ → 1 with l, r ∈ Cert.

Membership of a cell, given a finite derivation, is checked syntactically.

**What is known.**
- *Ordinary (non-Gray) case.* Every invertible cell of the free ω-category on a finite marked computad is in Cert. Cells of dimension above dim C are certified, so every invertibility tower becomes certified after finitely many levels.
- *Gray case: Cert is incomplete.* Take objects a, b; generators p : a → a, x : a → b, u : 1_a ⇒ p, v : p ⇒ 1_a; and a 3-cell f : 1_x ⇛ 1_x in the hom F(a, b). Mark four further generators:
  - a contraction u ; v ⇛ 1;
  - contractions of (pu) ; (pv) and (pv) ; (pu) to identities (pu means left whiskering by p);
  - a contraction of the whiskered cell p·f to an identity.

  Then f is invertible in F(C, M), but f ∉ Cert. The reason it is invertible: the cylinders Id ⇒ p· and p· ⇒ Id built from u and v have a composite that is invertible by rule 4, and change of base along u ; v ≅ 1 splits every based cell q with p·q invertible through an invertible cell. This produces an infinite reversal tower whose individual tiles u ⊗ q and v ⊗ q are never certified.
  - To see that f is not certified, take the two-object model with homs E, where E is the strict ω-category of bit-labelled cells composed by meet, with Gray multiplication by join. Designate only identities. The marks go to identities, but f does not, so no rule sound in every model with a designated class closed under 1–6 can certify f.
  - The alternating interchangers u ⊗ v ⊗ u ⊗ … ⊗ f give uncertified invertible cells in every dimension ≥ 3.
- *Coinduction is complete but infinitary.* Invertibility coincides with the following: a family of cells indexed by a set, with at each index two candidates and cancellations, each cancellation either in Cert or carried by a successor index. Along any branch the dimension increases, so a finite index set adds nothing to Cert. Validating an arbitrary program presenting such a family is undecidable (it can encode non-halting).
- *Undecidability.* Invertibility is not decidable uniformly in (C, M). It contains the unit problem of finitely presented monoids: one object, the generators as 1-cells, each relation u = v as a marked 2-cell. Whether a finite presentation presents a group is undecidable (Narendran–Ó'Dúnlaing–Otto, Discrete Math. 98 (1991)). Cert-membership with given derivations is semi-decidable.

## Questions

1. **(Main question.)** Is the set {((C, M), t) : t an invertible cell of F(C, M)} recursively enumerable, uniformly over finite marked computads? Equivalently: is there a certificate language with decidable checking that is sound for invertibility in every Gray ω-category and complete for invertibility in every free F(C, M)? Answer for strict Gray ω-categories and for the weak version.

2. **(If yes.)** Give such a language as Cert plus finitely many rules in the same style. For example, a *schematic coinduction* rule whose certificate is a finite recipe, uniform in a dimension parameter, that produces at each index the candidates and cancellations for the next, together with a finite proof that the recipe is well-typed and closes up. State its soundness and completeness theorems, and show how it certifies f in the example above.

3. **(If no.)** Prove it, for instance by reducing the complement of the halting problem (or another non-r.e. set) to invertibility in finite marked computads. Also identify the largest natural decidable fragment beyond Cert, such as towers that are eventually periodic up to suspension or whiskering.

## Researcher Response 1

**Invertibility is not recursively enumerable in either setting.** Given a deterministic Turing machine and its input, we construct a finite marked computad and a 3-cell that is invertible exactly when the machine runs forever. Each simulated transition supplies one further copy of an arrow needed to build the next cancellation. If the machine halts, a model with a finite-dimensional hom component rules out *every* reversal tower for the given cell. Thus question 2 has a false antecedent. Question 3 admits a finite, checkable periodic rule, but there is no largest sound extension with decidable certificate checking.

### A finite word presentation supplies the clock

Use a two-way tape, an explicit blank, a finite tape alphabet $\Gamma$, and a partial deterministic transition table. Encode an ordinary configuration by $L U q a V R$, where $a$ is the scanned letter and $U,V\in\Gamma^*$. The head state, endmarkers, clock letter $s$, sweep tokens $T,B$ and one token $D(q,a)$ for each letter and state occurring in the transition table (as source or target) are distinct from one another and from the tape alphabet. Orient the following finite list of string relations for the simulation. Each occurrence of $c$ in a transition row ranges over tape letters. Write $\square$ for the blank.

| Transition at $(q,a)$ | Forward rules |
| --- | --- |
| Write $b$, enter $q'$ and move right | $qac\to bD(q',c)T$ and $qaR\to bD(q',\square)TR$ |
| Write $b$, enter $q'$ and move left | $cqa\to D(q',c)Tb$ and $Lqa\to L D(q',\square)Tb$ |
| Write $b$, enter $q'$ and stay | $qa\to D(q',b)T$ |

Add the sweep rules

$$
Tc\longrightarrow cT,\qquad TR\longrightarrow BRs,\qquad
cB\longrightarrow Bc,\qquad D(q,c)B\longrightarrow qc .
$$

The forward run is deterministic even during a sweep. Token $T$ travels to the right endmarker, inserts one $s$ beyond it, and returns as $B$ to activate the new head. Thus for consecutive clock-free configuration words $w_i,w_{i+1}$ there is a finite derivation $w_i\to^*w_{i+1}s$. This holds also at a freshly allocated tape square.

We need a bound for the *symmetric* congruence when the run halts. The language of ordinary configurations followed by $s^*$, together with words of the form $L\Gamma^* D(q,a)\Gamma^*(T\mid B)\Gamma^* R s^*$, is closed under applying any rule in either direction inside a context. Indeed, a transition replaces the unique active head by an adjacent dormant head and sweep token, or does the converse. The edge rules check the adjacent endmarker. The sweep rules move the token only across a tape letter, turn it at the right endmarker together with its exterior clock, or activate an adjacent dormant head. This accounts also for backward rewrites with several possible predecessors. If the run halts after $N$ transitions at $h$, then $h s^N$ is terminal. Its basin under forward rewriting is closed under both orientations on this language. A predecessor converges by its displayed step, and the successor of a convergent nonterminal word is its unique forward step. All forward rules are length-nondecreasing. Consequently **every** word congruent to $w_0$ has length at most $|h|+N$.

### One clock letter pays for one reversal step

Take one object. Use every presentation letter as an endomorphism generator, add two fresh endomorphisms $t,x$, and for each displayed word rule mark a 2-generator between its two sides. Multiplication of words is ordered so the action of $ws$ on its right is first the action of $s$ and then that of $w$. Write $H$ for the single ordinary hom ω-category. Add unmarked cells $u:s\Rightarrow t$, $v:t\Rightarrow s$, and a cell $f:1_x\to1_x$ of hom degree two. The four additional marked generators have boundaries

$$
u;v\to1_s,\qquad
(tu);(tv)\to1_{ts},\qquad (tv);(tu)\to1_{tt},\qquad
tf\to1_{t(1_x)}.
$$

Here juxtaposition denotes left action when the left factor is a word. The middle two marks make $tu,tv$ invertible. The first and last make $u;v$ and $tf$ invertible. Unit and composition comparisons are inserted at the indicated boundaries in a weak hom. The test term is $w_0 f$. All these data are computable from the input.

We prove the following **clock criterion** in any such model. Suppose there are words $w_i$ and invertible comparisons $w_i\Rightarrow w_{i+1}s$ for all $i\geq0$. Then $w_0 f$ is invertible. We give the details because replacing this infinite chain by a separate factorization for each depth would not produce a reversal tower.

At an object $y$ of $H$ write $0_m(y)$ for its iterated identity of hom degree $m$. A based $m$-cell is an endocell of $0_{m-1}(y)$. For any such $q$ with $m\geq2$ and $tq$ invertible, there is a split of $sq$ at $sy$,

$$
sq\xrightarrow{D}c\xrightarrow{E}sq,\qquad
D;E\simeq1_{sq},\qquad c,\ tD,\ tE\text{ invertible}.
$$

Here and below $\simeq$ between parallel cells denotes a comparison by an invertible cell. To see the split, evaluate the cylinders for $u,v$ on $q$. Write $\beta=u_y$, $\gamma=v_y$ and $e=\beta;\gamma$. The strip goes from $(sq)e$ through $\beta(tq)\gamma$ to $e(sq)$. Its composite is the component of $u;v$ on $q$, hence invertible by Gray absorption. The two individual tiles after applying $t$ are invertible by the same argument applied to $tu,tv$.

The first mark at $y$ gives $e\simeq1_{sy}$. Change base along this comparison by conjugation in successive ordinary endomorphism categories. At the first level, conjugate by the comparison and a chosen opposite inverse. At the next level use the contraction of their composite to the identity as base comparison. Iterating identifies both outer cells with $sq$ by invertible cells and transports the middle cell to an invertible $c$, since $tq$ is invertible.

The transported paste $j=D;E_0$ remains invertible, as do $tD,tE_0$. Take $E=E_0;j^r$ for a right inverse of $j$. This proves the split. It is the two-functor form of the based split proved in round two, with the left endpoint functor now whiskering by $s$ throughout. The two-tile subdivision uses the Gray tensor outside the hom, and conjugation uses ordinary composition inside it. In weak enrichment the strip is the same Steiner shape and the endpoint identifications use the ordinary weak unit, associativity and naturality comparisons. [Detailed base-change calculation](../answered/invertibility-certificates-r2-2026-11-23.md#splitting-a-based-cell-through-an-invertible-cell) · [Ara–Lucas, §6.6 and Proposition 4.9](https://arxiv.org/pdf/1909.13564) · [Gepner–Heine, Theorem 3.8.1](https://arxiv.org/html/2510.10504v1#S3.SS8)

Call a contraction $A:z\to0_m(y)$ **split** for this proof if $z$ is based, there is $B:0_m(y)\to z$ with $A;B\simeq1_z$, and $tA,tB$ are invertible. Given the split through $c$ above, let $h$ be a left inverse of $c$. Whisker $D,E$ by $h$ on the left, then paste the outgoing leg with the invertible contraction $h;c\to0_m(sy)$ and paste its inverse onto the return leg. This is a split contraction of $h;(sq)$. Right whiskering with a right inverse gives the other split contraction. In particular both cancellations needed for $sf$ are split.

For any split $A,B$ the defect $d=B;A$ is based one degree higher at $y$, with $td$ invertible. Apply the split through $c$ to $s d$ and take a left inverse $h$ of its middle cell. The two inverse candidates for $s A$ are $h;(s B)$ and $s B$. They have cancellations

$$
(h;(s B));(s A)\simeq h;(s d)\longrightarrow 0_{m+1}(sy),
\qquad
(s A);(s B)\simeq1_{s z}.
$$

The first is again a split contraction, by the whiskered construction and invertible reassociation. The second is already invertible. The invariant concerns the legs *before* applying the machine prefix. In particular this argument needs no commutation between $s$ and $t$.

For clarity, let $\Phi(X)$ be the class of cells admitting a reversal step with both children in $X$. Changes of prefix can be used in such steps even though their endpoints need not agree. In a strict hom take the equivalence relation $R$ generated by reversible cylinders on globular cells, including cylinders between cells at different bases. Then $R\Phi(X)\subseteq\Phi(RX)$, where $RX$ denotes closure under this relation.

The two endpoint projections of the reversible cylinder object lift an arbitrary cell with prescribed parallel boundary cylinders. Starting from a cylinder at the root, lift the two opposite candidates with the root's face cylinders in exchanged source and target positions. Lift each cancellation with the composite and identity cylinders on its boundary. This provides a package at the other endpoint and cylinders joining the corresponding children. Apply the same lifts along successive cylinders in a zigzag. For a prefix comparison every component of its cylinder is invertible, by absorption for its positive invertible factor and by ordinary whiskering at vertices. [Lafont–Métayer–Worytkiewicz, Lemma 13 and Corollary 2](https://arxiv.org/pdf/0712.0617#page=15) · [Ara–Lucas, §§1.13–1.16](https://arxiv.org/pdf/1909.13564#page=11)

In a weak hom form all the indicated finite strips, prefix cylinders and their whiskerings in the original model. For assembling them one may work in the coinductive completion of the **ordinary** hom. If the presentation uses nonunivalent ordinary homs, first take their ordinary univalent presentation. Full faithfulness on iterated homs up to equivalence lifts packages at specified parallel boundaries, including the composition and identity comparisons.

Coinductive completion sends coinductive isomorphisms to genuine equivalences and is surjective on cells relative to prescribed globular boundaries, up to equivalence. It reflects existence of reversal towers because a prescribed lift of the root extends across each successive free candidate and cancellation attachment in an actual tower at the image. [Ozornova–Rovelli–Walde, Lemma 5.27 and Proposition 5.29](https://arxiv.org/html/2603.11005v2#S5.SS3)

For compatibility with the orientation used here, take the free walking tower with both contractions directed toward identities. In the localized two-stage presentation the two attaching 2-cells have become invertible. Reversing one of them therefore gives an equivalent localized presentation, whose localization is terminal by the two-stage calculation of Lemma 5.38. The iterative construction attaches suspensions of the preceding stage at these same two faces. The suspension induction of Lemma 5.38 and the colimit calculation of Corollary 5.39 therefore give a walking coinductive isomorphism for this orientation as well. The choice of such walking object leaves the classified cells independent by Lemma 5.20. [Ozornova–Rovelli–Walde, §§5.3–5.4](https://arxiv.org/html/2603.11005v2#S5.SS4)

In that completion a prefix cylinder gives a path between its two globular diagrams. For a disk of degree zero this says its vertex side is an equivalence. Inductively, a map out of the next disk is a choice of endpoints and a map from the preceding disk into their ordinary hom. Transport along equivalences of the endpoints is conjugation. The remaining cylinder in that hom compares the transported diagram to the other one, by the inductive assertion. All its comparison cells are equivalences. Thus the path includes the boundaries as well as the principal cell.

Transport along such a path in the space of packages (the homotopy fibre of restriction to the root disk) transports both candidates, the composites and the two children. This proves the same inclusion for $R$ given by paths of globular diagrams. Only ordinary hom functoriality of completion is used. [Gepner–Heine, Corollary 4.8.17 and Proposition 4.9.1(1)](https://arxiv.org/html/2510.10504v1#S4.SS9)

Now take the family consisting of all invertible cells, the root $w_0 f$ and all $w_i A$ for split contractions $A$ and $i\geq1$ (in the weak gluing argument take their images and include all invertibles in the completed hom). At the root use the cylinder from $w_0 f$ to $w_1(sf)$ and the two split cancellations of $sf$. At $w_i A$ use the cylinder to $w_{i+1}(s A)$, then apply $w_{i+1}$ to the displayed package. Each child is invertible or has the form $w_{i+1} A'$ for a split contraction $A'$, up to the comparisons just proved. Writing $X$ for this family, the constructed packages yield $X\subseteq R\Phi(RX)$. Closure under zigzags gives $R^2=R$. Transport of actual packages now gives $RX\subseteq R\Phi(RX)\subseteq\Phi(RX)$, the required postfixedness. This proves the clock criterion. An infinite machine run provides exactly the required prefix comparisons by composing whiskered marked word rules.

### A bounded clock rules out every tower

Let $P$ be the monoid on the machine letters, $s,t,x$, modulo the machine relations and the additional grading equation $t=s$. This last equation is used only for indexing a model. For $g\in P$ let $L(g)$ be the supremum of the lengths of all representatives and put $d(g)=2L(g)$, allowing infinity. Concatenation gives $d(gh)\geq d(g)+d(h)$. To bound $L([w_0x])$ when the machine halts, replace every $t$ by $s$. This preserves length and sends each grading relation to equality or a machine relation. The letter $x$ is fresh and occurs in no relation, so it stays last and the prefix is congruent to $w_0$. The bound proved above gives $L([w_0 x])\leq |h|+N+1$.

Recall the strict ω-category $E$ with objects the bits. Given parallel cells, a cell between them has one of the bit labels bounded by both boundary labels, with a unique cell for each such label and boundary. Identities retain the label and composition at every cut takes meet. For a strictly invertible positive cell the two cancellation equations force its label and both boundary labels to coincide. The parallel boundaries are then equal and the cell is their identity. The Gray multiplication on $E$ takes the join on products of cube faces, with unit bit zero. Admissible cubical labels are downsets of faces. Distributivity of join over meet gives compatibility with pasting in each variable. Multiplication by the object of bit one sends every cell to an iterated identity on one. [Construction and proof of the Gray multiplication](../answered/invertibility-certificates-r2-2026-11-23.md#a-model-separating-the-cell-from-every-recorded-certificate)

Make a one-object strict Gray category whose endomorphism hom is the disjoint union, over $g\in P$, of copies of $E$ retaining all cells through degree $d(g)$ and only iterated identities above that degree. At an infinite bound retain all of $E$. Use multiplication in $P$ on the indices and the stated Gray multiplication on the fibres. This restricts to the indicated dimensions. Indeed, the tensor of an $i$-category and a $j$-category has dimension at most $i+j$ because its generating cells are principal tensors and an identity factor factors through a disk of smaller dimension. Apply the bound for $d(gh)$. The unit is bit zero at unit grade, and associativity is inherited from the two multiplications. No computability of the index bounds is needed for a separating model. [Ara–Lucas, §1.11 and Remark 2.13](https://arxiv.org/pdf/1909.13564#page=17)

Send each generating letter to its grade, giving bit zero to all machine letters and $s$, and bit one to $t,x$. Each machine relation goes to an identity. Send $u,v$ to the label-zero arrows between bits zero and one in grade $[s]=[t]$. Their composite is the identity on zero, and their images under $t$ are identities on one. Send $f$ to the degree-two cell of label zero on the identity of bit one at grade $[x]$. This cell exists since $d([x])\geq2$, and $tf$ is an identity. Thus all four extra marks can also be interpreted by identities, with their entire reversal towers. The image of $w_0 f$ is still the label-zero cell on a bit-one identity.

**Every coinductively invertible positive cell in a finite-height fibre is an identity.** Above its height all cells are identities. Descending one degree, identity cancellations imply a strict left and a strict right inverse. These coincide, so strict gauntness gives the claim. Induction reaches the root. All candidates and cancellations at a hom cell of positive degree stay in its fibre, as the hom is a disjoint union. It follows that when the machine halts, the image of $w_0 f$ is not invertible. The lax monoidal embedding of strict targets for Gray induces an embedding of enriched categories, yielding the same separating target for the weak free model. These strict homs have discrete diagram spaces and no nonidentity strict isomorphisms, so finite-fibre descent applies to the same cells. [Gepner–Heine, Remarks 3.8.3 and 4.5.4](https://arxiv.org/html/2510.10504v1#S4.SS5)

The computable construction therefore reduces nonhalting to invertibility for each of the two settings. Fixing a universal deterministic machine gives even a *single* finite marked computad for which varying only the input prefix makes invertibility of these 3-cells non-r.e. If either set were recursively enumerable, halting and its complement would both be recursively enumerable, deciding halting by dovetailing. In particular, enumerating all finite strings and running a decidable certificate checker cannot be sound and complete for this problem. [Turing, *On computable numbers*](https://doi.org/10.1112/plms/s2-42.1.230)

### Which finite recipes can be checked?

One strict extension of Cert uses a **periodic clock certificate**. Supply the finite diagram of the clock criterion with Cert proofs for its four invertibility hypotheses, a finite nonempty list of prefix words, and a successor index at each position, beginning at the specified root. For each position supply a Cert derivation of a comparison from its word to the successor word followed by $s$. The root cell is the first word applied to the supplied based $f$. Checking these finitely many typed terms and derivations is decidable under the certificate-checking assumption of the question. Following successors gives an infinite sequence, so the clock criterion proves soundness even under substitution in any model.

To certify the four-mark example in the question, take $s=1_a,t=p$ and one prefix $1_a$ pointing to itself via the unit comparison. These hypotheses are exactly its four marks and the conclusion is $f$. The criterion is typed equally for the action on a hom from $a$ to a different object, as every construction above used only the left action.

There are two meanings of “decidable fragment.” If membership of *cells* is required to be decidable uniformly, even a sound superset of Cert cannot qualify. On the marked word-relator presentation of any finitely presented monoid, finite derivations of the two unit equations give certified cancellations for a unit word. Conversely, evaluation into the ordinary presented monoid forces any reversible word to be a unit. A decider for a sound superset of Cert would therefore decide whether every generator is a unit, hence whether a finite monoid presentation presents a group. This is undecidable. [Narendran–Ó'Dúnlaing–Otto](https://doi.org/10.1016/0012-365X(91)90040-9)

If decidability concerns *checking a supplied witness*, every such sound language accepts an r.e. set of inputs and misses some true instance by the reduction. Adjoining that one instance as a ground axiom strictly enlarges the accepted set while preserving decidable checking. To require stability under substitution, allow a finite interpretation of its generators and proofs for its marks with the axiom. Soundness follows by mapping its actual reversal tower along the interpretation. Even a single fixed ground axiom is sound in every model realizing its marked presentation by freeness. Hence no inclusion-maximal fragment of this kind exists without further restrictions on the allowed rules. The periodic clock rule gives one explicit choice with a checkable witness.

### Validation

Run `python3 -B scripts/s22/check_invertibility_clock.py` and `python3 -B scripts/s22/check_invertibility.py` from the repository root. The [clock checker](../../../scripts/s22/check_invertibility_clock.py) compares direct tape execution with the string relations, checks complete symmetric congruence components for three halting examples with branching predecessors and an isolated immediate halt, and verifies 24 successive prefix factorizations on each of three infinite runs including a repeated stationary configuration. It also computes reversible cells by descending from the top of bit fibres of heights two through six. The [strip checker](../../../scripts/s22/check_invertibility.py) checks the ungraded multiplication, the marked boundaries and two-tile cylinder subdivisions through hom degree nine. The halting basin bound, the clock criterion and the finite-height descent above prove the statements for arbitrary run length and degree.
