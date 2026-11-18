# Which polygraphs are homotopy polygraphs? A recognition theorem in every dimension

*A self-contained problem. It assumes familiarity with polygraphs (computads), strict ω-categories and (∞,ω)-categories, and nothing else. Everything under "What is known" is proved and is not re-asked.*

**What we are asking for.** A recognition theorem valid in every dimension, or counterexamples that delimit one. Isolated new examples in low dimension are of little use to us.

## 1. Setting

- A **polygraph** Γ (computad) is a set of generators of each dimension, each n-generator having a source and a target which are parallel (n−1)-cells of the free strict ω-category on the lower generators. All polygraphs here are finite.
- `F(Γ)` is the free strict ω-category on Γ.
- `Free(Γ)` is the free (∞,ω)-category on Γ: generators are attached one at a time along their boundaries by pushouts of `∂Dⁿ → Dⁿ` in (∞,ω)-categories (Loubaton's Cat_ω, arXiv 2406.05425, or Campion's framework, arXiv 2311.00200). Strict ω-categories are (∞,ω)-categories, so there is a canonical comparison `c_Γ : Free(Γ) → F(Γ)`.
- Γ is a **homotopy polygraph** (or *homotopical*) when c_Γ is an equivalence, i.e. when every strict pushout attaching a generator is also a homotopy pushout.
- A 2-cell `1_x ⇒ 1_x` of F(Γ) other than the identity is a **bubble**.
- Γ is **positive in every dimension** when every generator of dimension n ≥ 2 has a source and a target that are not identity cells. (For n = 2: both boundary paths are nonempty.)

## 2. Why it matters

Homotopy polygraphs are exactly the computads whose free (∞,ω)-category can be computed strictly. Many constructions need this as a hypothesis: finite presentations of Grothendieck constructions over a free base (a weight on F(Γ) has a finite cellular presentation of its total space only when the base is homotopical), the comparison of weak and strict free objects in type theories for weak ω-categories, and pasting theorems for diagrams of non-globular shape. At present each use has to check homotopicality by hand for its particular shape.

## 3. What is known

1. **Pasting theorems.** For a strongly loop-free Steiner complex K, ν(K) is the free (∞,ω)-category on its atoms (Campion, *Pasting diagrams in higher categories are free*, arXiv 2311.00200). Chanavat (*A strengthened (∞,n)-categorical pasting theorem*, arXiv 2603.22242) extends this to regular directed complexes with frame-acyclic molecules (Thm 3.17), and deduces that **positive 2-polygraphs** (Cor. 3.39) and **regular 3-polygraphs** in Henry's sense (Cor. 3.38) are homotopy polygraphs. Comment 3.40 there describes the extension to arbitrary regular and positive polygraphs as expected, without proof.
2. **Bubbles obstruct.** If F(Γ) has a bubble q (Γ of dimension 2), sending every 2-generator to 1 gives r : F(Γ) → B²ℕ with r(q) = k > 0, and q defines i : B²ℕ → F(Γ) by Eckmann–Hilton. Since ri = [k] acts by kʲ on H_{2j}(K(ℤ,2); ℚ), the groupoidification of F(Γ) has nonzero rational homology in every even degree. The groupoidification of Free(Γ) is a finite CW complex, so Γ is not homotopical. Example: (x; σ : 1_x ⇒ 1_x), where F(Γ) = B²ℕ groupoidifies to K(ℤ,2) (Ara, *A Quillen Theorem B for strict ∞-categories*, Thm 4.9, Ex. 4.10) and Free(Γ) to S².
3. **Bubble-freeness is undecidable**, already for one-vertex 2-polygraphs with no generating bubble: reachability `w ⇒* v` in a positive semi-Thue system R reduces to the existence of a bubble in R plus an insertion rule `ins : 1 ⇒ L w Z` and a deletion rule `del : L v Z ⇒ 1` with fresh letters L, Z.
4. **Positivity is not necessary.** (∗; t : ∗ → ∗; η : 1 ⇒ t) is homotopical: F₂ of it is BΔ⁺_inj (order-preserving injections under concatenation), and coherent freeness follows from Env_{E1}(E0) ≃ Δ⁺_inj (Blans–Linskens, arXiv 2605.03150). Its suspension (0, 1; f; α : f ⇒ f; T : 1_f ⇛ α) is a non-positive homotopical 3-polygraph.
5. **An operadic class.** If Γ has one vertex and every 2-generator has a single generating arrow as target (any source, possibly empty), then F₂(Γ) ≅ B Env_{E1}(P) for the free planar coloured operad P, and Γ is homotopical. The same holds with "source" for "target".
6. **Not every non-positive polygraph with one-sided units is homotopical.** For R = (∗; t; η : 1 ⇒ t, ε : t ⇒ 1), η · ε is a bubble, so R is not homotopical.
7. **Adjoining 1-generators preserves homotopicality** in dimension 2 (loops and cycles allowed): in Haugseng's matrix enrichment, adjoining f : s → t is a tensor algebra whose homs agree with the strict extension's homs. Consequently a **partition test** is sufficient and decidable: if the vertices split into parts such that no 2-generator's boundary uses an arrow between parts, and each part is either positive, or a single vertex whose 2-generators all have a single generating arrow as target (or all as source), then Γ is homotopical.
8. **Positivity in the top dimension alone is not enough.** One vertex, b : 1 ⇒ 1, Ω : b ⇛ b: Ω has non-identity boundaries, but b is a bubble.
9. **Regularity is not necessary.** The positive, non-regular 3-polygraph x, y, z; p, q : x → y, r : y → z; α, β : p ⇒ q; ζ : α ▷ r ⇛ β ▷ r is homotopical (the Θ-nerve of F is a union of the nerve of the 2-skeleton and a full sub-3-globe, meeting in ∂D₃).
10. **Some 3-dimensional attachments.** Let D be a strict 3-category with a finite homotopical presentation and vertices s, t such that no nonidentity 1-cell enters s or leaves t and D(s,s) = D(t,t) = 1. Replacing D(s,t) by a homotopical 2-cell attachment of it is a homotopical 3-cell attachment. With incoming and outgoing arrows, the correct attachment is along `I ∨ ∂D₃ → I ∨ D₃`, and wedge-suspension preserves homotopy pushouts.
11. **Strict versus "stricter".** Chanavat (*Homotopy theory of stricter n-categories*, arXiv 2509.26563) shows that strict n-categories and stricter n-categories (governed by regular directed complexes) agree for n ≤ 3 and differ from n = 4 (Comment 2.67: a 4-dimensional regular directed complex whose molecules do not form a polygraph under strict composition).
12. **Homological coherence.** Homotopical implies homologically coherent (polygraphic homology equals the homology of the Street nerve). Guetta conjectures that a free 2-category is homologically coherent exactly when it is bubble-free (*Homology of strict ω-categories*, PhD thesis, arXiv 2104.12662, Conj. 6.6.5); item 2 gives one half.

## 4. Questions

**Question 1 (main: positivity in every dimension).** Is every finite polygraph that is positive in every dimension a homotopy polygraph? This is the "positive" half of Chanavat's Comment 3.40. If it fails, find the smallest counterexample. Item 11 suggests where to look in dimension 4: a positive polygraph whose strict free ω-category satisfies an exchange relation that its free (∞,4)-category does not.

**Question 2 (dimension 2 exactly).** Is every finite bubble-free 2-polygraph homotopical? This would give, for 2-polygraphs, "homotopical ⇔ bubble-free" and the "if" half of Guetta's conjecture. The smallest open cases are one-sided polygraphs outside item 7, for example
- (∗; s, t; η : 1 ⇒ st, μ : ts ⇒ t);
- several vertices in one part, or 2-generators whose source and target are both composite and some boundary empty.

If the answer is no, characterise the homotopical 2-polygraphs (the class is then not decidable by item 3 alone, so the characterisation may be a non-decidable one).

**Question 3 (a criterion for all dimensions that covers the non-positive examples).** Give a sufficient condition for homotopicality, in every dimension, that contains both positive polygraphs (if Question 1 is positive) and the operadic class of items 4–5 and their suspensions, and that is checkable on finite data. One candidate shape: Γ is homotopical when it is bubble-free in a suitable all-dimensional sense (no nonidentity endo-cell of an iterated identity, in any dimension) and each generator's attachment is "locally" one of the known homotopical types.

## 5. What counts as a solution

A proof of Question 1 or 2; a counterexample with a proof of non-homotopicality (for example by a homology computation, as in item 2); a sufficient criterion for Question 3 with proof; or a published reference.

## 6. Literature (searched 2026-11-18)

- Campion, arXiv 2311.00200; Chanavat, arXiv 2603.22242 (Thm 3.17, Cors. 3.38–3.39, Comment 3.40); Chanavat, arXiv 2509.26563.
- Henry, *Regular polygraphs and the Simpson conjecture*, arXiv 1807.02627.
- Guetta, arXiv 2104.12662 (Conj. 6.6.5); Guetta, *Polygraphs and discrete Conduché ω-functors*, Higher Structures 4(2) (2020).
- Ara, *A Quillen Theorem B for strict ∞-categories*.
- Hadzihasanovic, *Combinatorics of higher-categorical diagrams*, arXiv 2404.07273.
- Blans–Linskens, arXiv 2605.03150.
- No published recognition theorem for homotopy polygraphs beyond the classes in item 1 was found.
