# Semistrict surface conservativity, round 2: researcher responses, filed and checked (2026-11-25)

The prompt and the 258 responses (about 2.8 MB) are in
[`semistrict-surface-conservativity-r2-2026-11-25.md`](semistrict-surface-conservativity-r2-2026-11-25.md).
Round 1 is filed in [`semistrict-surface-conservativity-partial-2026-11-24.md`](semistrict-surface-conservativity-partial-2026-11-24.md).
The follow-up prompt is [`../outbox/semistrict-surface-conservativity-r3.md`](../outbox/semistrict-surface-conservativity-r3.md).

**Verdict: partial.** None of (a), (b) or (c) is settled in every finite context and every dimension.

- **Settled in every finite context, by degree:**
  - (a) through degree 4, for every admissible E and both coherence rules;
  - (b) and (c) through degree 5 over ordinary CaTT.
- **Settled on pasting contexts:** (a) for the variable coherence rule, in every dimension.
- **The join** of insertion with the binary interchange surface fails whenever the context has a positive bubble. Recognising when the join reflects is Π⁰₂-complete.
- **The two coherence rules separate** in degree 5.
- **The bulk of the responses (about 200)** are class-by-class and degree-by-degree results on special presentations. The rest is homotopy-type data for reversible presentations, and decidability or complexity results.

By standard 11, the next round is one general prompt. It asks for the all-degree statements and supplies the rank-induction framework that Responses 233 and 235 set up.

Notation follows the round-2 prompt. The *full-support form* and the *variable form* are the two readings of the coherence case (§1.1 there). Spec ch. 2 now uses the variable form.

## How far this was checked

- **Checkers.** The cited checkers of the headline results were run on 2026-11-25 and all exit 0:
  - `tools/semistrict_surface_grid_tracks.py` (Response 233);
  - `tools/semistrict_surface_insertion_tracks.py` (235);
  - `tools/semistrict_surface_directed_power_queries.py` (83);
  - `tools/semistrict_surface_join_bubbles.py` (1);
  - `tools/semistrict_surface_component_braids.py` (28);
  - `tools/semistrict_surface_word_endpoints.py` (227);
  - `tools/semistrict_surface_mixed_winding.py` (190).

  `semistrict_surface_join_rank_gaps.py` needs a checkout argument and was not run. These are finite instance checks, not proofs.
- **Arguments read.** The arguments of Responses 3, 99, 233 and 235 were read at the level of their stated constructions, and no gap was found.
  - 233 and 235 use a rank induction: the rank-r equations reflect into rank r − 1 through degree r + 2. The step compares the "tracks" around every local confluence peak, not only the normal forms.
  - Their tree-lifting input is ordinary relative coherence on pasting contexts, which is known.
- **Everything else** was read at the headline level only and is **not independently verified**.

## Headline results

| # | Claim | Bears on | Check |
|---|---|---|---|
| 233 | The four ordinary binary surfaces containing interchange are conservative **through degree 5 in every finite context**. In degree 6 the maximal surface has exactly the inhabitation of 15 rank-≤3 equations (Response 230). Ten of these are conservative in every degree, so a degree-6 failure needs one of five higher-data laws: three rank-3 temporal laws and two rank-3 grid laws. | (b), Q3 | Argument read; checker run |
| 235 | Published insertion is conservative over CaTT **through degree 5 in every finite context**. In degree 6, its generating equations through degree 3 suffice for inhabitation. | (c), Q3 | Argument read; checker run |
| 227, 230 | Over CaTT, every type inhabited in a full binary surface (even with disc and endo-coherence removal adjoined) has an inhabitant using only the word equations (clause (i)). For the maximal surface, equations on equal-dimensional operands suffice in every context and dimension. | (b) reduction | Checker run (227) |
| 99 | For every admissible E, both coherence rules, and every S ⊆ {A, U}: reflection **through degree 4 in every finite context**. | (a), Q3 | Argument read |
| 3 | For the **variable form**, every interchange-free binary surface over every admissible E is conservative on every finite globular pasting context, in every dimension. The proof uses relative coherence for strict-image equality. | (a) on pasting contexts | Argument read |
| 2, 5, 41, 43, 96, 102, 225 | Other partial results for (a). The full-support form is conservative through degree 3 everywhere. Several classes reach degree 4–5, or all degrees: all degrees when the declarations below degree h have variable faces (Response 5); degree 5 with a globular 3-skeleton (Response 102). | (a) | Read |
| 9 | For the variable rule, the site of arities with free temporal composition that Response 222 of round 1 needs exists for every admissible E. Raw syntax is a cellular resolution of the operad of realizable values. The comparison with models on an arbitrary computad is left as a separate step. | (a), route via round-1 R222 | Read; this is the natural route to (a) |
| 83, 85, 113 | The two coherence rules **separate** on a pasting tree in degree 5: for V, for the two single-switch kernels, and for an admissible V + one equation. In the full-support form, equal-image terms can have no comparison in either direction, even with A, U. So full image equality is not conservative on pasting contexts for the full-support form. | spec choice, Prop. 4.3 | Checker run (83) |
| 13 | For both rules, the strict directed arity is not reached by raw terms in degree 4 on a pasting tree. The binary join h gives a forward strict cell between raw 3-terms whose old type stays empty after A, U. | uniform L analogue of r9 | Read |
| 1, 4, 28, 37, 176 | **The join J (insertion ∨ binary interchange) fails.** On 2-computads it is conservative iff the free strict 2-category has no nonidentity empty-to-empty cell (a bubble). A positive raw bubble rules out every finite extension (Response 4). Recognition of reflection through degree n is Π⁰₂-complete (n ≥ 4). Failure at empty 2-ends happens exactly with a positive 3-program back to them, and then in every degree ≥ 5. | (c) second part: **answered (fails)** | Checkers run (1, 28) |
| 190 | One-puncture parameters vanish, so each individual binary surface reflects through degree 5 on the inverse-probe presentations. | (b) | Checker run |
| 68 | A finite one-object computad has a 4-type that is empty in every theory, yet inhabited under every interpretation in a model with finitely many 1-cells. Countermodels finite in their 1-cells are characterised by regular languages. | method: finite models cannot separate | Read |
| 101, 103, 108, 109, 114 | Universality and localization. One fixed finite 3-computad tests uniform conservativity on all finite 3-computads (Response 101). Per-degree questions reduce to fixed globular contexts T_{n−1} or U_n (Responses 109, 114). | all | Read |
| 37, 74, 94, 95, 135, 137, 146–148, 169, 202, 210, 237, 241, 246 | Complexity of per-context recognition and inhabitation. It ranges from P-complete to Π⁰₂-complete, Ackermann-complete, and any c.e. Turing degree. | Q2 | Read |
| 160–222, 226, 228, 231–232, 236, 245, 247–248 | Homotopy-type analysis of globally reversible presentations: Hopf operations, Whitehead products and Moore spaces. These give exact or finite tests per class through degree 6, for each binary surface and for insertion. | Q2, (b), (c) | Read |
| 240, 249–258 | Single-head and rewriting tests at written boundaries. Nested operations carry comparisons through degree 6 (Response 255). | (b), (c) | Read |

## What this changes

1. **(c), second part, is answered.** The join of ≡_sua with ≈_{A,U,I} is not conservative. It fails exactly on contexts with positive bubbles, in the sense of Responses 1, 4 and 176.
2. **Q3 fallback.**
   - (b) and (c) are settled through degree 5 in every finite context.
   - (a) is settled through degree 4 in every finite context (both rules), and on pasting contexts in every dimension for the variable rule.
   - Degree 6 for (b) is reduced to five explicit rank-3 laws (Response 233). For (c) it is reduced to generating equations through degree 3 (Response 235).
3. **Coherence-rule choice.** The variable form (now the spec's rule) has the better conservativity behaviour on pasting contexts (Response 3). The full-support form fails there (Responses 83, 85, 113). This supports the spec's switch, and it matches `surface-conservativity.md` Prop. 4.3 for uniform L under the variable form.
4. **Proof technique.** Responses 233 and 235 prove a rank induction: rank-r equations reflect into rank r − 1 through degree r + 2. The all-degree questions (b) and (c) are equivalent to removing the "through degree r + 2" bound, that is, to coherence of the track comparisons in all higher degrees. The round-3 prompt asks exactly that.

## Still open

- (a) in every finite context and every degree ≥ 5. The variable form is the spec's rule; the full-support form is wanted too.
- (b) in every degree ≥ 6, starting with the five rank-3 laws of Response 233.
- (c), Catt_sua alone, in every degree ≥ 6.
- Independent verification of Responses 3, 99, 233 and 235 beyond the argument-level reading above. Round 1's positive results (3, 16, 50, 51, 170, 183, 222) are likewise unverified.
