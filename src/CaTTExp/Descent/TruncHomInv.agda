------------------------------------------------------------------------
-- Ledger F10f, part 6 (T-hom⁻ half; notes/universe-free-principles.md
-- §6a, "Correction: T-hom⁻ is false at n = 0").
--
-- T-hom⁻ in the 1-truncated encoding, with Trunc and Disc from
-- CaTTExp.Descent.TruncGrpdModel (levels −2, −1, 0, ≥ 1), and with the
-- premise read on global points: every hom-set, as a discrete
-- category, is trunc (n − 1).
--
-- What is machine-checked:
--   * n = −1 (`thom⁻-m1`): if every hom-set is contractible, C is
--     trunc −1 (a groupoid, thin, and connected);
--   * n = 0, counterexample (`thom⁻-0-fails`): every hom-set of the
--     walking arrow I is a proposition (trunc −1), but I is not
--     trunc 0;
--   * n = 0 with the extra premise that C is a groupoid
--     (`thom⁻-0-grpd`): then C is trunc 0;
--   * n ≥ 1 (`thom⁻-≥1`): holds, but vacuously here, since every
--     1-category is trunc ≥ 1.  The content of T-hom⁻ at n ≥ 1
--     concerns cells of dimension ≥ 2, which a 1-truncated encoding
--     does not have.
--
-- What is NOT machine-checked:
--   * the relative premise (homs over every generalised point, i.e.
--     relative truncation of [⟦D¹⟧, C] → C × C).  It implies the
--     global-point premise used here, so `thom⁻-m1` and `thom⁻-0-grpd`
--     also cover the relative reading.  The counterexample needs the
--     converse, that I meets the relative premise ([⟦D¹⟧, I] → I × I is
--     a full-subcategory inclusion); that is argued on paper, not
--     encoded;
--   * T-init's soundness: see CaTTExp.Descent.TInit.
------------------------------------------------------------------------
module CaTTExp.Descent.TruncHomInv where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas
open import CaTTExp.Descent.Collage using (I; IOb; o0; o1; IHom)
open import CaTTExp.Descent.TruncGrpdModel
  using (Lvl; m2; m1; l0; l1; Conn; Trunc; IsGrpd; Thin; Disc)

-- The premise of T-hom⁻ at level n, on global points.
HomsTrunc : Cat → Lvl → Set
HomsTrunc C k = ∀ x y → Trunc (Disc (Cat.Hom C x y)) k

------------------------------------------------------------------------
-- n = −1: contractible homs.

thom⁻-m1 : ∀ C → HomsTrunc C m2 → Trunc C m1
thom⁻-m1 C h = (grpd , thin) , conn
  where
  open Cat C
  pt : ∀ x y → Hom x y
  pt x y = snd (h x y)
  eq : ∀ {x y} (f g : Hom x y) → f ≡ g
  eq {x} {y} f g = snd (fst (h x y)) f g
  grpd : IsGrpd C
  grpd {x} {y} f = record { inv = pt y x ; left = eq _ _ ; right = eq _ _ }
  thin : Thin C
  thin = eq
  conn : Conn C
  conn = pt

------------------------------------------------------------------------
-- n = 0: the walking arrow has propositional homs but is not trunc 0.

private
  IHom-prop : ∀ {x y} (f g : IHom x y) → f ≡ g
  IHom-prop {o0} {o0} tt tt = refl
  IHom-prop {o0} {o1} tt tt = refl
  IHom-prop {o1} {o1} tt tt = refl
  IHom-prop {o1} {o0} () g

  disc-grpd : ∀ S → IsGrpd (Disc S)
  disc-grpd S refl = record { inv = refl ; left = refl ; right = refl }

I-homs-prop : HomsTrunc I m1
I-homs-prop x y = (disc-grpd _ , uip) , IHom-prop

I-not-set : Trunc I l0 → ⊥
I-not-set (g , _) = Cat.IsIso.inv (g {o0} {o1} tt)

thom⁻-0-fails : HomsTrunc I m1 × (Trunc I l0 → ⊥)
thom⁻-0-fails = I-homs-prop , I-not-set

-- n = 0 with the groupoid premise.
thom⁻-0-grpd : ∀ C → IsGrpd C → HomsTrunc C m1 → Trunc C l0
thom⁻-0-grpd C g h = g , λ {x} {y} f f' → snd (h x y) f f'

-- n ≥ 1: vacuous in 1-categories.
thom⁻-≥1 : ∀ C → HomsTrunc C l0 → Trunc C l1
thom⁻-≥1 C _ = tt
