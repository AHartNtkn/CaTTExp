------------------------------------------------------------------------
-- The side-condition hypotheses of CaTTExp.Binder.DesPresup for plain
-- CaTT, for every n and over every binder-free signature 𝕊₀:
--
--   side-comp n : the composite of n-cells over Dⁿ⁺¹ ∨ Dⁿ⁺¹ is an
--                 operation (it is CaTTExp.Derived's composite head
--                 BK n 0, accepted by `side-BK0`);
--   side-id n   : the identity over Dⁿ is a coherence (its source and
--                 target, with their type, use every variable of Dⁿ).
--
-- Both are proved over pure syntax and transferred by
-- CaTTExp.Binder.PureSide. So `catt-tm-ty` is presupposition for plain
-- CaTT + DES with the (MARK)-only mark judgment, given only Closed and
-- SigOK (𝕊₀'s constants have well-formed types).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
open import CaTTExp.Binder.Des
import CaTTExp.Pure as P
import CaTTExp.Derived as D
import CaTTExp.Binder.VarMark
open import CaTTExp.GrayCtx.Natural using (dbl; aL)

module CaTTExp.Binder.DesSideCatt (𝕊₀ : Old.Signature) where

open import CaTTExp.Binder.DesPresup 𝕊₀
open Signature 𝕊
open DesConstruction K DesF (λ b → b)
open import CaTTExp.Binder.Pasting 𝕊 using (embTy; embTm; embCtx)
open import CaTTExp.Binder.PureSide 𝕊 using (cattSide-pure)
import CaTTExp.Binder.Typing 𝕊 as NT
open PS using (tyP; diskP; compP; emb-tyP; emb-diskP; emb-compP)
open import CaTTExp.Binder.SyntaxLemmas K B using (+-suc)

------------------------------------------------------------------------
-- DES's pasting contexts are Derived's.

dbl-dd : ∀ n → dbl n ≡ n + n
dbl-dd zero    = refl
dbl-dd (suc n) = cong suc (trans (cong suc (dbl-dd n)) (sym (+-suc n n)))

tyP-aL : ∀ n → tyP n ≡ aL n
tyP-aL zero    = refl
tyP-aL (suc n) rewrite tyP-aL n | dbl-dd n = refl

diskP-Dsk : ∀ n → diskP n ≡ D.Dsk n
diskP-Dsk zero    = refl
diskP-Dsk (suc n) rewrite diskP-Dsk n | tyP-aL n | dbl-dd n = refl

compP-BK : ∀ n → compP n ≡ D.BK n 0
compP-BK n rewrite diskP-Dsk (suc n) | tyP-aL n | dbl-dd n = refl

------------------------------------------------------------------------
-- The identity over Dⁿ is a coherence, in pure CaTT.

private
  <→down : ∀ x m → T (x <ℕ m) → D.Mem x (P.downFrom m)
  <→down x (suc m) p with x ==ℕ m in e
  ... | true  = tt
  ... | false = <→down x m (lt x m p e)
    where
    lt : ∀ x m → T (x <ℕ suc m) → (x ==ℕ m) ≡ false → T (x <ℕ m)
    lt zero    zero    _ ()
    lt zero    (suc m) _ _ = tt
    lt (suc x) zero    () _
    lt (suc x) (suc m) p e = lt x m p e

  down→< : ∀ x m → D.Mem x (P.downFrom m) → T (x <ℕ m)
  down→< x (suc m) p with x ==ℕ m in e
  ... | true  = subst (λ y → T (y <ℕ suc m)) (sym (==ℕ-sound x m (subst T (sym e) tt))) (slf m)
    where
    slf : ∀ m → T (m <ℕ suc m)
    slf zero    = tt
    slf (suc m) = slf m
  ... | false = suc< x m (down→< x m p)
    where
    suc< : ∀ x m → T (x <ℕ m) → T (x <ℕ suc m)
    suc< zero    (suc m) _ = tt
    suc< (suc x) (suc m) p = suc< x m p

  <→up : ∀ x m → T (x <ℕ m) → D.Mem x (D.upTo m)
  <→up x (suc m) p with x ==ℕ m in e
  ... | true  = D.mem++r x (D.upTo m) (m ∷ []) (subst (λ b → T (b ∨ false)) (sym e) tt)
  ... | false = D.mem++l x (D.upTo m) (m ∷ []) (<→up x m (lt x m p e))
    where
    lt : ∀ x m → T (x <ℕ suc m) → (x ==ℕ m) ≡ false → T (x <ℕ m)
    lt zero    zero    _ ()
    lt zero    (suc m) _ _ = tt
    lt (suc x) zero    () _
    lt (suc x) (suc m) p e = lt x m p e

  -- d ∷ upTo d and downFrom (suc d) have the same elements.
  ≈-up-down : ∀ d → T (≈? (d ∷ D.upTo d) (P.downFrom (suc d)))
  ≈-up-down d = D.∧-in (D.⊆?-complete (d ∷ D.upTo d) (P.downFrom (suc d)) to)
                       (D.⊆?-complete (P.downFrom (suc d)) (d ∷ D.upTo d) from)
    where
    to : (d ∷ D.upTo d) D.⊆ P.downFrom (suc d)
    to x m with x ==ℕ d
    ... | true  = tt
    ... | false = <→down x d (D.mem-upTo x d m)
    from : P.downFrom (suc d) D.⊆ (d ∷ D.upTo d)
    from x m with x ==ℕ d
    ... | true  = tt
    ... | false = <→up x d (down→< x d m)

  coh-Dsk : ∀ n → T (P.isCoh (D.Dsk n) (aL n) (P.var (dbl n)) (P.var (dbl n)))
  coh-Dsk n = D.∧-in h h
    where
    h : T (≈? (P.fvTmTy (P.var (dbl n)) (aL n)) (P.varsCtx (D.Dsk n)))
    h rewrite D.fvTy-aL n | D.len-Sph n = ≈-up-down (dbl n)

side-Dsk : ∀ n → T (P.cattSide (D.Dsk n) (aL n) (P.var (dbl n)) (P.var (dbl n)))
side-Dsk n = D.∨-l (coh-Dsk n)

------------------------------------------------------------------------
-- The hypotheses, in the binder kernel.

side-comp : ∀ n → T (NT.cattSide (compPC n) (tyD n) (var (n + n)) (var (3 + (n + n))))
side-comp n =
  subst T (sym (trans (cong₂ (λ Δ A → NT.cattSide Δ A (var (n + n)) (var (3 + (n + n))))
                             (sym (emb-compP n)) (sym (emb-tyP n)))
                      (cattSide-pure (compP n) (tyP n) (P.var (n + n)) (P.var (3 + (n + n))))))
    (subst (λ X → T (P.cattSide (fst X) (snd X) (P.var (n + n)) (P.var (3 + (n + n)))))
           (cong₂ _,_ (sym (compP-BK n)) (sym (tyP-aL n)))
           (subst (λ d → T (P.cattSide (D.BK n 0) (aL n) (P.var d) (P.var (3 + d)))) (dbl-dd n)
                  (D.side-BK0 n)))

side-id : ∀ n → T (NT.cattSide (diskD n) (tyD n) (var (n + n)) (var (n + n)))
side-id n =
  subst T (sym (trans (cong₂ (λ Δ A → NT.cattSide Δ A (var (n + n)) (var (n + n)))
                             (sym (emb-diskP n)) (sym (emb-tyP n)))
                      (cattSide-pure (diskP n) (tyP n) (P.var (n + n)) (P.var (n + n)))))
    (subst (λ X → T (P.cattSide (fst X) (snd X) (P.var (n + n)) (P.var (n + n))))
           (cong₂ _,_ (sym (diskP-Dsk n)) (sym (tyP-aL n)))
           (subst (λ d → T (P.cattSide (D.Dsk n) (aL n) (P.var d) (P.var d))) (dbl-dd n)
                  (side-Dsk n)))

------------------------------------------------------------------------
-- Presupposition for plain CaTT + DES with the (MARK)-only judgment.

private
  module VM = CaTTExp.Binder.VarMark 𝕊 NT.cattSide
  module TY = Typed NT.cattSide varMark
  open import CaTTExp.Binder.Laws 𝕊 using (Closed)
  open import CaTTExp.Binder.Presup 𝕊 NT.cattSide varMark using (SigOK)

catt-tm-ty : Closed → SigOK → ∀ {Γ t A} → NT._⊢tm_∶_ Γ t A → NT._⊢ty_ Γ A
catt-tm-ty closed sig =
  TY.des-tm-ty closed VM.markRen VM.markSub VM.markVar side-comp side-id sig
