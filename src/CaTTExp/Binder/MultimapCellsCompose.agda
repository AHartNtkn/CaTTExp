------------------------------------------------------------------------
-- Canonical heads compose with the renaming onto a support (ledger
-- S26j, step 2b).
--
-- Fix b with its canonical support (atoms as_b, entries vs_b, renaming
-- ρ_b, context Φ_b; CaTTExp.Binder.MultimapCellsCanon, `Idem`). A term
-- u over that support (its entries, its type's entries and its atoms
-- among b's) has, after ρ_b, the same canonical head in Φ_b as in Φ,
-- and its support is the image of its support:
--
--   cidx   (canon |as_b| Φ_b (u[ρ_b])) ≡ cidx (canon k Φ u)
--   cvars  (canon |as_b| Φ_b (u[ρ_b])) ≡ map (position in vs_b) (supVars Φ u)
--   catoms (canon |as_b| Φ_b (u[ρ_b])) ≡ map (position in as_b) (supAtoms k Φ u)
--
-- This is what makes the kernel image of a boundary independent of the
-- support it is read over (CaTTExp.Binder.MultimapCellsPresup).
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsCompose where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Strengthen
open import CaTTExp.Gray.Biclosed.ListLemmas using (length-map)
open import CaTTExp.Binder.Multimap using (MMI; mmi)
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.MultimapCellsStrengthen
  using (T-if; F-if; dec; inl; inr; strengthen-on; filter-elem; upTo-elem; closeFrom-mono; nthY-just)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_; Deps↓; lookup-some; elem-split; cl-closed)
open import CaTTExp.Binder.MultimapCellsRen
open import CaTTExp.Binder.MultimapCellsComp
open import CaTTExp.Binder.MultimapCellsCanon
  using (module Idem; headOf; mapᵍ-map; mapᵍ-cong; mapG-map; atY-concatAt)

------------------------------------------------------------------------
-- Positions through a map that is injective on the list.

idx-map : ∀ (ys : List Nat) (f : Nat → Nat) →
          (∀ a c → In ys a → In ys c → f a ≡ f c → a ≡ c) →
          ∀ xs i → In ys i → xs ⊆ ys → idx (f i) (map f xs) ≡ idx i xs
idx-map ys f inj []       i iy xy = refl
idx-map ys f inj (x ∷ xs) i iy xy with dec (i ==ℕ x)
... | inl q = trans (T-if (f i ==ℕ f x) (subst (λ z → T (f i ==ℕ f z)) (==ℕ-sound i x q) (==ℕ-refl (f i))))
                    (sym (T-if (i ==ℕ x) q))
... | inr q = trans (F-if (f i ==ℕ f x) (λ r → q (subst (λ z → T (i ==ℕ z))
                                                  (inj i x iy (xy x (∨-l (x ==ℕ x) _ (==ℕ-refl x))) (==ℕ-sound (f i) (f x) r))
                                                  (==ℕ-refl i))))
                    (trans (cong suc (idx-map ys f inj xs i iy (λ j p → xy j (∨-r (j ==ℕ x) _ p))))
                           (sym (F-if (i ==ℕ x) q)))

idx-inj : ∀ ys a c → In ys a → In ys c → idx a ys ≡ idx c ys → a ≡ c
idx-inj ys a c pa pc e = trans (sym (nth-idx ys a pa)) (trans (cong (nth ys) e) (nth-idx ys c pc))

------------------------------------------------------------------------

module Compose (k : Nat) (Φ : Ctx) (w : T (wfCtx Φ)) (b : Tm) {B : CTy} (eB : infer Φ b ≡ just B)
               (wB : T (wf Φ B)) (ab : ∀ i → In (supAtomsOf Φ b) i → T (i <ℕ k)) where

  open Idem k Φ w b eB wB ab public

  asb-lt : ∀ i → In asb i → T (i <ℕ k)
  asb-lt i p = upTo-In-inv k i (snd (filter-In-inv (λ i → elem i S) (upTo k) i p))

  rr-inj : ∀ a c → In vs a → In vs c → rr a ≡ rr c → a ≡ c
  rr-inj = idx-inj vs

  ra-inj : ∀ a c → In asb a → In asb c → ra a ≡ ra c → a ≡ c
  ra-inj = idx-inj asb

  module On (u : Tm) {U : CTy} (eU : infer Φ u ≡ just U) (wU : T (wf Φ U))
            (uT : varsT u ⊆ vs) (uY : varsY U ⊆ vs) (uA : supAtomsOf Φ u ⊆ asb) where

    u′ : Tm
    u′ = sT ρ u

    vsu : List Nat
    vsu = supVars Φ u

    asu : List Nat
    asu = supAtoms k Φ u

    Su : List Nat
    Su = supAtomsOf Φ u

    startU : supStart Φ u ≡ varsT u ++ varsY U
    startU = cong (λ m → varsT u ++ varsYM m) eU

    ustart : supStart Φ u ⊆ vs
    ustart i p with elem-split i (varsT u) (varsY U) (subst (λ xs → In xs i) startU p)
    ... | inl q = uT i q
    ... | inr q = uY i q

    module FU = ForSet (supStart Φ u) ustart
    module SU = SupportRen Φ dd (supStart Φ u) asu

    infer-u′ : infer Φ′ u′ ≡ just (sY ρ U)
    infer-u′ = strengthen-on asb vs Φ u U (λ i q _ → uT i q) eU

    start-u′ : supStart Φ′ u′ ≡ map rr (supStart Φ u)
    start-u′ =
      trans (cong₂ (λ X m → X ++ varsYM m) (varsT-ren asb vs u uT) infer-u′)
        (trans (cong (map rr (varsT u) ++_) (varsY-ren asb vs U uY))
          (trans (sym (map-++ rr (varsT u) (varsY U))) (cong (map rr) (sym startU))))

    V1 : supVars Φ′ u′ ≡ map rr vsu
    V1 = trans (cong (supVarsFrom Φ′) start-u′) FU.supVars-ren

    vsu⊆vs : vsu ⊆ vs
    vsu⊆vs i p = FU.Rb⊆vs i (SU.vs-R i p) (SU.vs-lt i p)

    types-u′ : map (nthY Φ′) (supVars Φ′ u′) ≡ map (sY ρ) (map (nthY Φ) vsu)
    types-u′ = trans (cong (map (nthY Φ′)) V1)
                 (trans (mapᵍ-map (nthY Φ′) rr vsu)
                   (trans (mapᵍ-cong _ _ vsu (λ j p → nthY-Φ′ j (vsu⊆vs j p))) (sym (mapᵍ-map (sY ρ) (nthY Φ) vsu))))

    open AtRen asb vs using (atT-ren; atY-ren; concatAt-ren)

    A1 : supAtomsOf Φ′ u′ ≡ map ra Su
    A1 =
      trans (cong₂ (λ X Y → concatAt X ++ atT u′ ++ atYM Y) types-u′ infer-u′)
        (trans (cong₂ _++_ (concatAt-ren (map (nthY Φ) vsu)) (cong₂ _++_ (atT-ren u) (atY-ren U)))
          (trans (cong (map ra (concatAt (map (nthY Φ) vsu)) ++_) (sym (map-++ ra (atT u) (atY U))))
            (trans (sym (map-++ ra (concatAt (map (nthY Φ) vsu)) (atT u ++ atY U)))
                   (cong (λ Y → map ra (concatAt (map (nthY Φ) vsu) ++ atT u ++ Y)) (sym (cong atYM eU))))))

    A2 : supAtoms (length asb) Φ′ u′ ≡ map ra asu
    A2 = trans (cong (λ X → filter (λ i → elem i X) (upTo (length asb))) A1)
               (sym (sub-filter-ren asb asb-inc k asb-lt Su uA))

    asu⊆asb : asu ⊆ asb
    asu⊆asb i p = uA i (fst (filter-In-inv (λ i → elem i Su) (upTo k) i p))

    asu-in : ∀ i → In Su i → In asu i
    asu-in i p = filter-elem (λ i → elem i Su) (upTo k) i p (upTo-elem k i (asb-lt i (uA i p)))

    ρ₂ ρu : Sub
    ρ₂ = renOf (map ra asu) (map rr vsu)
    ρu = renOf asu vsu

    onA : ∀ xs → xs ⊆ asu → OnA ρ ρ₂ ρu xs
    onA xs h a p = cong obj (idx-map asb ra ra-inj asu a (asu⊆asb a (h a p)) asu⊆asb)

    onV : ∀ xs → xs ⊆ vsu → OnV ρ ρ₂ ρu xs
    onV xs h i p =
      let ivs = vsu⊆vs i (h i p)
          iu  = h i p
      in trans (cong (sT ρ₂) (T-if (elem i vs) ivs))
           (trans (T-if (elem (rr i) (map rr vsu)) (In-map rr vsu i iu))
             (trans (cong var (idx-map vs rr rr-inj vsu i ivs vsu⊆vs))
                    (sym (T-if (elem i vsu) iu))))

    tmEq : sT ρ₂ u′ ≡ sT ρu u
    tmEq = compT ρ ρ₂ ρu u
             (onA (atT u) (λ a p → asu-in a (elem-++r a (concatAt (map (nthY Φ) vsu)) _ (elem-++l a (atT u) _ p))))
             (onV (varsT u) (λ i p → SU.vs-in i (closeFrom-mono Φ SU.n (supStart Φ u) i
                                                   (elem-++l i (varsT u) (varsYM (infer Φ u)) p))
                                                 (infer-scope Φ u eU i p)))

    entryEq : ∀ j → In vsu j → sY ρ₂ (nthY Φ′ (rr j)) ≡ sY ρu (nthY Φ j)
    entryEq j p =
      let (A , eA) = lookup-some Φ j (SU.vs-lt j p)
          A≡ = nthY-just Φ j eA
      in trans (cong (sY ρ₂) (nthY-Φ′ j (vsu⊆vs j p)))
           (compY ρ ρ₂ ρu (nthY Φ j)
             (onA (atY (nthY Φ j)) (λ a q → asu-in a (elem-++l a (concatAt (map (nthY Φ) vsu)) _
                                                     (atY-concatAt (nthY Φ) vsu j p a q))))
             (onV (varsY (nthY Φ j)) (subst (λ X → varsY X ⊆ vsu) (sym A≡) (SU.vs-closed j eA p))))

    ctxEq : map (sY ρ₂) (map (nthY Φ′) (map rr vsu)) ≡ map (sY ρu) (map (nthY Φ) vsu)
    ctxEq =
      trans (mapG-map (sY ρ₂) (nthY Φ′) (map rr vsu))
        (trans (mapᵍ-map (λ x → sY ρ₂ (nthY Φ′ x)) rr vsu)
          (trans (mapᵍ-cong _ _ vsu entryEq)
                 (sym (mapG-map (sY ρu) (nthY Φ) vsu))))

    -- The canonical head of u is the same read over b's support.
    canon-comp : cidx (canon (length asb) Φ′ u′) ≡ cidx (canon k Φ u)
    canon-comp =
      trans (cong₂ (headOf (length asb) Φ′ u′) A2 V1)
        (cong₃′ mmi (length-map ra asu) ctxEq tmEq)

    cvars-comp : cvars (canon (length asb) Φ′ u′) ≡ map rr vsu
    cvars-comp = V1

    catoms-comp : catoms (canon (length asb) Φ′ u′) ≡ map ra asu
    catoms-comp = A2
