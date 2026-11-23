------------------------------------------------------------------------
-- The kernel images commute with the renaming onto a support (ledger
-- S26j, step 2b).
--
-- Fix b, inferring B in a well-formed Φ with its atoms below k, and its
-- canonical head c_b = canon k Φ b (atoms as_b, entries vs_b, renaming
-- ρ_b, context Φ_b). The kernel arguments of c_b are
-- σ_b = supArgs k c_b: atom i of c_b goes to atom (as_b)_i, entry p to
-- entry k + (vs_b)_p. Then for every admitted type C over the support
-- of b (its entries in vs_b, its atoms in as_b, well formed in Φ):
--
--   (trTy |as_b| Φ_b (C[ρ_b])) [σ_b] ≡ trTy k Φ C          (`commTy`)
--
-- so in particular for each entry of the support (`comm-entry`) and for
-- B itself (`comm-res`). For a boundary that is a variable this is
-- arithmetic on positions; for any other boundary u it is
-- CaTTExp.Binder.MultimapCellsCompose: u[ρ_b] has the canonical head of
-- u, on the image of u's support, which σ_b sends back to u's support.
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsComm where

open import CaTTExp.Prelude
open import CaTTExp.Binder.Multimap using (MMI; mmi; atomFm)
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.GrayForm using (GBF)
import CaTTExp.Binder.Syntax as Syntax
import CaTTExp.Binder.SyntaxLemmas as SL
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_; lookup-some)
import CaTTExp.Binder.MultimapCellsRen as MR
open import CaTTExp.Binder.MultimapCellsRen using (⊆-l; ⊆-r)
import CaTTExp.Binder.MultimapCellsCompose as MC
open import CaTTExp.Binder.MultimapCellsCanon using (mapᵍ-cong; mapG-map)
open import CaTTExp.Binder.MultimapCellsStrengthen using (T-if; nthY-just)
open import CaTTExp.Binder.MultimapCellsWf using (wf-agree; wfFrom-elim; lookup-take)
open import CaTTExp.Gray.Biclosed.Strengthen using (Agree; wf-deps; ∨-l; elem-++l; elem-++r)

------------------------------------------------------------------------
-- Lists of naturals.

nth-map : ∀ (f : Nat → Nat) xs p → T (p <ℕ GT.length xs) → MR.nth (GT.map f xs) p ≡ f (MR.nth xs p)
nth-map f (x ∷ xs) zero    _ = refl
nth-map f (x ∷ xs) (suc p) l = nth-map f xs p l

length-map′ : ∀ (f : Nat → Nat) xs → GT.length (GT.map f xs) ≡ GT.length xs
length-map′ f []       = refl
length-map′ f (x ∷ xs) = cong suc (length-map′ f xs)

eqMaybe-sound : ∀ m B → T (GT.eqMaybeTy m B) → m ≡ just B
eqMaybe-sound (just A) B p = cong just (GB.eqTy-sound A B p)

private
  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt
  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

-- An entry is well formed over the whole context.
wf-entry : ∀ Φ j {A} → T (GT.wfCtx Φ) → GT.lookup Φ j ≡ just A → T (GT.wf Φ A)
wf-entry Φ j {A} w e =
  subst T (wf-agree (GT.take j Φ) Φ A ag) (wfFrom-elim [] Φ j w e)
  where
  ag : Agree (GT.take j Φ) Φ (varsY A)
  ag i q = lookup-take Φ j i (wf-deps Φ j w e i q)

module _ (K B : Set) (injG : GBF → B) (injC : MMI → B) where

  open Syntax K B
  open SL K B using (<→≢; <-suc; <-self; ==-refl; +-suc; +-zero)
  open CellsConstruction K B injG injC

  ----------------------------------------------------------------------
  -- Substitutions of variables.

  tmsOf : Sub → List Tm → Sub
  tmsOf ρ []       = ρ
  tmsOf ρ (t ∷ ts) = tmsOf (ρ ,ₛ t) ts

  varsOf-tms : ∀ ρ js → varsOf ρ js ≡ tmsOf ρ (GT.map var js)
  varsOf-tms ρ []       = refl
  varsOf-tms ρ (j ∷ js) = varsOf-tms (ρ ,ₛ var j) js

  tmsOf-∘ : ∀ ρ σ ts → tmsOf ρ ts ∘ σ ≡ tmsOf (ρ ∘ σ) (GT.map (λ t → t [ σ ]tm) ts)
  tmsOf-∘ ρ σ []       = refl
  tmsOf-∘ ρ σ (t ∷ ts) = tmsOf-∘ (ρ ,ₛ t) σ ts

  -- σ sends the variables of xs to those of ys.
  varsOf-∘ : ∀ ρ σ xs ys → GT.map (lookupₛ σ) xs ≡ GT.map var ys → varsOf ρ xs ∘ σ ≡ tmsOf (ρ ∘ σ) (GT.map var ys)
  varsOf-∘ ρ σ xs ys e =
    trans (cong (_∘ σ) (varsOf-tms ρ xs))
      (trans (tmsOf-∘ ρ σ (GT.map var xs))
        (cong (tmsOf (ρ ∘ σ)) (trans (mapG-map (λ t → t [ σ ]tm) var xs) e)))

  args-∘ : ∀ σ as cs as′ cs′ → GT.map (lookupₛ σ) as ≡ GT.map var as′ → GT.map (lookupₛ σ) cs ≡ GT.map var cs′ →
           varsOf (varsOf ⟨⟩ as) cs ∘ σ ≡ varsOf (varsOf ⟨⟩ as′) cs′
  args-∘ σ as cs as′ cs′ ea ec =
    trans (varsOf-∘ (varsOf ⟨⟩ as) σ cs cs′ ec)
      (trans (cong (λ ρ → tmsOf ρ (GT.map var cs′))
                (trans (varsOf-∘ ⟨⟩ σ as as′ ea) (sym (varsOf-tms ⟨⟩ as′))))
             (sym (varsOf-tms (varsOf ⟨⟩ as′) cs′)))

  lenₛ-varsOf : ∀ ρ js → lenₛ (varsOf ρ js) ≡ lenₛ ρ + GT.length js
  lenₛ-varsOf ρ []       = sym (+-zero (lenₛ ρ))
  lenₛ-varsOf ρ (j ∷ js) = trans (lenₛ-varsOf (ρ ,ₛ var j) js) (sym (+-suc (lenₛ ρ) (GT.length js)))

  lookup-lo : ∀ ρ js i → T (i <ℕ lenₛ ρ) → lookupₛ (varsOf ρ js) i ≡ lookupₛ ρ i
  lookup-lo ρ []       i p = refl
  lookup-lo ρ (j ∷ js) i p =
    trans (lookup-lo (ρ ,ₛ var j) js i (<-suc i (lenₛ ρ) p))
          (cong (λ c → if c then var j else lookupₛ ρ i) (<→≢ i (lenₛ ρ) p))

  lookup-hi : ∀ ρ js q → T (q <ℕ GT.length js) → lookupₛ (varsOf ρ js) (lenₛ ρ + q) ≡ var (MR.nth js q)
  lookup-hi ρ (j ∷ js) zero _ rewrite +-zero (lenₛ ρ) =
    trans (lookup-lo (ρ ,ₛ var j) js (lenₛ ρ) (<-self (lenₛ ρ)))
          (cong (λ c → if c then var j else lookupₛ ρ (lenₛ ρ)) (==-refl (lenₛ ρ)))
  lookup-hi ρ (j ∷ js) (suc q) l rewrite +-suc (lenₛ ρ) q = lookup-hi (ρ ,ₛ var j) js q l

  ----------------------------------------------------------------------
  -- At a term b of Φ.

  module At (k : Nat) (Φ : GB.Ctx) (w : T (GT.wfCtx Φ)) (b : GB.Tm) {Bb : GB.CTy}
            (eB : GT.infer Φ b ≡ just Bb) (wB : T (GT.wf Φ Bb))
            (ab : ∀ i → In (supAtomsOf Φ b) i → T (i <ℕ k)) where

    module CB = MC.Compose k Φ w b eB wB ab
    open CB using (asb; vs; ρ; rr; ra; Φ′; m)

    K′ : Nat
    K′ = GT.length asb

    σb : Sub
    σb = supArgs k (canon k Φ b)

    σb-atom : ∀ i → T (i <ℕ K′) → lookupₛ σb i ≡ var (MR.nth asb i)
    σb-atom i p =
      trans (lookup-lo (varsOf ⟨⟩ asb) (GT.map (k +_) vs) i (subst (λ n → T (i <ℕ n)) (sym (lenₛ-varsOf ⟨⟩ asb)) p))
            (lookup-hi ⟨⟩ asb i p)

    σb-cell : ∀ p → T (p <ℕ m) → lookupₛ σb (K′ + p) ≡ var (k + MR.nth vs p)
    σb-cell p l =
      trans (cong (λ n → lookupₛ σb (n + p)) (sym (lenₛ-varsOf ⟨⟩ asb)))
        (trans (lookup-hi (varsOf ⟨⟩ asb) (GT.map (k +_) vs) p (subst (λ n → T (p <ℕ n)) (sym (length-map′ (k +_) vs)) l))
               (cong var (nth-map (k +_) vs p l)))

    σb-ra : ∀ a → In asb a → lookupₛ σb (ra a) ≡ var a
    σb-ra a p = trans (σb-atom (ra a) (MR.idx-lt asb a p)) (cong var (MR.nth-idx asb a p))

    σb-rr : ∀ v → In vs v → lookupₛ σb (K′ + rr v) ≡ var (k + v)
    σb-rr v p = trans (σb-cell (rr v) (MR.idx-lt vs v p)) (cong (λ z → var (k + z)) (MR.nth-idx vs v p))

    --------------------------------------------------------------------
    -- Formulas.

    commF : ∀ x → T (atomFm k x) → atF x ⊆ asb → fmV (GT.sF (GT.fo ρ) x) [ σb ]tm ≡ fmV x
    commF (GB.obj i)  _ h = σb-ra i (h i (∨-l (i ==ℕ i) _ (==ℕ-refl i)))
    commF (GB.rep _)  () _
    commF (GB.shp _)  () _
    commF (x GB.⊗ y)  p h = cong₂ _⊗ᵗ_  (commF x (∧-l _ _ p) (⊆-l (atF x) (atF y) asb h)) (commF y (∧-r _ _ p) (⊆-r (atF x) (atF y) asb h))
    commF (x GB.\\ y) p h = cong₂ _\\ᵗ_ (commF x (∧-l _ _ p) (⊆-l (atF x) (atF y) asb h)) (commF y (∧-r _ _ p) (⊆-r (atF x) (atF y) asb h))
    commF (x GB.// y) p h = cong₂ _//ᵗ_ (commF x (∧-l _ _ p) (⊆-l (atF x) (atF y) asb h)) (commF y (∧-r _ _ p) (⊆-r (atF x) (atF y) asb h))

    --------------------------------------------------------------------
    -- Boundaries.

    commHead : ∀ s {S} → GT.infer Φ s ≡ just S → T (GT.wf Φ S) → varsT s ⊆ vs → varsY S ⊆ vs →
               atT s ⊆ asb → atY S ⊆ asb → trHead K′ Φ′ (GT.sT ρ s) [ σb ]tm ≡ trHead k Φ s
    commHead s {S} eS wS sT sY aT aY =
      cong₂ (λ h ts → bnd (injC h) 0 ε ts) canon-comp argsEq
      where
      open CB.On s eS wS sT sY (CB.supAt⊆ s eS sT sY aT aY)
      argsEq : supArgs K′ (canon K′ Φ′ u′) ∘ σb ≡ supArgs k (canon k Φ s)
      argsEq =
        trans (cong₂ (λ X Y → varsOf (varsOf ⟨⟩ X) (GT.map (K′ +_) Y) ∘ σb) catoms-comp cvars-comp)
          (args-∘ σb (GT.map ra asu) (GT.map (K′ +_) (GT.map rr vsu)) asu (GT.map (k +_) vsu)
            (trans (mapG-map (lookupₛ σb) ra asu)
              (mapᵍ-cong _ _ asu (λ a p → σb-ra a (asu⊆asb a p))))
            (trans (mapG-map (lookupₛ σb) (K′ +_) (GT.map rr vsu))
              (trans (mapG-map (λ x → lookupₛ σb (K′ + x)) rr vsu)
                (trans (mapᵍ-cong _ _ vsu (λ v p → σb-rr v (vsu⊆vs v p)))
                       (sym (mapG-map var (k +_) vsu))))))

    commTm : ∀ s {S} → GT.infer Φ s ≡ just S → T (GT.wf Φ S) → varsT s ⊆ vs → varsY S ⊆ vs →
             atT s ⊆ asb → atY S ⊆ asb → trTm K′ Φ′ (GT.sT ρ s) [ σb ]tm ≡ trTm k Φ s
    commTm (GB.var j) eS wS sT sY aT aY =
      let jvs = sT j (∨-l (j ==ℕ j) _ (==ℕ-refl j)) in
      trans (cong (λ z → trTm K′ Φ′ z [ σb ]tm) (T-if (elem j vs) jvs)) (σb-rr j jvs)
    commTm s@(GB.mP _ _)      eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.eL _ _)      eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.eR _ _)      eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.pP _ _)      eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@GB.pt            eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.iP _)        eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.idt _)       eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.comp _ _)    eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.glue _ _ _)  eS wS sT sY aT aY = commHead s eS wS sT sY aT aY
    commTm s@(GB.here _ _ _ _) eS wS sT sY aT aY = commHead s eS wS sT sY aT aY

    --------------------------------------------------------------------
    -- Types.

    commTy : ∀ C → T (okTy k C) → T (GT.wf Φ C) → varsY C ⊆ vs → atY C ⊆ asb →
             trTy K′ Φ′ (GT.sY ρ C) [ σb ]ty ≡ trTy k Φ C
    commTy (GB.op ((x ∷ []) GB.▸ z)) p _ _ h =
      cong₂ (arr ⋆) (commF x (∧-l _ _ p) (λ i q → h i (elem-++l i (atF x ++ []) (atF z) (elem-++l i (atF x) [] q))))
                    (commF z (∧-r _ _ p) (λ i q → h i (elem-++r i (atF x ++ []) (atF z) q)))
    commTy (GB.op ([] GB.▸ _)) () _ _ _
    commTy (GB.op ((_ ∷ _ ∷ _) GB.▸ _)) () _ _ _
    commTy (GB.hom d g A s t) p wC hv ha =
      let wA  = ∧-l _ _ wC
          wst = ∧-r (GT.wf Φ A) _ wC
          eS  = eqMaybe-sound (GT.infer Φ s) A (∧-l _ _ wst)
          eT  = eqMaybe-sound (GT.infer Φ t) A (∧-r (GT.eqMaybeTy (GT.infer Φ s) A) _ wst)
          hA  = ⊆-l (varsY A) (varsT s ++ varsT t) vs hv
          hst = ⊆-r (varsY A) (varsT s ++ varsT t) vs hv
          aA  = ⊆-l (atY A) (atT s ++ atT t) asb ha
          ast = ⊆-r (atY A) (atT s ++ atT t) asb ha
      in cong₃ arr (commTy A (∧-r (g ==ℕ 1) _ p) wA hA aA)
                   (commTm s eS wA (⊆-l (varsT s) (varsT t) vs hst) hA (⊆-l (atT s) (atT t) asb ast) aA)
                   (commTm t eT wA (⊆-r (varsT s) (varsT t) vs hst) hA (⊆-r (atT s) (atT t) asb ast) aA)
      where
      cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
              a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
      cong₃ f refl refl refl = refl

    --------------------------------------------------------------------
    -- The entries of the support, and the type of b.

    comm-entry : ∀ v → In vs v → T (okTy k (nthY Φ v)) →
                 trTy K′ Φ′ (GT.sY ρ (nthY Φ v)) [ σb ]ty ≡ trTy k Φ (nthY Φ v)
    comm-entry v p ok =
      let (A , eA) = lookup-some Φ v (CB.vs-lt v p)
          A≡ = nthY-just Φ v eA
      in commTy (nthY Φ v) ok
           (subst (λ X → T (GT.wf Φ X)) (sym A≡) (wf-entry Φ v w eA))
           (subst (λ X → varsY X ⊆ vs) (sym A≡) (CB.vs-closed v eA p))
           (CB.entries-at v p)

    comm-res : T (okTy k Bb) → trTy K′ Φ′ (GT.sY ρ Bb) [ σb ]ty ≡ trTy k Φ Bb
    comm-res ok = commTy Bb ok wB CB.bvsY
      (λ i q → CB.S-in i (elem-++r i (concatAt (GT.map (nthY Φ) vs)) _
                           (elem-++r i (atT b) _ (subst (λ X → In (atYM X) i) (sym eB) q))))
