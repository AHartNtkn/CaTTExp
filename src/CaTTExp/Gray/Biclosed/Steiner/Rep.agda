------------------------------------------------------------------------
-- Representing corollas (S5 of the 𝔖̂ instance).
--
-- A corolla c : (Is ▸ O) is representing when every element t of ⟦O⟧
-- at K decomposes as t ∼ g^*(c(vs)) for some arguments vs at Ls and a
-- map g : K → ⊗Ls (`dLs`, `dvs`, `dg`, `deq`), and when any natural
-- family F on Is, put in a frame (fixed arguments around the slot),
-- gives the same value on two decompositions of the same element
-- (`dUP`, the universal property). From these, precomposition with c
-- at any slot is invertible:
--     (unC y)(…, t, …) = (1 ⊗ dg t ⊗ 1)^* y(…, dvs t, …)
-- with unC-l, unC-r, congruence and typing (`UC`). The four corollas
-- m, p, pt, ι are instances (`Corollas`).
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.Rep (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps using (length; take)
open import CaTTExp.Gray.Biclosed.ListLemmas using (drop; length-++) renaming (++-assoc to ++-assocL; ++-[] to ++-[]L)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC; globe; named)
open import CaTTExp.Gray.Biclosed.Steiner.Psh nmFB
open import CaTTExp.Gray.Biclosed.Steiner.PshOps nmFB
open import CaTTExp.Gray.Biclosed.Steiner.DayMult nmFB using (uip; decFm; decFm-refl)
open import CaTTExp.Gray.Biclosed.Steiner.Sem nmFB

module Rep (ob : Nat → Psh) where
  open Sem ob

  --------------------------------------------------------------------
  -- Slots for a list of inputs.

  record SlotN (Fs : List Fm) (i : Nat) (Is : List Fm) : Set where
    constructor slotN
    field
      sP sQ : List Fm
      eF : Fs ≡ sP ++ Is ++ sQ
      eP : length sP ≡ i

  private
    pfx : ∀ {F I : Fm} {Fs Is} → Maybe (F ≡ I) → Maybe (Σ (List Fm) (λ Q → Fs ≡ Is ++ Q)) →
          Maybe (Σ (List Fm) (λ Q → F ∷ Fs ≡ I ∷ Is ++ Q))
    pfx (just refl) (just (Q , refl)) = just (Q , refl)
    pfx (just refl) nothing           = nothing
    pfx nothing     _                 = nothing

  prefix : (Is Fs : List Fm) → Maybe (Σ (List Fm) (λ Q → Fs ≡ Is ++ Q))
  prefix []       Fs       = just (Fs , refl)
  prefix (I ∷ Is) []       = nothing
  prefix (I ∷ Is) (F ∷ Fs) = pfx (decFm F I) (prefix Is Fs)

  prefix-ok : ∀ Is Q → prefix Is (Is ++ Q) ≡ just (Q , refl)
  prefix-ok []       Q = refl
  prefix-ok (I ∷ Is) Q rewrite decFm-refl I | prefix-ok Is Q = refl

  compatN : ∀ Fs i Is → Maybe (SlotN Fs i Is)
  compatN Fs zero Is = z (prefix Is Fs)
    where z : Maybe (Σ (List Fm) (λ Q → Fs ≡ Is ++ Q)) → Maybe (SlotN Fs zero Is)
          z (just (Q , e)) = just (slotN [] Q e refl)
          z nothing        = nothing
  compatN []       (suc i) Is = nothing
  compatN (F ∷ Fs) (suc i) Is = s (compatN Fs i Is)
    where s : Maybe (SlotN Fs i Is) → Maybe (SlotN (F ∷ Fs) (suc i) Is)
          s (just (slotN P Q e l)) = just (slotN (F ∷ P) Q (cong (F ∷_) e) (cong suc l))
          s nothing                = nothing

  slotN-unique : ∀ {Fs i Is} (s s′ : SlotN Fs i Is) → s ≡ s′
  slotN-unique {Is = Is} (slotN P Q e l) (slotN P′ Q′ e′ l′)
    with app-inj P (Is ++ Q) P′ (Is ++ Q′) (trans l (sym l′)) (trans (sym e) e′)
  ... | refl , e₂ with app-inj Is Q Is Q′ refl e₂
  ...   | refl , refl with uip e e′ | uip l l′
  ...     | refl | refl = refl

  compatN-ok : ∀ P Is Q → Σ (SlotN (P ++ Is ++ Q) (length P) Is) (λ s → compatN (P ++ Is ++ Q) (length P) Is ≡ just s)
  compatN-ok []      Is Q rewrite prefix-ok Is Q = _ , refl
  compatN-ok (F ∷ P) Is Q with compatN (P ++ Is ++ Q) (length P) Is | compatN-ok P Is Q
  ... | .(just s) | s , refl = _ , refl

  compatN-just : ∀ {Fs i Is} (s : SlotN Fs i Is) → compatN Fs i Is ≡ just s
  compatN-just {Is = Is} (slotN P Q refl refl) with compatN-ok P Is Q
  ... | s′ , e = trans e (cong just (slotN-unique s′ _))

  --------------------------------------------------------------------
  -- Natural families in a frame.

  record Framed (Is : List Fm) (Z : Psh) : Set where
    field
      fKP fKQ : List Code
      fF   : List Code → List Uni → U Z
      fAt  : ∀ Ls vs → AtL Is Ls vs → At Z (concat (fKP ++ Ls ++ fKQ)) (fF Ls vs)
      fcg  : ∀ Ls vs vs′ → AtL Is Ls vs → AtL Is Ls vs′ → vs ∼L vs′ → _∼_ Z (fF Ls vs) (fF Ls vs′)
      fnat : ∀ {Ls′ Ls} (hs : Maps Ls′ Ls) vs → AtL Is Ls vs →
             _∼_ Z (fF Ls′ (resL hs vs)) (res Z (⊗s (idMaps fKP ++ᵐ (hs ++ᵐ idMaps fKQ))) (fF Ls vs))
  open Framed public

  private
    ∼L-sym′ : ∀ {as bs} → as ∼L bs → bs ∼L as
    ∼L-sym′ {[]} {[]} _ = tt
    ∼L-sym′ {a ∷ as} {b ∷ bs} (p , ps) = ∼U-sym p , ∼L-sym′ ps

    lenUK : ∀ {As Ks us} → AtL As Ks us → length us ≡ length Ks
    lenUK {As} {Ks} {us} a = trans (AtL-lenU As Ks us a) (sym (AtL-lenK As Ks us a))

    -- resL of a framed list of maps
    resL-frame : ∀ {KP′ KP Ls′ Ls KQ′ KQ} (hP : Maps KP′ KP) (hs : Maps Ls′ Ls) (hQ : Maps KQ′ KQ) uP vs uQ →
                 length uP ≡ length KP → length vs ≡ length Ls →
                 resL (hP ++ᵐ (hs ++ᵐ hQ)) (uP ++ vs ++ uQ) ≡ resL hP uP ++ resL hs vs ++ resL hQ uQ
    resL-frame hP hs hQ uP vs uQ lP lv =
      trans (resL-++ hP (hs ++ᵐ hQ) uP (vs ++ uQ) lP) (cong (resL hP uP ++_) (resL-++ hs hQ vs uQ lv))

  framedV : ∀ {P Is Q Z} (r : List Code → List Uni → UF Z) → Ok ((P ++ Is ++ Q) ▸ Z) r →
            ∀ KP uP KQ uQ → AtL P KP uP → AtL Q KQ uQ → Framed Is ⟦ Z ⟧
  framedV {P} {Is} {Q} {Z} r o KP uP KQ uQ aP aQ = record
    { fKP = KP ; fKQ = KQ
    ; fF = λ Ls vs → r (KP ++ Ls ++ KQ) (uP ++ vs ++ uQ)
    ; fAt = λ Ls vs a → vAt o _ _ (AtL-++ {P} {Is ++ Q} {KP} {Ls ++ KQ} {uP} aP (AtL-++ {Is} {Q} {Ls} {KQ} {vs} a aQ))
    ; fcg = λ Ls vs vs′ a b e →
        vcong o _ _ _ (AtL-++ {P} {Is ++ Q} {KP} {Ls ++ KQ} {uP} aP (AtL-++ {Is} {Q} {Ls} {KQ} {vs} a aQ))
                      (AtL-++ {P} {Is ++ Q} {KP} {Ls ++ KQ} {uP} aP (AtL-++ {Is} {Q} {Ls} {KQ} {vs′} b aQ))
                      (∼L-++ {uP} {uP} (∼L-refl uP) (∼L-++ {vs} {vs′} e (∼L-refl uQ)))
    ; fnat = λ {Ls′} {Ls} hs vs a →
        let A = AtL-++ {P} {Is ++ Q} {KP} {Ls ++ KQ} {uP} aP (AtL-++ {Is} {Q} {Ls} {KQ} {vs} a aQ)
            e = resL-frame (idMaps KP) hs (idMaps KQ) uP vs uQ (lenUK aP) (lenUK a)
        in ∼-trans ⟦ Z ⟧
             (vcong o _ _ _
                (AtL-++ {P} {Is ++ Q} {KP} {Ls′ ++ KQ} {uP} aP (AtL-++ {Is} {Q} {Ls′} {KQ} {resL hs vs} (AtL-res Is hs vs a) aQ))
                (AtL-res (P ++ Is ++ Q) (idMaps KP ++ᵐ (hs ++ᵐ idMaps KQ)) _ A)
                (subst (λ ws → (uP ++ resL hs vs ++ uQ) ∼L ws) (sym e)
                   (∼L-++ {uP} {resL (idMaps KP) uP} (∼L-sym′ (resL-ids P KP uP aP))
                      (∼L-++ {resL hs vs} {resL hs vs} (∼L-refl (resL hs vs)) (∼L-sym′ (resL-ids Q KQ uQ aQ))))))
             (vnat o (idMaps KP ++ᵐ (hs ++ᵐ idMaps KQ)) (uP ++ vs ++ uQ) A)
    }

  --------------------------------------------------------------------
  -- Representing corollas.

  record CorD (Is : List Fm) (O : Fm) : Set₁ where
    field
      cr   : List Code → List Uni → UF O
      cok  : Ok (Is ▸ O) cr
      dLs  : Code → UF O → List Code
      dvs  : Code → UF O → List Uni
      dg   : ∀ K t → Map K (concat (dLs K t))
      dAt  : ∀ K t → At ⟦ O ⟧ K t → AtL Is (dLs K t) (dvs K t)
      deq  : ∀ K t → At ⟦ O ⟧ K t → _∼_ ⟦ O ⟧ t (res ⟦ O ⟧ (dg K t) (cr (dLs K t) (dvs K t)))
      dUP  : ∀ {Z} (F : Framed Is Z) {K Ls₁ vs₁ Ls₂ vs₂} (g₁ : Map K (concat Ls₁)) (g₂ : Map K (concat Ls₂)) →
             AtL Is Ls₁ vs₁ → AtL Is Ls₂ vs₂ →
             _∼_ ⟦ O ⟧ (res ⟦ O ⟧ g₁ (cr Ls₁ vs₁)) (res ⟦ O ⟧ g₂ (cr Ls₂ vs₂)) →
             _∼_ Z (res Z (Fr (fKP F) (fKQ F) Ls₁ g₁) (fF F Ls₁ vs₁)) (res Z (Fr (fKP F) (fKQ F) Ls₂ g₂) (fF F Ls₂ vs₂))

  module UC {Is O} (D : CorD Is O) where
    open CorD D

    corV : Val
    corV = mk (Is ▸ O) cr cok

    hdC : List Code → Code
    hdC []      = []
    hdC (K ∷ _) = K

    hdU : List Uni → UF O
    hdU []      = def ⟦ O ⟧
    hdU (u ∷ _) = co O u

    ucraw : ∀ Z → (List Code → List Uni → UF Z) → Nat → List Code → List Uni → UF Z
    ucraw Z r i Ks us =
      res ⟦ Z ⟧ (Fr (take i Ks) (drop 1 (drop i Ks)) (dLs (hdC (drop i Ks)) (hdU (drop i us))) (dg (hdC (drop i Ks)) (hdU (drop i us))))
        (r (take i Ks ++ dLs (hdC (drop i Ks)) (hdU (drop i us)) ++ drop 1 (drop i Ks))
           (take i us ++ dvs (hdC (drop i Ks)) (hdU (drop i us)) ++ drop 1 (drop i us)))

    ucev : ∀ Z r i KP K KQ uP u uQ → length KP ≡ i → length uP ≡ i →
           ucraw Z r i (KP ++ K ∷ KQ) (uP ++ u ∷ uQ)
             ≡ res ⟦ Z ⟧ (Fr KP KQ (dLs K (co O u)) (dg K (co O u))) (r (KP ++ dLs K (co O u) ++ KQ) (uP ++ dvs K (co O u) ++ uQ))
    ucev Z r i KP K KQ uP u uQ lK lu
      rewrite take-++ KP (K ∷ KQ) i lK | drop-++ KP (K ∷ KQ) i lK
            | take-++ uP (u ∷ uQ) i lu | drop-++ uP (u ∷ uQ) i lu = refl

    -- the shape of an argument list at a slot holding O
    record At1 (P Q : List Fm) (Ks : List Code) (us : List Uni) : Set where
      constructor mkAt1
      field
        KP KQ : List Code
        K     : Code
        uP uQ : List Uni
        x     : UF O
        eK    : Ks ≡ KP ++ K ∷ KQ
        eU    : us ≡ uP ++ (O , x) ∷ uQ
        aP    : AtL P KP uP
        ax    : At ⟦ O ⟧ K x
        aQ    : AtL Q KQ uQ

    at1 : ∀ P Q Ks us → AtL (P ++ O ∷ Q) Ks us → At1 P Q Ks us
    at1 P Q Ks us a with split3 P (O ∷ []) Q Ks us a
    ... | sp3 KP KX KQ uP uX uQ refl refl aP aX aQ with AtL-cons aX
    ...   | cns K _ x _ refl refl ax as with AtL-nil as
    ...     | refl , refl = mkAt1 KP KQ K uP uQ x refl refl aP ax aQ

    module _ {P Q Z} {r : List Code → List Uni → UF Z} (o : Ok ((P ++ Is ++ Q) ▸ Z) r) where
      private
        Zp = ⟦ Z ⟧
        i = length P
        lK : ∀ {KP uP} → AtL P KP uP → length KP ≡ i
        lK {KP} {uP} a = AtL-lenK P KP uP a
        lU : ∀ {KP uP} → AtL P KP uP → length uP ≡ i
        lU {KP} {uP} a = AtL-lenU P KP uP a
        tAt : ∀ {K x} → At ⟦ O ⟧ K x → At ⟦ O ⟧ K (co O (O , x))
        tAt {K} {x} a = subst (At ⟦ O ⟧ K) (sym (co-id O x)) a
        AtF : ∀ {KP uP KQ uQ Ls vs} → AtL P KP uP → AtL Is Ls vs → AtL Q KQ uQ → AtL (P ++ Is ++ Q) (KP ++ Ls ++ KQ) (uP ++ vs ++ uQ)
        AtF {KP} {uP} {KQ} {uQ} {Ls} {vs} aP a aQ = AtL-++ {P} {Is ++ Q} {KP} {Ls ++ KQ} {uP} aP (AtL-++ {Is} {Q} {Ls} {KQ} {vs} a aQ)

      ucat : ∀ Ks us → AtL (P ++ O ∷ Q) Ks us → At Zp (concat Ks) (ucraw Z r i Ks us)
      ucat Ks us a with at1 P Q Ks us a
      ... | mkAt1 KP KQ K uP uQ x refl refl aP ax aQ =
        subst (At Zp (concat (KP ++ K ∷ KQ))) (sym (ucev Z r i KP K KQ uP (O , x) uQ (lK aP) (lU aP)))
              (At-res Zp (Fr KP KQ (dLs K t) (dg K t)) (vAt o _ _ (AtF aP (dAt K t (tAt ax)) aQ)))
        where t = co O (O , x)

      uccg : ∀ Ks us vs → AtL (P ++ O ∷ Q) Ks us → AtL (P ++ O ∷ Q) Ks vs → us ∼L vs →
             _∼_ Zp (ucraw Z r i Ks us) (ucraw Z r i Ks vs)
      uccg Ks us vs a b e with at1 P Q Ks us a
      ... | mkAt1 KP KQ K uP uQ x refl refl aP ax aQ with at1 P Q (KP ++ K ∷ KQ) vs b
      ...   | mkAt1 KP′ KQ′ K′ vP vQ y eK refl bP bx bQ
              with split-K {P} {O ∷ []} {Q} KP (K ∷ []) KQ KP′ (K′ ∷ []) KQ′ uP ((O , x) ∷ []) uQ vP ((O , y) ∷ []) vQ
                           aP ((refl , ax) , tt) bP ((refl , bx) , tt) eK
      ...     | refl , refl , refl =
        let e₁ = ∼L-split uP ((O , x) ∷ uQ) vP ((O , y) ∷ vQ) (trans (lU aP) (sym (lU bP))) e
            t = co O (O , x) ; t′ = co O (O , y)
            Ls = dLs K t ; vs₁ = dvs K t ; Ls′ = dLs K t′ ; vs₂ = dvs K t′
        in Zp ⟨ ∼-≡ Zp (ucev Z r i KP K KQ uP (O , x) uQ (lK aP) (lU aP)) ⟩
           Zp ⟨ res-cong Zp ≈M-refl
                  (vcong o _ _ _ (AtF aP (dAt K t (tAt ax)) aQ) (AtF bP (dAt K t (tAt ax)) bQ)
                         (∼L-++ {uP} {vP} (fst e₁) (∼L-++ {vs₁} {vs₁} (∼L-refl vs₁) (snd (snd e₁))))) ⟩
           Zp ⟨ dUP (framedV r o KP vP KQ vQ bP bQ) (dg K t) (dg K t′) (dAt K t (tAt ax)) (dAt K t′ (tAt bx))
                  (⟦ O ⟧ ⟨ ∼-sym ⟦ O ⟧ (deq K t (tAt ax)) ⟩
                   ⟦ O ⟧ ⟨ co-cong O (fst (snd e₁)) ⟩ deq K t′ (tAt bx)) ⟩
                ∼-≡ Zp (sym (ucev Z r i KP K KQ vP (O , y) vQ (lK bP) (lU bP)))

      ucnat : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL (P ++ O ∷ Q) Ks us →
              _∼_ Zp (ucraw Z r i Ks′ (resL hs us)) (res Zp (⊗s hs) (ucraw Z r i Ks us))
      ucnat {Ks′} {Ks} hs us a with at1 P Q Ks us a
      ... | mkAt1 KP KQ K uP uQ x refl refl aP ax aQ with Maps-split KP (K ∷ KQ) hs
      ...   | KP′ , R′ , hP , hR , refl , refl with hR
      ...     | _∷_ {K′} {_} {KQ′} h hQ =
        Zp ⟨ ∼-≡ Zp (cong (ucraw Z r i (KP′ ++ K′ ∷ KQ′)) (resL-++ hP (h ∷ hQ) uP ((O , x) ∷ uQ) (lenUK aP))) ⟩
        Zp ⟨ ∼-≡ Zp (ucev Z r i KP′ K′ KQ′ uP′ (O , res ⟦ O ⟧ h x) uQ′
                          (trans (Maps-lenˡ hP) (lK aP)) (trans (resL-len hP uP (lenUK aP)) (lU aP))) ⟩
        Zp ⟨ dUP (framedV r o KP′ uP′ KQ′ uQ′ aP′ aQ′) (dg K′ t′) (dg K t ∘M h) (dAt K′ t′ (tAt (At-res ⟦ O ⟧ h ax))) aL hyp ⟩
        Zp ⟨ res-cong Zp ≈M-refl
               (Zp ⟨ vcong o _ _ _ (AtF aP′ aL aQ′)
                       (AtL-res (P ++ Is ++ Q) (hP ++ᵐ (idMaps Ls ++ᵐ hQ)) _ (AtF aP aL aQ))
                       (subst (λ ws → (uP′ ++ vs ++ uQ′) ∼L ws)
                          (sym (resL-frame hP (idMaps Ls) hQ uP vs uQ (lenUK aP) (lenUK aL)))
                          (∼L-++ {uP′} {uP′} (∼L-refl uP′)
                             (∼L-++ {vs} {resL (idMaps Ls) vs} (∼L-sym′ (resL-ids Is Ls vs aL)) (∼L-refl uQ′)))) ⟩
                     vnat o (hP ++ᵐ (idMaps Ls ++ᵐ hQ)) (uP ++ vs ++ uQ) (AtF aP aL aQ)) ⟩
        Zp ⟨ ∼-sym Zp (res-∘ Zp (Fr KP′ KQ′ Ls (dg K t ∘M h)) (⊗s (hP ++ᵐ (idMaps Ls ++ᵐ hQ))) YAt) ⟩
        Zp ⟨ res-cong Zp Meq (∼-refl Zp) ⟩
        Zp ⟨ res-∘ Zp (⊗s (hP ++ᵐ (h ∷ hQ))) (Fr KP KQ Ls (dg K t)) YAt ⟩
             ∼-≡ Zp (cong (res Zp (⊗s (hP ++ᵐ (h ∷ hQ)))) (sym (ucev Z r i KP K KQ uP (O , x) uQ (lK aP) (lU aP))))
        where
          t = co O (O , x)
          Ls = dLs K t
          vs = dvs K t
          aL = dAt K t (tAt ax)
          uP′ = resL hP uP
          uQ′ = resL hQ uQ
          aP′ = AtL-res P hP uP aP
          aQ′ = AtL-res Q hQ uQ aQ
          t′ = co O (O , res ⟦ O ⟧ h x)
          Y = r (KP ++ Ls ++ KQ) (uP ++ vs ++ uQ)
          YAt = vAt o _ _ (AtF aP aL aQ)
          crAt = vAt cok Ls vs aL
          hyp : _∼_ ⟦ O ⟧ (res ⟦ O ⟧ (dg K′ t′) (cr (dLs K′ t′) (dvs K′ t′))) (res ⟦ O ⟧ (dg K t ∘M h) (cr Ls vs))
          hyp = ⟦ O ⟧ ⟨ ∼-sym ⟦ O ⟧ (deq K′ t′ (tAt (At-res ⟦ O ⟧ h ax))) ⟩
                ⟦ O ⟧ ⟨ ∼-≡ ⟦ O ⟧ (trans (co-id O (res ⟦ O ⟧ h x)) (cong (res ⟦ O ⟧ h) (sym (co-id O x)))) ⟩
                ⟦ O ⟧ ⟨ res-cong ⟦ O ⟧ ≈M-refl (deq K t (tAt ax)) ⟩
                        ∼-sym ⟦ O ⟧ (res-∘ ⟦ O ⟧ h (dg K t) crAt)
          Meq : (⊗s (hP ++ᵐ (idMaps Ls ++ᵐ hQ)) ∘M Fr KP′ KQ′ Ls (dg K t ∘M h)) ≈M (Fr KP KQ Ls (dg K t) ∘M ⊗s (hP ++ᵐ (h ∷ hQ)))
          Meq = ≈M-trans _ (Fr-post hP (idMaps Ls) hQ (dg K t ∘M h))
                (≈M-trans _ (castM-≈M refl (concat-flat KP Ls KQ)
                               (⊗s-cong (≈ᵐ-++ (≈ᵐ-refl hP)
                                  (≈M-trans _ (∘M-cong (⊗s-ids Ls) ≈M-refl) (∘M-idl (dg K t ∘M h)) , ≈ᵐ-refl hQ))))
                            (≈M-sym (Fr-pre hP h hQ (dg K t))))

      ucok : Ok ((P ++ O ∷ Q) ▸ Z) (ucraw Z r i)
      ucok = ok ucat uccg ucnat

    unC-at : ∀ {Fs Z} (r : List Code → List Uni → UF Z) → Ok (Fs ▸ Z) r → ∀ i → Maybe (SlotN Fs i Is) → Val
    unC-at {Z = Z} r o i (just (slotN P Q refl refl)) = mk ((P ++ O ∷ Q) ▸ Z) (ucraw Z r (length P)) (ucok o)
    unC-at {Fs} {Z} r o i nothing = mk (Fs ▸ Z) r o

    unCv : Nat → Val → Val
    unCv i (mk (Fs ▸ Z) r o) = unC-at r o i (compatN Fs i Is)

    unC-just : ∀ {P Q Z} (r : List Code → List Uni → UF Z) (o : Ok ((P ++ Is ++ Q) ▸ Z) r) →
               unCv (length P) (mk ((P ++ Is ++ Q) ▸ Z) r o) ≡ mk ((P ++ O ∷ Q) ▸ Z) (ucraw Z r (length P)) (ucok o)
    unC-just {P} {Q} r o = cong (unC-at r o (length P)) (compatN-just (slotN P Q refl refl))

    T-unC : ∀ {y P Q Z} → y ∶ ((P ++ Is ++ Q) ▸ Z) → unCv (length P) y ∶ ((P ++ O ∷ Q) ▸ Z)
    T-unC {mk _ r o} refl = cong prof (unC-just r o)

    unC-cong : ∀ {y y′} i → y ≈ y′ → unCv i y ≈ unCv i y′
    unC-cong i (≈c {Fs ▸ Z} {r} {r′} {o} {o′} e) = go (compatN Fs i Is)
      where
        go : (m : Maybe (SlotN Fs i Is)) → unC-at r o i m ≈ unC-at r′ o′ i m
        go nothing = ≈c e
        go (just (slotN P Q refl refl)) = ≈c H
          where
            H : ∀ Ks us → AtL (P ++ O ∷ Q) Ks us → _∼_ ⟦ Z ⟧ (ucraw Z r (length P) Ks us) (ucraw Z r′ (length P) Ks us)
            H Ks us a with at1 P Q Ks us a
            ... | mkAt1 KP KQ K uP uQ x refl refl aP ax aQ =
              ∼-trans ⟦ Z ⟧ (∼-≡ ⟦ Z ⟧ (ucev Z r _ KP K KQ uP (O , x) uQ (AtL-lenK P KP uP aP) (AtL-lenU P KP uP aP)))
              (∼-trans ⟦ Z ⟧ (res-cong ⟦ Z ⟧ ≈M-refl
                               (e _ _ (AtL-++ {P} {Is ++ Q} {KP} {dLs K t ++ KQ} {uP} aP
                                         (AtL-++ {Is} {Q} {dLs K t} {KQ} {dvs K t} (dAt K t (subst (At ⟦ O ⟧ K) (sym (co-id O x)) ax)) aQ))))
                             (∼-≡ ⟦ Z ⟧ (sym (ucev Z r′ _ KP K KQ uP (O , x) uQ (AtL-lenK P KP uP aP) (AtL-lenU P KP uP aP)))))
              where t = co O (O , x)

    private
      sl : ∀ P Q → Slot (P ++ O ∷ Q) (length P) O
      sl P Q = slot P Q refl refl

    unC-l : ∀ {x P Q Z} → x ∶ ((P ++ O ∷ Q) ▸ Z) → unCv (length P) (pc x (length P) corV) ≈ x
    unC-l {mk _ r o} {P} {Q} {Z} refl =
      ≈-trans (≈-≡ (trans (cong (unCv (length P)) (pc-just o cok (length P) (sl P Q)))
                          (unC-just (PC.rc o cok (length P) (sl P Q)) (PC.cok o cok (length P) (sl P Q)))))
              (≈c H)
      where
        rc = PC.rc o cok (length P) (sl P Q)
        H : ∀ Ks us → AtL (P ++ O ∷ Q) Ks us → _∼_ ⟦ Z ⟧ (ucraw Z rc (length P) Ks us) (r Ks us)
        H Ks us a with at1 P Q Ks us a
        ... | mkAt1 KP KQ K uP uQ x refl refl aP ax aQ =
          ⟦ Z ⟧ ⟨ ∼-≡ ⟦ Z ⟧ (trans (ucev Z rc _ KP K KQ uP (O , x) uQ (AtL-lenK P KP uP aP) (AtL-lenU P KP uP aP))
                            (trans (cong (res ⟦ Z ⟧ (Fr KP KQ Ls g)) (PC.evA o cok (length P) (sl P Q) {KQ = KQ} {uQ = uQ} aP aL))
                                   (res-cast ⟦ Z ⟧ refl (concat-flat KP Ls KQ) (⊗s hs) _))) ⟩
          ⟦ Z ⟧ ⟨ ∼-sym ⟦ Z ⟧ (vnat o hs (uP ++ (O , cr Ls vs) ∷ uQ)
                                 (AtL-++ {P} {O ∷ Q} {KP} {concat Ls ∷ KQ} {uP} aP ((refl , vAt cok Ls vs aL) , aQ))) ⟩
                  vcong o _ _ _
                    (AtL-res (P ++ O ∷ Q) hs _ (AtL-++ {P} {O ∷ Q} {KP} {concat Ls ∷ KQ} {uP} aP ((refl , vAt cok Ls vs aL) , aQ)))
                    (AtL-++ {P} {O ∷ Q} {KP} {K ∷ KQ} {uP} aP ((refl , ax) , aQ))
                    (subst (λ ws → ws ∼L (uP ++ (O , x) ∷ uQ))
                       (sym (resL-++ (idMaps KP) (g ∷ idMaps KQ) uP ((O , cr Ls vs) ∷ uQ) (lenUK aP)))
                       (∼L-++ {resL (idMaps KP) uP} {uP} (resL-ids P KP uP aP)
                          (∼u (∼-trans ⟦ O ⟧ (∼-sym ⟦ O ⟧ (deq K t tA)) (∼-≡ ⟦ O ⟧ (co-id O x))) , resL-ids Q KQ uQ aQ)))
          where
            t = co O (O , x)
            tA = subst (At ⟦ O ⟧ K) (sym (co-id O x)) ax
            Ls = dLs K t
            vs = dvs K t
            g = dg K t
            aL = dAt K t tA
            hs = idMaps KP ++ᵐ (g ∷ idMaps KQ)

    unC-r : ∀ {y P Q Z} → y ∶ ((P ++ Is ++ Q) ▸ Z) → pc (unCv (length P) y) (length P) corV ≈ y
    unC-r {mk _ r o} {P} {Q} {Z} refl =
      ≈-trans (≈-≡ (trans (cong (λ v → pc v (length P) corV) (unC-just r o)) (pc-just (ucok o) cok (length P) (sl P Q))))
              (≈c H)
      where
        rc = PC.rc (ucok o) cok (length P) (sl P Q)
        H : ∀ Ks us → AtL (P ++ Is ++ Q) Ks us → _∼_ ⟦ Z ⟧ (rc Ks us) (r Ks us)
        H Ks us a with split3 P Is Q Ks us a
        ... | sp3 KP Ls KQ uP vs uQ refl refl aP aL aQ =
          ⟦ Z ⟧ ⟨ ∼-≡ ⟦ Z ⟧ (trans (PC.evA (ucok o) cok (length P) (sl P Q) {KQ = KQ} {uQ = uQ} aP aL)
                                   (ucev Z r _ KP (concat Ls) KQ uP (O , cr Ls vs) uQ (AtL-lenK P KP uP aP) (AtL-lenU P KP uP aP))) ⟩
          ⟦ Z ⟧ ⟨ dUP (framedV r o KP uP KQ uQ aP aQ) (dg (concat Ls) t) (idMap (concat Ls)) (dAt (concat Ls) t tA) aL
                    (⟦ O ⟧ ⟨ ∼-sym ⟦ O ⟧ (deq (concat Ls) t tA) ⟩
                     ⟦ O ⟧ ⟨ ∼-≡ ⟦ O ⟧ (co-id O (cr Ls vs)) ⟩ ∼-sym ⟦ O ⟧ (res-id ⟦ O ⟧ crA)) ⟩
          ⟦ Z ⟧ ⟨ ∼-≡ ⟦ Z ⟧ (trans (res-cast ⟦ Z ⟧ refl (concat-flat KP Ls KQ) _ Y)
                                   (cong (λ hs → res ⟦ Z ⟧ (⊗s hs) Y)
                                         (trans (cong (idMaps KP ++ᵐ_) refl) (sym (idMaps-++ KP (concat Ls ∷ KQ)))))) ⟩
          ⟦ Z ⟧ ⟨ res-cong ⟦ Z ⟧ (⊗s-ids (KP ++ concat Ls ∷ KQ)) (∼-refl ⟦ Z ⟧) ⟩
                  res-id ⟦ Z ⟧ (At-≡ ⟦ Z ⟧ (sym (concat-flat KP Ls KQ)) (vAt o _ _ (AtL-++ {P} {Is ++ Q} {KP} {Ls ++ KQ} {uP} aP (AtL-++ {Is} {Q} {Ls} {KQ} {vs} aL aQ))))
          where
            crA = vAt cok Ls vs aL
            t = co O (O , cr Ls vs)
            tA = subst (At ⟦ O ⟧ (concat Ls)) (sym (co-id O (cr Ls vs))) crA
            Y = r (KP ++ Ls ++ KQ) (uP ++ vs ++ uQ)
