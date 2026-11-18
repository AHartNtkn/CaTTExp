------------------------------------------------------------------------
-- The sides of a coherence in the free model (ledger item A3a, general
-- case).
--
-- Let coh Θ (s →_B u) be allowed by the side condition, with d = dim B,
-- and let Xs, Xu be the generic values of s and u in the free model
-- (each a cell with the boundary B prescribes). Then
--
--     Xs = s_d (tr Θ),   Xu = t_d (tr Θ),   and tr Θ has dimension ≤ d+1.
--
-- Coherence case: Xs and Xu have the labels of all of Θ, so both are
-- tr Θ (support injectivity), which then has dimension ≤ d. Operation
-- case, with i = dim Θ − 1: Xs and Xu have the labels of ∂⁻ᵢΘ and ∂⁺ᵢΘ,
-- the labels of the truncations of tr Θ at i (CaTTExp.Strict.TrFlat), so
-- Xs = sᵢ(tr Θ) and Xu = tᵢ(tr Θ). Since s mentions a variable of
-- dimension i, i ≤ d. If i = d this is the claim. If i < d (a
-- degenerate operation) both Xs and Xu equal the (d−1)-source of B, so
-- sᵢ(tr Θ) = tᵢ(tr Θ), which forces tr Θ to have dimension ≤ i
-- (CaTTExp.Strict.FreeTV.stab), and the claim follows again.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Typing
import CaTTExp.Subst

module CaTTExp.Strict.Key
  (𝕊 : Signature) (closed : CaTTExp.Subst.Closed 𝕊 (CaTTExp.Typing.cattSide 𝕊))
  where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.PsTree 𝕊 using (tr)
open import CaTTExp.Strict.LabelSets
open import CaTTExp.Strict.PsFacts 𝕊 using (ps-facts; ord; src-has; dimv)
open import CaTTExp.Strict.GenericEnv 𝕊
open import CaTTExp.Strict.FreeTV 𝕊 using (TV; inj; tv-bdm; tv-bdp; stab)
open import CaTTExp.Strict.TrFlat 𝕊 using (flat-src; flat-tgt; flat-tr; upTo≈; height; tv-tr)
open import CaTTExp.Strict.Support 𝕊 closed using (supp)
open import CaTTExp.Strict.Dim 𝕊 closed using (≈?-elem; dim-tmty)
import CaTTExp.Strict.Lambda 𝕊 as L
import CaTTExp.Strict.OmegaEval 𝕊 𝒯 M𝒯 as E
open ωCat 𝒯 using (src-src-≥; src-tgt-≥; tgt-src-≥; src-src-<; tgt-tgt-≥)
open Basics 𝒯 using (tgt-of-dim; dim-up)

private
  L→ : ∀ {m n} → m L.≤ n → m ≤ n
  L→ L.z≤n     = z≤n
  L→ (L.s≤s p) = s≤s (L→ p)

  ∧-l : ∀ {a b} → T (a ∧ b) → T a
  ∧-l {true} _ = tt

  ∧-r : ∀ {a b} → T (a ∧ b) → T b
  ∧-r {true} p = p

  pred≤ : ∀ h → h ≤ suc (h ∸ 1)
  pred≤ zero    = z≤n
  pred≤ (suc h) = ≤-refl (suc h)

  pred<ℕ : ∀ h → T ((h ∸ 1) <ℕ suc h)
  pred<ℕ zero          = tt
  pred<ℕ (suc zero)    = tt
  pred<ℕ (suc (suc h)) = pred<ℕ (suc h)

  mdet𝒯 : E.Mk-det
  mdet𝒯 ()

  ≈⇒ : ∀ {xs ys} → (∀ v → elem v xs ≡ elem v ys) → xs ≈ ys
  ≈⇒ = ≈-elem

key : ∀ {Θ z B s u Xs Xu} → (dΘ : Θ ⊢ps z ∶ ⋆) → Θ ⊢tm s ∶ B → Θ ⊢tm u ∶ B → T (cattSide Θ B s u) →
      E.Ev (η Θ) s Xs → E.VE Xs B (η Θ) → E.Ev (η Θ) u Xu → E.VE Xu B (η Θ) →
      (Xs ≡ bdm (dim B) (tr Θ)) × (Xu ≡ bdp (dim B) (tr Θ)) × (bdm (suc (dim B)) (tr Θ) ≡ tr Θ)
key {Θ} {z} {B} {s} {u} {Xs} {Xu} dΘ ds du side evs ves evu veu with isCoh Θ B s u in eC
... | true =
  let p = side′
      eS = ≈-trans (≈-trans fS (≈⇒ (≈?-elem (fvTmTy s B) (varsCtx Θ) (∧-l p)))) (≈-sym allT)
      eU = ≈-trans (≈-trans fU (≈⇒ (≈?-elem (fvTmTy u B) (varsCtx Θ) (∧-r {≈? (fvTmTy s B) (varsCtx Θ)} p)))) (≈-sym allT)
      xs≡ = inj Θ o ⋆ Xs Tr tS tvT (fst eS) (snd eS)
      xu≡ = inj Θ o ⋆ Xu Tr tU tvT (fst eU) (snd eU)
      dimT : bdm d Tr ≡ Tr
      dimT = subst (λ X → bdm d X ≡ X) xs≡ (fst ves)
  in trans xs≡ (sym dimT) , trans xu≡ (sym (tgt-of-dim dimT)) , dim-up (≤-suc (≤-refl d)) dimT
  where
  side′ : T (isCoh Θ B s u)
  side′ rewrite eC = tt
  d = dim B
  Tr = tr Θ
  o = ord (ps-facts dΘ)
  tvT = tv-tr dΘ
  sS = supp dΘ ds evs
  sU = supp dΘ du evu
  tS = fst sS
  tU = fst sU
  fS = snd sS
  fU = snd sU
  allT : flat Tr ≈ varsCtx Θ
  allT = ≈-trans (≡→≈ (flat-tr dΘ)) (upTo≈ (len Θ))
... | false = op (tri d i)
  where
  d = dim B
  h = dimCtx Θ
  i = h ∸ 1
  Tr = tr Θ
  o = ord (ps-facts dΘ)
  tvT = tv-tr dΘ
  pOp : T (isOp Θ B s u)
  pOp = side
  sS = supp dΘ ds evs
  sU = supp dΘ du evu
  eS : flat Xs ≈ flat (bdm i Tr)
  eS = ≈-trans (≈-trans (snd sS) (≈⇒ (≈?-elem (fvTmTy s B) (∂⁻ Θ) (∧-l pOp)))) (≡→≈ (sym (flat-src dΘ i)))
  eU : flat Xu ≈ flat (bdp i Tr)
  eU = ≈-trans (≈-trans (snd sU) (≈⇒ (≈?-elem (fvTmTy u B) (∂⁺ Θ) (∧-r {≈? (fvTmTy s B) (∂⁻ Θ)} pOp))))
               (≡→≈ (sym (flat-tgt dΘ i)))
  xs≡ : Xs ≡ bdm i Tr
  xs≡ = inj Θ o ⋆ Xs (bdm i Tr) (fst sS) (tv-bdm Θ o i ⋆ Tr tvT) (fst eS) (snd eS)
  xu≡ : Xu ≡ bdp i Tr
  xu≡ = inj Θ o ⋆ Xu (bdp i Tr) (fst sU) (tv-bdp Θ o i ⋆ Tr tvT) (fst eU) (snd eU)
  i≤d : i ≤ d
  i≤d = let (w , mw , dw) = src-has dΘ i (pred<ℕ h)
            mw′ = trans (≈?-elem (fvTmTy s B) (∂⁻ Θ) (∧-l pOp) w) mw
        in subst (_≤ d) dw (L→ (dim-tmty ds w mw′))
  hgt : bdm (suc i) Tr ≡ Tr
  hgt = trans (cong (bdm (suc i)) (sym (height dΘ))) (trans (src-src-≥ Tr (pred≤ h)) (height dΘ))
  op : Tri d i → (Xs ≡ bdm d Tr) × (Xu ≡ bdp d Tr) × (bdm (suc d) Tr ≡ Tr)
  op (tri< l) = ⊥-elim (≤-<-⊥ i≤d l)
  op (tri≡ e) = trans xs≡ (cong (λ k → bdm k Tr) (sym e)) ,
                trans xu≡ (cong (λ k → bdp k Tr) (sym e)) ,
                trans (cong (λ k → bdm (suc k) Tr) e) hgt
  op (tri> l) =
    let e  : bdm i Tr ≡ bdp i Tr
        e  = trans (sym xs≡) (trans (degen B i l ves veu xs≡ xu≡) xu≡)
        tT : Tr ≡ bdm i Tr
        tT = trans (sym hgt) (stab Θ o i ⋆ Tr tvT e)
        le = <→≤ l
        sd : bdm d Tr ≡ bdm i Tr
        sd = trans (cong (bdm d) tT) (src-src-≥ Tr le)
        td : bdp d Tr ≡ bdm i Tr
        td = trans (cong (bdp d) tT) (tgt-src-≥ Tr le)
    in trans xs≡ (sym sd) ,
       trans (sym (degen B i l ves veu xs≡ xu≡)) (trans xs≡ (sym td)) ,
       trans (cong (bdm (suc d)) tT) (trans (src-src-≥ Tr (≤-suc le)) (sym tT))
    where
    degen : ∀ B′ i → i < dim B′ → E.VE Xs B′ (η Θ) → E.VE Xu B′ (η Θ) →
            Xs ≡ bdm i Tr → Xu ≡ bdp i Tr → Xs ≡ Xu
    degen (arr B″ s′ u′) i (s≤s l′) (_ , e₁ , _) (_ , e₂ , _) p q =
      E.ev-det (λ {k} {c} {c′} m → mdet𝒯 {k} {c} {c′} m)
        (subst (E.Ev (η Θ) s′) (trans (cong (bdm (dim B″)) p) (trans (src-src-≥ Tr l′) (sym p))) e₁)
        (subst (E.Ev (η Θ) s′) (trans (cong (bdm (dim B″)) q) (trans (src-tgt-≥ Tr l′) (sym q))) e₂)
