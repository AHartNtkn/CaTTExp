------------------------------------------------------------------------
-- Presupposition for lim and the universal cone (ledger S27 (f)).
--
-- For every cone shape, every valid head of CaTTExp.Binder.LimHeads
-- has a well-formed type over its arity (`HeadOK`), in the kernel with
-- plain CaTT's side condition and any mark judgment stable under
-- renaming and substitution that gives variables their entry's marks
-- (MarkRen, MarkSub, MarkVar; `Gen`). The instance at the end of this
-- module is rule (MARK) alone (`varMark`); CaTTExp.Binder.UniMark uses
-- it with (MARK) + (HEAD-inv):
--
--   Γ ⊢ ⋆                                       (lim_Γ)
--   Γ ⊢ A_g [Γ, lim_Γ[id], λ_{Γ,0}[id], …, λ_{Γ,g−1}[id]]   (λ_{Γ,g})
--
-- where A_g is the type of cell g of the cone context K over Γ. The
-- shape's validity (CaTTExp.Binder.LimHeads, `shapeOK`) says only
-- that Γ and K are well-formed pure contexts and K starts with Γ, c : ⋆.
-- The proof is by induction on g: the substitution
-- (Γ, lim_Γ[id], λ_{Γ,0}[id], …, λ_{Γ,g−1}[id]) is well typed into the
-- first |Γ| + 1 + g entries of K (`cone-sub`), each leg typed by rule
-- (op) once the earlier ones are, and then A_g, well formed over those
-- entries, is well formed over Γ by substitution. On the way, every
-- earlier leg is shown valid.
--
-- Hence PresupLaws (`lim-presup`): with CaTTExp.Binder.Presup, every
-- term of CaTT with lim and its universal cone, over any shape, has a
-- well-formed type.
--
-- The argument is stated for any head family containing lim and the
-- legs with the same data, and any mark judgment as above (`Gen`), so
-- that CaTTExp.Binder.UniPresup reuses it for the family with uni.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.LimHeads
open import CaTTExp.Binder.HeadSpec using (HeadSpec)
import CaTTExp.Binder.HeadSpec as HS
import CaTTExp.Binder.Laws as BL
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Typing as Tg
import CaTTExp.Binder.Rename as Rn
import CaTTExp.Binder.Subst as Sb

module CaTTExp.Binder.LimPresup (shape : P.Ctx → Maybe P.Ctx) where

------------------------------------------------------------------------
-- The argument, for any head family that contains lim and the legs
-- (through `inj`, with the same arities, types and validity), so that
-- families extending lim (CaTTExp.Binder.UniPresup) reuse it.

module Gen (hs : HeadSpec P.K) (inj : LimF → HeadSpec.H hs)
  (hctx-eq : ∀ l y → HeadSpec.hctx hs (inj l) y ≡ LimConstruction.hctx P.K (HeadSpec.H hs) inj shape l y)
  (hty-eq  : ∀ l y → HeadSpec.hty hs (inj l) y ≡ LimConstruction.hty P.K (HeadSpec.H hs) inj shape l y)
  (hok-eq  : ∀ l y → HeadSpec.hok hs (inj l) y ≡ LimConstruction.hok P.K (HeadSpec.H hs) inj shape l y)
  (mark : Signature.Ctx (HS.Laws.𝕊 P.∅ hs) → BM.Mark → Signature.Tm (HS.Laws.𝕊 P.∅ hs) → Bool)
  (markRen : Rn.MarkRen (HS.Laws.𝕊 P.∅ hs) (Tg.cattSide (HS.Laws.𝕊 P.∅ hs)) mark)
  (markSub : Sb.MarkSub (HS.Laws.𝕊 P.∅ hs) (Tg.cattSide (HS.Laws.𝕊 P.∅ hs)) mark)
  (markVar : Sb.MarkVar (HS.Laws.𝕊 P.∅ hs) (Tg.cattSide (HS.Laws.𝕊 P.∅ hs)) mark)
  where

 open HS.Laws P.∅ hs using (𝕊; spec-honest; spec-head; spec-laws)
 open Signature 𝕊
 open import CaTTExp.Binder.SyntaxLemmas K B
 open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
 open import CaTTExp.Binder.TypingWith 𝕊 cattSide mark
 open import CaTTExp.Binder.Scoping 𝕊 cattSide mark
 open import CaTTExp.Binder.Rename 𝕊 cattSide mark
 open import CaTTExp.Binder.Subst 𝕊 cattSide mark
 open import CaTTExp.Binder.HonestHeads 𝕊 using (HonestAt; honest?)
 open import CaTTExp.Binder.HonestHeads 𝕊 using (module Typed)
 open Typed cattSide mark using (op-intro; honest-ok)
 import CaTTExp.Binder.Heads 𝕊 as Hd
 open Hd.Typed cattSide mark using (HeadOK; head-presup; arity; resTy)
 open import CaTTExp.Binder.PureSide 𝕊 using (cattSide-pure)
 open import CaTTExp.Binder.PureEmbed 𝕊 cattSide mark using (SidePure; ctx-emb; ty-emb)
 open LimConstruction P.K B inj shape
 open PureEmb P.K B
 open BL 𝕊 using (Closed; BinderLaws)
 open import CaTTExp.Binder.Presup 𝕊 cattSide mark using (PresupLaws; tm-ty)

 closed : Closed
 closed ()

 laws : BinderLaws
 laws = spec-laws

 sp : SidePure
 sp Δ A t u p = subst T (sym (cattSide-pure Δ A t u)) p

 ------------------------------------------------------------------------
 -- The kernel's pure embedding is LimHeads'.

 mutual
   pe-ty : ∀ A → peTy A ≡ embTy A
   pe-ty P.⋆           = refl
   pe-ty (P.arr A t u) rewrite pe-ty A | pe-tm t | pe-tm u = refl

   pe-tm : ∀ t → peTm t ≡ embTm t
   pe-tm (P.var i)     = refl
   pe-tm (P.coh Θ A τ) rewrite pe-ctx Θ | pe-ty A | pe-sub τ = refl
   pe-tm (P.cst ())

   pe-ctx : ∀ Γ → peCtx Γ ≡ embCtx Γ
   pe-ctx P.ε       = refl
   pe-ctx (Γ P.▸ A) rewrite pe-ctx Γ | pe-ty A = refl

   pe-sub : ∀ σ → peSub σ ≡ embSub σ
   pe-sub P.⟨⟩       = refl
   pe-sub (σ P.,ₛ t) rewrite pe-sub σ | pe-tm t = refl

 mutual
   lc-peTy : ∀ A → T (lcTy? 0 (peTy A))
   lc-peTy P.⋆           = tt
   lc-peTy (P.arr A t u) = ∧T (lc-peTy A) (∧T (lc-peTm t) (lc-peTm u))

   lc-peTm : ∀ t → T (lcTm? 0 (peTm t))
   lc-peTm (P.var i)     = tt
   lc-peTm (P.coh Θ A τ) = lc-peSub τ
   lc-peTm (P.cst ())

   lc-peSub : ∀ σ → T (lcSub? 0 (peSub σ))
   lc-peSub P.⟨⟩       = tt
   lc-peSub (σ P.,ₛ t) = ∧T (lc-peSub σ) (lc-peTm t)

 len-pe : ∀ Γ → len (peCtx Γ) ≡ P.len Γ
 len-pe P.ε       = refl
 len-pe (Γ P.▸ _) = cong suc (len-pe Γ)

 pe-ctx-wf : ∀ {Γ} → Γ P.⊢ctx → peCtx Γ ⊢ctx
 pe-ctx-wf {Γ} w = subst _⊢ctx (sym (pe-ctx Γ)) (ctx-emb sp w)

 pe-ty-wf : ∀ {Γ A} → Γ P.⊢ty A → peCtx Γ ⊢ty peTy A
 pe-ty-wf {Γ} {A} a rewrite pe-ctx Γ | pe-ty A = ty-emb sp a

 ------------------------------------------------------------------------
 -- Prefixes of a pure context.

 pre : P.Ctx → Nat → P.Ctx
 pre K i = dropR (P.len K ∸ i) K

 private
   fromT : ∀ {X : Set} (m : Maybe X) → T (is-just m) → X
   fromT (just x) _ = x

   sub-suc : ∀ m n → T (n <ℕ suc m) → suc m ∸ n ≡ suc (m ∸ n)
   sub-suc m       zero    _ = refl
   sub-suc (suc m) (suc n) p = sub-suc m n p
   sub-suc zero    (suc zero) ()
   sub-suc zero    (suc (suc n)) ()

   n∸n : ∀ n → n ∸ n ≡ 0
   n∸n zero    = refl
   n∸n (suc n) = n∸n n

   sn∸n : ∀ n → suc n ∸ n ≡ 1
   sn∸n zero    = refl
   sn∸n (suc n) = sn∸n n

   ≢→< : ∀ i n → (i ==ℕ n) ≡ false → T (i <ℕ suc n) → T (i <ℕ n)
   ≢→< zero    zero    () _
   ≢→< zero    (suc n) _ _ = tt
   ≢→< (suc i) (suc n) e p = ≢→< i n e p
   ≢→< (suc i) zero    _ ()

 -- Lookup at i in range, and the prefix up to i.
 lk-range : ∀ K i {A} → P.lookup K i ≡ just A → T (i <ℕ P.len K)
 lk-range P.ε       i ()
 lk-range (K P.▸ B) i e with i ==ℕ P.len K in q
 ... | true  rewrite ==→≡ i (P.len K) q = <-self (P.len K)
 ... | false = <-suc i (P.len K) (lk-range K i e)

 lk-in : ∀ K i → T (i <ℕ P.len K) → Σ P.Ty λ A → P.lookup K i ≡ just A
 lk-in P.ε       i ()
 lk-in (K P.▸ B) i p with i ==ℕ P.len K in q
 ... | true  = B , refl
 ... | false = lk-in K i (≢→< i (P.len K) q p)

 lk-wf : ∀ {K} → K P.⊢ctx → ∀ i {A} → P.lookup K i ≡ just A →
         (pre K i P.⊢ty A) × (pre K (suc i) ≡ pre K i P.▸ A)
 lk-wf {K P.▸ B} (P.▸-wf w b) i e with i ==ℕ P.len K in q
 ... | true rewrite ==→≡ i (P.len K) q | sn∸n (P.len K) | n∸n (P.len K) with e
 ...   | refl = b , refl
 lk-wf {K P.▸ B} (P.▸-wf w b) i e | false
   rewrite sub-suc (P.len K) i (<-suc i (P.len K) (lk-range K i e))
         | sub-suc (P.len K ∸ suc i) 0 tt =
   let (a , s) = lk-wf w i e in
   a , trans (cong (λ k → dropR k (K P.▸ B)) (sub-eq (P.len K) i (lk-range K i e))) s
   where
   sub-eq : ∀ m i → T (i <ℕ m) → m ∸ i ≡ suc (m ∸ suc i)
   sub-eq (suc m) zero    _ = sym (sub-suc m 0 tt)
   sub-eq (suc m) (suc i) p = sub-eq m i p

 ------------------------------------------------------------------------
 -- The identity substitution.

 idsub : ∀ {Γ} → Γ ⊢ctx → Γ ⊢sub fresh 0 (len Γ) ∶ Γ
 idsub {ε} w = ⟨⟩-wf w
 idsub {Γ ▸[ ms ] A} w@(▸-wf wΓ a) =
   ,-wf (wk-sub closed laws markRen wΓ (idsub wΓ) w)
        (subst (λ X → (Γ ▸[ ms ] A) ⊢tm var (len Γ) ∶ X)
               (sym (id-ty (len Γ) A (ty-sc closed laws a)))
               (var-wf w (lookup-top Γ {ms} A (len Γ) (==-self {len Γ} refl))))
        (subst (λ ns → T (marksOK (Γ ▸[ ms ] A) ns (var (len Γ))))
               (marksAt-top Γ ms A (len Γ) (==-self {len Γ} refl))
               (markVar w (lookup-top Γ {ms} A (len Γ) (==-self {len Γ} refl))))

 ------------------------------------------------------------------------
 -- The heads at a valid shape.

 -- hok and hty of a leg, read off the shape.
 -- The family's validity, arity and type at inj l are lim's.
 side-at : ∀ l y → T (hok l y) → T (honest? (hctx l y)) →
           T (scTy? (len (hctx l y)) (hty l y)) → T (lcTy? 0 (hty l y)) → T (bside (inj l) y ε)
 side-at l y a b c d rewrite hok-eq l y | hctx-eq l y | hty-eq l y = ∧T a (∧T b (∧T c d))

 side-hok : ∀ l y → T (bside (inj l) y ε) → T (hok l y)
 side-hok l y p rewrite hok-eq l y = fst (T∧ {hok l y} p)

 side-hon : ∀ l y → T (bside (inj l) y ε) → T (honest? (hctx l y))
 side-hon l y p rewrite hok-eq l y | hctx-eq l y = fst (T∧ {honest? (hctx l y)} (snd (T∧ {hok l y} p)))

 op-at : ∀ l y {Ξ σ} → T (bside (inj l) y ε) → Ξ ⊢ctx → Ξ ⊢sub σ ∶ hctx l y →
         Ξ ⊢tm bnd (inj l) y ε σ ∶ hty l y [ σ ]ty
 op-at l y {Ξ} {σ} ok w s =
   subst (λ X → Ξ ⊢tm bnd (inj l) y ε σ ∶ X [ σ ]ty) (hty-eq l y)
     (op-intro (spec-honest (inj l) y ok) ok w (subst (Ξ ⊢sub σ ∶_) (sym (hctx-eq l y)) s))

 ok-at : ∀ l y → (p : T (bside (inj l) y ε)) → hctx l y ⊢ty hty l y →
         arity (inj l) y ε ⊢ty resTy (inj l) y ε
 ok-at l y p a =
   honest-ok (spec-honest (inj l) y p)
     (subst (_⊢ty HeadSpec.hty hs (inj l) y) (sym (hctx-eq l y))
        (subst (hctx l y ⊢ty_) (sym (hty-eq l y)) a)) ε p

 hok-leg : ∀ Γ g {K A} → shape Γ ≡ just K → T (shapeOK Γ K) →
           P.lookup K (suc (P.len Γ + g)) ≡ just A → T (hok (legF Γ) g)
 hok-leg Γ g {K} e ok l rewrite e | l = ∧T ok tt

 hty-leg : ∀ Γ g {A} → cellTy Γ g ≡ just A → hty (legF Γ) g ≡ peTy A [ coneSub Γ g ]ty
 hty-leg Γ g e with cellTy Γ g
 hty-leg Γ g refl | just _ = refl

 module AtShape (Γ K : P.Ctx) (e : shape Γ ≡ just K) (ok : T (shapeOK Γ K))
                (hon : T (honest? (peCtx Γ))) where

   nΓ = P.len Γ
   G  = peCtx Γ

   private
     p₁ = T∧ {is-just (P.checkCtx Γ)} ok
     p₂ = T∧ {is-just (P.checkCtx K)} (snd p₁)
     p₃ = T∧ {suc (P.len Γ) <ℕ suc (P.len K)} (snd p₂)

   wΓ : Γ P.⊢ctx
   wΓ = fromT (P.checkCtx Γ) (fst p₁)

   wK : K P.⊢ctx
   wK = fromT (P.checkCtx K) (fst p₂)

   eq₀ : pre K (suc nΓ) ≡ Γ P.▸ P.⋆
   eq₀ = P.==Ctx-sound _ _ (snd p₃)

   wG : G ⊢ctx
   wG = pe-ctx-wf wΓ

   lenG : len G ≡ nΓ
   lenG = len-pe Γ

   idG : G ⊢sub fresh 0 nΓ ∶ G
   idG = subst (λ n → G ⊢sub fresh 0 n ∶ G) lenG (idsub wG)

   lim-ok : T (bside (inj (limF Γ)) 0 ε)
   lim-ok = side-at (limF Γ) 0 (fst p₁) hon tt tt

   lim-wf : G ⊢tm limId Γ ∶ ⋆
   lim-wf = op-at (limF Γ) 0 lim-ok wG idG

   -- Leg g, given that the cone substitution below it is well typed:
   -- its type is well formed, it is valid, and it is well typed.
   module Leg (g : Nat) (A : P.Ty) (l : P.lookup K (suc (nΓ + g)) ≡ just A)
              (s : G ⊢sub coneSub Γ g ∶ peCtx (pre K (suc (nΓ + g)))) where

     a : G ⊢ty peTy A [ coneSub Γ g ]ty
     a = ty[] closed laws markRen markSub markVar (pe-ty-wf (fst (lk-wf wK (suc (nΓ + g)) l))) s

     cell : cellTy Γ g ≡ just A
     cell rewrite e = l

     hty≡ : hty (legF Γ) g ≡ peTy A [ coneSub Γ g ]ty
     hty≡ = hty-leg Γ g cell

     a′ : G ⊢ty hty (legF Γ) g
     a′ = subst (G ⊢ty_) (sym hty≡) a

     sc : T (scTy? (len G) (hty (legF Γ) g))
     sc = ty-sc closed laws a′

     lc : T (lcTy? 0 (hty (legF Γ) g))
     lc = subst (λ X → T (lcTy? 0 X)) (sym hty≡)
            (lc-ty[] 0 (peTy A) (coneSub Γ g) (lc-peTy A) (sub-lc s))

     leg-ok : T (bside (inj (legF Γ)) g ε)
     leg-ok = side-at (legF Γ) g (hok-leg Γ g e ok l) hon sc lc

     leg-wf : G ⊢tm legId Γ g ∶ peTy A [ coneSub Γ g ]ty
     leg-wf = subst (G ⊢tm legId Γ g ∶_)
                (trans (id-ty nΓ (hty (legF Γ) g) sc′) hty≡)
                (op-at (legF Γ) g leg-ok wG idG)
       where
       sc′ : T (scTy? nΓ (hty (legF Γ) g))
       sc′ = subst (λ n → T (scTy? n (hty (legF Γ) g))) lenG sc

   -- The cone substitution below cell g is well typed.
   cone-sub : ∀ g → T ((nΓ + g) <ℕ P.len K) →
              G ⊢sub coneSub Γ g ∶ peCtx (pre K (suc (nΓ + g)))
   cone-sub zero _ =
     subst (λ X → G ⊢sub coneSub Γ zero ∶ peCtx X)
       (sym (trans (cong (λ n → pre K (suc n)) (+-zero nΓ)) eq₀))
       (,-wf idG lim-wf tt)
   cone-sub (suc g) q =
     subst (λ X → G ⊢sub coneSub Γ (suc g) ∶ peCtx X)
       (sym (trans (cong (λ n → pre K (suc n)) (+-suc nΓ g)) (snd (lk-wf wK (suc (nΓ + g)) l))))
       (,-wf s (Leg.leg-wf g A l s) tt)
     where
     q′ : T (suc (nΓ + g) <ℕ P.len K)
     q′ = subst (λ n → T (n <ℕ P.len K)) (+-suc nΓ g) q
     s = cone-sub g (<-trans (nΓ + g) (suc (nΓ + g)) (P.len K) (<-self (nΓ + g)) q′)
     A = fst (lk-in K (suc (nΓ + g)) q′)
     l = snd (lk-in K (suc (nΓ + g)) q′)

 ------------------------------------------------------------------------
 -- HeadOK for every head, and the presupposition law.

 private
   hok-inv : ∀ Γ g → T (hok (legF Γ) g) →
             Σ P.Ctx λ K → (shape Γ ≡ just K) × T (shapeOK Γ K)
               × Σ P.Ty λ A → P.lookup K (suc (P.len Γ + g)) ≡ just A
   hok-inv Γ g h with shape Γ in e
   ... | just K with P.lookup K (suc (P.len Γ + g)) in l
   ...   | just A  = K , refl , fst (T∧ {shapeOK Γ K} h) , A , l
   ...   | nothing = ⊥-elim (nope (snd (T∧ {shapeOK Γ K} h)))
     where
     nope : T false → ⊥
     nope ()

   <-pred : ∀ i n → T (suc i <ℕ n) → T (i <ℕ n)
   <-pred i n p = <-trans i (suc i) n (<-self i) p

 ok-lim : ∀ l → HeadOK (inj l)
 ok-lim l y (_ ▸[ _ ] _) ()
 ok-lim (limF Γ) y ε p = ok-at (limF Γ) y p (⋆-wf (pe-ctx-wf w))
   where
   h = side-hok (limF Γ) y p
   w = fromT (P.checkCtx Γ) (snd (T∧ {y ==ℕ 0} h))
 ok-lim (legF Γ) g ε p with hok-inv Γ g (side-hok (legF Γ) g p)
 ... | K , e , ok , A , l = ok-at (legF Γ) g p (Leg.a′ g A l (cone-sub g rg))
   where
   hon = side-hon (legF Γ) g p
   open AtShape Γ K e ok hon
   rg : T ((nΓ + g) <ℕ P.len K)
   rg = <-pred (nΓ + g) (P.len K) (lk-range K (suc (nΓ + g)) l)

 -- Presupposition, once every head of the family is HeadOK.
 presup-from : (∀ b → HeadOK b) → PresupLaws
 presup-from ok = head-presup closed spec-head ok markRen markSub markVar

 tm-ty-from : PresupLaws → ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
 tm-ty-from pl = tm-ty closed laws markRen markSub markVar (λ {_} {k} _ _ → ⊥-elim k) pl

------------------------------------------------------------------------
-- lim and the cone alone.

open HS.Laws P.∅ (limSpec P.K shape) using (𝕊)
open Signature 𝕊 using (Ctx; Tm; Ty; varMark)
open import CaTTExp.Binder.VarMark 𝕊 (Tg.cattSide 𝕊) using (markRen; markSub; markVar)

open Gen (limSpec P.K shape) (λ l → l) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)
  varMark markRen markSub markVar public
import CaTTExp.Binder.Heads 𝕊 as Hd
open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
open Hd.Typed cattSide varMark using (HeadOK)
open import CaTTExp.Binder.TypingWith 𝕊 cattSide varMark using (_⊢tm_∶_; _⊢ty_)
open import CaTTExp.Binder.Presup 𝕊 cattSide varMark using (PresupLaws)

ok-all : ∀ b → HeadOK b
ok-all = ok-lim

lim-presup : PresupLaws
lim-presup = presup-from ok-all

-- Every term of CaTT with lim and the universal cone, over any shape,
-- has a well-formed type.
lim-tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
lim-tm-ty = tm-ty-from lim-presup
