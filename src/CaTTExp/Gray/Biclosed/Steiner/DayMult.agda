------------------------------------------------------------------------
-- The Day multicategory of presheaves on codes (S4 of the 𝔖̂ instance,
-- notes/gray-model-formal-plan.md), for any interpretation ⟦_⟧ of
-- formulas as presheaves.
--
-- An argument is a formula with an element of its presheaf (`Uni`). A
-- value is a profile Fs ▸ Z with a family
--     raw : (codes K₁ … Kₙ) (arguments u₁ … uₙ) → ⟦Z⟧
-- that, on arguments with uᵢ at Kᵢ (`AtL`), lands at K₁ ++ … ++ Kₙ
-- (`vAt`), respects ∼ (`vcong`) and is natural in every Kᵢ (`vnat`):
--     raw Ks′ (h₁ u₁, …, hₙ uₙ) ∼ (h₁ ⊗ … ⊗ hₙ)^* (raw Ks us).
-- These are the multimaps (⟦F₁⟧, …, ⟦Fₙ⟧ ▸ ⟦Z⟧) of Day convolution.
-- Values are typed by construction; ≈ compares raw families on
-- arguments that are At, with the same profile.
--
-- Composition `pc f i g` plugs g into slot i when the slot's formula is
-- g's output, and is f otherwise.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.DayMult (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps using (length; take; lookup)
open import CaTTExp.Gray.Biclosed.ListLemmas using (drop; length-++)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC)
open import CaTTExp.Gray.Biclosed.Steiner.Psh nmFB

uip : ∀ {A : Set} {a b : A} (p q : a ≡ b) → p ≡ q
uip refl refl = refl

------------------------------------------------------------------------
-- Decidable equality of formulas, as a Maybe.

decFm-go : ∀ {A B : Fm} (b : Bool) → (T b → A ≡ B) → Maybe (A ≡ B)
decFm-go true  s = just (s tt)
decFm-go false s = nothing

decFm : (A B : Fm) → Maybe (A ≡ B)
decFm A B = decFm-go (eqFm A B) (eqFm-sound A B)

decFm-refl : ∀ A → decFm A A ≡ just refl
decFm-refl A = go (eqFm A A) (eqFm-sound A A) (eqFm-refl A)
  where go : (b : Bool) (s : T b → A ≡ A) → T b → decFm-go b s ≡ just refl
        go true  s _ = cong just (uip (s tt) refl)
        go false s ()

module Interp (⟦_⟧ : Fm → Psh) where

  UF : Fm → Set
  UF A = U ⟦ A ⟧

  Uni : Set
  Uni = Σ Fm UF

  ----------------------------------------------------------------------
  -- Coercion of an argument to a formula.

  co′ : ∀ {A B} → Maybe (B ≡ A) → UF B → UF A
  co′ {A} (just e) x = subst UF e x
  co′ {A} nothing  x = def ⟦ A ⟧

  co : (A : Fm) → Uni → UF A
  co A (B , x) = co′ (decFm B A) x

  co-id : ∀ A x → co A (A , x) ≡ x
  co-id A x = cong (λ m → co′ m x) (decFm-refl A)

  ----------------------------------------------------------------------
  -- Equivalence and At on arguments.

  infix 4 _∼U_ _∼L_
  data _∼U_ : Uni → Uni → Set where
    ∼u : ∀ {A x y} → _∼_ ⟦ A ⟧ x y → (A , x) ∼U (A , y)

  ∼U-refl : ∀ {u} → u ∼U u
  ∼U-refl {A , x} = ∼u (∼-refl ⟦ A ⟧)

  ∼U-sym : ∀ {u v} → u ∼U v → v ∼U u
  ∼U-sym (∼u {A} e) = ∼u (∼-sym ⟦ A ⟧ e)

  ∼U-trans : ∀ {u v w} → u ∼U v → v ∼U w → u ∼U w
  ∼U-trans (∼u {A} e) (∼u e′) = ∼u (∼-trans ⟦ A ⟧ e e′)

  co-cong : ∀ A {u v} → u ∼U v → _∼_ ⟦ A ⟧ (co A u) (co A v)
  co-cong A (∼u {B} {x} {y} e) = go (decFm B A)
    where go : (m : Maybe (B ≡ A)) → _∼_ ⟦ A ⟧ (co′ m x) (co′ m y)
          go (just refl) = e
          go nothing     = ∼-refl ⟦ A ⟧

  AtU : Fm → Code → Uni → Set
  AtU A K (B , x) = (B ≡ A) × At ⟦ B ⟧ K x

  -- an argument At A is (A , its coercion)
  AtU-co : ∀ {A K u} → AtU A K u → u ≡ (A , co A u)
  AtU-co {A} {K} {.A , x} (refl , _) = cong (A ,_) (sym (co-id A x))

  AtU-At : ∀ {A K u} → AtU A K u → At ⟦ A ⟧ K (co A u)
  AtU-At {A} {K} {.A , x} (refl , a) = subst (At ⟦ A ⟧ K) (sym (co-id A x)) a

  AtU-∼ : ∀ {A K u v} → u ∼U v → AtU A K u → AtU A K v
  AtU-∼ (∼u {B} e) (p , a) = p , At-∼ ⟦ B ⟧ e a

  _∼L_ : List Uni → List Uni → Set
  []       ∼L []       = ⊤
  (u ∷ us) ∼L (v ∷ vs) = (u ∼U v) × (us ∼L vs)
  _        ∼L _        = ⊥

  ∼L-refl : ∀ us → us ∼L us
  ∼L-refl []       = tt
  ∼L-refl (u ∷ us) = ∼U-refl , ∼L-refl us

  ∼L-++ : ∀ {as bs cs ds} → as ∼L bs → cs ∼L ds → (as ++ cs) ∼L (bs ++ ds)
  ∼L-++ {[]}     {[]}     _        q = q
  ∼L-++ {a ∷ as} {b ∷ bs} (p , ps) q = p , ∼L-++ ps q

  AtL : List Fm → List Code → List Uni → Set
  AtL []       []       []       = ⊤
  AtL (A ∷ As) (K ∷ Ks) (u ∷ us) = AtU A K u × AtL As Ks us
  AtL _        _        _        = ⊥

  AtL-∼ : ∀ As Ks {us vs} → us ∼L vs → AtL As Ks us → AtL As Ks vs
  AtL-∼ []       []       {[]}     {[]}     _        _        = tt
  AtL-∼ (A ∷ As) (K ∷ Ks) {u ∷ us} {v ∷ vs} (p , ps) (a , as) = AtU-∼ p a , AtL-∼ As Ks ps as

  AtL-++ : ∀ {As Bs Ks Ls us vs} → AtL As Ks us → AtL Bs Ls vs → AtL (As ++ Bs) (Ks ++ Ls) (us ++ vs)
  AtL-++ {[]}     {Ks = []}     {us = []}     _        q = q
  AtL-++ {A ∷ As} {Ks = K ∷ Ks} {us = u ∷ us} (a , as) q = a , AtL-++ {As} {Ks = Ks} {us = us} as q

  AtL-lenK : ∀ As Ks us → AtL As Ks us → length Ks ≡ length As
  AtL-lenK []       []       []       _        = refl
  AtL-lenK (A ∷ As) (K ∷ Ks) (u ∷ us) (_ , as) = cong suc (AtL-lenK As Ks us as)

  AtL-lenU : ∀ As Ks us → AtL As Ks us → length us ≡ length As
  AtL-lenU []       []       []       _        = refl
  AtL-lenU (A ∷ As) (K ∷ Ks) (u ∷ us) (_ , as) = cong suc (AtL-lenU As Ks us as)

  -- splitting At-lists
  record Sp (As Bs : List Fm) (Ks : List Code) (us : List Uni) : Set where
    constructor sp
    field
      K₁ K₂ : List Code
      u₁ u₂ : List Uni
      eK : Ks ≡ K₁ ++ K₂
      eU : us ≡ u₁ ++ u₂
      a₁ : AtL As K₁ u₁
      a₂ : AtL Bs K₂ u₂

  AtL-split : ∀ As Bs Ks us → AtL (As ++ Bs) Ks us → Sp As Bs Ks us
  AtL-split []       Bs Ks       us       a        = sp [] Ks [] us refl refl tt a
  AtL-split (A ∷ As) Bs (K ∷ Ks) (u ∷ us) (x , xs) with AtL-split As Bs Ks us xs
  ... | sp K₁ K₂ u₁ u₂ refl refl a₁ a₂ = sp (K ∷ K₁) K₂ (u ∷ u₁) u₂ refl refl (x , a₁) a₂

  ----------------------------------------------------------------------
  -- Restriction of arguments.

  resU : ∀ {K L} → Map K L → Uni → Uni
  resU f (A , x) = A , res ⟦ A ⟧ f x

  resL : ∀ {Ks′ Ks} → Maps Ks′ Ks → List Uni → List Uni
  resL []       us       = us
  resL (h ∷ hs) []       = []
  resL (h ∷ hs) (u ∷ us) = resU h u ∷ resL hs us

  AtL-res : ∀ As {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL As Ks us → AtL As Ks′ (resL hs us)
  AtL-res []       []       []       _              = tt
  AtL-res (A ∷ As) (h ∷ hs) (u ∷ us) ((refl , a) , as) = (refl , At-res ⟦ A ⟧ h a) , AtL-res As hs us as

  resL-++ : ∀ {Ks′ Ks Ls′ Ls} (hs : Maps Ks′ Ks) (gs : Maps Ls′ Ls) us vs →
            length us ≡ length Ks → resL (hs ++ᵐ gs) (us ++ vs) ≡ resL hs us ++ resL gs vs
  resL-++ []       gs []       vs _ = refl
  resL-++ (h ∷ hs) gs (u ∷ us) vs e = cong (resU h u ∷_) (resL-++ hs gs us vs (suc-inj e))
    where suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
          suc-inj refl = refl

  -- splitting lists of maps
  record SpM {Ks′ : List Code} (A B : List Code) (hs : Maps Ks′ (A ++ B)) : Set where
    constructor spm
    field
      A′ B′ : List Code
      eK′ : Ks′ ≡ A′ ++ B′
      h₁ : Maps A′ A
      h₂ : Maps B′ B

  Maps-split : ∀ A B {Ks′} (hs : Maps Ks′ (A ++ B)) →
               Σ (List Code) λ A′ → Σ (List Code) λ B′ → Σ (Maps A′ A) λ h₁ → Σ (Maps B′ B) λ h₂ →
               Σ (Ks′ ≡ A′ ++ B′) λ e → subst (λ X → Maps X (A ++ B)) e hs ≡ (h₁ ++ᵐ h₂)
  Maps-split []      B hs       = [] , _ , [] , hs , refl , refl
  Maps-split (K ∷ A) B (h ∷ hs) with Maps-split A B hs
  ... | A′ , B′ , h₁ , h₂ , refl , refl = _ ∷ A′ , B′ , h ∷ h₁ , h₂ , refl , refl

  ----------------------------------------------------------------------
  -- Values.

  record Ok (prof : MTy) (raw : List Code → List Uni → UF (out prof)) : Set where
    constructor ok
    field
      vAt   : ∀ Ks us → AtL (ins prof) Ks us → At ⟦ out prof ⟧ (concat Ks) (raw Ks us)
      vcong : ∀ Ks us vs → AtL (ins prof) Ks us → AtL (ins prof) Ks vs → us ∼L vs →
              _∼_ ⟦ out prof ⟧ (raw Ks us) (raw Ks vs)
      vnat  : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL (ins prof) Ks us →
              _∼_ ⟦ out prof ⟧ (raw Ks′ (resL hs us)) (res ⟦ out prof ⟧ (⊗s hs) (raw Ks us))
  open Ok public

  record Val : Set where
    constructor mk
    field
      prof : MTy
      raw  : List Code → List Uni → UF (out prof)
      vok  : Ok prof raw
  open Val public

  infix 4 _≈_ _∶_
  data _≈_ : Val → Val → Set where
    ≈c : ∀ {M r r′} {o : Ok M r} {o′ : Ok M r′} →
         (∀ Ks us → AtL (ins M) Ks us → _∼_ ⟦ out M ⟧ (r Ks us) (r′ Ks us)) →
         mk M r o ≈ mk M r′ o′

  _∶_ : Val → MTy → Set
  x ∶ M = prof x ≡ M

  ≈-refl : ∀ {x} → x ≈ x
  ≈-refl {mk M r o} = ≈c (λ Ks us _ → ∼-refl ⟦ out M ⟧)

  ≈-sym : ∀ {x y} → x ≈ y → y ≈ x
  ≈-sym (≈c {M} e) = ≈c (λ Ks us p → ∼-sym ⟦ out M ⟧ (e Ks us p))

  ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans (≈c {M} e) (≈c e′) = ≈c (λ Ks us p → ∼-trans ⟦ out M ⟧ (e Ks us p) (e′ Ks us p))

  ∶-≈ : ∀ {x y M} → x ≈ y → x ∶ M → y ∶ M
  ∶-≈ (≈c _) p = p

  ----------------------------------------------------------------------
  -- List lemmas.

  private
    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl

  take-++ : ∀ {A : Set} (as bs : List A) n → length as ≡ n → take n (as ++ bs) ≡ as
  take-++ []       bs zero    refl = refl
  take-++ (a ∷ as) bs (suc n) e    = cong (a ∷_) (take-++ as bs n (suc-inj e))

  drop-++ : ∀ {A : Set} (as bs : List A) n → length as ≡ n → drop n (as ++ bs) ≡ bs
  drop-++ []       bs zero    refl = refl
  drop-++ (a ∷ as) bs (suc n) e    = drop-++ as bs n (suc-inj e)

  cons-inj′ : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
  cons-inj′ refl = refl , refl

  app-inj : ∀ {A : Set} (as bs cs ds : List A) → length as ≡ length cs → as ++ bs ≡ cs ++ ds → (as ≡ cs) × (bs ≡ ds)
  app-inj []       bs []       ds _ e = refl , e
  app-inj (a ∷ as) bs (c ∷ cs) ds l e with cons-inj′ {x = a} {y = c} {xs = as ++ bs} {ys = cs ++ ds} e
  ... | refl , e′ with app-inj as bs cs ds (suc-inj l) e′
  ...   | refl , refl = refl , refl
  app-inj []       bs (c ∷ cs) ds () e
  app-inj (a ∷ as) bs []       ds () e

  resL-len : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → length us ≡ length Ks → length (resL hs us) ≡ length us
  resL-len []       []       _ = refl
  resL-len (h ∷ hs) (u ∷ us) e = cong suc (resL-len hs us (suc-inj e))

  Maps-lenˡ : ∀ {Ks′ Ks} → Maps Ks′ Ks → length Ks′ ≡ length Ks
  Maps-lenˡ []       = refl
  Maps-lenˡ (h ∷ hs) = cong suc (Maps-lenˡ hs)

  ∼L-split : ∀ as bs cs ds → length as ≡ length cs → (as ++ bs) ∼L (cs ++ ds) → (as ∼L cs) × (bs ∼L ds)
  ∼L-split []       bs []       ds _ e = tt , e
  ∼L-split (a ∷ as) bs (c ∷ cs) ds l (p , ps) =
    let r = ∼L-split as bs cs ds (suc-inj l) ps in (p , fst r) , snd r
  ∼L-split []       bs (c ∷ cs) ds () e
  ∼L-split (a ∷ as) bs []       ds () e

  ----------------------------------------------------------------------
  -- Slots.

  record Slot (Fs : List Fm) (i : Nat) (Y : Fm) : Set where
    constructor slot
    field
      sP sQ : List Fm
      eF : Fs ≡ sP ++ Y ∷ sQ
      eP : length sP ≡ i

  compat : ∀ Fs i Y → Maybe (Slot Fs i Y)
  compat []       i       Y = nothing
  compat (F ∷ Fs) zero    Y with decFm F Y
  ... | just e  = just (slot [] Fs (cong (_∷ Fs) e) refl)
  ... | nothing = nothing
  compat (F ∷ Fs) (suc i) Y with compat Fs i Y
  ... | just (slot P Q e l) = just (slot (F ∷ P) Q (cong (F ∷_) e) (cong suc l))
  ... | nothing             = nothing

  slot-unique : ∀ {Fs i Y} (s s′ : Slot Fs i Y) → s ≡ s′
  slot-unique (slot P Q e l) (slot P′ Q′ e′ l′)
    with app-inj P (_ ∷ Q) P′ (_ ∷ Q′) (trans l (sym l′)) (trans (sym e) e′)
  ... | refl , refl with uip e e′ | uip l l′
  ...   | refl | refl = refl

  compat-ok : ∀ P Y Q → Σ (Slot (P ++ Y ∷ Q) (length P) Y) (λ s → compat (P ++ Y ∷ Q) (length P) Y ≡ just s)
  compat-ok []      Y Q rewrite decFm-refl Y = _ , refl
  compat-ok (F ∷ P) Y Q with compat (P ++ Y ∷ Q) (length P) Y | compat-ok P Y Q
  ... | .(just s) | s , refl = _ , refl

  ----------------------------------------------------------------------
  -- Splitting an input along P ++ Xs ++ Q.

  record Sp3 (P Xs Q : List Fm) (Ks : List Code) (us : List Uni) : Set where
    constructor sp3
    field
      KP KX KQ : List Code
      uP uX uQ : List Uni
      eK : Ks ≡ KP ++ KX ++ KQ
      eU : us ≡ uP ++ uX ++ uQ
      aP : AtL P KP uP
      aX : AtL Xs KX uX
      aQ : AtL Q KQ uQ

  split3 : ∀ P Xs Q Ks us → AtL (P ++ Xs ++ Q) Ks us → Sp3 P Xs Q Ks us
  split3 P Xs Q Ks us a with AtL-split P (Xs ++ Q) Ks us a
  ... | sp KP R uP uR refl refl aP aR with AtL-split Xs Q R uR aR
  ...   | sp KX KQ uX uQ refl refl aX aQ = sp3 KP KX KQ uP uX uQ refl refl aP aX aQ

  -- two splits of the same codes agree
  split-K : ∀ {P Xs Q : List Fm} (KP KX KQ KP′ KX′ KQ′ : List Code) (uP uX uQ uP′ uX′ uQ′ : List Uni) →
            AtL P KP uP → AtL Xs KX uX → AtL P KP′ uP′ → AtL Xs KX′ uX′ →
            KP ++ KX ++ KQ ≡ KP′ ++ KX′ ++ KQ′ → (KP ≡ KP′) × (KX ≡ KX′) × (KQ ≡ KQ′)
  split-K {P} {Xs} KP KX KQ KP′ KX′ KQ′ uP uX uQ uP′ uX′ uQ′ aP aX aP′ aX′ e
    with app-inj KP (KX ++ KQ) KP′ (KX′ ++ KQ′) (trans (AtL-lenK P KP uP aP) (sym (AtL-lenK P KP′ uP′ aP′))) e
  ... | refl , e₂ with app-inj KX KQ KX′ KQ′ (trans (AtL-lenK Xs KX uX aX) (sym (AtL-lenK Xs KX′ uX′ aX′))) e₂
  ...   | refl , refl = refl , refl , refl

  ----------------------------------------------------------------------
  -- The composite of f and g at slot i.

  module PC {Mf : MTy} {rf : List Code → List Uni → UF (out Mf)} (of : Ok Mf rf)
            {Mg : MTy} {rg : List Code → List Uni → UF (out Mg)} (og : Ok Mg rg)
            (i : Nat) (s : Slot (ins Mf) i (out Mg)) where
    open Slot s
    n : Nat
    n = length (ins Mg)
    Y : Fm
    Y = out Mg
    Mc : MTy
    Mc = (sP ++ ins Mg ++ sQ) ▸ out Mf

    rc : List Code → List Uni → UF (out Mf)
    rc Ks us = rf (take i Ks ++ concat (take n (drop i Ks)) ∷ drop n (drop i Ks))
                  (take i us ++ (Y , rg (take n (drop i Ks)) (take n (drop i us))) ∷ drop n (drop i us))

    ev : ∀ KP KX KQ uP uX uQ → length KP ≡ i → length uP ≡ i → length KX ≡ n → length uX ≡ n →
         rc (KP ++ KX ++ KQ) (uP ++ uX ++ uQ) ≡ rf (KP ++ concat KX ∷ KQ) (uP ++ (Y , rg KX uX) ∷ uQ)
    ev KP KX KQ uP uX uQ lKP luP lKX luX
      rewrite take-++ KP (KX ++ KQ) i lKP | drop-++ KP (KX ++ KQ) i lKP
            | take-++ uP (uX ++ uQ) i luP | drop-++ uP (uX ++ uQ) i luP
            | take-++ KX KQ n lKX | drop-++ KX KQ n lKX
            | take-++ uX uQ n luX | drop-++ uX uQ n luX = refl

    inF : ∀ {KP KX KQ uP uX uQ} → AtL sP KP uP → AtL (ins Mg) KX uX → AtL sQ KQ uQ →
          AtL (ins Mf) (KP ++ concat KX ∷ KQ) (uP ++ (Y , rg KX uX) ∷ uQ)
    inF {KP} {KX} {KQ} {uP} {uX} {uQ} aP aX aQ =
      subst (λ Fs → AtL Fs (KP ++ concat KX ∷ KQ) (uP ++ (Y , rg KX uX) ∷ uQ)) (sym eF)
            (AtL-++ {sP} {Y ∷ sQ} {KP} {concat KX ∷ KQ} {uP} aP ((refl , vAt og KX uX aX) , aQ))

    private
      lens : ∀ {KP KX uP uX} → AtL sP KP uP → AtL (ins Mg) KX uX →
             (length KP ≡ i) × (length uP ≡ i) × (length KX ≡ n) × (length uX ≡ n)
      lens {KP} {KX} {uP} {uX} aP aX =
        trans (AtL-lenK sP KP uP aP) eP , trans (AtL-lenU sP KP uP aP) eP ,
        AtL-lenK (ins Mg) KX uX aX , AtL-lenU (ins Mg) KX uX aX

    evA : ∀ {KP KX KQ uP uX uQ} → AtL sP KP uP → AtL (ins Mg) KX uX →
          rc (KP ++ KX ++ KQ) (uP ++ uX ++ uQ) ≡ rf (KP ++ concat KX ∷ KQ) (uP ++ (Y , rg KX uX) ∷ uQ)
    evA {KP} {KX} {KQ} {uP} {uX} {uQ} aP aX =
      let l = lens aP aX in ev KP KX KQ uP uX uQ (fst l) (fst (snd l)) (fst (snd (snd l))) (snd (snd (snd l)))

    cAt : ∀ Ks us → AtL (ins Mc) Ks us → At ⟦ out Mf ⟧ (concat Ks) (rc Ks us)
    cAt Ks us a with split3 sP (ins Mg) sQ Ks us a
    ... | sp3 KP KX KQ uP uX uQ refl refl aP aX aQ =
      subst (At ⟦ out Mf ⟧ (concat (KP ++ KX ++ KQ))) (sym (evA {KQ = KQ} {uQ = uQ} aP aX))
            (At-≡ ⟦ out Mf ⟧ (concat-flat KP KX KQ) (vAt of _ _ (inF aP aX aQ)))

    ccong : ∀ Ks us vs → AtL (ins Mc) Ks us → AtL (ins Mc) Ks vs → us ∼L vs →
            _∼_ ⟦ out Mf ⟧ (rc Ks us) (rc Ks vs)
    ccong Ks us vs a b e with split3 sP (ins Mg) sQ Ks us a
    ... | sp3 KP KX KQ uP uX uQ refl refl aP aX aQ with split3 sP (ins Mg) sQ (KP ++ KX ++ KQ) vs b
    ...   | sp3 KP′ KX′ KQ′ vP vX vQ eK′ refl bP bX bQ
            with split-K {sP} {ins Mg} {sQ} KP KX KQ KP′ KX′ KQ′ uP uX uQ vP vX vQ aP aX bP bX eK′
    ...     | refl , refl , refl =
      let lu = lens aP aX ; lv = lens bP bX
          e₁ = ∼L-split uP (uX ++ uQ) vP (vX ++ vQ) (trans (fst (snd lu)) (sym (fst (snd lv)))) e
          e₂ = ∼L-split uX uQ vX vQ (trans (snd (snd (snd lu))) (sym (snd (snd (snd lv))))) (snd e₁)
      in subst₂′ (_∼_ ⟦ out Mf ⟧) (sym (evA {KQ = KQ} {uQ = uQ} aP aX)) (sym (evA {KQ = KQ} {uQ = vQ} bP bX))
           (vcong of _ _ _ (inF aP aX aQ) (inF bP bX bQ)
              (∼L-++ {uP} {vP} (fst e₁) ((∼u (vcong og KX uX vX aX bX (fst e₂))) , snd e₂)))
      where
        subst₂′ : ∀ {A : Set} (R : A → A → Set) {a a′ b b′} → a ≡ a′ → b ≡ b′ → R a b → R a′ b′
        subst₂′ R refl refl r = r
