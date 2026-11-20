------------------------------------------------------------------------
-- Derived facts in a model of the biclosed kernel (Model.agda):
-- planar composition as iterated one-place composition, how a
-- one-place composition commutes past it, and cells with their faces
-- and degeneracies.  No postulates.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Gray.Biclosed.ModelFacts (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.Gray.Biclosed.ListLemmas
open Model 𝔐

------------------------------------------------------------------------
-- Reasoning

infixr 2 _≈⟨_⟩_
infix  3 _∎

_≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y ≈ z → x ≈ z
x ≈⟨ p ⟩ q = ≈-trans p q

_∎ : ∀ x → x ≈ x
x ∎ = ≈-refl

≡→≈ : ∀ {x y} → x ≡ y → x ≈ y
≡→≈ refl = ≈-refl

-- typing along an equality of types
retype : ∀ {x M N} → x ∶ M → M ≡ N → x ∶ N
retype p refl = p

-- one-place composition at a position given up to equality
pc-at : ∀ f {i j} g → i ≡ j → pc f i g ≈ pc f j g
pc-at f g refl = ≈-refl

T-pc′ : ∀ {f g Ys P Y Q Z Xs i} → f ∶ (Ys ▸ Z) → Ys ≡ P ++ Y ∷ Q → g ∶ (Xs ▸ Y) →
        i ≡ length P → pc f i g ∶ ((P ++ Xs ++ Q) ▸ Z)
T-pc′ {f} {g} pf refl pg refl = T-pc pf pg

------------------------------------------------------------------------
-- Typed argument lists

data Args : List V → List MTy → Set where
  []  : Args [] []
  _∷_ : ∀ {g gs M Ms} → g ∶ M → Args gs Ms → Args (g ∷ gs) (M ∷ Ms)

Args-++ : ∀ {gs hs Ms Ns} → Args gs Ms → Args hs Ns → Args (gs ++ hs) (Ms ++ Ns)
Args-++ []       q = q
Args-++ (p ∷ ps) q = p ∷ Args-++ ps q

------------------------------------------------------------------------
-- Planar composition: f ∘ (g₀, …, gₖ₋₁), composing from the right so
-- that the earlier positions do not move

cmpFrom : V → Nat → List V → V
cmpFrom f i []       = f
cmpFrom f i (g ∷ gs) = pc (cmpFrom f (suc i) gs) i g

cmp : V → List V → V
cmp f gs = cmpFrom f 0 gs

T-cmpFrom : ∀ {F P R Z gs Ms i} → F ∶ ((P ++ map out Ms ++ R) ▸ Z) → Args gs Ms →
            length P ≡ i → cmpFrom F i gs ∶ ((P ++ concatIns Ms ++ R) ▸ Z)
T-cmpFrom pF [] refl = pF
T-cmpFrom {F} {P} {R} {Z} {g ∷ gs} {N ∷ Ns} pF (pg ∷ ps) refl =
  retype (T-pc {P = P} {Y = out N} {Q = concatIns Ns ++ R}
            (retype pG (cong (_▸ Z) (sym (snoc-hinge P (out N) (concatIns Ns ++ R))))) pg)
         (cong (λ L → (P ++ L) ▸ Z) (sym (++-assoc (ins N) (concatIns Ns) R)))
  where
  pG : cmpFrom F (suc (length P)) gs ∶ (((P ++ out N ∷ []) ++ concatIns Ns ++ R) ▸ Z)
  pG = T-cmpFrom {P = P ++ out N ∷ []}
         (retype pF (cong (_▸ Z) (snoc-hinge P (out N) (map out Ns ++ R)))) ps (length-snoc P (out N))

cmpFrom-cong : ∀ {F F′} i gs → F ≈ F′ → cmpFrom F i gs ≈ cmpFrom F′ i gs
cmpFrom-cong i []       p = p
cmpFrom-cong i (g ∷ gs) p = pc-cong i (cmpFrom-cong (suc i) gs p) ≈-refl

cmpFrom-++ : ∀ F i gs hs → cmpFrom F i (gs ++ hs) ≡ cmpFrom (cmpFrom F (i + length gs) hs) i gs
cmpFrom-++ F i []       hs = cong (λ k → cmpFrom F k hs) (sym (+-zero i))
cmpFrom-++ F i (g ∷ gs) hs =
  cong (λ G → pc G i g)
    (trans (cmpFrom-++ F (suc i) gs hs)
           (cong (λ k → cmpFrom (cmpFrom F k hs) (suc i) gs) (sym (+-suc i (length gs)))))

------------------------------------------------------------------------
-- A one-place composition to the right of all arguments
--   (F ∘ (gs at P)) ∘_{P + |gs ins| + M} h  ≈  (F ∘_{P + |gs| + M} h) ∘ (gs at P)

past-right : ∀ {F P M W Q Z gs Ms h Ws i} →
  F ∶ ((P ++ map out Ms ++ M ++ W ∷ Q) ▸ Z) → Args gs Ms → h ∶ (Ws ▸ W) → length P ≡ i →
  pc (cmpFrom F i gs) (i + sumIns Ms + length M) h
    ≈ cmpFrom (pc F (i + length Ms + length M) h) i gs
past-right pF [] ph refl = ≈-refl
past-right {F} {P} {M} {W} {Q} {Z} {g ∷ gs} {N ∷ Ns} {h} {Ws} pF (pg ∷ ps) ph refl =
  pc (pc G i g) (i + sumIns (N ∷ Ns) + d) h
    ≈⟨ pc-at (pc G i g) h pos₁ ⟩
  pc (pc G i g) (i + b + length K) h
    ≈⟨ par {P = P} {Y = out N} {M = K} {W = W} {Q = Q} pG pg ph ⟩
  pc (pc G (i + suc (length K)) h) i g
    ≈⟨ pc-cong i (≈-trans (pc-at G h pos₂) ih) ≈-refl ⟩
  pc (cmpFrom (pc F (suc i + length Ns + d) h) (suc i) gs) i g
    ≈⟨ pc-cong i (≡→≈ (cong (λ k → cmpFrom (pc F k h) (suc i) gs) pos₃)) ≈-refl ⟩
  cmpFrom (pc F (i + length (N ∷ Ns) + d) h) i (g ∷ gs) ∎
  where
  i = length P
  b = length (ins N)
  c = sumIns Ns
  d = length M
  K = concatIns Ns ++ M
  P′ = P ++ out N ∷ []
  G = cmpFrom F (suc i) gs
  pF′ : F ∶ ((P′ ++ map out Ns ++ M ++ W ∷ Q) ▸ Z)
  pF′ = retype pF (cong (_▸ Z) (snoc-hinge P (out N) (map out Ns ++ M ++ W ∷ Q)))
  pG : G ∶ ((P ++ out N ∷ K ++ W ∷ Q) ▸ Z)
  pG = retype (T-cmpFrom {P = P′} {R = M ++ W ∷ Q} pF′ ps (length-snoc P (out N)))
         (cong (_▸ Z) (trans (sym (snoc-hinge P (out N) (concatIns Ns ++ M ++ W ∷ Q)))
                             (cong (λ L → P ++ out N ∷ L) (sym (++-assoc (concatIns Ns) M (W ∷ Q))))))
  pos₁ : i + sumIns (N ∷ Ns) + d ≡ i + b + length K
  pos₁ = trans (cong (λ x → i + x + d) (length-++ (ins N) (concatIns Ns)))
         (trans (+-assoc i (b + c) d)
         (trans (cong (i +_) (+-assoc b c d))
         (trans (sym (+-assoc i b (c + d)))
                (cong (i + b +_) (sym (length-++ (concatIns Ns) M))))))
  pos₂ : i + suc (length K) ≡ suc i + c + d
  pos₂ = trans (+-suc i (length K))
         (cong suc (trans (cong (i +_) (length-++ (concatIns Ns) M)) (sym (+-assoc i c d))))
  pos₃ : suc i + length Ns + d ≡ i + suc (length Ns) + d
  pos₃ = cong (_+ d) (sym (+-suc i (length Ns)))
  ih : pc G (suc i + c + d) h ≈ cmpFrom (pc F (suc i + length Ns + d) h) (suc i) gs
  ih = past-right {P = P′} {M = M} {W = W} {Q = Q} pF′ ps ph (length-snoc P (out N))

------------------------------------------------------------------------
-- A one-place composition to the left of all arguments
--   (F ∘ (gs at P,W,M)) ∘_P h  ≈  (F ∘_P h) ∘ (gs at P,Ws,M)

past-left : ∀ {F P W M Q Z gs Ms h Ws i} →
  F ∶ ((P ++ W ∷ M ++ map out Ms ++ Q) ▸ Z) → Args gs Ms → h ∶ (Ws ▸ W) → length P ≡ i →
  pc (cmpFrom F (i + suc (length M)) gs) i h
    ≈ cmpFrom (pc F i h) (i + length Ws + length M) gs
past-left pF [] ph refl = ≈-refl
past-left {F} {P} {W} {M} {Q} {Z} {g ∷ gs} {N ∷ Ns} {h} {Ws} pF (pg ∷ ps) ph refl =
  pc (pc G j g) i h
    ≈⟨ ≈-sym (par {P = P} {Y = W} {M = M} {W = out N} {Q = concatIns Ns ++ Q} pG ph pg) ⟩
  pc (pc G i h) (i + length Ws + length M) g
    ≈⟨ pc-cong (i + length Ws + length M)
         (≈-trans (pc-cong i (≡→≈ (cong (λ k → cmpFrom F k gs) pos₁)) ≈-refl) ih) ≈-refl ⟩
  pc (cmpFrom (pc F i h) (i + length Ws + length M′) gs) (i + length Ws + length M) g
    ≈⟨ pc-cong (i + length Ws + length M)
         (≡→≈ (cong (λ k → cmpFrom (pc F i h) k gs) pos₂)) ≈-refl ⟩
  cmpFrom (pc F i h) (i + length Ws + length M) (g ∷ gs) ∎
  where
  i = length P
  j = i + suc (length M)
  y = out N
  M′ = M ++ y ∷ []
  G = cmpFrom F (suc j) gs
  pF′ : F ∶ ((P ++ W ∷ M′ ++ map out Ns ++ Q) ▸ Z)
  pF′ = retype pF (cong (λ L → (P ++ W ∷ L) ▸ Z) (sym (++-assoc M (y ∷ []) (map out Ns ++ Q))))
  shuffle : ∀ R → (P ++ W ∷ M′) ++ R ≡ P ++ W ∷ M ++ y ∷ R
  shuffle R = trans (++-assoc P (W ∷ M′) R) (cong (λ L → P ++ W ∷ L) (++-assoc M (y ∷ []) R))
  lenP′ : length (P ++ W ∷ M′) ≡ suc j
  lenP′ = trans (length-++ P (W ∷ M′))
          (trans (cong (λ k → i + suc k) (length-snoc M y)) (+-suc i (suc (length M))))
  pG : G ∶ ((P ++ W ∷ M ++ y ∷ concatIns Ns ++ Q) ▸ Z)
  pG = retype (T-cmpFrom {P = P ++ W ∷ M′} {R = Q}
                 (retype pF (cong (_▸ Z) (sym (shuffle (map out Ns ++ Q))))) ps lenP′)
              (cong (_▸ Z) (shuffle (concatIns Ns ++ Q)))
  pos₁ : suc j ≡ i + suc (length M′)
  pos₁ = sym (trans (cong (λ k → i + suc k) (length-snoc M y)) (+-suc i (suc (length M))))
  pos₂ : i + length Ws + length M′ ≡ suc (i + length Ws + length M)
  pos₂ = trans (cong (i + length Ws +_) (length-snoc M y)) (+-suc (i + length Ws) (length M))
  ih : pc (cmpFrom F (i + suc (length M′)) gs) i h
         ≈ cmpFrom (pc F i h) (i + length Ws + length M′) gs
  ih = past-left {P = P} {W = W} {M = M′} {Q = Q} pF′ ps ph refl

------------------------------------------------------------------------
-- A one-place composition into an argument
--   (F ∘ (gs₁, x, gs₂)) ∘_{P + |gs₁ ins| + |Pre|} h  ≈  F ∘ (gs₁, x ∘_{|Pre|} h, gs₂)

face-arg : ∀ {F P Q Z gs₁ Ms₁ x Pre X Post Y gs₂ Ms₂ h Ws i} →
  F ∶ ((P ++ map out Ms₁ ++ Y ∷ map out Ms₂ ++ Q) ▸ Z) → Args gs₁ Ms₁ →
  x ∶ ((Pre ++ X ∷ Post) ▸ Y) → Args gs₂ Ms₂ → h ∶ (Ws ▸ X) → length P ≡ i →
  pc (cmpFrom F i (gs₁ ++ x ∷ gs₂)) (i + sumIns Ms₁ + length Pre) h
    ≈ cmpFrom F i (gs₁ ++ pc x (length Pre) h ∷ gs₂)
face-arg {F} {P} {Q} {Z} {[]} {[]} {x} {Pre} {X} {Post} {Y} {gs₂} {Ms₂} {h} pF [] px ps₂ ph refl =
  pc (pc G i x) (i + 0 + length Pre) h
    ≈⟨ pc-at (pc G i x) h (cong (_+ length Pre) (+-zero i)) ⟩
  pc (pc G i x) (i + length Pre) h
    ≈⟨ seq {P = P} {Y = Y} {Q = concatIns Ms₂ ++ Q} {P′ = Pre} pG px ph ⟩
  pc G i (pc x (length Pre) h) ∎
  where
  i = length P
  G = cmpFrom F (suc i) gs₂
  pG : G ∶ ((P ++ Y ∷ concatIns Ms₂ ++ Q) ▸ Z)
  pG = retype (T-cmpFrom {P = P ++ Y ∷ []} {R = Q}
                 (retype pF (cong (_▸ Z) (snoc-hinge P Y (map out Ms₂ ++ Q)))) ps₂ (length-snoc P Y))
              (cong (_▸ Z) (sym (snoc-hinge P Y (concatIns Ms₂ ++ Q))))
face-arg {F} {P} {Q} {Z} {g ∷ gs₁} {N ∷ Ns} {x} {Pre} {X} {Post} {Y} {gs₂} {Ms₂} {h} {Ws}
         pF (pg ∷ ps) px ps₂ ph refl =
  pc (pc G i g) (i + sumIns (N ∷ Ns) + length Pre) h
    ≈⟨ pc-at (pc G i g) h pos₁ ⟩
  pc (pc G i g) (i + b + length K) h
    ≈⟨ par {P = P} {Y = out N} {M = K} {W = X} {Q = Post ++ concatIns Ms₂ ++ Q} pG pg ph ⟩
  pc (pc G (i + suc (length K)) h) i g
    ≈⟨ pc-cong i (≈-trans (pc-at G h pos₂) ih) ≈-refl ⟩
  cmpFrom F i (g ∷ gs₁ ++ pc x (length Pre) h ∷ gs₂) ∎
  where
  i = length P
  b = length (ins N)
  c = sumIns Ns
  d = length Pre
  K = concatIns Ns ++ Pre
  P′ = P ++ out N ∷ []
  Mx = (Pre ++ X ∷ Post) ▸ Y
  G = cmpFrom F (suc i) (gs₁ ++ x ∷ gs₂)
  pF′ : F ∶ ((P′ ++ map out Ns ++ Y ∷ map out Ms₂ ++ Q) ▸ Z)
  pF′ = retype pF (cong (_▸ Z) (snoc-hinge P (out N) (map out Ns ++ Y ∷ map out Ms₂ ++ Q)))
  E1 : map out (Ns ++ Mx ∷ Ms₂) ++ Q ≡ map out Ns ++ Y ∷ map out Ms₂ ++ Q
  E1 = trans (cong (_++ Q) (map-++ out Ns (Mx ∷ Ms₂))) (++-assoc (map out Ns) (Y ∷ map out Ms₂) Q)
  E2 : concatIns (Ns ++ Mx ∷ Ms₂) ++ Q ≡ K ++ X ∷ Post ++ concatIns Ms₂ ++ Q
  E2 = trans (cong (_++ Q) (concatIns-++ Ns (Mx ∷ Ms₂)))
       (trans (++-assoc (concatIns Ns) ((Pre ++ X ∷ Post) ++ concatIns Ms₂) Q)
       (trans (cong (concatIns Ns ++_) (++-assoc (Pre ++ X ∷ Post) (concatIns Ms₂) Q))
       (trans (cong (concatIns Ns ++_) (++-assoc Pre (X ∷ Post) (concatIns Ms₂ ++ Q)))
              (sym (++-assoc (concatIns Ns) Pre (X ∷ Post ++ concatIns Ms₂ ++ Q))))))
  pG : G ∶ ((P ++ out N ∷ K ++ X ∷ Post ++ concatIns Ms₂ ++ Q) ▸ Z)
  pG = retype (T-cmpFrom {P = P′} {R = Q} {Ms = Ns ++ Mx ∷ Ms₂}
                 (retype pF′ (cong (λ L → (P′ ++ L) ▸ Z) (sym E1)))
                 (Args-++ ps (px ∷ ps₂)) (length-snoc P (out N)))
              (cong (_▸ Z) (trans (sym (snoc-hinge P (out N) _)) (cong (λ L → P ++ out N ∷ L) E2)))
  pos₁ : i + sumIns (N ∷ Ns) + d ≡ i + b + length K
  pos₁ = trans (cong (λ z → i + z + d) (length-++ (ins N) (concatIns Ns)))
         (trans (+-assoc i (b + c) d)
         (trans (cong (i +_) (+-assoc b c d))
         (trans (sym (+-assoc i b (c + d)))
                (cong (i + b +_) (sym (length-++ (concatIns Ns) Pre))))))
  pos₂ : i + suc (length K) ≡ suc i + c + d
  pos₂ = trans (+-suc i (length K))
         (cong suc (trans (cong (i +_) (length-++ (concatIns Ns) Pre)) (sym (+-assoc i c d))))
  ih : pc G (suc i + c + d) h ≈ cmpFrom F (suc i) (gs₁ ++ pc x (length Pre) h ∷ gs₂)
  ih = face-arg {P = P′} pF′ ps px ps₂ ph (length-snoc P (out N))

Args-length : ∀ {gs Ms} → Args gs Ms → length gs ≡ length Ms
Args-length []       = refl
Args-length (_ ∷ ps) = cong suc (Args-length ps)

length-map-out : ∀ {gs Ms} → Args gs Ms → length (map out Ms) ≡ length gs
length-map-out {gs} {Ms} ps = trans (length-map out Ms) (sym (Args-length ps))

------------------------------------------------------------------------
-- Whiskering: a cell F with its time slot (dsrc k) after the inputs of
-- vs₁, composed with the operations vs₁, vs₂ on either side of it

whS : Nat → V → List V → List V → V
whS k F vs₁ vs₂ = cmpFrom (cmpFrom F (length vs₁ + length (dsrc k)) vs₂) 0 vs₁

T-whS : ∀ {F k Ms₁ Ms₂ vs₁ vs₂ Z} →
  F ∶ ((map out Ms₁ ++ dsrc k ++ map out Ms₂) ▸ Z) → Args vs₁ Ms₁ → Args vs₂ Ms₂ →
  whS k F vs₁ vs₂ ∶ ((concatIns Ms₁ ++ dsrc k ++ concatIns Ms₂) ▸ Z)
T-whS {F} {k} {Ms₁} {Ms₂} {vs₁} {vs₂} {Z} pF p₁ p₂ =
  retype (T-cmpFrom {P = []} {R = dsrc k ++ concatIns Ms₂} {Ms = Ms₁}
            (retype pInner (cong (_▸ Z) (trans (cong ((map out Ms₁ ++ dsrc k) ++_) (++-[] (concatIns Ms₂)))
                                               (++-assoc (map out Ms₁) (dsrc k) (concatIns Ms₂)))))
            p₁ refl)
         refl
  where
  lenP : length (map out Ms₁ ++ dsrc k) ≡ length vs₁ + length (dsrc k)
  lenP = trans (length-++ (map out Ms₁) (dsrc k)) (cong (_+ length (dsrc k)) (length-map-out p₁))
  pInner : cmpFrom F (length vs₁ + length (dsrc k)) vs₂ ∶ (((map out Ms₁ ++ dsrc k) ++ concatIns Ms₂ ++ []) ▸ Z)
  pInner = T-cmpFrom {P = map out Ms₁ ++ dsrc k} {R = []}
             (retype pF (cong (_▸ Z) (trans (sym (++-assoc (map out Ms₁) (dsrc k) (map out Ms₂)))
                                           (cong ((map out Ms₁ ++ dsrc k) ++_) (sym (++-[] (map out Ms₂)))))))
             p₂ lenP

whS-0 : ∀ F vs₁ vs₂ → whS 0 F vs₁ vs₂ ≡ cmpFrom F 0 (vs₁ ++ vs₂)
whS-0 F vs₁ vs₂ = trans (cong (λ k → cmpFrom (cmpFrom F k vs₂) 0 vs₁) (+-zero (length vs₁)))
                        (sym (cmpFrom-++ F 0 vs₁ vs₂))

whS-cong : ∀ {F F′} k vs₁ vs₂ → F ≈ F′ → whS k F vs₁ vs₂ ≈ whS k F′ vs₁ vs₂
whS-cong k vs₁ vs₂ p = cmpFrom-cong 0 vs₁ (cmpFrom-cong _ vs₂ p)

-- the face of a whiskered cell is the whiskered face
face-whS : ∀ {F k Ms₁ Ms₂ vs₁ vs₂ Z} α →
  F ∶ ((map out Ms₁ ++ dsrc (suc k) ++ map out Ms₂) ▸ Z) → Args vs₁ Ms₁ → Args vs₂ Ms₂ →
  pc (whS (suc k) F vs₁ vs₂) (sumIns Ms₁) (δ α k)
    ≈ whS k (pc F (length vs₁) (δ α k)) vs₁ vs₂
face-whS {F} {k} {Ms₁} {Ms₂} {vs₁} {vs₂} {Z} α pF p₁ p₂ =
  pc (cmpFrom F′ 0 vs₁) (sumIns Ms₁) (δ α k)
    ≈⟨ pc-at (cmpFrom F′ 0 vs₁) (δ α k) (sym (+-zero (sumIns Ms₁))) ⟩
  pc (cmpFrom F′ 0 vs₁) (0 + sumIns Ms₁ + 0) (δ α k)
    ≈⟨ past-right {P = []} {M = []} {W = D (suc k)} {Q = concatIns Ms₂} pF′ p₁ (T-δ α k) refl ⟩
  cmpFrom (pc F′ (0 + length Ms₁ + 0) (δ α k)) 0 vs₁
    ≈⟨ cmpFrom-cong 0 vs₁ (≈-trans (pc-at F′ (δ α k) posL) inner) ⟩
  whS k (pc F (length vs₁) (δ α k)) vs₁ vs₂ ∎
  where
  F′ = cmpFrom F (length vs₁ + 1) vs₂
  pF′ : F′ ∶ (([] ++ map out Ms₁ ++ [] ++ D (suc k) ∷ concatIns Ms₂) ▸ Z)
  pF′ = retype (T-cmpFrom {P = map out Ms₁ ++ D (suc k) ∷ []} {R = []}
                  (retype pF (cong (_▸ Z) (trans (snoc-hinge (map out Ms₁) (D (suc k)) (map out Ms₂))
                       (cong ((map out Ms₁ ++ D (suc k) ∷ []) ++_) (sym (++-[] (map out Ms₂)))))))
                  p₂
                  (trans (length-snoc (map out Ms₁) (D (suc k)))
                         (trans (cong suc (length-map-out p₁)) (sym (+-one (length vs₁))))))
               (cong (_▸ Z) (trans (cong ((map out Ms₁ ++ D (suc k) ∷ []) ++_) (++-[] (concatIns Ms₂)))
                                   (sym (snoc-hinge (map out Ms₁) (D (suc k)) (concatIns Ms₂)))))
    where
    +-one : ∀ n → n + 1 ≡ suc n
    +-one zero    = refl
    +-one (suc n) = cong suc (+-one n)
  posL : 0 + length Ms₁ + 0 ≡ length vs₁
  posL = trans (+-zero (length Ms₁)) (sym (Args-length p₁))
  inner : pc F′ (length vs₁) (δ α k) ≈ cmpFrom (pc F (length vs₁) (δ α k)) (length vs₁ + length (dsrc k)) vs₂
  inner = ≈-trans
    (past-left {P = map out Ms₁} {W = D (suc k)} {M = []} {Q = []}
       (retype pF (cong (λ L → (map out Ms₁ ++ D (suc k) ∷ L) ▸ Z) (sym (++-[] (map out Ms₂)))))
       p₂ (T-δ α k) (length-map-out p₁))
    (≡→≈ (cong (λ n → cmpFrom (pc F (length vs₁) (δ α k)) n vs₂) (+-zero (length vs₁ + length (dsrc k)))))

------------------------------------------------------------------------
-- Composing with identities

cmp-ids : ∀ {F P L Q Z i} → F ∶ ((P ++ L ++ Q) ▸ Z) → length P ≡ i → cmpFrom F i (map idv L) ≈ F
cmp-ids {F} {P} {[]} pF refl = ≈-refl
cmp-ids {F} {P} {A ∷ L} {Q} {Z} pF refl =
  ≈-trans (pc-cong (length P)
             (cmp-ids {P = P ++ A ∷ []} {L = L} {Q = Q} (retype pF (cong (_▸ Z) (snoc-hinge P A (L ++ Q))))
                      (length-snoc P A))
             ≈-refl)
          (unit-r {P = P} {Y = A} {Q = L ++ Q} pF)

------------------------------------------------------------------------
-- Degenerate cells and their faces

degen : Nat → Nat → V → V
degen zero    g w = pc (unC cpt g w) g (σ 0)
degen (suc n) g w = pc w g (σ (suc n))

T-degen : ∀ {w n Pre Post Z g} → w ∶ ((Pre ++ dsrc n ++ Post) ▸ Z) → length Pre ≡ g →
          degen n g w ∶ ((Pre ++ D (suc n) ∷ Post) ▸ Z)
T-degen {w} {zero} {Pre} {Post} pw refl =
  T-pc {P = Pre} {Y = D 0} {Q = Post} (T-unC {P = Pre} {c = cpt} {Q = Post} pw) (T-σ 0)
T-degen {w} {suc n} {Pre} {Post} pw refl =
  T-pc {P = Pre} {Y = D (suc n)} {Q = Post} pw (T-σ (suc n))

face-degen : ∀ {w n Pre Post Z g} α → w ∶ ((Pre ++ dsrc n ++ Post) ▸ Z) → length Pre ≡ g →
             pc (degen n g w) g (δ α n) ≈ w
face-degen {w} {zero} {Pre} {Post} α pw refl =
  ≈-trans (pc-at (degen 0 (length Pre) w) (δ α 0) (sym (+-zero (length Pre))))
  (≈-trans (seq {P = Pre} {Y = D 0} {Q = Post} {P′ = []} {X = D 1} {Q′ = []}
              (T-unC {P = Pre} {c = cpt} {Q = Post} pw) (T-σ 0) (T-δ α 0))
  (≈-trans (pc-cong (length Pre) ≈-refl (σδ-0 α))
           (unC-r {P = Pre} {c = cpt} {Q = Post} pw)))
face-degen {w} {suc n} {Pre} {Post} α pw refl =
  ≈-trans (pc-at (degen (suc n) (length Pre) w) (δ α (suc n)) (sym (+-zero (length Pre))))
  (≈-trans (seq {P = Pre} {Y = D (suc n)} {Q = Post} {P′ = []} {X = D (suc (suc n))} {Q′ = []}
              pw (T-σ (suc n)) (T-δ α (suc n)))
  (≈-trans (pc-cong (length Pre) ≈-refl (σδ-suc α n))
           (unit-r {P = Pre} {Y = D (suc n)} {Q = Post} pw)))

------------------------------------------------------------------------
-- Congruence in one argument; arguments taken and dropped

cmpFrom-arg-cong : ∀ F i gs₁ {x x′} gs₂ → x ≈ x′ →
                   cmpFrom F i (gs₁ ++ x ∷ gs₂) ≈ cmpFrom F i (gs₁ ++ x′ ∷ gs₂)
cmpFrom-arg-cong F i []        gs₂ p = pc-cong i ≈-refl p
cmpFrom-arg-cong F i (g ∷ gs₁) gs₂ p = pc-cong i (cmpFrom-arg-cong F (suc i) gs₁ gs₂ p) ≈-refl

Args-take : ∀ n {gs Ms} → Args gs Ms → Args (take n gs) (take n Ms)
Args-take zero    ps       = []
Args-take (suc n) []       = []
Args-take (suc n) (p ∷ ps) = p ∷ Args-take n ps

Args-drop : ∀ n {gs Ms} → Args gs Ms → Args (drop n gs) (drop n Ms)
Args-drop zero    ps       = ps
Args-drop (suc n) []       = []
Args-drop (suc n) (p ∷ ps) = Args-drop n ps
