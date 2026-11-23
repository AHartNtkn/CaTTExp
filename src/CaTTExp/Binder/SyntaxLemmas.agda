------------------------------------------------------------------------
-- Lemmas on the raw syntax with binders: scoping, local closure,
-- extension, associativity and closedness of substitution, and the
-- commutation of opening with substitution.
------------------------------------------------------------------------
open import CaTTExp.Prelude

module CaTTExp.Binder.SyntaxLemmas (K : Set) (B : Set) where

open import CaTTExp.Binder.Syntax K B

------------------------------------------------------------------------
-- Booleans and arithmetic.

T∧ : ∀ {a b} → T (a ∧ b) → T a × T b
T∧ {true} p = tt , p

∧T : ∀ {a b} → T a → T b → T (a ∧ b)
∧T {true} _ q = q

≡→T : ∀ {b} → b ≡ true → T b
≡→T refl = tt

T→≡ : ∀ {b} → T b → b ≡ true
T→≡ {true} _ = refl

<-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
<-suc zero    (suc n) _ = tt
<-suc (suc i) (suc n) p = <-suc i n p

<→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
<→≢ zero    (suc n) _ = refl
<→≢ (suc i) (suc n) p = <→≢ i n p

<suc-≢ : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
<suc-≢ zero    zero    _ ()
<suc-≢ zero    (suc n) _ _ = tt
<suc-≢ (suc i) zero    p _ = ⊥-elim (no-<0 i p)
  where
  no-<0 : ∀ i → T (i <ℕ zero) → ⊥
  no-<0 _ ()
<suc-≢ (suc i) (suc n) p q = <suc-≢ i n p q

==→<suc : ∀ i n → (i ==ℕ n) ≡ true → T (i <ℕ suc n)
==→<suc zero    zero    _ = tt
==→<suc (suc i) (suc n) p = ==→<suc i n p
==→<suc zero    (suc n) ()
==→<suc (suc i) zero    ()

==→≡ : ∀ i n → (i ==ℕ n) ≡ true → i ≡ n
==→≡ i n p = ==ℕ-sound i n (≡→T p)

==-refl : ∀ n → (n ==ℕ n) ≡ true
==-refl zero    = refl
==-refl (suc n) = ==-refl n

<-self : ∀ n → T (n <ℕ suc n)
<-self zero    = tt
<-self (suc n) = <-self n

<-trans : ∀ i j k → T (i <ℕ j) → T (j <ℕ k) → T (i <ℕ k)
<-trans zero    (suc j) (suc k) _ _ = tt
<-trans (suc i) (suc j) (suc k) p q = <-trans i j k p q

<-+ : ∀ i n k → T (i <ℕ n) → T (i <ℕ (n + k))
<-+ zero    (suc n) k _ = tt
<-+ (suc i) (suc n) k p = <-+ i n k p

+-<suc : ∀ n k → T ((n + k) <ℕ (n + suc k))
+-<suc zero    k = <-self k
+-<suc (suc n) k = +-<suc n k

+-suc : ∀ n k → n + suc k ≡ suc (n + k)
+-suc zero    k = refl
+-suc (suc n) k = cong suc (+-suc n k)

+-zero : ∀ n → n + zero ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

------------------------------------------------------------------------
-- Lengths.

lenₛ-∘ : ∀ τ σ → lenₛ (τ ∘ σ) ≡ lenₛ τ
lenₛ-∘ ⟨⟩       σ = refl
lenₛ-∘ (τ ,ₛ t) σ = cong suc (lenₛ-∘ τ σ)

lenₛ-++ : ∀ σ τ → lenₛ (σ ++ₛ τ) ≡ lenₛ σ + lenₛ τ
lenₛ-++ σ ⟨⟩       = sym (+-zero (lenₛ σ))
lenₛ-++ σ (τ ,ₛ t) = trans (cong suc (lenₛ-++ σ τ)) (sym (+-suc (lenₛ σ) (lenₛ τ)))

len-⧺ : ∀ Γ Ξ → len (Γ ⧺ Ξ) ≡ len Γ + len Ξ
len-⧺ Γ ε       = sym (+-zero (len Γ))
len-⧺ Γ (Ξ ▸[ ms ] A) = trans (cong suc (len-⧺ Γ Ξ)) (sym (+-suc (len Γ) (len Ξ)))

len-tel[] : ∀ Δ σ → len (Δ [ σ ]tel) ≡ len Δ
len-tel[] ε       σ = refl
len-tel[] (Δ ▸[ ms ] A) σ = cong suc (len-tel[] Δ σ)

len-openTel : ∀ n Δ → len (openTel n Δ) ≡ len Δ
len-openTel n ε       = refl
len-openTel n (Δ ▸[ ms ] A) = cong suc (len-openTel n Δ)

lenₛ-fresh : ∀ n k → lenₛ (fresh n k) ≡ k
lenₛ-fresh n zero    = refl
lenₛ-fresh n (suc k) = cong suc (lenₛ-fresh n k)

------------------------------------------------------------------------
-- Scoping (Boolean, from CaTTExp.Binder.Syntax) is monotone.

mutual
  scTy-suc : ∀ {n} A → T (scTy? n A) → T (scTy? (suc n) A)
  scTy-suc ⋆           _ = tt
  scTy-suc {n} (arr A t u) p =
    let (a , q) = T∧ {scTy? n A} p ; (b , c) = T∧ {scTm? n t} q in
    ∧T (scTy-suc A a) (∧T (scTm-suc t b) (scTm-suc u c))

  scTm-suc : ∀ {n} t → T (scTm? n t) → T (scTm? (suc n) t)
  scTm-suc {n} (var i)       p = <-suc i n p
  scTm-suc (bvar _ _)        _ = tt
  scTm-suc (coh _ _ σ)       p = scSub-suc σ p
  scTm-suc (cst _)           _ = tt
  scTm-suc {n} (bnd _ _ Δ σ) p =
    let (a , b) = T∧ {scTel? n Δ} p in ∧T (scTel-suc Δ a) (scSub-suc σ b)

  scTel-suc : ∀ {n} Δ → T (scTel? n Δ) → T (scTel? (suc n) Δ)
  scTel-suc ε       _ = tt
  scTel-suc {n} (Δ ▸[ ms ] A) p =
    let (a , b) = T∧ {scTel? n Δ} p in ∧T (scTel-suc Δ a) (scTy-suc A b)

  scSub-suc : ∀ {n} σ → T (scSub? n σ) → T (scSub? (suc n) σ)
  scSub-suc ⟨⟩       _ = tt
  scSub-suc {n} (σ ,ₛ t) p =
    let (a , b) = T∧ {scSub? n σ} p in ∧T (scSub-suc σ a) (scTm-suc t b)

scTy-mono : ∀ n A → T (scTy? 0 A) → T (scTy? n A)
scTy-mono zero    A p = p
scTy-mono (suc n) A p = scTy-suc A (scTy-mono n A p)

scTy-+ : ∀ n k A → T (scTy? n A) → T (scTy? (n + k) A)
scTy-+ n zero    A p rewrite +-zero n = p
scTy-+ n (suc k) A p rewrite +-suc n k = scTy-suc A (scTy-+ n k A p)

------------------------------------------------------------------------
-- Local closure: every bound variable refers to a binder inside the
-- term (at depth d, bvar e j needs e < d).

LC : Sub → Set
LC σ = T (lcSub? 0 σ)

mutual
  lcTm-suc : ∀ {d} t → T (lcTm? d t) → T (lcTm? (suc d) t)
  lcTm-suc (var _)          _ = tt
  lcTm-suc {d} (bvar e _)   p = <-suc e d p
  lcTm-suc (coh _ _ σ)      p = lcSub-suc σ p
  lcTm-suc (cst _)          _ = tt
  lcTm-suc {d} (bnd _ _ Δ σ) p =
    let (a , b) = T∧ {lcTel? (suc d) Δ} p in ∧T (lcTel-suc Δ a) (lcSub-suc σ b)

  lcTy-suc : ∀ {d} A → T (lcTy? d A) → T (lcTy? (suc d) A)
  lcTy-suc ⋆ _ = tt
  lcTy-suc {d} (arr A t u) p =
    let (a , q) = T∧ {lcTy? d A} p ; (b , c) = T∧ {lcTm? d t} q in
    ∧T (lcTy-suc A a) (∧T (lcTm-suc t b) (lcTm-suc u c))

  lcTel-suc : ∀ {d} Δ → T (lcTel? d Δ) → T (lcTel? (suc d) Δ)
  lcTel-suc ε _ = tt
  lcTel-suc {d} (Δ ▸[ ms ] A) p =
    let (a , b) = T∧ {lcTel? d Δ} p in ∧T (lcTel-suc Δ a) (lcTy-suc A b)

  lcSub-suc : ∀ {d} σ → T (lcSub? d σ) → T (lcSub? (suc d) σ)
  lcSub-suc ⟨⟩ _ = tt
  lcSub-suc {d} (σ ,ₛ t) p =
    let (a , b) = T∧ {lcSub? d σ} p in ∧T (lcSub-suc σ a) (lcTm-suc t b)

lcTm-mono : ∀ d t → T (lcTm? 0 t) → T (lcTm? d t)
lcTm-mono zero    t p = p
lcTm-mono (suc d) t p = lcTm-suc t (lcTm-mono d t p)

lc-lookup : ∀ σ i → LC σ → T (lcTm? 0 (lookupₛ σ i))
lc-lookup ⟨⟩       i _ = tt
lc-lookup (σ ,ₛ t) i p with i ==ℕ lenₛ σ
... | true  = snd (T∧ {lcSub? 0 σ} p)
... | false = lc-lookup σ i (fst (T∧ {lcSub? 0 σ} p))

lc-++ : ∀ σ τ → LC σ → LC τ → LC (σ ++ₛ τ)
lc-++ σ ⟨⟩       p _ = p
lc-++ σ (τ ,ₛ t) p q = let (a , b) = T∧ {lcSub? 0 τ} q in ∧T (lc-++ σ τ p a) b

lc-fresh : ∀ n k → LC (fresh n k)
lc-fresh n zero    = tt
lc-fresh n (suc k) = ∧T (lc-fresh n k) tt

------------------------------------------------------------------------
-- Opening leaves locally closed syntax alone.

mutual
  opTy-lc : ∀ d ts A → T (lcTy? d A) → opTy d ts A ≡ A
  opTy-lc d ts ⋆ _ = refl
  opTy-lc d ts (arr A t u) p =
    let (a , q) = T∧ {lcTy? d A} p ; (b , c) = T∧ {lcTm? d t} q in
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (opTy-lc d ts A a) (cong₂ _,_ (opTm-lc d ts t b) (opTm-lc d ts u c))

  opTm-lc : ∀ d ts t → T (lcTm? d t) → opTm d ts t ≡ t
  opTm-lc d ts (var i) _ = refl
  opTm-lc d ts (bvar e j) p rewrite <→≢ e d p = refl
  opTm-lc d ts (coh Γ A σ) p = cong (coh Γ A) (opSub-lc d ts σ p)
  opTm-lc d ts (cst k) _ = refl
  opTm-lc d ts (bnd b y Δ σ) p =
    let (a , c) = T∧ {lcTel? (suc d) Δ} p in
    cong₂ (bnd b y) (opTel-lc (suc d) (shSub 0 ts) Δ a) (opSub-lc d ts σ c)

  opTel-lc : ∀ d ts Δ → T (lcTel? d Δ) → opTel d ts Δ ≡ Δ
  opTel-lc d ts ε _ = refl
  opTel-lc d ts (Δ ▸[ ms ] A) p =
    let (a , b) = T∧ {lcTel? d Δ} p in cong₂ (_▸[ ms ]_) (opTel-lc d ts Δ a) (opTy-lc d ts A b)

  opSub-lc : ∀ d ts σ → T (lcSub? d σ) → opSub d ts σ ≡ σ
  opSub-lc d ts ⟨⟩ _ = refl
  opSub-lc d ts (σ ,ₛ t) p =
    let (a , b) = T∧ {lcSub? d σ} p in cong₂ _,ₛ_ (opSub-lc d ts σ a) (opTm-lc d ts t b)

------------------------------------------------------------------------
-- Shifting leaves locally closed syntax alone, and commutes with
-- substitution by locally closed terms.

mutual
  shTy-lc : ∀ c A → T (lcTy? c A) → shTy c A ≡ A
  shTy-lc c ⋆ _ = refl
  shTy-lc c (arr A t u) p =
    let (a , q) = T∧ {lcTy? c A} p ; (b , d) = T∧ {lcTm? c t} q in
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (shTy-lc c A a) (cong₂ _,_ (shTm-lc c t b) (shTm-lc c u d))

  shTm-lc : ∀ c t → T (lcTm? c t) → shTm c t ≡ t
  shTm-lc c (var i) _ = refl
  shTm-lc c (bvar e j) p rewrite T→≡ p = refl
  shTm-lc c (coh Γ A σ) p = cong (coh Γ A) (shSub-lc c σ p)
  shTm-lc c (cst k) _ = refl
  shTm-lc c (bnd b y Δ σ) p =
    let (a , d) = T∧ {lcTel? (suc c) Δ} p in cong₂ (bnd b y) (shTel-lc (suc c) Δ a) (shSub-lc c σ d)

  shTel-lc : ∀ c Δ → T (lcTel? c Δ) → shTel c Δ ≡ Δ
  shTel-lc c ε _ = refl
  shTel-lc c (Δ ▸[ ms ] A) p = let (a , b) = T∧ {lcTel? c Δ} p in cong₂ (_▸[ ms ]_) (shTel-lc c Δ a) (shTy-lc c A b)

  shSub-lc : ∀ c σ → T (lcSub? c σ) → shSub c σ ≡ σ
  shSub-lc c ⟨⟩ _ = refl
  shSub-lc c (σ ,ₛ t) p = let (a , b) = T∧ {lcSub? c σ} p in cong₂ _,ₛ_ (shSub-lc c σ a) (shTm-lc c t b)

mutual
  sh-[]ty : ∀ c A σ → LC σ → (shTy c A) [ σ ]ty ≡ shTy c (A [ σ ]ty)
  sh-[]ty c ⋆ σ _ = refl
  sh-[]ty c (arr A t u) σ l =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (sh-[]ty c A σ l) (cong₂ _,_ (sh-[]tm c t σ l) (sh-[]tm c u σ l))

  sh-[]tm : ∀ c t σ → LC σ → (shTm c t) [ σ ]tm ≡ shTm c (t [ σ ]tm)
  sh-[]tm c (var i) σ l = sym (shTm-lc c (lookupₛ σ i) (lcTm-mono c (lookupₛ σ i) (lc-lookup σ i l)))
  sh-[]tm c (bvar e j) σ l with e <ℕ c
  ... | true  = refl
  ... | false = refl
  sh-[]tm c (coh Γ A τ) σ l = cong (coh Γ A) (sh-∘ c τ σ l)
  sh-[]tm c (cst k) σ l = refl
  sh-[]tm c (bnd b y Δ τ) σ l = cong₂ (bnd b y) (sh-[]tel (suc c) Δ σ l) (sh-∘ c τ σ l)

  sh-[]tel : ∀ c Δ σ → LC σ → (shTel c Δ) [ σ ]tel ≡ shTel c (Δ [ σ ]tel)
  sh-[]tel c ε σ _ = refl
  sh-[]tel c (Δ ▸[ ms ] A) σ l = cong₂ (_▸[ ms ]_) (sh-[]tel c Δ σ l) (sh-[]ty c A σ l)

  sh-∘ : ∀ c τ σ → LC σ → shSub c τ ∘ σ ≡ shSub c (τ ∘ σ)
  sh-∘ c ⟨⟩ σ _ = refl
  sh-∘ c (τ ,ₛ t) σ l = cong₂ _,ₛ_ (sh-∘ c τ σ l) (sh-[]tm c t σ l)

sh-fresh : ∀ c n k → shSub c (fresh n k) ≡ fresh n k
sh-fresh c n zero    = refl
sh-fresh c n (suc k) = cong (_,ₛ var (n + k)) (sh-fresh c n k)

mutual
  sc-shTm : ∀ {n} c t → T (scTm? n t) → T (scTm? n (shTm c t))
  sc-shTm c (var i) p = p
  sc-shTm c (bvar e j) _ with e <ℕ c
  ... | true  = tt
  ... | false = tt
  sc-shTm c (coh Γ A σ) p = sc-shSub c σ p
  sc-shTm c (cst k) _ = tt
  sc-shTm {n} c (bnd b y Δ σ) p =
    let (a , d) = T∧ {scTel? n Δ} p in ∧T (sc-shTel (suc c) Δ a) (sc-shSub c σ d)

  sc-shTy : ∀ {n} c A → T (scTy? n A) → T (scTy? n (shTy c A))
  sc-shTy c ⋆ _ = tt
  sc-shTy {n} c (arr A t u) p =
    let (a , q) = T∧ {scTy? n A} p ; (b , d) = T∧ {scTm? n t} q in
    ∧T (sc-shTy c A a) (∧T (sc-shTm c t b) (sc-shTm c u d))

  sc-shTel : ∀ {n} c Δ → T (scTel? n Δ) → T (scTel? n (shTel c Δ))
  sc-shTel c ε _ = tt
  sc-shTel {n} c (Δ ▸[ ms ] A) p = let (a , b) = T∧ {scTel? n Δ} p in ∧T (sc-shTel c Δ a) (sc-shTy c A b)

  sc-shSub : ∀ {n} c σ → T (scSub? n σ) → T (scSub? n (shSub c σ))
  sc-shSub c ⟨⟩ _ = tt
  sc-shSub {n} c (σ ,ₛ t) p = let (a , b) = T∧ {scSub? n σ} p in ∧T (sc-shSub c σ a) (sc-shTm c t b)

------------------------------------------------------------------------
-- Opening commutes with substitution by a locally closed σ.

pickOr-∘ : ∀ ts σ j t → (pickOr ts j t) [ σ ]tm ≡ pickOr (ts ∘ σ) j (t [ σ ]tm)
pickOr-∘ ⟨⟩        σ j t = refl
pickOr-∘ (ts ,ₛ s) σ j t rewrite lenₛ-∘ ts σ with j ==ℕ lenₛ ts
... | true  = refl
... | false = pickOr-∘ ts σ j t

mutual
  op-[]ty : ∀ d ts A σ → LC σ → (opTy d ts A) [ σ ]ty ≡ opTy d (ts ∘ σ) (A [ σ ]ty)
  op-[]ty d ts ⋆ σ _ = refl
  op-[]ty d ts (arr A t u) σ l =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (op-[]ty d ts A σ l) (cong₂ _,_ (op-[]tm d ts t σ l) (op-[]tm d ts u σ l))

  op-[]tm : ∀ d ts t σ → LC σ → (opTm d ts t) [ σ ]tm ≡ opTm d (ts ∘ σ) (t [ σ ]tm)
  op-[]tm d ts (var i) σ l =
    sym (opTm-lc d (ts ∘ σ) (lookupₛ σ i) (lcTm-mono d (lookupₛ σ i) (lc-lookup σ i l)))
  op-[]tm d ts (bvar e j) σ l with e ==ℕ d
  ... | true  = pickOr-∘ ts σ j (bvar e j)
  ... | false = refl
  op-[]tm d ts (coh Γ A τ) σ l = cong (coh Γ A) (op-∘ d ts τ σ l)
  op-[]tm d ts (cst k) σ l = refl
  op-[]tm d ts (bnd b y Δ τ) σ l =
    cong₂ (bnd b y)
      (trans (op-[]tel (suc d) (shSub 0 ts) Δ σ l) (cong (λ z → opTel (suc d) z (Δ [ σ ]tel)) (sh-∘ 0 ts σ l)))
      (op-∘ d ts τ σ l)

  op-[]tel : ∀ d ts Δ σ → LC σ → (opTel d ts Δ) [ σ ]tel ≡ opTel d (ts ∘ σ) (Δ [ σ ]tel)
  op-[]tel d ts ε σ _ = refl
  op-[]tel d ts (Δ ▸[ ms ] A) σ l = cong₂ (_▸[ ms ]_) (op-[]tel d ts Δ σ l) (op-[]ty d ts A σ l)

  op-∘ : ∀ d ts τ σ → LC σ → (opSub d ts τ) ∘ σ ≡ opSub d (ts ∘ σ) (τ ∘ σ)
  op-∘ d ts ⟨⟩ σ _ = refl
  op-∘ d ts (τ ,ₛ t) σ l = cong₂ _,ₛ_ (op-∘ d ts τ σ l) (op-[]tm d ts t σ l)

------------------------------------------------------------------------
-- Substitution lemmas.

lookupₛ-∘ : ∀ τ σ i → T (i <ℕ lenₛ τ) → lookupₛ (τ ∘ σ) i ≡ lookupₛ τ i [ σ ]tm
lookupₛ-∘ (τ ,ₛ t) σ i p rewrite lenₛ-∘ τ σ with i ==ℕ lenₛ τ in eq
... | true  = refl
... | false = lookupₛ-∘ τ σ i (<suc-≢ i (lenₛ τ) p eq)

-- Extending a substitution does not change syntax scoped below it.
mutual
  ext-ty : ∀ A σ s → T (scTy? (lenₛ σ) A) → A [ σ ,ₛ s ]ty ≡ A [ σ ]ty
  ext-ty ⋆           σ s _ = refl
  ext-ty (arr A t u) σ s p =
    let (a , q) = T∧ {scTy? (lenₛ σ) A} p ; (b , c) = T∧ {scTm? (lenₛ σ) t} q in
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (ext-ty A σ s a) (cong₂ _,_ (ext-tm t σ s b) (ext-tm u σ s c))

  ext-tm : ∀ t σ s → T (scTm? (lenₛ σ) t) → t [ σ ,ₛ s ]tm ≡ t [ σ ]tm
  ext-tm (var i)       σ s p rewrite <→≢ i (lenₛ σ) p = refl
  ext-tm (bvar d j)    σ s _ = refl
  ext-tm (coh Δ A τ)   σ s p = cong (coh Δ A) (ext-sub τ σ s p)
  ext-tm (cst k)       σ s _ = refl
  ext-tm (bnd b y Δ τ) σ s p =
    let (a , c) = T∧ {scTel? (lenₛ σ) Δ} p in
    cong₂ (bnd b y) (ext-tel Δ σ s a) (ext-sub τ σ s c)

  ext-tel : ∀ Δ σ s → T (scTel? (lenₛ σ) Δ) → Δ [ σ ,ₛ s ]tel ≡ Δ [ σ ]tel
  ext-tel ε σ s _ = refl
  ext-tel (Δ ▸[ ms ] A) σ s p =
    let (a , b) = T∧ {scTel? (lenₛ σ) Δ} p in cong₂ (_▸[ ms ]_) (ext-tel Δ σ s a) (ext-ty A σ s b)

  ext-sub : ∀ τ σ s → T (scSub? (lenₛ σ) τ) → τ ∘ (σ ,ₛ s) ≡ τ ∘ σ
  ext-sub ⟨⟩       σ s _ = refl
  ext-sub (τ ,ₛ t) σ s p =
    let (a , b) = T∧ {scSub? (lenₛ σ) τ} p in cong₂ _,ₛ_ (ext-sub τ σ s a) (ext-tm t σ s b)

ext-ty-++ : ∀ A σ τ → T (scTy? (lenₛ σ) A) → A [ σ ++ₛ τ ]ty ≡ A [ σ ]ty
ext-ty-++ A σ ⟨⟩       p = refl
ext-ty-++ A σ (τ ,ₛ t) p =
  trans (ext-ty A (σ ++ₛ τ) t
          (subst (λ n → T (scTy? n A)) (sym (lenₛ-++ σ τ)) (scTy-+ (lenₛ σ) (lenₛ τ) A p)))
        (ext-ty-++ A σ τ p)

-- Associativity of substitution.
mutual
  assoc-ty : ∀ A τ σ → T (scTy? (lenₛ τ) A) → A [ τ ]ty [ σ ]ty ≡ A [ τ ∘ σ ]ty
  assoc-ty ⋆           τ σ _ = refl
  assoc-ty (arr A t u) τ σ p =
    let (a , q) = T∧ {scTy? (lenₛ τ) A} p ; (b , c) = T∧ {scTm? (lenₛ τ) t} q in
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (assoc-ty A τ σ a) (cong₂ _,_ (assoc-tm t τ σ b) (assoc-tm u τ σ c))

  assoc-tm : ∀ t τ σ → T (scTm? (lenₛ τ) t) → t [ τ ]tm [ σ ]tm ≡ t [ τ ∘ σ ]tm
  assoc-tm (var i)       τ σ p = sym (lookupₛ-∘ τ σ i p)
  assoc-tm (bvar d j)    τ σ _ = refl
  assoc-tm (coh Δ A ρ)   τ σ p = cong (coh Δ A) (assoc-sub ρ τ σ p)
  assoc-tm (cst k)       τ σ _ = refl
  assoc-tm (bnd b y Δ ρ) τ σ p =
    let (a , c) = T∧ {scTel? (lenₛ τ) Δ} p in
    cong₂ (bnd b y) (assoc-tel Δ τ σ a) (assoc-sub ρ τ σ c)

  assoc-tel : ∀ Δ τ σ → T (scTel? (lenₛ τ) Δ) → Δ [ τ ]tel [ σ ]tel ≡ Δ [ τ ∘ σ ]tel
  assoc-tel ε τ σ _ = refl
  assoc-tel (Δ ▸[ ms ] A) τ σ p =
    let (a , b) = T∧ {scTel? (lenₛ τ) Δ} p in cong₂ (_▸[ ms ]_) (assoc-tel Δ τ σ a) (assoc-ty A τ σ b)

  assoc-sub : ∀ ρ τ σ → T (scSub? (lenₛ τ) ρ) → (ρ ∘ τ) ∘ σ ≡ ρ ∘ (τ ∘ σ)
  assoc-sub ⟨⟩       τ σ _ = refl
  assoc-sub (ρ ,ₛ t) τ σ p =
    let (a , b) = T∧ {scSub? (lenₛ τ) ρ} p in cong₂ _,ₛ_ (assoc-sub ρ τ σ a) (assoc-tm t τ σ b)

-- Closed syntax is fixed by substitution.
closed-ty : ∀ A σ → T (scTy? 0 A) → A [ σ ]ty ≡ A
closed-ty A ⟨⟩ p = go A p
  where
  mutual
    go : ∀ A → T (scTy? 0 A) → A [ ⟨⟩ ]ty ≡ A
    go ⋆ _ = refl
    go (arr A t u) p =
      let (a , q) = T∧ {scTy? 0 A} p ; (b , c) = T∧ {scTm? 0 t} q in
      cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (go A a) (cong₂ _,_ (gt t b) (gt u c))
    gt : ∀ t → T (scTm? 0 t) → t [ ⟨⟩ ]tm ≡ t
    gt (var i) ()
    gt (bvar d j) _ = refl
    gt (coh Δ A τ) p = cong (coh Δ A) (gs τ p)
    gt (cst k) _ = refl
    gt (bnd b y Δ τ) p = let (a , c) = T∧ {scTel? 0 Δ} p in cong₂ (bnd b y) (gl Δ a) (gs τ c)
    gl : ∀ Δ → T (scTel? 0 Δ) → Δ [ ⟨⟩ ]tel ≡ Δ
    gl ε _ = refl
    gl (Δ ▸[ ms ] A) p = let (a , b) = T∧ {scTel? 0 Δ} p in cong₂ (_▸[ ms ]_) (gl Δ a) (go A b)
    gs : ∀ τ → T (scSub? 0 τ) → τ ∘ ⟨⟩ ≡ τ
    gs ⟨⟩ _ = refl
    gs (τ ,ₛ t) p = let (a , b) = T∧ {scSub? 0 τ} p in cong₂ _,ₛ_ (gs τ a) (gt t b)
closed-ty A (σ ,ₛ s) p =
  trans (ext-ty A σ s (scTy-mono (lenₛ σ) A p)) (closed-ty A σ p)

-- Substituting a scoped substitution preserves scoping.
mutual
  sc-ty[] : ∀ {n} A σ → T (scTy? (lenₛ σ) A) → T (scSub? n σ) → T (scTy? n (A [ σ ]ty))
  sc-ty[] ⋆ σ _ _ = tt
  sc-ty[] (arr A t u) σ p s =
    let (a , q) = T∧ {scTy? (lenₛ σ) A} p ; (b , c) = T∧ {scTm? (lenₛ σ) t} q in
    ∧T (sc-ty[] A σ a s) (∧T (sc-tm[] t σ b s) (sc-tm[] u σ c s))

  sc-tm[] : ∀ {n} t σ → T (scTm? (lenₛ σ) t) → T (scSub? n σ) → T (scTm? n (t [ σ ]tm))
  sc-tm[] (var i)       σ p s = sc-lookup σ i p s
  sc-tm[] (bvar _ _)    σ _ _ = tt
  sc-tm[] (coh Δ A ρ)   σ p s = sc-∘ ρ σ p s
  sc-tm[] (cst k)       σ _ _ = tt
  sc-tm[] (bnd b y Δ ρ) σ p s =
    let (a , c) = T∧ {scTel? (lenₛ σ) Δ} p in ∧T (sc-tel[] Δ σ a s) (sc-∘ ρ σ c s)

  sc-tel[] : ∀ {n} Δ σ → T (scTel? (lenₛ σ) Δ) → T (scSub? n σ) → T (scTel? n (Δ [ σ ]tel))
  sc-tel[] ε σ _ _ = tt
  sc-tel[] (Δ ▸[ ms ] A) σ p s =
    let (a , b) = T∧ {scTel? (lenₛ σ) Δ} p in ∧T (sc-tel[] Δ σ a s) (sc-ty[] A σ b s)

  sc-∘ : ∀ {n} ρ σ → T (scSub? (lenₛ σ) ρ) → T (scSub? n σ) → T (scSub? n (ρ ∘ σ))
  sc-∘ ⟨⟩ σ _ _ = tt
  sc-∘ (ρ ,ₛ t) σ p s =
    let (a , b) = T∧ {scSub? (lenₛ σ) ρ} p in ∧T (sc-∘ ρ σ a s) (sc-tm[] t σ b s)

  sc-lookup : ∀ {n} σ i → T (i <ℕ lenₛ σ) → T (scSub? n σ) → T (scTm? n (lookupₛ σ i))
  sc-lookup {n} (σ ,ₛ t) i p s with i ==ℕ lenₛ σ in eq
  ... | true  = snd (T∧ {scSub? n σ} s)
  ... | false = sc-lookup σ i (<suc-≢ i (lenₛ σ) p eq) (fst (T∧ {scSub? n σ} s))

-- Substitution preserves local closure (by locally closed terms).
mutual
  lc-ty[] : ∀ d A σ → T (lcTy? d A) → LC σ → T (lcTy? d (A [ σ ]ty))
  lc-ty[] d ⋆ σ _ _ = tt
  lc-ty[] d (arr A t u) σ p l =
    let (a , q) = T∧ {lcTy? d A} p ; (b , c) = T∧ {lcTm? d t} q in
    ∧T (lc-ty[] d A σ a l) (∧T (lc-tm[] d t σ b l) (lc-tm[] d u σ c l))

  lc-tm[] : ∀ d t σ → T (lcTm? d t) → LC σ → T (lcTm? d (t [ σ ]tm))
  lc-tm[] d (var i) σ _ l = lcTm-mono d (lookupₛ σ i) (lc-lookup σ i l)
  lc-tm[] d (bvar e j) σ p _ = p
  lc-tm[] d (coh Δ A ρ) σ p l = lc-∘ d ρ σ p l
  lc-tm[] d (cst k) σ _ _ = tt
  lc-tm[] d (bnd b y Δ ρ) σ p l =
    let (a , c) = T∧ {lcTel? (suc d) Δ} p in ∧T (lc-tel[] (suc d) Δ σ a l) (lc-∘ d ρ σ c l)

  lc-tel[] : ∀ d Δ σ → T (lcTel? d Δ) → LC σ → T (lcTel? d (Δ [ σ ]tel))
  lc-tel[] d ε σ _ _ = tt
  lc-tel[] d (Δ ▸[ ms ] A) σ p l =
    let (a , b) = T∧ {lcTel? d Δ} p in ∧T (lc-tel[] d Δ σ a l) (lc-ty[] d A σ b l)

  lc-∘ : ∀ d ρ σ → T (lcSub? d ρ) → LC σ → T (lcSub? d (ρ ∘ σ))
  lc-∘ d ⟨⟩ σ _ _ = tt
  lc-∘ d (ρ ,ₛ t) σ p l =
    let (a , b) = T∧ {lcSub? d ρ} p in ∧T (lc-∘ d ρ σ a l) (lc-tm[] d t σ b l)

------------------------------------------------------------------------
-- Scoping of opened syntax.

sc-pickOr : ∀ {n} ts j t → T (scSub? n ts) → T (scTm? n t) → T (scTm? n (pickOr ts j t))
sc-pickOr ⟨⟩ j t _ q = q
sc-pickOr {n} (ts ,ₛ s) j t p q with j ==ℕ lenₛ ts
... | true  = snd (T∧ {scSub? n ts} p)
... | false = sc-pickOr ts j t (fst (T∧ {scSub? n ts} p)) q

mutual
  sc-opTy : ∀ {n} d ts A → T (scSub? n ts) → T (scTy? n A) → T (scTy? n (opTy d ts A))
  sc-opTy d ts ⋆ _ _ = tt
  sc-opTy {n} d ts (arr A t u) s p =
    let (a , q) = T∧ {scTy? n A} p ; (b , c) = T∧ {scTm? n t} q in
    ∧T (sc-opTy d ts A s a) (∧T (sc-opTm d ts t s b) (sc-opTm d ts u s c))

  sc-opTm : ∀ {n} d ts t → T (scSub? n ts) → T (scTm? n t) → T (scTm? n (opTm d ts t))
  sc-opTm d ts (var i) _ p = p
  sc-opTm d ts (bvar e j) s _ with e ==ℕ d
  ... | true  = sc-pickOr ts j (bvar e j) s tt
  ... | false = tt
  sc-opTm d ts (coh Γ A σ) s p = sc-opSub d ts σ s p
  sc-opTm d ts (cst k) _ _ = tt
  sc-opTm {n} d ts (bnd b y Δ σ) s p =
    let (a , c) = T∧ {scTel? n Δ} p in ∧T (sc-opTel (suc d) (shSub 0 ts) Δ (sc-shSub 0 ts s) a) (sc-opSub d ts σ s c)

  sc-opTel : ∀ {n} d ts Δ → T (scSub? n ts) → T (scTel? n Δ) → T (scTel? n (opTel d ts Δ))
  sc-opTel d ts ε _ _ = tt
  sc-opTel {n} d ts (Δ ▸[ ms ] A) s p =
    let (a , b) = T∧ {scTel? n Δ} p in ∧T (sc-opTel d ts Δ s a) (sc-opTy d ts A s b)

  sc-opSub : ∀ {n} d ts σ → T (scSub? n ts) → T (scSub? n σ) → T (scSub? n (opSub d ts σ))
  sc-opSub d ts ⟨⟩ _ _ = tt
  sc-opSub {n} d ts (σ ,ₛ t) s p =
    let (a , b) = T∧ {scSub? n σ} p in ∧T (sc-opSub d ts σ s a) (sc-opTm d ts t s b)

------------------------------------------------------------------------
-- Fresh variables.

sc-fresh : ∀ n k → T (scSub? (n + k) (fresh n k))
sc-fresh n zero    = tt
sc-fresh n (suc k) rewrite +-suc n k =
  ∧T (scSub-suc (fresh n k) (sc-fresh n k)) (<-self (n + k))

-- Looking up the opened variables in σ ++ fresh n′ k gives the fresh
-- variables at n′.
lookup-fresh : ∀ σ n′ k j → T (j <ℕ k) →
               lookupₛ (σ ++ₛ fresh n′ k) (lenₛ σ + j) ≡ var (n′ + j)
lookup-fresh σ n′ (suc k) j p
  rewrite lenₛ-++ σ (fresh n′ k) | lenₛ-fresh n′ k
  with (lenₛ σ + j) ==ℕ (lenₛ σ + k) in e
... | true  = cong (λ x → var (n′ + x)) (sym (+-cancel (lenₛ σ) j k (==→≡ _ _ e)))
  where
  +-cancel : ∀ m a b → m + a ≡ m + b → a ≡ b
  +-cancel zero    a b q = q
  +-cancel (suc m) a b q = +-cancel m a b (suc-inj q)
    where
    suc-inj : ∀ {x y} → suc x ≡ suc y → x ≡ y
    suc-inj refl = refl
... | false = lookup-fresh σ n′ k j (<suc-≢ j k p (+-≢ (lenₛ σ) j k e))
  where
  +-≢ : ∀ m a b → ((m + a) ==ℕ (m + b)) ≡ false → (a ==ℕ b) ≡ false
  +-≢ zero    a b q = q
  +-≢ (suc m) a b q = +-≢ m a b q

fresh-∘ : ∀ σ n′ k → fresh (lenₛ σ) k ∘ (σ ++ₛ fresh n′ k) ≡ fresh n′ k
fresh-∘ σ n′ k = go k k (<-refl-ish k)
  where
  <-refl-ish : ∀ k → T (k <ℕ suc k)
  <-refl-ish = <-self
  -- fresh (lenₛ σ) m ∘ ρ for m ≤ k, where ρ = σ ++ fresh n′ k.
  go : ∀ m k → T (m <ℕ suc k) → fresh (lenₛ σ) m ∘ (σ ++ₛ fresh n′ k) ≡ fresh n′ m
  go zero    k _ = refl
  go (suc m) k p =
    cong₂ _,ₛ_ (go m k (<-trans m (suc m) (suc k) (<-self m) p))
               (lookup-fresh σ n′ k m p)

-- Substitution by σ ++ fresh n′ k, on syntax scoped below lenₛ σ + k,
-- is σ, then fresh.
