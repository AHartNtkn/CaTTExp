------------------------------------------------------------------------
-- Why the cospan generators are forced.
--
-- In r7's completion C(Q), the composite α ; I (a seed, then a
-- nonempty inner path) has no right division by a nonempty inner path
-- R whose last arrow differs from the last arrow of I:
--
--   no-division : no H with  H ; R = α ; I.
--
-- Any functor in the class of CaTTExp.Join.CospanNatural that sends a
-- fresh seed τ to α ; I must send r7's j τ R (with j τ R ; R = τ) to
-- such an H, so every completion that contains r7's generators and is
-- natural for that class must contain a division of α ; I by R. For
-- (I, R) with common last arrow, H = j α I′ R′ of the smaller cospan
-- works, so the new generators needed are exactly the cospan
-- generators j α I R of CaTTExp.Join.Cospan with distinct last arrows.
-- CaTTExp.Join.NotNatural is the instance I = f, R = e.
--
-- No finiteness, decidability or acyclicity is assumed.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver
import CaTTExp.Join.Completion as Completion

module CaTTExp.Join.Forced {V : Set} (E P : V → V → Set) where

open Completion E P

-- The last arrow of an inner path.
private
  last′ : ∀ {a b m} → E a b → IPath b m → Maybe (Σ V λ z → E z m)
  last′ e []      = just (_ , e)
  last′ e (f ∷ p) = last′ f p

lastE : ∀ {a m} → IPath a m → Maybe (Σ V λ z → E z m)
lastE []      = nothing
lastE (e ∷ p) = last′ e p

private
  last′-++ : ∀ {a b x y m} (g : E a b) (p : IPath b x) (e : E x y) (R : IPath y m) →
             last′ g (p ++ᵖ (e ∷ R)) ≡ last′ e R
  last′-++ g []      e R = refl
  last′-++ g (f ∷ p) e R = last′-++ f p e R

  lastE-++ : ∀ {a x y m} (p : IPath a x) (e : E x y) (R : IPath y m) →
             lastE (p ++ᵖ (e ∷ R)) ≡ last′ e R
  lastE-++ []      e R = refl
  lastE-++ (g ∷ p) e R = last′-++ g p e R

  ∷-inj : ∀ {A : Set} {x y : A} {xs ys} → _≡_ {A = List A} (x ∷ xs) (y ∷ ys) →
          (x ≡ y) × (xs ≡ ys)
  ∷-inj refl = refl , refl

  innW-++ : ∀ {a b c} (p : IPath a b) (q : IPath b c) → innW (p ++ᵖ q) ≡ innW p ++ᵖ innW q
  innW-++ []      q = refl
  innW-++ (e ∷ p) q = cong (inn e ∷_) (innW-++ p q)

  innW-nf : ∀ {a b} (p : IPath a b) → Normal (innW p)
  innW-nf (e ∷ p) _ (skip _ s) = innW-nf p _ s

  seeds-innW : ∀ {a b} (p : IPath a b) → seeds (innW p) ≡ []
  seeds-innW []      = refl
  seeds-innW (e ∷ p) = seeds-innW p

  seeds-++ : ∀ {a b c} (w : Word a b) (r : Word b c) →
             seeds (w ++ᵖ r) ≡ seeds w ++ seeds r
  seeds-++ []           r = refl
  seeds-++ (inn e ∷ w)  r = seeds-++ w r
  seeds-++ (jn α R ∷ w) r = cong (seed α ∷_) (seeds-++ w r)

  ++-[]L : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-[]L []       = refl
  ++-[]L (x ∷ xs) = cong (x ∷_) (++-[]L xs)

  all-inner : ∀ {a b} (w : Word a b) → seeds w ≡ [] → Σ (IPath a b) λ p → w ≡ innW p
  all-inner []           _  = [] , refl
  all-inner (inn e ∷ w)  eq with all-inner w eq
  ... | p , refl = e ∷ p , refl
  all-inner (jn α R ∷ w) ()

  -- A word with exactly one seed α.
  one-seed : ∀ {a s t u} (α : P s t) (H : Word a u) → seeds H ≡ seed α ∷ [] →
             Σ (IPath a s) λ P₀ → Σ V λ x → Σ (IPath x t) λ S → Σ (IPath x u) λ L →
             H ≡ innW P₀ ++ᵖ (jn α S ∷ innW L)
  one-seed α []            ()
  one-seed α (inn e ∷ H)   eq with one-seed α H eq
  ... | P₀ , x , S , L , refl = e ∷ P₀ , x , S , L , refl
  one-seed α (jn α′ S ∷ H) eq with ∷-inj eq
  ... | refl , eq′ with all-inner H eq′
  ...   | L , refl = [] , _ , S , L , refl

  -- A leading inner arrow is never rewritten.
  head-inn : ∀ {a b c} (e : E a b) {w : Word b c} {W} → inn e ∷ w ⇒* W →
             Σ (Word b c) λ w′ → W ≡ inn e ∷ w′
  head-inn e ε                  = _ , refl
  head-inn e (skip _ s ◅ rest)  = head-inn e rest

  hd : ∀ {a b} → Word a b → Maybe (Σ V (Gen a))
  hd []      = nothing
  hd (g ∷ w) = just (_ , g)

  tl : ∀ {a b} → Word a b → Σ V λ c → Word c b
  tl {a} []  = a , []
  tl (g ∷ w) = _ , w

  Σ-inj : ∀ {A : Set} {B : A → Set} {x} {y z : B x} →
          _≡_ {A = Σ A B} (x , y) (x , z) → y ≡ z
  Σ-inj refl = refl

  innW-inj : ∀ {a b} (p q : IPath a b) → innW p ≡ innW q → p ≡ q
  innW-inj []      []      _  = refl
  innW-inj []      (f ∷ q) ()
  innW-inj (e ∷ p) []      ()
  innW-inj (e ∷ p) (f ∷ q) eq with cong hd eq
  ... | refl = cong (e ∷_) (innW-inj p q (Σ-inj (cong tl eq)))

  -- Reducing  j α S ; L  to  α ; I  only cancels a common prefix of
  -- S and L, so L = S ; I.
  reach : ∀ {s t x y} (α : P s t) (S : IPath x t) (L : IPath x y) (I : IPath t y)
          {W : Word s y} → jn α S ∷ innW L ⇒* W → W ≡ jn α [] ∷ innW I →
          L ≡ S ++ᵖ I
  reach α S L I ε eq with cong hd eq
  ... | refl = innW-inj L I (Σ-inj (cong tl eq))
  reach α S []      I (skip _ () ◅ _) eq
  reach α (e ∷ S) (.e ∷ L) I (ctr .α .e .S .(innW L) ◅ rest) eq =
    cong (e ∷_) (reach α S L I rest eq)
  reach α S (e ∷ L) I (skip _ s ◅ _) eq = ⊥-elim (innW-nf (e ∷ L) _ s)

  target-nf : ∀ {s t y} (α : P s t) (I : IPath t y) → Normal (jn α [] ∷ innW I)
  target-nf α I _ (skip _ s) = innW-nf I _ s

-- The main statement.
no-division : ∀ {s t x₁ x₂ m u} (α : P s t)
              (I₀ : IPath t x₁) (i : E x₁ m) (R₀ : IPath u x₂) (r : E x₂ m) →
              ¬ (_≡_ {A = Σ V λ z → E z m} (_ , i) (_ , r)) →
              ¬ (Σ (Word s u) λ H →
                   H ++ᵖ innW (R₀ ++ᵖ (r ∷ [])) ~ jn α [] ∷ innW (I₀ ++ᵖ (i ∷ [])))
no-division {s} {t} {x₁} {x₂} {m} {u} α I₀ i R₀ r ne (H , eqn) = main
  where
  R = R₀ ++ᵖ (r ∷ [])
  I = I₀ ++ᵖ (i ∷ [])

  seedsH : seeds H ≡ seed α ∷ []
  seedsH = trans (sym (++-[]L (seeds H)))
           (trans (cong (seeds H ++_) (sym (seeds-innW R)))
           (trans (sym (seeds-++ H (innW R)))
           (trans (seeds-~ eqn) (cong (seed α ∷_) (seeds-innW I)))))

  go : (P₀ : IPath s s) {x : V} (S : IPath x t) (L : IPath x u) →
       H ≡ innW P₀ ++ᵖ (jn α S ∷ innW L) →
       H ++ᵖ innW R ⇒* jn α [] ∷ innW I → ⊥
  go P₀ S L eqH red = go′ P₀ (subst (λ h → h ++ᵖ innW R ⇒* _) eqH red)
    where
    shape : ∀ {a} (P₀ : IPath a s) →
            (innW P₀ ++ᵖ (jn α S ∷ innW L)) ++ᵖ innW R ≡
            innW P₀ ++ᵖ (jn α S ∷ innW (L ++ᵖ R))
    shape P₀ = trans (++ᵖ-assoc (innW P₀) _ (innW R))
                     (cong (λ z → innW P₀ ++ᵖ (jn α S ∷ z)) (sym (innW-++ L R)))
    go′ : (P₀ : IPath s s) →
          (innW P₀ ++ᵖ (jn α S ∷ innW L)) ++ᵖ innW R ⇒* jn α [] ∷ innW I → ⊥
    go′ [] red′ with reach α S (L ++ᵖ R) I (subst (_⇒* jn α [] ∷ innW I) (shape []) red′) refl
    ... | eqL with trans (sym (lastE-++ (L ++ᵖ R₀) r []))
                    (trans (cong lastE (++ᵖ-assoc L R₀ (r ∷ [])))
                    (trans (cong lastE eqL)
                    (trans (cong lastE (sym (++ᵖ-assoc S I₀ (i ∷ []))))
                           (lastE-++ (S ++ᵖ I₀) i []))))
    ...   | refl = ne refl
    go′ (e ∷ P₀) red′ with head-inn e (subst (_⇒* jn α [] ∷ innW I) (shape (e ∷ P₀)) red′)
    ... | _ , ()

  main : ⊥
  main with church-rosser eqn
  ... | c , red , red′ with normal-⇒* (target-nf α I) red′
  ...   | refl with one-seed α H seedsH
  ...     | P₀ , x , S , L , eqH = go P₀ S L eqH red
