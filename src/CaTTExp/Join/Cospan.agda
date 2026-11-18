------------------------------------------------------------------------
-- The cospan completion: a source-only joining completion that is
-- natural under substitution-like maps (E6, requirement 5).
--
-- r7's completion divides each seed α : s → t by inner paths R into t.
-- CaTTExp.Join.NotNatural shows this is not closed under maps sending
-- a seed to a composite α ; I. The cospan completion divides every
-- composite "seed, then inner path" by inner paths:
--
--   for α : s → t, I : t → m inner, R : u → m inner,
--   j α I R : s → u     (read: α ; I ; R⁻¹)
--
-- with j α [] [] the original α, and the equations
--
--   (C1)  j α I (e ∷ R) ; e  =  j α I R
--   (C0)  j α I []           =  α ; I
--
-- r7's generators are the case I = []. Orient (C1) as a contraction
-- and (C0) as an expansion (for nonempty I). Left-hand sides are
-- (j with R ≠ [], inner) and (j with R = [], I ≠ []), which never
-- overlap, so the system has the diamond property: it is confluent
-- and normal forms are unique, with no termination argument.
-- Everything else of r7 §1 carries over:
--
--   * unique normal forms, computed when inner arrows have decidable
--     equality (Normalise);
--   * original paths are normal, so Path(Q) embeds (embed);
--   * seed lists are invariant (seeds-~);
--   * with a rank φ every j strictly raises φ, so the completed quiver
--     is acyclic and supports of normal forms are injective (Rank).
--
-- Naturality is CaTTExp.Join.CospanNatural; the reason the cospan
-- generators are forced is CaTTExp.Join.Forced.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver

module CaTTExp.Join.Cospan {V : Set} (E P : V → V → Set) where

IPath : V → V → Set
IPath = Path E

data Gen : V → V → Set where
  inn : ∀ {a b} → E a b → Gen a b
  jn  : ∀ {s t m u} → P s t → IPath t m → IPath u m → Gen s u

Word : V → V → Set
Word = Path Gen

innW : ∀ {a b} → IPath a b → Word a b
innW []      = []
innW (e ∷ p) = inn e ∷ innW p

innW-++ : ∀ {a b c} (p : IPath a b) (q : IPath b c) → innW (p ++ᵖ q) ≡ innW p ++ᵖ innW q
innW-++ []      q = refl
innW-++ (e ∷ p) q = cong (inn e ∷_) (innW-++ p q)

------------------------------------------------------------------------
-- The original quiver.

data Orig : V → V → Set where
  oe : ∀ {a b} → E a b → Orig a b
  op : ∀ {a b} → P a b → Orig a b

ιg : ∀ {a b} → Orig a b → Gen a b
ιg (oe e) = inn e
ιg (op α) = jn α [] []

ι : ∀ {a b} → Path Orig a b → Word a b
ι []      = []
ι (g ∷ p) = ιg g ∷ ι p

ι-++ : ∀ {a b c} (p : Path Orig a b) (q : Path Orig b c) → ι (p ++ᵖ q) ≡ ι p ++ᵖ ι q
ι-++ []      q = refl
ι-++ (g ∷ p) q = cong (ιg g ∷_) (ι-++ p q)

------------------------------------------------------------------------
-- Rewriting.

infix 4 _⇒_ _⇒*_ _~_

data _⇒_ : ∀ {a b} → Word a b → Word a b → Set where
  ctr  : ∀ {s t m u v c} (α : P s t) (I : IPath t m) (e : E u v) (R : IPath v m)
         (w : Word v c) →
         jn α I (e ∷ R) ∷ inn e ∷ w ⇒ jn α I R ∷ w
  exp  : ∀ {s t x m c} (α : P s t) (e : E t x) (I : IPath x m) (w : Word m c) →
         jn α (e ∷ I) [] ∷ w ⇒ jn α [] [] ∷ inn e ∷ (innW I ++ᵖ w)
  skip : ∀ {a b c} (g : Gen a b) {w w′ : Word b c} → w ⇒ w′ → g ∷ w ⇒ g ∷ w′

⇒-++ˡ : ∀ {a b c} (l : Word a b) {w w′ : Word b c} → w ⇒ w′ → l ++ᵖ w ⇒ l ++ᵖ w′
⇒-++ˡ []      s = s
⇒-++ˡ (g ∷ l) s = skip g (⇒-++ˡ l s)

++-assoc-innW : ∀ {a b c d} (I : IPath a b) (w : Word b c) (r : Word c d) →
                (innW I ++ᵖ w) ++ᵖ r ≡ innW I ++ᵖ (w ++ᵖ r)
++-assoc-innW I w r = ++ᵖ-assoc (innW I) w r

⇒-++ʳ : ∀ {a b c} {w w′ : Word a b} (r : Word b c) → w ⇒ w′ → w ++ᵖ r ⇒ w′ ++ᵖ r
⇒-++ʳ r (ctr α I e R w) = ctr α I e R (w ++ᵖ r)
⇒-++ʳ r (exp α e I w)   =
  subst (λ z → jn α (e ∷ I) [] ∷ (w ++ᵖ r) ⇒ jn α [] [] ∷ inn e ∷ z)
        (sym (++-assoc-innW I w r)) (exp α e I (w ++ᵖ r))
⇒-++ʳ r (skip g s)      = skip g (⇒-++ʳ r s)

data _⇒*_ {a b} : Word a b → Word a b → Set where
  ε   : ∀ {w} → w ⇒* w
  _◅_ : ∀ {w w₁ w₂} → w ⇒ w₁ → w₁ ⇒* w₂ → w ⇒* w₂
infixr 5 _◅_ _◅◅_

_◅◅_ : ∀ {a b} {w w₁ w₂ : Word a b} → w ⇒* w₁ → w₁ ⇒* w₂ → w ⇒* w₂
ε       ◅◅ q = q
(s ◅ p) ◅◅ q = s ◅ (p ◅◅ q)

⇒*-skip : ∀ {a b c} (g : Gen a b) {w w′ : Word b c} → w ⇒* w′ → g ∷ w ⇒* g ∷ w′
⇒*-skip g ε       = ε
⇒*-skip g (s ◅ p) = skip g s ◅ ⇒*-skip g p

⇒*-++ˡ : ∀ {a b c} (l : Word a b) {w w′ : Word b c} → w ⇒* w′ → l ++ᵖ w ⇒* l ++ᵖ w′
⇒*-++ˡ l ε       = ε
⇒*-++ˡ l (s ◅ p) = ⇒-++ˡ l s ◅ ⇒*-++ˡ l p

data _~_ {a b} : Word a b → Word a b → Set where
  fwd    : ∀ {w w′} → w ⇒ w′ → w ~ w′
  rfl    : ∀ {w} → w ~ w
  sym~   : ∀ {w w′} → w ~ w′ → w′ ~ w
  trans~ : ∀ {w w′ w″} → w ~ w′ → w′ ~ w″ → w ~ w″

⇒*→~ : ∀ {a b} {w w′ : Word a b} → w ⇒* w′ → w ~ w′
⇒*→~ ε       = rfl
⇒*→~ (s ◅ p) = trans~ (fwd s) (⇒*→~ p)

~-++ˡ : ∀ {a b c} (l : Word a b) {w w′ : Word b c} → w ~ w′ → l ++ᵖ w ~ l ++ᵖ w′
~-++ˡ l (fwd s)      = fwd (⇒-++ˡ l s)
~-++ˡ l rfl          = rfl
~-++ˡ l (sym~ p)     = sym~ (~-++ˡ l p)
~-++ˡ l (trans~ p q) = trans~ (~-++ˡ l p) (~-++ˡ l q)

~-++ʳ : ∀ {a b c} {w w′ : Word a b} (r : Word b c) → w ~ w′ → w ++ᵖ r ~ w′ ++ᵖ r
~-++ʳ r (fwd s)      = fwd (⇒-++ʳ r s)
~-++ʳ r rfl          = rfl
~-++ʳ r (sym~ p)     = sym~ (~-++ʳ r p)
~-++ʳ r (trans~ p q) = trans~ (~-++ʳ r p) (~-++ʳ r q)

------------------------------------------------------------------------
-- Diamond property, confluence, Church–Rosser.

diamond : ∀ {a b} {w w₁ w₂ : Word a b} → w ⇒ w₁ → w ⇒ w₂ →
          (w₁ ≡ w₂) ⊎ Σ (Word a b) λ w₃ → (w₁ ⇒ w₃) × (w₂ ⇒ w₃)
diamond (ctr α I e R w) (ctr .α .I .e .R .w) = inj₁ refl
diamond (ctr α I e R w) (skip _ (skip _ s))  = inj₂ (_ , skip _ s , ctr α I e R _)
diamond (exp α e I w)   (exp .α .e .I .w)    = inj₁ refl
diamond (exp α e I w)   (skip _ s)           =
  inj₂ (_ , skip _ (skip _ (⇒-++ˡ (innW I) s)) , exp α e I _)
diamond (skip _ (skip _ s)) (ctr α I e R w)  = inj₂ (_ , ctr α I e R _ , skip _ s)
diamond (skip _ s)      (exp α e I w)        =
  inj₂ (_ , exp α e I _ , skip _ (skip _ (⇒-++ˡ (innW I) s)))
diamond (skip g s) (skip .g s′) with diamond s s′
... | inj₁ refl         = inj₁ refl
... | inj₂ (w₃ , p , q) = inj₂ (g ∷ w₃ , skip g p , skip g q)

private
  strip : ∀ {a b} {w w₁ w₂ : Word a b} → w ⇒ w₁ → w ⇒* w₂ →
          Σ (Word a b) λ c → (w₁ ⇒* c) × ((w₂ ≡ c) ⊎ (w₂ ⇒ c))
  strip s ε = _ , ε , inj₂ s
  strip s (t ◅ p) with diamond s t
  ... | inj₁ refl = _ , p , inj₁ refl
  ... | inj₂ (d , s′ , t′) with strip t′ p
  ...   | c , q , r = c , s′ ◅ q , r

confluent : ∀ {a b} {w w₁ w₂ : Word a b} → w ⇒* w₁ → w ⇒* w₂ →
            Σ (Word a b) λ c → (w₁ ⇒* c) × (w₂ ⇒* c)
confluent ε q = _ , q , ε
confluent (s ◅ p) q with strip s q
... | d , q′ , inj₁ refl with confluent p q′
...   | c , x , y = c , x , y
confluent (s ◅ p) q | d , q′ , inj₂ t with confluent p q′
...   | c , x , y = c , x , t ◅ y

church-rosser : ∀ {a b} {w w′ : Word a b} → w ~ w′ →
                Σ (Word a b) λ c → (w ⇒* c) × (w′ ⇒* c)
church-rosser (fwd s) = _ , s ◅ ε , ε
church-rosser rfl     = _ , ε , ε
church-rosser (sym~ p) with church-rosser p
... | c , x , y = c , y , x
church-rosser (trans~ p q) with church-rosser p | church-rosser q
... | c , x , y | d , y′ , z with confluent y y′
...   | f , u , v = f , x ◅◅ u , z ◅◅ v

Normal : ∀ {a b} → Word a b → Set
Normal w = ∀ w′ → ¬ (w ⇒ w′)

normal-⇒* : ∀ {a b} {n c : Word a b} → Normal n → n ⇒* c → n ≡ c
normal-⇒* nn ε       = refl
normal-⇒* nn (s ◅ _) = ⊥-elim (nn _ s)

nf-unique : ∀ {a b} {n n′ : Word a b} → Normal n → Normal n′ → n ~ n′ → n ≡ n′
nf-unique nn nn′ p with church-rosser p
... | c , x , y = trans (normal-⇒* nn x) (sym (normal-⇒* nn′ y))

------------------------------------------------------------------------
-- Original paths are normal; Path(Q) embeds.

ι-normal : ∀ {a b} (p : Path Orig a b) → Normal (ι p)
ι-normal (oe e ∷ p) _ (skip _ s) = ι-normal p _ s
ι-normal (op α ∷ p) _ (skip _ s) = ι-normal p _ s

private
  hd : ∀ {a b} → Word a b → Maybe (Σ V (Gen a))
  hd []      = nothing
  hd (g ∷ w) = just (_ , g)

  tl : ∀ {a b} → Word a b → Σ V λ c → Word c b
  tl {a} []  = a , []
  tl (g ∷ w) = _ , w

  Σ-inj : ∀ {A : Set} {B : A → Set} {x} {y z : B x} →
          _≡_ {A = Σ A B} (x , y) (x , z) → y ≡ z
  Σ-inj refl = refl

  ιg-inj : ∀ {a c c′} (g : Orig a c) (h : Orig a c′) →
           _≡_ {A = Maybe (Σ V (Gen a))} (just (c , ιg g)) (just (c′ , ιg h)) →
           _≡_ {A = Σ V (Orig a)} (c , g) (c′ , h)
  ιg-inj (oe e) (oe .e) refl = refl
  ιg-inj (op α) (op .α) refl = refl
  ιg-inj (oe e) (op α)  ()
  ιg-inj (op α) (oe e)  ()

ι-inj : ∀ {a b} (p q : Path Orig a b) → ι p ≡ ι q → p ≡ q
ι-inj []      []      _ = refl
ι-inj []      (h ∷ q) ()
ι-inj (g ∷ p) []      ()
ι-inj (g ∷ p) (h ∷ q) eq with ιg-inj g h (cong hd eq)
... | refl = cong (g ∷_) (ι-inj p q (Σ-inj (cong tl eq)))

embed : ∀ {a b} (p q : Path Orig a b) → ι p ~ ι q → p ≡ q
embed p q r = ι-inj p q (nf-unique (ι-normal p) (ι-normal q) r)

------------------------------------------------------------------------
-- Seed lists are invariant.

record Seed : Set where
  constructor seed
  field
    {from to} : V
    arrow     : P from to

seeds : ∀ {a b} → Word a b → List Seed
seeds []             = []
seeds (inn e ∷ w)    = seeds w
seeds (jn α I R ∷ w) = seed α ∷ seeds w

seeds-innW : ∀ {a b c} (I : IPath a b) (w : Word b c) → seeds (innW I ++ᵖ w) ≡ seeds w
seeds-innW []      w = refl
seeds-innW (e ∷ I) w = seeds-innW I w

seeds-⇒ : ∀ {a b} {w w′ : Word a b} → w ⇒ w′ → seeds w ≡ seeds w′
seeds-⇒ (ctr α I e R w)     = refl
seeds-⇒ (exp α e I w)       = cong (seed α ∷_) (sym (seeds-innW I w))
seeds-⇒ (skip (inn e) s)    = seeds-⇒ s
seeds-⇒ (skip (jn α I R) s) = cong (seed α ∷_) (seeds-⇒ s)

seeds-~ : ∀ {a b} {w w′ : Word a b} → w ~ w′ → seeds w ≡ seeds w′
seeds-~ (fwd s)      = seeds-⇒ s
seeds-~ rfl          = refl
seeds-~ (sym~ p)     = sym (seeds-~ p)
seeds-~ (trans~ p q) = trans (seeds-~ p) (seeds-~ q)

------------------------------------------------------------------------
-- Normal forms exist when inner arrows have decidable equality.

module Normalise (decE : ∀ {u} (x y : Σ V (E u)) → Dec (x ≡ y)) where

  private
    innW-nf : ∀ {a b c} (I : IPath a b) (w : Word b c) → Normal w → Normal (innW I ++ᵖ w)
    innW-nf []      w nw = nw
    innW-nf (e ∷ I) w nw _ (skip _ s) = innW-nf I w nw _ s

    seed-nf : ∀ {s t c} (α : P s t) (w : Word t c) → Normal w → Normal (jn α [] [] ∷ w)
    seed-nf α w nw _ (skip _ s) = nw _ s

  push₀ : ∀ {s t m c} → P s t → IPath t m → Word m c → Word s c
  push₀ α []      w = jn α [] [] ∷ w
  push₀ α (e ∷ I) w = jn α [] [] ∷ inn e ∷ (innW I ++ᵖ w)

  push₁ : ∀ {s t m u v c} → P s t → IPath t m → E u v → IPath v m → Word u c → Word s c
  push₁ α I e R []             = jn α I (e ∷ R) ∷ []
  push₁ α I e R (jn β J S ∷ w) = jn α I (e ∷ R) ∷ jn β J S ∷ w
  push₁ α I e R (inn e′ ∷ w) with decE (_ , e) (_ , e′)
  push₁ α I e []      (inn e′ ∷ w) | yes refl = push₀ α I w
  push₁ α I e (f ∷ R) (inn e′ ∷ w) | yes refl = push₁ α I f R w
  ... | no _ = jn α I (e ∷ R) ∷ inn e′ ∷ w

  push : ∀ {a b c} → Gen a b → Word b c → Word a c
  push (inn e)          w = inn e ∷ w
  push (jn α I [])      w = push₀ α I w
  push (jn α I (e ∷ R)) w = push₁ α I e R w

  push₀-red : ∀ {s t m c} (α : P s t) (I : IPath t m) (w : Word m c) →
              jn α I [] ∷ w ⇒* push₀ α I w
  push₀-red α []      w = ε
  push₀-red α (e ∷ I) w = exp α e I w ◅ ε

  push₁-red : ∀ {s t m u v c} (α : P s t) (I : IPath t m) (e : E u v) (R : IPath v m)
              (w : Word u c) → jn α I (e ∷ R) ∷ w ⇒* push₁ α I e R w
  push₁-red α I e R []             = ε
  push₁-red α I e R (jn β J S ∷ w) = ε
  push₁-red α I e R (inn e′ ∷ w) with decE (_ , e) (_ , e′)
  push₁-red α I e []      (inn e′ ∷ w) | yes refl = ctr α I e [] w ◅ push₀-red α I w
  push₁-red α I e (f ∷ R) (inn e′ ∷ w) | yes refl = ctr α I e (f ∷ R) w ◅ push₁-red α I f R w
  ... | no _ = ε

  push-red : ∀ {a b c} (g : Gen a b) (w : Word b c) → g ∷ w ⇒* push g w
  push-red (inn e)          w = ε
  push-red (jn α I [])      w = push₀-red α I w
  push-red (jn α I (e ∷ R)) w = push₁-red α I e R w

  push₀-nf : ∀ {s t m c} (α : P s t) (I : IPath t m) (w : Word m c) → Normal w →
             Normal (push₀ α I w)
  push₀-nf α []      w nw = seed-nf α w nw
  push₀-nf α (e ∷ I) w nw = seed-nf α _ (innW-nf (e ∷ I) w nw)

  push₁-nf : ∀ {s t m u v c} (α : P s t) (I : IPath t m) (e : E u v) (R : IPath v m)
             (w : Word u c) → Normal w → Normal (push₁ α I e R w)
  push₁-nf α I e R []             nw _ (skip _ ())
  push₁-nf α I e R (jn β J S ∷ w) nw _ (skip _ s) = nw _ s
  push₁-nf α I e R (inn e′ ∷ w) nw with decE (_ , e) (_ , e′)
  push₁-nf α I e []      (inn e′ ∷ w) nw | yes refl = push₀-nf α I w (λ w′ s → nw _ (skip _ s))
  push₁-nf α I e (f ∷ R) (inn e′ ∷ w) nw | yes refl = push₁-nf α I f R w (λ w′ s → nw _ (skip _ s))
  ... | no ne = λ { _ (ctr _ _ _ _ _) → ne refl ; _ (skip _ s) → nw _ s }

  push-nf : ∀ {a b c} (g : Gen a b) (w : Word b c) → Normal w → Normal (push g w)
  push-nf (inn e)          w nw _ (skip _ s) = nw _ s
  push-nf (jn α I [])      w nw = push₀-nf α I w nw
  push-nf (jn α I (e ∷ R)) w nw = push₁-nf α I e R w nw

  nf : ∀ {a b} → Word a b → Word a b
  nf []      = []
  nf (g ∷ w) = push g (nf w)

  nf-red : ∀ {a b} (w : Word a b) → w ⇒* nf w
  nf-red []      = ε
  nf-red (g ∷ w) = ⇒*-skip g (nf-red w) ◅◅ push-red g (nf w)

  nf-normal : ∀ {a b} (w : Word a b) → Normal (nf w)
  nf-normal []      _ ()
  nf-normal (g ∷ w) = push-nf g (nf w) (nf-normal w)

  nf-sound : ∀ {a b} {w w′ : Word a b} → w ~ w′ → nf w ≡ nf w′
  nf-sound {w = w} {w′} p =
    nf-unique (nf-normal w) (nf-normal w′)
      (trans~ (sym~ (⇒*→~ (nf-red w))) (trans~ p (⇒*→~ (nf-red w′))))

  nf-complete : ∀ {a b} {w w′ : Word a b} → nf w ≡ nf w′ → w ~ w′
  nf-complete {w = w} {w′} eq =
    trans~ (⇒*→~ (nf-red w))
      (subst (λ z → z ~ w′) (sym eq) (sym~ (⇒*→~ (nf-red w′))))

------------------------------------------------------------------------
-- A rank makes the completed quiver acyclic.

module Rank (O : Set) (_<_ : O → O → Set)
            (<-trans : ∀ {x y z} → x < y → y < z → x < z)
            (<-irrefl : ∀ {x} → ¬ (x < x))
            (φ : V → O)
            (φE : ∀ {a b} → E a b → φ a ≡ φ b)
            (φP : ∀ {a b} → P a b → φ a < φ b)
            (acycE : ∀ {a} (p : IPath a a) → p ≡ []) where

  φI : ∀ {a b} → IPath a b → φ a ≡ φ b
  φI []      = refl
  φI (e ∷ p) = trans (φE e) (φI p)

  -- j α I R : s → u raises φ: φ u = φ m = φ t > φ s.
  φJ : ∀ {s t m u} (α : P s t) (I : IPath t m) (R : IPath u m) → φ s < φ u
  φJ α I R = subst (φ _ <_) (trans (φI I) (sym (φI R))) (φP α)

  classify : ∀ {a b} (w : Word a b) →
             (Σ (IPath a b) λ p → w ≡ innW p) ⊎ (φ a < φ b)
  classify [] = inj₁ ([] , refl)
  classify {b = b} (inn e ∷ w) with classify w
  ... | inj₁ (p , refl) = inj₁ (e ∷ p , refl)
  ... | inj₂ lt         = inj₂ (subst (λ x → x < φ b) (sym (φE e)) lt)
  classify (jn α I R ∷ w) with classify w
  ... | inj₁ (p , _) = inj₂ (subst (φ _ <_) (φI p) (φJ α I R))
  ... | inj₂ lt      = inj₂ (<-trans (φJ α I R) lt)

  acyclic : ∀ {a} (w : Word a a) → w ≡ []
  acyclic w with classify w
  ... | inj₂ lt = ⊥-elim (<-irrefl lt)
  ... | inj₁ (p , refl) with acycE p
  ...   | refl = refl

  open Acyclic Gen acyclic public

  nf-supp : ∀ {a b} {w w′ n n′ : Word a b} →
            w ⇒* n → Normal n → w′ ⇒* n′ → Normal n′ → SameSupp n n′ → w ~ w′
  nf-supp r nn r′ nn′ s with supp-inj _ _ s
  ... | refl = trans~ (⇒*→~ r) (sym~ (⇒*→~ r′))

------------------------------------------------------------------------
-- (5) for the cospan completion: functors to any category that send
-- inner arrows to identities correspond, by restriction along ι, to
-- such functors out of Path(Q). Under E = 1, (C0) and (C1) say
-- F (j α I R) is F α transported along I and R.

module Collapse (Ob : Set) (Hom : Ob → Ob → Set) where

  record KillQ : Set where
    field
      F₀  : V → Ob
      Feq : ∀ {a b} → E a b → F₀ a ≡ F₀ b
      FP  : ∀ {s t} → P s t → Hom (F₀ s) (F₀ t)

  private
    Feq* : ∀ {F₀ : V → Ob} (Feq : ∀ {a b} → E a b → F₀ a ≡ F₀ b) →
           ∀ {u t} → IPath u t → F₀ u ≡ F₀ t
    Feq* Feq []      = refl
    Feq* Feq (e ∷ R) = trans (Feq e) (Feq* Feq R)

  record KillC : Set where
    field
      F₀  : V → Ob
      Feq : ∀ {a b} → E a b → F₀ a ≡ F₀ b
      FJ  : ∀ {s t m u} → P s t → IPath t m → IPath u m → Hom (F₀ s) (F₀ u)
      F1  : ∀ {s t m u v} (α : P s t) (I : IPath t m) (e : E u v) (R : IPath v m) →
            subst (Hom (F₀ s)) (Feq e) (FJ α I (e ∷ R)) ≡ FJ α I R
      F0  : ∀ {s t m} (α : P s t) (I : IPath t m) →
            FJ α I [] ≡ subst (Hom (F₀ s)) (Feq* Feq I) (FJ α [] [])

  private
    tr-tr : ∀ {A : Set} (H : A → Set) {x y z : A} (p : x ≡ y) (r : y ≡ z) (h : H z) →
            subst H p (subst H (sym (trans p r)) h) ≡ subst H (sym r) h
    tr-tr H refl refl h = refl

    tr-back : ∀ {A : Set} (H : A → Set) {x y z : A} (p : x ≡ y) (r : y ≡ z)
              {h : H x} {k : H z} →
              subst H p h ≡ subst H (sym r) k → h ≡ subst H (sym (trans p r)) k
    tr-back H refl refl q = q

  restrict : KillC → KillQ
  restrict F = record { F₀ = F₀ ; Feq = Feq ; FP = λ α → FJ α [] [] }
    where open KillC F

  extend : KillQ → KillC
  extend F = record
    { F₀ = F₀ ; Feq = Feq
    ; FJ = λ {s} α I R → subst (Hom (F₀ s)) (sym (Feq* Feq R))
                           (subst (Hom (F₀ s)) (Feq* Feq I) (FP α))
    ; F1 = λ {s} α I e R → tr-tr (Hom (F₀ s)) (Feq e) (Feq* Feq R) _
    ; F0 = λ α I → refl }
    where open KillQ F

  restrict-extend : ∀ (F : KillQ) {s t} (α : P s t) →
                    KillQ.FP (restrict (extend F)) α ≡ KillQ.FP F α
  restrict-extend F α = refl

  extend-unique : ∀ (F : KillC) {s t m u} (α : P s t) (I : IPath t m) (R : IPath u m) →
                  KillC.FJ F α I R ≡ KillC.FJ (extend (restrict F)) α I R
  extend-unique F α I []      = KillC.F0 F α I
  extend-unique F {s} α I (e ∷ R) =
    tr-back (Hom (F₀ s)) (Feq e) (Feq* Feq R)
      (trans (F1 α I e R) (extend-unique F α I R))
    where open KillC F
