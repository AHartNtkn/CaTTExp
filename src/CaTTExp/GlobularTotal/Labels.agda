------------------------------------------------------------------------
-- F2c, toward (1′): the labels of composites.
--
--   mem-merge  : labels (merge k a b) = labels a ∪ labels b   (a, b composable)
--   mem-bd     : labels (bd β k a) ⊆ labels a                 (a well formed)
--   mem-flat   : labels (flatG J d T) = ⋃ over labels z of T of labels (J z)
--                (⊆ always; ⊇ for compatible images)
--
-- Membership is the boolean `mem` of CaTTExp.GlobularTotal.Uniq; equal
-- label sets are proved as two implications (`bool-ext`).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.Labels where

open import CaTTExp.Prelude
open import CaTTExp.GlobularFiller using (LT; lt; merge; mergeL; bd; bdL; module Lists)
open Lists using (headN; lastN; drop)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; Compat; len)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL)

------------------------------------------------------------------------
-- Booleans as propositions.

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  ∨-inl : ∀ a b → a ≡ true → (a ∨ b) ≡ true
  ∨-inl true b e = refl

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  f≢t : false ≡ true → ⊥
  f≢t ()

bool-ext : ∀ a b → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) → a ≡ b
bool-ext true  true  f g = refl
bool-ext true  false f g = sym (f refl)
bool-ext false true  f g = g refl
bool-ext false false f g = refl

------------------------------------------------------------------------
-- Lists.

private
  memL-++ : ∀ y xs ys → memL y (xs ++ ys) ≡ true → (memL y xs ≡ true) ⊎ (memL y ys ≡ true)
  memL-++ y []       ys e = inr e
  memL-++ y (x ∷ xs) ys e with ∨-split (y ==ℕ x) (memL y (xs ++ ys)) e
  ... | inl h = inl (∨-inl _ _ h)
  ... | inr h with memL-++ y xs ys h
  ...   | inl m = inl (∨-inr (y ==ℕ x) _ m)
  ...   | inr m = inr m

  memL-++l : ∀ y xs ys → memL y xs ≡ true → memL y (xs ++ ys) ≡ true
  memL-++l y []       ys ()
  memL-++l y (x ∷ xs) ys e with ∨-split (y ==ℕ x) (memL y xs) e
  ... | inl h = ∨-inl _ _ h
  ... | inr h = ∨-inr (y ==ℕ x) _ (memL-++l y xs ys h)

  memL-++r : ∀ y xs ys → memL y ys ≡ true → memL y (xs ++ ys) ≡ true
  memL-++r y []       ys e = e
  memL-++r y (x ∷ xs) ys e = ∨-inr (y ==ℕ x) _ (memL-++r y xs ys e)

  memCs-++ : ∀ y cs ds → memCs y (cs ++ ds) ≡ true → (memCs y cs ≡ true) ⊎ (memCs y ds ≡ true)
  memCs-++ y []       ds e = inr e
  memCs-++ y (c ∷ cs) ds e with ∨-split (mem y c) (memCs y (cs ++ ds)) e
  ... | inl h = inl (∨-inl _ _ h)
  ... | inr h with memCs-++ y cs ds h
  ...   | inl m = inl (∨-inr (mem y c) _ m)
  ...   | inr m = inr m

  memCs-++l : ∀ y cs ds → memCs y cs ≡ true → memCs y (cs ++ ds) ≡ true
  memCs-++l y []       ds ()
  memCs-++l y (c ∷ cs) ds e with ∨-split (mem y c) (memCs y cs) e
  ... | inl h = ∨-inl _ _ h
  ... | inr h = ∨-inr (mem y c) _ (memCs-++l y cs ds h)

  memCs-++r : ∀ y cs ds → memCs y ds ≡ true → memCs y (cs ++ ds) ≡ true
  memCs-++r y []       ds e = e
  memCs-++r y (c ∷ cs) ds e = ∨-inr (mem y c) _ (memCs-++r y cs ds e)

  memL-drop : ∀ y xs → memL y (drop 1 xs) ≡ true → memL y xs ≡ true
  memL-drop y []       e = e
  memL-drop y (x ∷ xs) e = ∨-inr (y ==ℕ x) _ e

  memL-last : ∀ x xs → memL (lastN (x ∷ xs)) (x ∷ xs) ≡ true
  memL-last x []        = ∨-inl _ _ (T-≡ (==ℕ-refl x))
  memL-last x (x' ∷ xs) = ∨-inr (lastN (x' ∷ xs) ==ℕ x) _ (memL-last x' xs)

  memL-head : ∀ x xs → memL (headN (x ∷ xs)) (x ∷ xs) ≡ true
  memL-head x xs = ∨-inl _ _ (T-≡ (==ℕ-refl x))

  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

  0≢suc : ∀ {n} → zero ≡ suc n → ⊥
  0≢suc ()

------------------------------------------------------------------------
-- Composites.

mutual
  -- labels (merge k a b) ⊆ labels a ∪ labels b, with no hypotheses
  mem-merge⊆ : ∀ k a b y → mem y (merge k a b) ≡ true → (mem y a ≡ true) ⊎ (mem y b ≡ true)
  mem-merge⊆ zero (lt osa csa) (lt osb csb) y e
    with ∨-split (memL y (osa ++ drop 1 osb)) (memCs y (csa ++ csb)) e
  ... | inl mo with memL-++ y osa (drop 1 osb) mo
  ...   | inl m = inl (∨-inl _ _ m)
  ...   | inr m = inr (∨-inl _ _ (memL-drop y osb m))
  mem-merge⊆ zero (lt osa csa) (lt osb csb) y e | inr mc with memCs-++ y csa csb mc
  ...   | inl m = inl (∨-inr (memL y osa) _ m)
  ...   | inr m = inr (∨-inr (memL y osb) _ m)
  mem-merge⊆ (suc k) (lt osa csa) (lt osb csb) y e
    with ∨-split (memL y osa) (memCs y (mergeL k csa csb)) e
  ... | inl mo = inl (∨-inl _ _ mo)
  ... | inr mc with memL-merge⊆ k csa csb y mc
  ...   | inl m = inl (∨-inr (memL y osa) _ m)
  ...   | inr m = inr (∨-inr (memL y osb) _ m)

  memL-merge⊆ : ∀ k cs ds y → memCs y (mergeL k cs ds) ≡ true →
                (memCs y cs ≡ true) ⊎ (memCs y ds ≡ true)
  memL-merge⊆ k []       ds       y ()
  memL-merge⊆ k (c ∷ cs) []       y ()
  memL-merge⊆ k (c ∷ cs) (d ∷ ds) y e with ∨-split (mem y (merge k c d)) (memCs y (mergeL k cs ds)) e
  ... | inl m with mem-merge⊆ k c d y m
  ...   | inl h = inl (∨-inl _ _ h)
  ...   | inr h = inr (∨-inl _ _ h)
  memL-merge⊆ k (c ∷ cs) (d ∷ ds) y e | inr m with memL-merge⊆ k cs ds y m
  ...   | inl h = inl (∨-inr (mem y c) _ h)
  ...   | inr h = inr (∨-inr (mem y d) _ h)

mutual
  -- labels a ⊆ labels (merge k a b), for composable a, b
  mem-merge-l : ∀ k a b y → Compat k a b → mem y a ≡ true → mem y (merge k a b) ≡ true
  mem-merge-l zero (lt osa csa) (lt osb csb) y c e with ∨-split (memL y osa) (memCs y csa) e
  ... | inl m = ∨-inl _ _ (memL-++l y osa (drop 1 osb) m)
  ... | inr m = ∨-inr (memL y (osa ++ drop 1 osb)) _ (memCs-++l y csa csb m)
  mem-merge-l (suc k) (lt osa csa) (lt osb csb) y c e with ∨-split (memL y osa) (memCs y csa) e
  ... | inl m = ∨-inl _ _ m
  ... | inr m = ∨-inr (memL y osa) _ (memL-merge-l k csa csb y (lt-injₛ c) m)

  memL-merge-l : ∀ k cs ds y → bdL true k cs ≡ bdL false k ds →
                 memCs y cs ≡ true → memCs y (mergeL k cs ds) ≡ true
  memL-merge-l k []       []       y c ()
  memL-merge-l k []       (d ∷ ds) y () e
  memL-merge-l k (c ∷ cs) []       y () e
  memL-merge-l k (c ∷ cs) (d ∷ ds) y cp e with ∨-split (mem y c) (memCs y cs) e
  ... | inl m = ∨-inl _ _ (mem-merge-l k c d y (∷-injₕ cp) m)
  ... | inr m = ∨-inr (mem y (merge k c d)) _ (memL-merge-l k cs ds y (∷-injₜ cp) m)

mutual
  -- labels b ⊆ labels (merge k a b), for composable well-formed a, b
  mem-merge-r : ∀ k a b y → WF a → Compat k a b → mem y b ≡ true → mem y (merge k a b) ≡ true
  mem-merge-r zero (lt [] csa) b y (l , _) c e = ⊥-elim (0≢suc l)
  mem-merge-r zero (lt (o ∷ osa) csa) (lt [] csb) y wa c e =
    ∨-inr (memL y ((o ∷ osa) ++ [])) _ (memCs-++r y csa csb e)
  mem-merge-r zero (lt (o ∷ osa) csa) (lt (h ∷ osb) csb) y wa c e
    with ∨-split (memL y (h ∷ osb)) (memCs y csb) e
  ... | inr m = ∨-inr (memL y ((o ∷ osa) ++ osb)) _ (memCs-++r y csa csb m)
  ... | inl m with ∨-split (y ==ℕ h) (memL y osb) m
  ...   | inr m' = ∨-inl _ _ (memL-++r y (o ∷ osa) osb m')
  ...   | inl yh with ==ℕ-sound y h (≡-T yh)
  ...     | refl = ∨-inl _ _ (memL-++l y (o ∷ osa) osb
                    (subst (λ z → memL z (o ∷ osa) ≡ true) (∷-injₕ (lt-injₒ c)) (memL-last o osa)))
  mem-merge-r (suc k) (lt osa csa) (lt osb csb) y wa c e with lt-injₒ c
  ... | refl with ∨-split (memL y osa) (memCs y csb) e
  ...   | inl m = ∨-inl _ _ m
  ...   | inr m = ∨-inr (memL y osa) _ (memL-merge-r k csa csb y (snd wa) (lt-injₛ c) m)

  memL-merge-r : ∀ k cs ds y → WFs cs → bdL true k cs ≡ bdL false k ds →
                 memCs y ds ≡ true → memCs y (mergeL k cs ds) ≡ true
  memL-merge-r k []       []       y w c ()
  memL-merge-r k []       (d ∷ ds) y w () e
  memL-merge-r k (c ∷ cs) []       y w () e
  memL-merge-r k (c ∷ cs) (d ∷ ds) y (wc , ws) cp e with ∨-split (mem y d) (memCs y ds) e
  ... | inl m = ∨-inl _ _ (mem-merge-r k c d y wc (∷-injₕ cp) m)
  ... | inr m = ∨-inr (mem y (merge k c d)) _ (memL-merge-r k cs ds y ws (∷-injₜ cp) m)

------------------------------------------------------------------------
-- Boundaries.

mutual
  mem-bd : ∀ β k a y → WF a → mem y (bd β k a) ≡ true → mem y a ≡ true
  mem-bd false zero    (lt []       cs) y (l , _) e = ⊥-elim (0≢suc l)
  mem-bd true  zero    (lt []       cs) y (l , _) e = ⊥-elim (0≢suc l)
  mem-bd false zero    (lt (o ∷ os) cs) y w e with ∨-split (memL y (o ∷ [])) false e
  ... | inr ()
  ... | inl h' with ∨-split (y ==ℕ o) false h'
  ...   | inl h = ∨-inl _ _ (∨-inl _ _ h)
  ...   | inr ()
  mem-bd true  zero    (lt (o ∷ os) cs) y w e with ∨-split (memL y (lastN (o ∷ os) ∷ [])) false e
  ... | inr ()
  ... | inl h' with ∨-split (y ==ℕ lastN (o ∷ os)) false h'
  ...   | inr ()
  ...   | inl h with ==ℕ-sound y _ (≡-T h)
  ...     | refl = ∨-inl _ _ (memL-last o os)
  mem-bd false (suc k) (lt os cs) y (_ , w) e with ∨-split (memL y os) (memCs y (bdL false k cs)) e
  ... | inl m = ∨-inl _ _ m
  ... | inr m = ∨-inr (memL y os) _ (memL-bd false k cs y w m)
  mem-bd true  (suc k) (lt os cs) y (_ , w) e with ∨-split (memL y os) (memCs y (bdL true k cs)) e
  ... | inl m = ∨-inl _ _ m
  ... | inr m = ∨-inr (memL y os) _ (memL-bd true k cs y w m)

  memL-bd : ∀ β k cs y → WFs cs → memCs y (bdL β k cs) ≡ true → memCs y cs ≡ true
  memL-bd β k []       y _        ()
  memL-bd β k (c ∷ cs) y (wc , w) e with ∨-split (mem y (bd β k c)) (memCs y (bdL β k cs)) e
  ... | inl m = ∨-inl _ _ (mem-bd β k c y wc m)
  ... | inr m = ∨-inr (mem y c) _ (memL-bd β k cs y w m)

------------------------------------------------------------------------
-- Composites of diagrams.

open import CaTTExp.GlobularTotal.FlatBd

-- y is a label of the image of z.
memI : (Nat → Maybe LT) → Nat → Nat → Bool
memI J y z with J z
... | just a  = mem y a
... | nothing = false

anyL : (Nat → Bool) → List Nat → Bool
anyL f []       = false
anyL f (x ∷ xs) = f x ∨ anyL f xs

mutual
  anyLab : (Nat → Bool) → LT → Bool
  anyLab f (lt os cs) = anyL f os ∨ anyCs f cs

  anyCs : (Nat → Bool) → List LT → Bool
  anyCs f []       = false
  anyCs f (c ∷ cs) = anyLab f c ∨ anyCs f cs

private
  memI-just : ∀ J y z a → J z ≡ just a → memI J y z ≡ mem y a
  memI-just J y z a e with J z
  memI-just J y z a refl | .(just a) = refl

  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ x → (m ≡ just x) × (f x ≡ just b)
  bind-inv nothing  f ()
  bind-inv (just x) f e = x , refl , e

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

module _ (J : Nat → Maybe LT) where

  -- labels (flat T) ⊆ ⋃ labels of images
  mutual
    flat⊆ : ∀ d T x y → flatG J d T ≡ just x → mem y x ≡ true → anyLab (memI J y) T ≡ true
    flat⊆ d (lt os (c ∷ cs))      x y e m = ∨-inr (anyL _ os) _ (flatL⊆ d c cs x y e m)
    flat⊆ d (lt [] [])            x y () m
    flat⊆ d (lt (z ∷ []) [])      x y e m =
      ∨-inl _ _ (∨-inl _ _ (trans (memI-just J y z x e) m))
    flat⊆ d (lt (z ∷ z' ∷ zs) []) x y () m

    flatL⊆ : ∀ d c cs x y → flatGL J d c cs ≡ just x → mem y x ≡ true → anyCs (memI J y) (c ∷ cs) ≡ true
    flatL⊆ d c []        x y e m = ∨-inl _ _ (flat⊆ (suc d) c x y e m)
    flatL⊆ d c (c' ∷ cs) x y e m
      with bind-inv (flatG J (suc d) c) _ e
    ... | a , ea , e'
      with bind-inv (flatGL J d c' cs) _ e'
    ... | b , eb , refl with mem-merge⊆ d a b y m
    ...   | inl ma = ∨-inl _ _ (flat⊆ (suc d) c a y ea ma)
    ...   | inr mb = ∨-inr (anyLab _ c) _ (flatL⊆ d c' cs b y eb mb)

  -- ⋃ labels of images ⊆ labels (flat T), for compatible images
  mutual
    flat⊇ : ∀ d P T x y → Good J d P T → flatG J d T ≡ just x →
            anyLab (memI J y) T ≡ true → mem y x ≡ true
    flat⊇ d P (lt []            [])       x y (_ , ()) e m
    flat⊇ d P (lt (z ∷ [])      [])       x y _ e m
      with ∨-split (anyL (memI J y) (z ∷ [])) false m
    ... | inr ()
    ... | inl m' with ∨-split (memI J y z) false m'
    ...   | inr ()
    ...   | inl mz = trans (sym (memI-just J y z x e)) mz
    flat⊇ d P (lt (z ∷ z' ∷ zs) [])       x y (_ , ()) e m
    flat⊇ d P (lt []            (c ∷ cs)) x y (_ , ()) e m
    flat⊇ d P (lt (o ∷ os)      (c ∷ cs)) x y (_ , g) e m = flatL⊇ d o os c cs x y g e m

    flatL⊇ : ∀ d o os c cs x y → GoodCs J d (o ∷ os) (c ∷ cs) → flatGL J d c cs ≡ just x →
             (anyL (memI J y) (o ∷ os) ∨ anyCs (memI J y) (c ∷ cs)) ≡ true → mem y x ≡ true
    flatL⊇ d o []               c cs        x y () e m
    flatL⊇ d o (o' ∷ [])        c []        x y (gc , _) e m
      with flat-bd J (suc d) (Par J d o o') c x gc e | flat-ends J d o o' c x gc e
    ... | wx , _ | eo , eo'
      with ∨-split (anyL (memI J y) (o ∷ o' ∷ [])) (anyCs (memI J y) (c ∷ [])) m
    ... | inr mc with ∨-split (anyLab (memI J y) c) false mc
    ...   | inl mc' = flat⊇ (suc d) (Par J d o o') c x y gc e mc'
    ...   | inr ()
    flatL⊇ d o (o' ∷ [])        c []        x y (gc , _) e m | wx , _ | eo , eo' | inl mo
      with ∨-split (memI J y o) _ mo
    ... | inl m₁ = mem-bd false d x y wx (trans (sym (memI-just J y o _ eo)) m₁)
    ... | inr mo' with ∨-split (memI J y o') false mo'
    ...   | inl m₂ = mem-bd true d x y wx (trans (sym (memI-just J y o' _ eo')) m₂)
    ...   | inr ()
    flatL⊇ d o (o' ∷ o'' ∷ os)  c []        x y (_ , ()) e m
    flatL⊇ d o (o' ∷ [])        c (c' ∷ cs) x y (_ , ()) e m
    flatL⊇ d o (o' ∷ o'' ∷ os)  c (c' ∷ cs) x y (gc , gs) e m
      with bind-inv (flatG J (suc d) c) _ e
    ... | a , ea , e'
      with bind-inv (flatGL J d c' cs) _ e'
    ... | b , eb , refl
      with flat-bd J (suc d) (Par J d o o') c a gc ea | flat-ends J d o o' c a gc ea
         | flatL-bd J d o' (o'' ∷ os) c' cs b gs eb
    ... | wa , _ | ea₀ , ea₁ | wb , _ , eb₀ , _ = go
      where
      cp : Compat d a b
      cp = just-inj (trans (sym ea₁) eb₀)

      inA : mem y a ≡ true → mem y (merge d a b) ≡ true
      inA = mem-merge-l d a b y cp

      inB : mem y b ≡ true → mem y (merge d a b) ≡ true
      inB = mem-merge-r d a b y wa cp

      go : mem y (merge d a b) ≡ true
      go with ∨-split (anyL (memI J y) (o ∷ o' ∷ o'' ∷ os)) (anyCs (memI J y) (c ∷ c' ∷ cs)) m
      ... | inl mo with ∨-split (memI J y o) _ mo
      ...   | inl m₁ = inA (mem-bd false d a y wa (trans (sym (memI-just J y o _ ea₀)) m₁))
      ...   | inr mrest = inB (flatL⊇ d o' (o'' ∷ os) c' cs b y gs eb (∨-inl _ _ mrest))
      go | inr mc with ∨-split (anyLab (memI J y) c) _ mc
      ...   | inl m₁ = inA (flat⊇ (suc d) (Par J d o o') c a y gc ea m₁)
      ...   | inr mrest = inB (flatL⊇ d o' (o'' ∷ os) c' cs b y gs eb
                                 (∨-inr (anyL (memI J y) (o' ∷ o'' ∷ os)) _ mrest))
