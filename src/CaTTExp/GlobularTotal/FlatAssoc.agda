------------------------------------------------------------------------
-- F2c, toward lemma 1b: substitution into composites is associative.
--
-- Let I give each label of a tree T an image tree, and J give each
-- label of those image trees a further image. Writing I;J for
-- y ↦ I y >>= flatG J 0 (substitute, then substitute again),
--
--   flat-assoc : flatG I d T ≡ just a  ⟹  flatG (I;J) d T ≡ flatG J 0 a
--
-- given that T is compatible for I and every image of I is compatible
-- for J. On the way: compatibility is closed under composition
-- (good-merge) and under flat (good-flat), and flat is defined on
-- compatible trees (flat-def).
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.FlatAssoc where

open import CaTTExp.Prelude
open import CaTTExp.GlobularFiller using (LT; lt; merge; mergeL; bd; bdL; module Lists)
open Lists using (headN; lastN; drop)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; Compat; len)
open import CaTTExp.GlobularTotal.FlatBd
open import CaTTExp.GlobularTotal.MergeLaws
open import CaTTExp.GlobularTotal.FlatMerge

private
  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ x → (m ≡ just x) × (f x ≡ just b)
  bind-inv nothing  f ()
  bind-inv (just x) f e = x , refl , e

  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

  Top : LT → Set
  Top _ = ⊤

module _ (J : Nat → Maybe LT) where

  ----------------------------------------------------------------------
  -- Compatibility is closed under composition.

  private
    all-++ : ∀ {P : Nat → Set} xs ys → AllL J P xs → AllL J P ys → AllL J P (xs ++ ys)
    all-++ []       ys _        q = q
    all-++ (x ∷ xs) ys (p , ps) q = p , all-++ xs ys ps q

    all-drop1 : ∀ {P : Nat → Set} xs → AllL J P xs → AllL J P (drop 1 xs)
    all-drop1 []       _        = tt
    all-drop1 (x ∷ xs) (_ , ps) = ps

  goodCs-++ : ∀ e osa csa osb csb → GoodCs J e osa csa → GoodCs J e osb csb →
              lastN osa ≡ headN osb → GoodCs J e (osa ++ drop 1 osb) (csa ++ csb)
  goodCs-++ e []            csa       osb csb () gb l
  goodCs-++ e (o ∷ [])      []        []  csb ga () l
  goodCs-++ e (o ∷ [])      []        (o' ∷ osb) csb ga gb refl = gb
  goodCs-++ e (o ∷ [])      (c ∷ csa) osb csb () gb l
  goodCs-++ e (o ∷ o' ∷ os) []        osb csb () gb l
  goodCs-++ e (o ∷ o' ∷ os) (c ∷ csa) osb csb (gc , ga) gb l =
    gc , goodCs-++ e (o' ∷ os) csa osb csb ga gb l

  mutual
    good-merge : ∀ e k P a b → Good J e P a → Good J e P b → Compat k a b →
                 Good J e P (merge k a b)
    good-merge e zero P (lt (o ∷ []) []) b ga gb c =
      subst (Good J e P) (sym (merge-unitl zero (lt (o ∷ []) []) b refl (good-wf J e P b gb) c)) gb
    good-merge e zero P (lt [] []) b (_ , ()) gb c
    good-merge e zero P (lt (o ∷ o' ∷ os) []) b (_ , ()) gb c
    good-merge e zero P a (lt (o ∷ []) []) ga gb c =
      subst (Good J e P) (sym (merge-unitr zero a (lt (o ∷ []) []) refl c)) ga
    good-merge e zero P a (lt [] []) ga (_ , ()) c
    good-merge e zero P a (lt (o ∷ o' ∷ os) []) ga (_ , ()) c
    good-merge e zero P (lt osa (ca ∷ csa)) (lt osb (cb ∷ csb)) (oa , ga) (ob , gb) c =
      all-++ osa (drop 1 osb) oa (all-drop1 osb ob) ,
      goodCs-++ e osa (ca ∷ csa) osb (cb ∷ csb) ga gb (∷-injₕ (lt-injₒ c))
    good-merge e (suc k) P (lt osa csa) (lt osb csb) (oa , ga) (ob , gb) c
      with lt-injₒ c
    ... | refl = oa , goodCs-merge e k osa csa csb ga gb (lt-injₛ c)

    goodCs-merge : ∀ e k os cs ds → GoodCs J e os cs → GoodCs J e os ds →
                   bdL true k cs ≡ bdL false k ds → GoodCs J e os (mergeL k cs ds)
    goodCs-merge e k []            cs       ds       () gb c
    goodCs-merge e k (o ∷ [])      []       []       ga gb c = tt
    goodCs-merge e k (o ∷ [])      (x ∷ cs) ds       () gb c
    goodCs-merge e k (o ∷ [])      []       (x ∷ ds) ga () c
    goodCs-merge e k (o ∷ o' ∷ os) []       ds       () gb c
    goodCs-merge e k (o ∷ o' ∷ os) (x ∷ cs) []       ga () c
    goodCs-merge e k (o ∷ o' ∷ os) (x ∷ cs) (y ∷ ds) (gx , ga) (gy , gb) c =
      good-merge (suc e) k (Par J e o o') x y gx gy (∷-injₕ c) ,
      goodCs-merge e k (o' ∷ os) cs ds ga gb (∷-injₜ c)

  ----------------------------------------------------------------------
  -- flat is defined on compatible trees.

  mutual
    flat-def : ∀ e P T → Good J e P T → Σ LT λ x → flatG J e T ≡ just x
    flat-def e P (lt []               [])       (_ , ())
    flat-def e P (lt (o ∷ [])         [])       (((x , ex , _) , _) , _) = x , ex
    flat-def e P (lt (o ∷ o' ∷ os)    [])       (_ , ())
    flat-def e P (lt []               (c ∷ cs)) (_ , ())
    flat-def e P (lt (o ∷ os)         (c ∷ cs)) (_ , g) = flatL-def e o os c cs g

    flatL-def : ∀ e o os c cs → GoodCs J e (o ∷ os) (c ∷ cs) → Σ LT λ x → flatGL J e c cs ≡ just x
    flatL-def e o []              c cs       ()
    flatL-def e o (o' ∷ [])       c []       (gc , _) = flat-def (suc e) (Par J e o o') c gc
    flatL-def e o (o' ∷ o'' ∷ os) c []       (_ , ())
    flatL-def e o (o' ∷ [])       c (c' ∷ cs) (_ , ())
    flatL-def e o (o' ∷ o'' ∷ os) c (c' ∷ cs) (gc , g)
      with flat-def (suc e) (Par J e o o') c gc | flatL-def e o' (o'' ∷ os) c' cs g
    ... | x , ex | y , ey rewrite ex | ey = merge e x y , refl

------------------------------------------------------------------------
-- Substituting twice.

module _ (I J : Nat → Maybe LT)
         (HI : ∀ y a → I y ≡ just a → Good J 0 Top a) where

  I∘J : Nat → Maybe LT
  I∘J y = I y >>= flatG J 0

  mutual
    -- The composite of a compatible tree is compatible.
    good-flat : ∀ d P T a → Good I d P T → flatG I d T ≡ just a → Good J 0 Top a
    good-flat d P (lt []            [])       a (_ , ()) e
    good-flat d P (lt (y ∷ [])      [])       a _ e = HI y a e
    good-flat d P (lt (y ∷ y' ∷ ys) [])       a (_ , ()) e
    good-flat d P (lt []            (c ∷ cs)) a (_ , ()) e
    good-flat d P (lt (o ∷ os)      (c ∷ cs)) a (_ , g) e = goodL-flat d o os c cs a g e

    goodL-flat : ∀ d o os c cs a → GoodCs I d (o ∷ os) (c ∷ cs) → flatGL I d c cs ≡ just a →
                 Good J 0 Top a
    goodL-flat d o []              c cs        a () e
    goodL-flat d o (o' ∷ [])       c []        a (gc , _) e = good-flat (suc d) (Par I d o o') c a gc e
    goodL-flat d o (o' ∷ o'' ∷ os) c []        a (_ , ()) e
    goodL-flat d o (o' ∷ [])       c (c' ∷ cs) a (_ , ()) e
    goodL-flat d o (o' ∷ o'' ∷ os) c (c' ∷ cs) a (gc , gs) e
      with bind-inv (flatG I (suc d) c) _ e
    ... | a₁ , e₁ , e'
      with bind-inv (flatGL I d c' cs) _ e'
    ... | b , e₂ , refl =
      good-merge J 0 d Top a₁ b
        (good-flat (suc d) (Par I d o o') c a₁ gc e₁)
        (goodL-flat d o' (o'' ∷ os) c' cs b gs e₂)
        (just-inj (trans (sym (snd (flat-ends I d o o' c a₁ gc e₁)))
                         (fst (snd (snd (flatL-bd I d o' (o'' ∷ os) c' cs b gs e₂))))))

  mutual
    flat-assoc : ∀ d P T a → Good I d P T → flatG I d T ≡ just a →
                 flatG I∘J d T ≡ flatG J 0 a
    flat-assoc d P (lt []            [])       a (_ , ()) e
    flat-assoc d P (lt (y ∷ [])      [])       a _ e rewrite e = refl
    flat-assoc d P (lt (y ∷ y' ∷ ys) [])       a (_ , ()) e
    flat-assoc d P (lt []            (c ∷ cs)) a (_ , ()) e
    flat-assoc d P (lt (o ∷ os)      (c ∷ cs)) a (_ , g) e = flatL-assoc d o os c cs a g e

    flatL-assoc : ∀ d o os c cs a → GoodCs I d (o ∷ os) (c ∷ cs) → flatGL I d c cs ≡ just a →
                  flatGL I∘J d c cs ≡ flatG J 0 a
    flatL-assoc d o []              c cs        a () e
    flatL-assoc d o (o' ∷ [])       c []        a (gc , _) e = flat-assoc (suc d) (Par I d o o') c a gc e
    flatL-assoc d o (o' ∷ o'' ∷ os) c []        a (_ , ()) e
    flatL-assoc d o (o' ∷ [])       c (c' ∷ cs) a (_ , ()) e
    flatL-assoc d o (o' ∷ o'' ∷ os) c (c' ∷ cs) a (gc , gs) e
      with bind-inv (flatG I (suc d) c) _ e
    ... | a₁ , e₁ , e'
      with bind-inv (flatGL I d c' cs) _ e'
    ... | b , e₂ , refl
      with good-flat (suc d) (Par I d o o') c a₁ gc e₁ | goodL-flat d o' (o'' ∷ os) c' cs b gs e₂
    ... | g₁ | g₂
      with flat-def J 0 Top a₁ g₁ | flat-def J 0 Top b g₂
    ... | x , ex | y , ey
      rewrite flat-assoc (suc d) (Par I d o o') c a₁ gc e₁
            | flatL-assoc d o' (o'' ∷ os) c' cs b gs e₂
            | ex | ey
      = sym (flat-merge J 0 d Top a₁ b x y g₁ g₂ cp ex ey)
      where
      cp : Compat d a₁ b
      cp = just-inj (trans (sym (snd (flat-ends I d o o' c a₁ gc e₁)))
                           (fst (snd (snd (flatL-bd I d o' (o'' ∷ os) c' cs b gs e₂)))))
