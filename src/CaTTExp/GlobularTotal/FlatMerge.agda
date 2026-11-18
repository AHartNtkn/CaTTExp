------------------------------------------------------------------------
-- F2c, toward lemma 1b: the composite of a diagram of composites.
--
-- flatG J replaces each locally maximal label y of a labelled tree by
-- the image J y and composes. If a and b are k-composable trees with
-- compatible images (FlatBd.Good), then
--
--   flat-merge : flatG J e (merge k a b) ≡ just (merge (e + k) x y)
--
-- where x, y are the composites of a and b: substituting into a
-- composite gives the composite of the substitutions, i.e. the strict
-- image of a substitution is a functor on labelled trees. The proof
-- uses the laws of CaTTExp.GlobularTotal.MergeLaws (associativity for
-- k = 0, interchange for k > 0, units at the leaves) and the boundary
-- computation of CaTTExp.GlobularTotal.FlatBd.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.FlatMerge where

open import CaTTExp.Prelude
open import CaTTExp.GlobularFiller using (LT; lt; merge; mergeL; bd; bdL; module Lists)
open Lists using (headN; lastN; drop)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; Compat; len)
open import CaTTExp.GlobularTotal.FlatBd
open import CaTTExp.GlobularTotal.MergeLaws

private
  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ x → (m ≡ just x) × (f x ≡ just b)
  bind-inv nothing  f ()
  bind-inv (just x) f e = x , refl , e

  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {a} {A : Set a} {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
  ∷-injₜ refl = refl

module _ (J : Nat → Maybe LT) where

  ----------------------------------------------------------------------
  -- Compatible trees are well formed.

  mutual
    good-wf : ∀ e P T → Good J e P T → WF T
    good-wf e P (lt os cs) (_ , g) = goodCs-wf e os cs g

    goodCs-wf : ∀ e os cs → GoodCs J e os cs → (len os ≡ suc (len cs)) × WFs cs
    goodCs-wf e []            cs       ()
    goodCs-wf e (o ∷ [])      []       g = refl , tt
    goodCs-wf e (o ∷ [])      (c ∷ cs) ()
    goodCs-wf e (o ∷ o' ∷ os) []       ()
    goodCs-wf e (o ∷ o' ∷ os) (c ∷ cs) (gc , g) with goodCs-wf e (o' ∷ os) cs g
    ... | l , w = cong suc l , good-wf (suc e) _ c gc , w

  ----------------------------------------------------------------------
  -- k = 0: composing two branch lists is appending them.

  fold-++ : ∀ e o os c cs d ds u v → GoodCs J e (o ∷ os) (c ∷ cs) →
            flatGL J e c cs ≡ just u → flatGL J e d ds ≡ just v →
            flatGL J e c (cs ++ (d ∷ ds)) ≡ just (merge e u v)
  fold-++ e o os c [] d ds u v g eu ev rewrite eu | ev = refl
  fold-++ e o []            c (c' ∷ cs) d ds u v () eu ev
  fold-++ e o (o' ∷ [])     c (c' ∷ cs) d ds u v (_ , ()) eu ev
  fold-++ e o (o' ∷ o'' ∷ os) c (c' ∷ cs) d ds u v (gc , gs) eu ev
    with bind-inv (flatG J (suc e) c) _ eu
  ... | a₁ , e₁ , eu'
    with bind-inv (flatGL J e c' cs) _ eu'
  ... | u' , e₂ , refl
    rewrite e₁ | fold-++ e o' (o'' ∷ os) c' cs d ds u' v gs e₂ ev
    = cong just (sym (merge-assoc e a₁ u' v (fst (flatL-bd J e o' (o'' ∷ os) c' cs u' gs e₂))))

  ----------------------------------------------------------------------
  -- The theorem.

  mutual
    flat-merge : ∀ e k P a b x y → Good J e P a → Good J e P b → Compat k a b →
                 flatG J e a ≡ just x → flatG J e b ≡ just y →
                 flatG J e (merge k a b) ≡ just (merge (e + k) x y)
    -- k = 0, a a single cell: a is a left unit
    flat-merge e zero P (lt (o ∷ []) []) b x y ga gb c ex ey
      with ga | flat-bd J e P b y gb ey
    ... | ((x' , ex' , wx , dx , _) , _) , _ | wy , comb with trans (sym ex') ex
    ... | refl =
      trans (cong (flatG J e) (merge-unitl zero (lt (o ∷ []) []) b refl (good-wf e P b gb) c))
            (trans ey (cong just (sym (merge-unitl (e + 0) x y (dx false 0) wy cxy))))
      where
      cxy : Compat (e + 0) x y
      cxy = trans (dx true 0)
                  (just-inj (trans (sym ex') (trans (cong (flatG J e) c) (comb false 0))))
    flat-merge e zero P (lt [] []) b x y (_ , ()) gb c ex ey
    flat-merge e zero P (lt (o ∷ o' ∷ os) []) b x y (_ , ()) gb c ex ey
    -- k = 0, b a single cell: b is a right unit
    flat-merge e zero P (lt osa (ca ∷ csa)) (lt (o ∷ []) []) x y ga gb c ex ey
      with gb | flat-bd J e P (lt osa (ca ∷ csa)) x ga ex
    ... | ((y' , ey' , wy , dy , _) , _) , _ | wx , coma with trans (sym ey') ey
    ... | refl =
      trans (cong (flatG J e) (merge-unitr zero (lt osa (ca ∷ csa)) (lt (o ∷ []) []) refl c))
            (trans ex (cong just (sym (merge-unitr (e + 0) x y (dy true 0) cxy))))
      where
      cxy : Compat (e + 0) x y
      cxy = sym (trans (dy false 0)
                  (just-inj (trans (sym ey') (trans (cong (flatG J e) (sym c)) (coma true 0)))))
    flat-merge e zero P (lt osa (ca ∷ csa)) (lt [] []) x y ga (_ , ()) c ex ey
    flat-merge e zero P (lt osa (ca ∷ csa)) (lt (o ∷ o' ∷ os) []) x y ga (_ , ()) c ex ey
    -- k = 0, both proper: append the branch lists
    flat-merge e zero P (lt [] (ca ∷ csa)) (lt osb (cb ∷ csb)) x y (_ , ()) gb c ex ey
    flat-merge e zero P (lt (o ∷ osa) (ca ∷ csa)) (lt osb (cb ∷ csb)) x y (_ , ga) gb c ex ey
      rewrite fold-++ e o osa ca csa cb csb x y ga ex ey | +-zero e = refl
    -- k > 0: compose branchwise, then interchange
    flat-merge e (suc k) P (lt osa csa) (lt osb csb) x y ga gb c ex ey
      with lt-injₒ c
    flat-merge e (suc k) P (lt [] []) (lt _ []) x y (_ , ()) gb c ex ey | refl
    flat-merge e (suc k) P (lt (o ∷ o' ∷ os) []) (lt _ []) x y (_ , ()) gb c ex ey | refl
    flat-merge e (suc k) P (lt (o ∷ []) []) (lt _ []) x y (((x' , ex' , wx , dx , _) , _) , _) gb c ex ey | refl
      with trans (sym ex') ex | trans (sym ex') ey
    ... | refl | refl = trans ex' (
      cong just (sym (merge-unitl (e + suc k) x x (dx false (suc k)) wx
                       (trans (dx true (suc k)) (sym (dx false (suc k)))))))
    flat-merge e (suc k) P (lt osa []) (lt osb (cb ∷ csb)) x y ga gb c ex ey | refl
      with lt-injₛ c
    ... | ()
    flat-merge e (suc k) P (lt osa (ca ∷ csa)) (lt osb []) x y ga gb c ex ey | refl
      with lt-injₛ c
    ... | ()
    flat-merge e (suc k) P (lt [] (ca ∷ csa)) (lt osb (cb ∷ csb)) x y (_ , ()) gb c ex ey | refl
    flat-merge e (suc k) P (lt (o ∷ os) (ca ∷ csa)) (lt _ (cb ∷ csb)) x y (_ , ga) (_ , gb) c ex ey | refl =
      flatL-merge e k o os ca csa cb csb x y ga gb (lt-injₛ c) ex ey

    flatL-merge : ∀ e k o os ca csa cb csb X Y →
                  GoodCs J e (o ∷ os) (ca ∷ csa) → GoodCs J e (o ∷ os) (cb ∷ csb) →
                  bdL true k (ca ∷ csa) ≡ bdL false k (cb ∷ csb) →
                  flatGL J e ca csa ≡ just X → flatGL J e cb csb ≡ just Y →
                  flatGL J e (merge k ca cb) (mergeL k csa csb) ≡ just (merge (e + suc k) X Y)
    flatL-merge e k o []       ca csa cb csb X Y () gb c ex ey
    flatL-merge e k o (o' ∷ os) ca [] cb [] X Y (ga , _) (gb , _) c ex ey
      rewrite +-suc e k = flat-merge (suc e) k (Par J e o o') ca cb X Y ga gb (∷-injₕ c) ex ey
    flatL-merge e k o (o' ∷ os) ca [] cb (d ∷ csb) X Y ga gb c ex ey with ∷-injₜ c
    ... | ()
    flatL-merge e k o (o' ∷ os) ca (d ∷ csa) cb [] X Y ga gb c ex ey with ∷-injₜ c
    ... | ()
    flatL-merge e k o (o' ∷ []) ca (c' ∷ csa) cb (d' ∷ csb) X Y (_ , ()) gb c ex ey
    flatL-merge e k o (o' ∷ o'' ∷ os) ca (c' ∷ csa) cb (d' ∷ csb) X Y
                (gca , gas) (gcb , gbs) c ex ey
      with bind-inv (flatG J (suc e) ca) _ ex | bind-inv (flatG J (suc e) cb) _ ey
    ... | xa , exa , ex' | ya , eya , ey'
      with bind-inv (flatGL J e c' csa) _ ex' | bind-inv (flatGL J e d' csb) _ ey'
    ... | Xr , eXr , refl | Yr , eYr , refl
      rewrite flat-merge (suc e) k (Par J e o o') ca cb xa ya gca gcb (∷-injₕ c) exa eya
            | flatL-merge e k o' (o'' ∷ os) c' csa d' csb Xr Yr gas gbs (∷-injₜ c) eXr eYr
            | +-suc e k
      = cong just (sym (merge-xch e (suc (e + k)) xa Xr ya Yr (<-+suc′ e k) cxy))
      where
      <-+suc′ : ∀ e k → T (e <ℕ suc (e + k))
      <-+suc′ zero    k = tt
      <-+suc′ (suc e) k = <-+suc′ e k

      cxy : Compat (suc (e + k)) xa ya
      cxy = just-inj (trans (sym (snd (flat-bd J (suc e) (Par J e o o') ca xa gca exa) true k))
                     (trans (cong (flatG J (suc e)) (∷-injₕ c))
                            (snd (flat-bd J (suc e) (Par J e o o') cb ya gcb eya) false k)))
