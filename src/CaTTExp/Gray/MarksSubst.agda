------------------------------------------------------------------------
-- Substitution preserves the mark judgments of CaTTExp.Gray.Marks
-- (notes/invertibility-markings.md §1.2: "a substitution must send every
-- marked variable to a term with the same mark"; §2: "substitution
-- preserves every judgment").
--
--   Γ ⊢ t ∶ A,  Δ ⊢ σ ∶ Γ,  σ respects the marks
--     ⇒  Γ ⊢ t m ⇒ Δ ⊢ t[σ] m     for m = inv, ps, ps*
--
-- "σ respects the marks" (`Resp N`): a variable marked inv (ps) goes to
-- a term judged inv (ps) at every fuel ≥ N, and an object marked
-- grpd_k goes to a variable marked grpd_k' with k' ≤ k.
--
-- Fuel. `judge k` descends k levels into boundaries for (PS*). The
-- theorem is stated with a shift: a judgment of t at fuel k gives the
-- same judgment of t[σ] at fuel k + N, where N is the fuel at which
-- the images of the marked variables have their marks. `judgeT` uses
-- fuel = dimension; that this is enough for derivable terms (fuel
-- stability) is argued, not proved.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.MarksSubst (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Typing 𝕊
open import CaTTExp.Gray.Marks 𝕊
open import CaTTExp.Subst 𝕊 graySide

------------------------------------------------------------------------
-- Boolean implication.

_⇒B_ : Bool → Bool → Set
a ⇒B b = T a → T b

private
  ∨-mono : ∀ {a b c d} → a ⇒B c → b ⇒B d → (a ∨ b) ⇒B (c ∨ d)
  ∨-mono {true}  {c = true}  f g p = tt
  ∨-mono {true}  {c = false} f g p = ⊥-elim (f tt)
  ∨-mono {false} {c = true}  f g p = tt
  ∨-mono {false} {c = false} f g p = g p

  ∧-mono : ∀ {a b c d} → a ⇒B c → b ⇒B d → (a ∧ b) ⇒B (c ∧ d)
  ∧-mono {true} {c = true}  f g p = g p
  ∧-mono {true} {c = false} f g p = ⊥-elim (f tt)
  ∧-mono {false} f g ()

  ∨-l : ∀ {a b} → T a → T (a ∨ b)
  ∨-l {true} _ = tt

  ∨-r : ∀ {a b} → T b → T (a ∨ b)
  ∨-r {true}  _ = tt
  ∨-r {false} p = p

  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

IP≤ : IP → IP → Set
IP≤ x y = (jinv x ⇒B jinv y) × (jps x ⇒B jps y) × (jpss x ⇒B jpss y)

data Pw {A : Set} (R : A → A → Set) : List A → List A → Set where
  []  : Pw R [] []
  _∷_ : ∀ {x y xs ys} → R x y → Pw R xs ys → Pw R (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Monotonicity of the rule premises in the judgments of γ.

private
  pw-++ : ∀ {A R} {xs ys xs' ys' : List A} → Pw R xs ys → Pw R xs' ys' → Pw R (xs ++ xs') (ys ++ ys')
  pw-++ []       q = q
  pw-++ (r ∷ p) q = r ∷ pw-++ p q

  nth-mono : ∀ w {xs ys} → Pw IP≤ xs ys → IP≤ (nthIP w xs) (nthIP w ys)
  nth-mono w       []       = (λ p → p) , (λ p → p) , (λ p → p)
  nth-mono zero    (r ∷ _)  = r
  nth-mono (suc w) (_ ∷ p)  = nth-mono w p

  FR : Nat × IP → Nat × IP → Set
  FR a b = (fst a ≡ fst b) × IP≤ (snd a) (snd b)

  facOf-pw : ∀ cs g {xs ys} → Pw IP≤ xs ys → Pw FR (facOf cs xs g) (facOf cs ys g)
  facOf-pw cs []       p = []
  facOf-pw cs (w ∷ ws) p = (refl , nth-mono w p) ∷ facOf-pw cs ws p

  any-mono : ∀ {A : Set} {R : A → A → Set} {p q : A → Bool} {xs ys} →
             (∀ {a b} → R a b → p a ⇒B q b) → Pw R xs ys → any p xs ⇒B any q ys
  any-mono f []       ()
  any-mono f (r ∷ rs) = ∨-mono (f r) (any-mono f rs)

  all-mono : ∀ {A : Set} {R : A → A → Set} {p q : A → Bool} {xs ys} →
             (∀ {a b} → R a b → p a ⇒B q b) → Pw R xs ys → all p xs ⇒B all q ys
  all-mono f []       _ = tt
  all-mono f (r ∷ rs)   = ∧-mono (f r) (all-mono f rs)

  all-same : ∀ {A : Set} {p q : A → Bool} (xs : List A) →
             (∀ x → p x ⇒B q x) → all p xs ⇒B all q xs
  all-same []       f _ = tt
  all-same (x ∷ xs) f   = ∧-mono (f x) (all-same xs f)

  psFac-mono : ∀ seen {xs ys} → Pw FR xs ys → psFac seen xs ⇒B psFac seen ys
  psFac-mono seen [] ()
  psFac-mono seen {(d , j) ∷ xs} {(.d , j') ∷ ys} ((refl , r) ∷ p) =
    ∨-mono {seen ∧ pos d ∧ jpss j} {_} {seen ∧ pos d ∧ jpss j'}
      (∧-mono {seen} {pos d ∧ jpss j} {seen} {pos d ∧ jpss j'} (λ q → q)
        (∧-mono {pos d} {jpss j} {pos d} {jpss j'} (λ q → q) (snd (snd r))))
      (psFac-mono (seen ∨ pos d) p)

  grayInv-mono : ∀ {xs ys} → Pw FR xs ys → grayInv xs ⇒B grayInv ys
  grayInv-mono p =
    ∨-mono (any-mono (λ { {a} {b} (e , r) → subst (λ n → (pos (fst a) ∧ jinv (snd a)) ⇒B (pos n ∧ jinv (snd b))) e (∧-mono (λ q → q) (fst r)) }) p)
    (∨-mono (all-mono (λ { {a} {b} (e , r) → subst (λ n → (not (pos (fst a)) ∧ jinv (snd a)) ⇒B (not (pos n) ∧ jinv (snd b))) e (∧-mono (λ q → q) (fst r)) }) p)
            (psFac-mono false p))

  grayPs-mono : ∀ {xs ys} → Pw FR xs ys → grayPs xs ⇒B grayPs ys
  grayPs-mono p =
    ∨-mono (grayInv-mono p)
      (any-mono (λ { {a} {b} (e , r) → subst (λ n → (pos (fst a) ∧ jpss (snd a)) ⇒B (pos n ∧ jpss (snd b))) e (∧-mono (λ q → q) (snd (snd r))) }) p)

invC-mono : ∀ Θ A t u {cs cs'} → Pw IP≤ cs cs' → invC Θ A t u cs ⇒B invC Θ A t u cs'
invC-mono Θ A t u p =
  ∨-mono {cohCase Θ A t u} {_} {cohCase Θ A t u} (λ q → q) (∧-mono {opCase Θ A t u} {_} {opCase Θ A t u} (λ q → q)
    (all-same (topT (homs Θ)) (λ g → grayInv-mono (facOf-pw (cells Θ) g p))))

psC-mono : ∀ Θ A t u {cs cs'} → Pw IP≤ cs cs' → psC Θ A t u cs ⇒B psC Θ A t u cs'
psC-mono Θ A t u p =
  ∧-mono {opCase Θ A t u} {_} {opCase Θ A t u} (λ q → q) (all-same (topT (homs Θ)) (λ g → grayPs-mono (facOf-pw (cells Θ) g p)))

------------------------------------------------------------------------
-- Types under substitution.

dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-[] ⋆           σ = refl
dim-[] (arr A _ _) σ = cong suc (dim-[] A σ)

endsTy-[] : ∀ A σ {s t} → endsTy A ≡ just (s , t) → endsTy (A [ σ ]ty) ≡ just (s [ σ ]tm , t [ σ ]tm)
endsTy-[] ⋆                     σ ()
endsTy-[] (arr ⋆ a b)           σ refl = refl
endsTy-[] (arr (arr A s' t') _ _) σ eq = endsTy-[] (arr A s' t') σ eq

-- Closed types have no variable endpoint, so OBJ-k never fires on them.
private
  closed-ends : ∀ A {s C} → ScTy 0 A → endsTy A ≡ just (s , var C) → ⊥
  closed-ends ⋆ _ ()
  closed-ends (arr ⋆ a (var C)) (_ , _ , ()) refl
  closed-ends (arr (arr A s' t') _ _) (a , _ , _) eq = closed-ends (arr A s' t') a eq

  objAt-closed : ∀ ms n A → ScTy 0 A → objAt ms n (endsTy A) ≡ false
  objAt-closed ms n A sc with endsTy A in eq
  ... | nothing                = refl
  ... | just (s , var C)       = ⊥-elim (closed-ends A sc eq)
  ... | just (s , coh _ _ _)   = refl
  ... | just (s , cst _)       = refl

------------------------------------------------------------------------
-- Weakening (de Bruijn levels: no shifting) and validity of lookups.

private
  lt-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  lt-suc zero    n       _ = tt
  lt-suc (suc i) (suc n) p = lt-suc i n p

  n<sn : ∀ n → T (n <ℕ suc n)
  n<sn zero    = tt
  n<sn (suc n) = n<sn n

  lt-ne : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  lt-ne zero    (suc n) _ = refl
  lt-ne (suc i) (suc n) p = lt-ne i n p

  lookup-lt : ∀ Γ i {A} → lookup Γ i ≡ just A → T (i <ℕ len Γ)
  lookup-lt ε       i ()
  lookup-lt (Γ ▸ B) i eq with i ==ℕ len Γ in e
  ... | true  = subst (λ j → T (j <ℕ suc (len Γ))) (sym (==ℕ-sound i (len Γ) (subst T (sym e) tt))) (n<sn (len Γ))
  ... | false = lt-suc i (len Γ) (lookup-lt Γ i eq)

  lookup-▸ : ∀ Γ B i {A} → lookup Γ i ≡ just A → lookup (Γ ▸ B) i ≡ just A
  lookup-▸ Γ B i eq rewrite lt-ne i (len Γ) (lookup-lt Γ i eq) = eq

mutual
  wk-tm : ∀ {Γ B t A} → Γ ▸ B ⊢ctx → Γ ⊢tm t ∶ A → Γ ▸ B ⊢tm t ∶ A
  wk-tm {Γ} {B} w (var-wf {i} _ eq)     = var-wf w (lookup-▸ Γ B i eq)
  wk-tm w (coh-wf p wΘ a ok s)          = coh-wf p wΘ a ok (wk-sub w s)
  wk-tm w (cst-wf _ v)                  = cst-wf w v

  wk-sub : ∀ {Γ B σ Θ} → Γ ▸ B ⊢ctx → Γ ⊢sub σ ∶ Θ → Γ ▸ B ⊢sub σ ∶ Θ
  wk-sub w (⟨⟩-wf _)  = ⟨⟩-wf w
  wk-sub w (,-wf s t) = ,-wf (wk-sub w s) (wk-tm w t)

wk-ty : ∀ {Γ B A} → Γ ▸ B ⊢ctx → Γ ⊢ty A → Γ ▸ B ⊢ty A
wk-ty w (⋆-wf _)     = ⋆-wf w
wk-ty w (arr-wf a b) = arr-wf (wk-tm w a) (wk-tm w b)

lookup-valid : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
lookup-valid ε-wf ()
lookup-valid {Γ ▸ B} {i} (▸-wf w b) eq with i ==ℕ len Γ
lookup-valid {Γ ▸ B} {i} (▸-wf w b) refl | true  = wk-ty (▸-wf w b) b
lookup-valid {Γ ▸ B} {i} (▸-wf w b) eq   | false = wk-ty (▸-wf w b) (lookup-valid w eq)

-- The ps* component of every judgment is (PS*) applied to its ps one.
judge-star : ∀ n ms Γ t → jpss (judge n ms Γ t) ≡ star n ms Γ (typeOf Γ t) (jps (judge n ms Γ t))
judge-star n ms Γ (var x)               = refl
judge-star n ms Γ (cst k)               = refl
judge-star n ms Γ (coh Θ ⋆ γ)           = refl
judge-star n ms Γ (coh Θ (arr A t u) γ) = refl

------------------------------------------------------------------------
-- Marked substitutions.

record Resp (N : Nat) (ms : Marks) (ms' : Marks) (Δ : Ctx) (σ : Sub) : Set where
  field
    r-inv  : ∀ k x → T (hasMark isInvM ms x) → T (jinv (judge (k + N) ms' Δ (lookupₛ σ x)))
    r-ps   : ∀ k x → T (hasMark isPsM ms x)  → T (jps  (judge (k + N) ms' Δ (lookupₛ σ x)))
    r-grpd : ∀ C h → T (hasMark (grpdLe h) ms C) →
             Σ Nat (λ D → (lookupₛ σ C ≡ var D) × T (hasMark (grpdLe h) ms' D))
open Resp

module _ {N ms ms' Δ σ} (r : Resp N ms ms' Δ σ) where

  objAt-[] : ∀ n A → objAt ms n (endsTy A) ⇒B objAt ms' n (endsTy (A [ σ ]ty))
  objAt-[] n A p with endsTy A in eq
  ... | just (s , var C) rewrite endsTy-[] A σ eq with r-grpd r C (n ∸ 1) (∧-fst p)
  ...   | D , e , m rewrite e = ∧-intro m (∧-snd {hasMark (grpdLe (n ∸ 1)) ms C} p)

  objRule-[] : ∀ A → objRule ms (just A) ⇒B objRule ms' (just (A [ σ ]ty))
  objRule-[] A p rewrite dim-[] A σ = objAt-[] (dim A) A p

-- OBJ-k and INV⇒PS are built into `judge` for every term.
inv-obj : ∀ n ms Γ t → objRule ms (typeOf Γ t) ⇒B jinv (judge n ms Γ t)
inv-obj n ms Γ (var x)               p = ∨-r p
inv-obj n ms Γ (cst k)               p = p
inv-obj n ms Γ (coh Θ ⋆ γ)           ()
inv-obj n ms Γ (coh Θ (arr A t u) γ) p = ∨-r p

ps-inv : ∀ n ms Γ t → (jinv (judge n ms Γ t) ∧ hdAtLeast 1 (typeOf Γ t)) ⇒B jps (judge n ms Γ t)
ps-inv n ms Γ (var x)               p = ∨-r p
ps-inv n ms Γ (cst k)               p = p
ps-inv n ms Γ (coh Θ ⋆ γ)           ()
ps-inv n ms Γ (coh Θ (arr A t u) γ) p = ∨-r p

private
  hd-[] : ∀ A σ → hdAtLeast 1 (just A) ⇒B hdAtLeast 1 (just (A [ σ ]ty))
  hd-[] A σ p rewrite dim-[] A σ = p

  -- case analysis on a disjunction
  ∨-case : ∀ {a b} {C : Set} → T (a ∨ b) → (T a → C) → (T b → C) → C
  ∨-case {true}  p f g = f tt
  ∨-case {false} p f g = g p

------------------------------------------------------------------------
-- The theorem.

module _ (closed : Closed) where

  mutual
    judge-[] : ∀ {N ms ms' Γ Δ t A σ} k → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
               IP≤ (judge k ms Γ t) (judge (k + N) ms' Δ (t [ σ ]tm))
    judge-[] {N} {ms} {ms'} {Γ} {Δ} {var x} {A} {σ} k (var-wf w eq) sd r =
      inv-part , ps-part , pss-part
      where
      s-wf : Δ ⊢tm lookupₛ σ x ∶ A [ σ ]ty
      s-wf = lookup-sub closed w eq sd
      ty-s : typeOf Δ (lookupₛ σ x) ≡ just (A [ σ ]ty)
      ty-s = typeOf-sound s-wf
      obj : objRule ms (lookup Γ x) ⇒B jinv (judge (k + N) ms' Δ (lookupₛ σ x))
      obj p = inv-obj (k + N) ms' Δ (lookupₛ σ x)
                (subst (λ m → T (objRule ms' m)) (sym ty-s)
                  (objRule-[] r A (subst (λ m → T (objRule ms m)) eq p)))
      inv-part : jinv (judge k ms Γ (var x)) ⇒B jinv (judge (k + N) ms' Δ (lookupₛ σ x))
      inv-part p = ∨-case {hasMark isInvM ms x} p (r-inv r k x) obj
      ps-part : jps (judge k ms Γ (var x)) ⇒B jps (judge (k + N) ms' Δ (lookupₛ σ x))
      ps-part p = ∨-case {hasMark isPsM ms x} p (r-ps r k x) λ q →
        ps-inv (k + N) ms' Δ (lookupₛ σ x)
          (∧-intro (inv-part (∧-fst q))
            (subst (λ m → T (hdAtLeast 1 m)) (sym ty-s)
              (hd-[] A σ (subst (λ m → T (hdAtLeast 1 m)) eq
                (∧-snd {hasMark isInvM ms x ∨ objRule ms (lookup Γ x)} q)))))
      pss-part : jpss (judge k ms Γ (var x)) ⇒B jpss (judge (k + N) ms' Δ (lookupₛ σ x))
      pss-part q =
        subst T (sym (judge-star (k + N) ms' Δ (lookupₛ σ x)))
          (subst (λ m → T (star (k + N) ms' Δ m (jps (judge (k + N) ms' Δ (lookupₛ σ x))))) (sym ty-s)
            (star-[] k (lookup-valid w eq) sd r ps-part
              (subst (λ m → T (star k ms Γ m (jps (judge k ms Γ (var x))))) eq q)))
    judge-[] {N} {ms} {ms'} {Γ} {Δ} {coh Θ (arr A t u) γ} {_} {σ} k (coh-wf p w a ok γd) sd r =
      inv-part , ps-part , pss-part
      where
      B : Ty
      B = arr A t u
      pw : Pw IP≤ (judgeSub k ms Γ γ) (judgeSub (k + N) ms' Δ (γ ∘ σ))
      pw = judgeSub-[] k γd sd r
      e : B [ γ ]ty [ σ ]ty ≡ B [ γ ∘ σ ]ty
      e = assoc-ty B γ σ (subst (λ n → ScTy n B) (sym (snd (sub-sc closed γd))) (ty-sc closed a))
      obj : objRule ms (just (B [ γ ]ty)) ⇒B objRule ms' (just (B [ γ ∘ σ ]ty))
      obj q = subst (λ X → T (objRule ms' (just X))) e (objRule-[] r (B [ γ ]ty) q)
      inv-part : jinv (judge k ms Γ (coh Θ B γ)) ⇒B jinv (judge (k + N) ms' Δ (coh Θ B (γ ∘ σ)))
      inv-part = ∨-mono (invC-mono Θ A t u pw) obj
      hdS : hdAtLeast 1 (just (B [ γ ]ty)) ⇒B hdAtLeast 1 (just (B [ γ ∘ σ ]ty))
      hdS q = subst (λ X → T (hdAtLeast 1 (just X))) e (hd-[] (B [ γ ]ty) σ q)
      ps-part : jps (judge k ms Γ (coh Θ B γ)) ⇒B jps (judge (k + N) ms' Δ (coh Θ B (γ ∘ σ)))
      ps-part = ∨-mono (psC-mono Θ A t u pw) (∧-mono inv-part hdS)
      pss-part : jpss (judge k ms Γ (coh Θ B γ)) ⇒B jpss (judge (k + N) ms' Δ (coh Θ B (γ ∘ σ)))
      pss-part q = subst (λ X → T (star (k + N) ms' Δ (just X) (jps (judge (k + N) ms' Δ (coh Θ B (γ ∘ σ)))))) e
                     (star-[] k (ty[] closed a γd) sd r ps-part q)
    judge-[] {N} {ms} {ms'} {t = cst c} k (cst-wf _ _) sd r
      rewrite objAt-closed ms (dim (ty c)) (ty c) (closed c) =
        (λ ()) , (λ ()) , ∨-mono {dim (ty c) ==ℕ 1} {false} {dim (ty c) ==ℕ 1} (λ q → q) (λ ())

    judgeSub-[] : ∀ {N ms ms' Γ Δ Θ γ σ} k → Γ ⊢sub γ ∶ Θ → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
                  Pw IP≤ (judgeSub k ms Γ γ) (judgeSub (k + N) ms' Δ (γ ∘ σ))
    judgeSub-[] k (⟨⟩-wf _)    sd r = []
    judgeSub-[] k (,-wf γd td) sd r = pw-++ (judgeSub-[] k γd sd r) (judge-[] k td sd r ∷ [])

    -- (PS*) is preserved, given that ps is.
    star-[] : ∀ {N ms ms' Γ Δ A σ p p'} k → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
              p ⇒B p' → star k ms Γ (just A) p ⇒B star (k + N) ms' Δ (just (A [ σ ]ty)) p'
    star-[] {A = A} {σ} k a sd r pp rewrite dim-[] A σ =
      ∨-mono (λ q → q) (∧-mono pp (∨-mono (λ q → q) (bdStar-[] k a sd r)))

    bdStar-[] : ∀ {N ms ms' Γ Δ A σ} k → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
                bdStar k ms Γ A ⇒B bdStar (k + N) ms' Δ (A [ σ ]ty)
    bdStar-[] zero    a              sd r ()
    bdStar-[] (suc k) (⋆-wf _)       sd r ()
    bdStar-[] (suc k) (arr-wf ds du) sd r =
      ∧-mono (snd (snd (judge-[] k ds sd r))) (snd (snd (judge-[] k du sd r)))

  -- The statements of invertibility-markings.md §2, "Substitution".
  inv-[] : ∀ {N ms ms' Γ Δ t A σ} k → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
           T (jinv (judge k ms Γ t)) → T (jinv (judge (k + N) ms' Δ (t [ σ ]tm)))
  inv-[] k d sd r = fst (judge-[] k d sd r)

  ps-[] : ∀ {N ms ms' Γ Δ t A σ} k → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
          T (jps (judge k ms Γ t)) → T (jps (judge (k + N) ms' Δ (t [ σ ]tm)))
  ps-[] k d sd r = fst (snd (judge-[] k d sd r))

  ps*-[] : ∀ {N ms ms' Γ Δ t A σ} k → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Resp N ms ms' Δ σ →
           T (jpss (judge k ms Γ t)) → T (jpss (judge (k + N) ms' Δ (t [ σ ]tm)))
  ps*-[] k d sd r = snd (snd (judge-[] k d sd r))
