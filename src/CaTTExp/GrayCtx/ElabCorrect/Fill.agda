------------------------------------------------------------------------
-- Correctness of Elab.fill (ledger S20 (ii), step 1).
--
-- `fill Γ P top` reads a substitution into a pasting context P off the
-- images of some of P's variables (the "keys"): each image's type is
-- unified with the key's type in P, which assigns the key's iterated
-- boundary variables. The theorem: if the images are those of a well
-- typed σ₀ : P, and the keys with their boundaries cover P, then fill
-- returns σ₀ itself:
--
--   fill-ok : Γ ⊢sub σ₀ ∶ P → P ⊢ps → T (covers P keys) →
--             fill Γ P (zipK keys σ₀) ≡ just σ₀
--
-- `covers` is a Boolean on P and the keys alone (no Γ), so it is a
-- fact about the shape, proved once per shape (by computation for a
-- fixed tree).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.ElabCorrect.Fill where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab using (Assign; unify; findA; subOf; fillGo; fill; tyOf; zipA)
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.Derived using (ps-ctx)
open import CaTTExp.GrayCtx.NaturalWF using (<→≢; <-suc; n<sn; T-≡; ≡-T)

closed : Sb.Closed
closed ()

private
  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

bind-just : ∀ {A B : Set} {m : Maybe A} {x : A} {f : A → Maybe B} → m ≡ just x → (m >>= f) ≡ f x
bind-just refl = refl

------------------------------------------------------------------------
-- Types whose boundaries are variables (every type of a pasting
-- context).

data VarTy : Ty → Set where
  vt⋆   : VarTy ⋆
  vtarr : ∀ {A a b} → VarTy A → VarTy (arr A (var a) (var b))

VarCtx : Ctx → Set
VarCtx P = ∀ i A → lookup P i ≡ just A → VarTy A

lk-snoc : ∀ {Γ B i A} (Q : Ty → Set) → Q B → (lookup Γ i ≡ just A → Q A) →
          lookup (Γ ▸ B) i ≡ just A → Q A
lk-snoc {Γ} {B} {i} Q qb qr e with i ==ℕ len Γ
... | true  = subst Q (just-inj e) qb
... | false = qr e

ps-var : ∀ {Γ x A} → Γ ⊢ps x ∶ A → VarTy A × VarCtx Γ
ps-var pss = vt⋆ , λ i A e → lk-snoc {ε} {⋆} {i} {A} VarTy vt⋆ (λ ()) e
ps-var (pse {Γ} {x} {A} d) =
  let (va , vc) = ps-var d in
  vtarr va , λ i C e → lk-snoc {Γ ▸ A} {arr A (var x) (var (len Γ))} {i} {C} VarTy (vtarr va)
                          (lk-snoc {Γ} {A} {i} {C} VarTy va (vc i C)) e
ps-var (psd d) with ps-var d
... | vtarr va , vc = va , vc

ps-varctx : ∀ {P} → P ⊢ps → VarCtx P
ps-varctx (ps d) = snd (ps-var d)

------------------------------------------------------------------------
-- Unification against a substituted type.

bvV : ∀ {B} → VarTy B → Sub → Assign
bvV vt⋆                     σ = []
bvV (vtarr {A} {a} {b} v)   σ = (a , lookupₛ σ a) ∷ (b , lookupₛ σ b) ∷ bvV v σ

unify-ok : ∀ {B} (v : VarTy B) σ → unify B (B [ σ ]ty) ≡ just (bvV v σ)
unify-ok vt⋆       σ = refl
unify-ok (vtarr v) σ rewrite unify-ok v σ = refl

-- The boundary variables of a type, read off P alone.
vn : Tm → List Nat
vn (var a) = a ∷ []
vn _       = []

bvars : Ty → List Nat
bvars ⋆           = []
bvars (arr A s t) = vn s ++ vn t ++ bvars A

------------------------------------------------------------------------
-- Assignments that agree with σ.

Good : Sub → Assign → Set
Good σ []             = ⊤
Good σ ((k , t) ∷ as) = (t ≡ lookupₛ σ k) × Good σ as

good-++ : ∀ σ as bs → Good σ as → Good σ bs → Good σ (as ++ bs)
good-++ σ []             bs _        gb = gb
good-++ σ ((k , t) ∷ as) bs (e , ga) gb = e , good-++ σ as bs ga gb

bv-good : ∀ {B} (v : VarTy B) σ → Good σ (bvV v σ)
bv-good vt⋆       σ = tt
bv-good (vtarr v) σ = refl , refl , bv-good v σ

keysOf : Assign → List Nat
keysOf []             = []
keysOf ((k , _) ∷ as) = k ∷ keysOf as

keys-++ : ∀ as bs → keysOf (as ++ bs) ≡ keysOf as ++ keysOf bs
keys-++ []             bs = refl
keys-++ ((k , _) ∷ as) bs = cong (k ∷_) (keys-++ as bs)

bv-keys : ∀ {B} (v : VarTy B) σ → keysOf (bvV v σ) ≡ bvars B
bv-keys vt⋆       σ = refl
bv-keys (vtarr v) σ = cong (λ l → _ ∷ _ ∷ l) (bv-keys v σ)

------------------------------------------------------------------------
-- The images.

zipK : List Nat → Sub → Assign
zipK []       σ = []
zipK (k ∷ ks) σ = (k , lookupₛ σ k) ∷ zipK ks σ

zipK-good : ∀ ks σ → Good σ (zipK ks σ)
zipK-good []       σ = tt
zipK-good (k ∷ ks) σ = refl , zipK-good ks σ

zipK-keys : ∀ ks σ → keysOf (zipK ks σ) ≡ ks
zipK-keys []       σ = refl
zipK-keys (k ∷ ks) σ = cong (k ∷_) (zipK-keys ks σ)

-- Elab builds the images with zipA from a list of terms.
mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

zipA-zipK : ∀ ks σ → zipA ks (mapL (lookupₛ σ) ks) ≡ just (zipK ks σ)
zipA-zipK []       σ = refl
zipA-zipK (k ∷ ks) σ rewrite zipA-zipK ks σ = refl

------------------------------------------------------------------------
-- A typed term's inferred type.

tyOf-typed : ∀ {Γ u B} → Γ ⊢tm u ∶ B → tyOf Γ u ≡ just B
tyOf-typed (var-wf _ e)       = e
tyOf-typed (coh-wf _ _ _ _ _) = refl
tyOf-typed (cst-wf {k} _ _)   = ⊥-elim k

------------------------------------------------------------------------
-- The boundary keys.

lookupTy : Ctx → Nat → Ty
lookupTy P p with lookup P p
... | just B  = B
... | nothing = ⋆

bkeys : Ctx → List Nat → List Nat
bkeys P []       = []
bkeys P (p ∷ qs) = bvars (lookupTy P p) ++ bkeys P qs

lookup-lt : ∀ P p → T (p <ℕ len P) → Σ Ty λ B → lookup P p ≡ just B
lookup-lt ε       p ()
lookup-lt (P ▸ A) p h with p ==ℕ len P in e
... | true  = A , refl
... | false = lookup-lt P p (lt-pred p (len P) h e)
  where
  lt-pred : ∀ p n → T (p <ℕ suc n) → (p ==ℕ n) ≡ false → T (p <ℕ n)
  lt-pred zero    zero    _ ()
  lt-pred zero    (suc n) _ _ = tt
  lt-pred (suc p) zero    () _
  lt-pred (suc p) (suc n) h e = lt-pred p n h e

lookupTy-just : ∀ P p {B} → lookup P p ≡ just B → lookupTy P p ≡ B
lookupTy-just P p e with lookup P p
... | just _ = just-inj e

AllLt : List Nat → Nat → Set
AllLt []       n = ⊤
AllLt (k ∷ ks) n = T (k <ℕ n) × AllLt ks n

fillGo-ok : ∀ {Γ P σ₀} ks → Γ ⊢sub σ₀ ∶ P → P ⊢ctx → VarCtx P → AllLt ks (len P) →
            Σ Assign λ rest → (fillGo Γ P (zipK ks σ₀) ≡ just rest)
                              × Good σ₀ rest × (keysOf rest ≡ bkeys P ks)
fillGo-ok []       s w vc _ = [] , refl , tt , refl
fillGo-ok {Γ} {P} {σ₀} (p ∷ ks) s w vc (lt , lts)
  with lookup-lt P p lt
... | B , eB
  with fillGo-ok ks s w vc lts
... | rest , eq , g , kk =
  bvV v σ₀ ++ rest , e , good-++ σ₀ (bvV v σ₀) rest (bv-good v σ₀) g ,
  trans (keys-++ (bvV v σ₀) rest)
        (cong₂ _++_ (trans (bv-keys v σ₀) (cong bvars (sym (lookupTy-just P p eB)))) kk)
  where
  v : VarTy B
  v = vc p B eB
  tyE : tyOf Γ (lookupₛ σ₀ p) ≡ just (B [ σ₀ ]ty)
  tyE = tyOf-typed (Sb.lookup-sub closed w eB s)
  e : fillGo Γ P (zipK (p ∷ ks) σ₀) ≡ just (bvV v σ₀ ++ rest)
  e = trans (bind-just {m = lookup P p} eB)
       (trans (bind-just {m = tyOf Γ (lookupₛ σ₀ p)} tyE)
       (trans (bind-just {m = unify B (B [ σ₀ ]ty)} (unify-ok v σ₀))
              (bind-just {m = fillGo Γ P (zipK ks σ₀)} eq)))

------------------------------------------------------------------------
-- Reading the substitution back.

memN : Nat → List Nat → Bool
memN k []       = false
memN k (m ∷ ms) = (k ==ℕ m) ∨ memN k ms

or-l : ∀ a b → T (a ∨ b) → (a ≡ false) → T b
or-l true  b _ ()
or-l false b h _ = h

findA-good : ∀ σ as k → Good σ as → T (memN k (keysOf as)) → findA as k ≡ just (lookupₛ σ k)
findA-good σ []             k _ ()
findA-good σ ((m , t) ∷ as) k (e , g) h with k ==ℕ m in eq
... | true  = cong just (trans e (cong (lookupₛ σ) (sym (==ℕ-sound k m (≡-T eq)))))
... | false = findA-good σ as k g (or-l false _ h refl)

pre : Sub → Nat → Sub
pre σ zero    = ⟨⟩
pre σ (suc n) = pre σ n ,ₛ lookupₛ σ n

subOf-ok : ∀ σ as n → (∀ k → T (k <ℕ n) → findA as k ≡ just (lookupₛ σ k)) →
           subOf n as ≡ just (pre σ n)
subOf-ok σ as zero    h = refl
subOf-ok σ as (suc n) h
  rewrite subOf-ok σ as n (λ k p → h k (<-suc k n p)) | h n (n<sn n) = refl

pre-ext : ∀ σ t n → T (n <ℕ suc (lenₛ σ)) → pre (σ ,ₛ t) n ≡ pre σ n
pre-ext σ t zero    _ = refl
pre-ext σ t (suc n) h
  rewrite pre-ext σ t n (<-suc n (lenₛ σ) h) | <→≢ n (lenₛ σ) h = refl

pre-full : ∀ σ → pre σ (lenₛ σ) ≡ σ
pre-full ⟨⟩       = refl
pre-full (σ ,ₛ t)
  rewrite pre-ext σ t (lenₛ σ) (n<sn (lenₛ σ)) | pre-full σ
        | T-≡ (==ℕ-refl (lenₛ σ)) = refl

------------------------------------------------------------------------
-- Coverage of P by the keys and their boundaries (a fact about P).

allBelow : (Nat → Bool) → Nat → Bool
allBelow f zero    = true
allBelow f (suc n) = allBelow f n ∧ f n

allLtB : List Nat → Nat → Bool
allLtB []       n = true
allLtB (k ∷ ks) n = (k <ℕ n) ∧ allLtB ks n

covers : Ctx → List Nat → Bool
covers P ks = allLtB ks (len P) ∧ allBelow (λ k → memN k (ks ++ bkeys P ks)) (len P)

private
  ∧-l : ∀ {a b} → T (a ∧ b) → T a
  ∧-l {true} _ = tt
  ∧-r : ∀ {a b} → T (a ∧ b) → T b
  ∧-r {true} h = h

  allLt-ok : ∀ ks n → T (allLtB ks n) → AllLt ks n
  allLt-ok []       n _ = tt
  allLt-ok (k ∷ ks) n h = ∧-l {k <ℕ n} h , allLt-ok ks n (∧-r {k <ℕ n} h)

  allBelow-ok : ∀ f n → T (allBelow f n) → ∀ k → T (k <ℕ n) → T (f k)
  allBelow-ok f zero    _ k ()
  allBelow-ok f (suc n) h k p with k ==ℕ n in e
  ... | true  = subst (λ m → T (f m)) (sym (==ℕ-sound k n (≡-T e))) (∧-r {allBelow f n} h)
  ... | false = allBelow-ok f n (∧-l {allBelow f n} h) k (lt-pred k n p e)
    where
    lt-pred : ∀ p n → T (p <ℕ suc n) → (p ==ℕ n) ≡ false → T (p <ℕ n)
    lt-pred zero    zero    _ ()
    lt-pred zero    (suc n) _ _ = tt
    lt-pred (suc p) zero    () _
    lt-pred (suc p) (suc n) h e = lt-pred p n h e

------------------------------------------------------------------------
-- The theorem.

fill-ok : ∀ {Γ P σ₀} ks → Γ ⊢sub σ₀ ∶ P → P ⊢ps → T (covers P ks) →
          fill Γ P (zipK ks σ₀) ≡ just σ₀
fill-ok {Γ} {P} {σ₀} ks s p cv
  with fillGo-ok ks s (ps-ctx p) (ps-varctx p) (allLt-ok ks (len P) (∧-l {allLtB ks (len P)} cv))
... | rest , eq , g , kk rewrite eq =
  trans (subOf-ok σ₀ (zipK ks σ₀ ++ rest) (len P) find)
        (cong just (cong (pre σ₀) (sym l) ∙ pre-full σ₀))
  where
  _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _∙_ = trans
  l : lenₛ σ₀ ≡ len P
  l = snd (Sb.sub-sc closed s)
  g' : Good σ₀ (zipK ks σ₀ ++ rest)
  g' = good-++ σ₀ (zipK ks σ₀) rest (zipK-good ks σ₀) g
  kk' : keysOf (zipK ks σ₀ ++ rest) ≡ ks ++ bkeys P ks
  kk' = trans (keys-++ (zipK ks σ₀) rest) (cong₂ _++_ (zipK-keys ks σ₀) kk)
  find : ∀ k → T (k <ℕ len P) → findA (zipK ks σ₀ ++ rest) k ≡ just (lookupₛ σ₀ k)
  find k h = findA-good σ₀ _ k g'
    (subst (λ l → T (memN k l)) (sym kk')
      (allBelow-ok (λ k → memN k (ks ++ bkeys P ks)) (len P) (∧-r {allLtB ks (len P)} cv) k h))
