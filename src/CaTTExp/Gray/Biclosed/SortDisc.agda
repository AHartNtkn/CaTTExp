------------------------------------------------------------------------
-- D7e follow-up: the sort discipline of F.7.4 §2 under substitution.
--
-- The kernel's instances (KInst) are the AdmI instances (Instances.agda)
-- whose substitution is data-sorted: it sends the template's output
-- variable to a non-representable formula whose head variable, if any,
-- is data-sorted in Γ.  AdmI itself is a superset; inst-typed and
-- inst-dir hold on it, hence on KInst.
--
-- Results (no postulates):
--   * sF-nonRep : substituting into a non-representable formula gives
--                 a non-representable one, provided its head variable
--                 (if it is a variable) goes to a non-representable;
--   * disc-⨾    : a composite σ ⨾ τ is disciplined on S when σ is
--                 disciplined on S and τ is disciplined on the head
--                 variables of σ on S.
--   * KInst S Γ A : kernel instances, with S the data-sorted object
--                 variables of Γ; kinst-subst: closed under well-typed,
--                 data-sorted substitution; adm→kinst; kinst→inst;
--   * templates-sorted : every entry of every template context satisfies
--                 the context-variable clause of F.7.4 §2 for the
--                 template's data variable.
--   * sorted-sub, sortedCtx-sub : the clause is preserved by data-sorted
--                 substitution, so the substituted template context of a
--                 kernel instance is well sorted for Γ's data variables.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.SortDisc where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Templates using (_∈_)
open import CaTTExp.Gray.Biclosed.Subst
open import CaTTExp.Gray.Biclosed.Instances using (_⨾_)

nonRep : Fm → Bool
nonRep (rep _) = false
nonRep _       = true

-- the head variable of a formula, when it is a bare variable
headVar : Fm → Maybe Nat
headVar (obj i) = just i
headVar _       = nothing

sF-nonRep : ∀ φ a → T (nonRep a) →
            (∀ j → headVar a ≡ just j → T (nonRep (φ j))) →
            T (nonRep (sF φ a))
sF-nonRep φ (obj i)  _ h = h i refl
sF-nonRep φ (rep _)  () h
sF-nonRep φ (shp _)  _ h = tt
sF-nonRep φ (a ⊗ b)  _ h = tt
sF-nonRep φ (a \\ b) _ h = tt
sF-nonRep φ (a // b) _ h = tt

-- σ is disciplined on the object variables S
DiscOn : List Nat → Sub → Set
DiscOn S σ = ∀ i → i ∈ S → T (nonRep (fo σ i))

disc-⨾ : ∀ S σ τ → DiscOn S σ →
         (∀ i j → i ∈ S → headVar (fo σ i) ≡ just j → T (nonRep (fo τ j))) →
         DiscOn S (σ ⨾ τ)
disc-⨾ S σ τ dσ dτ i i∈S =
  sF-nonRep (fo τ) (fo σ i) (dσ i i∈S) (λ j e → dτ i j i∈S e)

-- the identity substitution is disciplined on any S
disc-id : ∀ S → DiscOn S (sub obj var)
disc-id S i _ = tt

------------------------------------------------------------------------
-- Kernel instances.
--
-- A context declares its data-sorted object variables S (those that
-- may stand in an output position, so range over non-representable
-- formulas).  A substitution σ from data variables S to data
-- variables S′ sends each i ∈ S to a non-representable formula whose
-- head variable, if it has one, is again data-sorted in S′.  The data
-- variable of a template is the head of its output Z or C.  A kernel
-- instance is an AdmI instance whose substitution is data-sorted.

open import CaTTExp.Gray.Biclosed.Typing using (baseM)
open import CaTTExp.Gray.Biclosed.Templates
  using (Tmpl; tmpl; row; gap; mode; dimn; Row; pairR; probeR; unitR; evLR; evRR;
         H; B; outOf; okT; canon; isObj; ctx; cgoal; egoal; levels; block;
         tyU; tyB; tyRU; Admissible; adm-c; adm-ε; here!; there!)
open import CaTTExp.Gray.Biclosed.Instances
  using (idS; ⨾-typed; id-typed; sY-id; AdmI; inst-c; inst-ε; module Comp)

DSub : List Nat → List Nat → Sub → Set
DSub S S′ σ = ∀ i → i ∈ S →
  T (nonRep (fo σ i)) × (∀ j → headVar (fo σ i) ≡ just j → j ∈ S′)

headVar-sF : ∀ φ a k → headVar (sF φ a) ≡ just k →
             Σ Nat (λ j → headVar a ≡ just j × headVar (φ j) ≡ just k)
headVar-sF φ (obj i)  k e = i , refl , e
headVar-sF φ (rep _)  k ()
headVar-sF φ (a ⊗ b)  k ()
headVar-sF φ (a \\ b) k ()
headVar-sF φ (a // b) k ()

private
  just-inj′ : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj′ refl = refl

dsub-id : ∀ S → DSub S S idS
dsub-id S i i∈S = tt , λ j e → subst (λ k → k ∈ S) (just-inj′ e) i∈S

dsub-⨾ : ∀ S S′ S″ σ τ → DSub S S′ σ → DSub S′ S″ τ → DSub S S″ (σ ⨾ τ)
dsub-⨾ S S′ S″ σ τ dσ dτ i i∈S =
  sF-nonRep (fo τ) (fo σ i) (fst (dσ i i∈S))
            (λ j e → fst (dτ j (snd (dσ i i∈S) j e))) ,
  λ k e → let r = headVar-sF (fo τ) (fo σ i) k e
              j = fst r
          in snd (dτ j (snd (dσ i i∈S) j (fst (snd r)))) k (snd (snd r))

fromMaybe : Maybe Nat → List Nat
fromMaybe nothing  = []
fromMaybe (just i) = i ∷ []

-- the data variable of a template: the head of its output
tmplData : Tmpl → List Nat
tmplData t = fromMaybe (headVar (outOf (row t)))

data KInst (S : List Nat) (Γ : Ctx) (A : CTy) : Set where
  kinst-c : (t : Tmpl) → T (okT t) → (σ : Sub) → Γ ⊢ σ ∶ ctx t →
            DSub (tmplData t) S σ → A ≡ sY σ (cgoal t) → KInst S Γ A
  kinst-ε : (t : Tmpl) → T (okT t) → (σ : Sub) → Γ ⊢ σ ∶ ctx t →
            DSub (tmplData t) S σ → A ≡ sY σ (egoal t) → KInst S Γ A

-- kernel instances are AdmI instances (so inst-typed, inst-dir apply)
kinst→inst : ∀ {S Γ A} → KInst S Γ A → AdmI Γ A
kinst→inst (kinst-c t ok σ h _ e) = inst-c t ok σ h e
kinst→inst (kinst-ε t ok σ h _ e) = inst-ε t ok σ h e

-- the generic goals are kernel instances, with the template's own data
-- variable declared
adm→kinst : ∀ {Γ A} (a : Admissible Γ A) → Σ (List Nat) (λ S → KInst S Γ A)
adm→kinst (adm-c t ok refl refl) =
  tmplData t , kinst-c t ok idS (id-typed _) (dsub-id _) (sym (sY-id _))
adm→kinst (adm-ε t ok refl refl) =
  tmplData t , kinst-ε t ok idS (id-typed _) (dsub-id _) (sym (sY-id _))

-- closure: kernel instances are closed under well-typed, data-sorted
-- substitution
kinst-subst : ∀ {S S′ Θ Γ A τ} → KInst S Γ A → Θ ⊢ τ ∶ Γ → DSub S S′ τ →
              KInst S′ Θ (sY τ A)
kinst-subst {S} {S′} {τ = τ} (kinst-c t ok σ h d refl) k dτ =
  kinst-c t ok (σ ⨾ τ) (⨾-typed h k) (dsub-⨾ _ S S′ σ τ d dτ)
          (Comp.sY-⨾ σ τ (cgoal t))
kinst-subst {S} {S′} {τ = τ} (kinst-ε t ok σ h d refl) k dτ =
  kinst-ε t ok (σ ⨾ τ) (⨾-typed h k) (dsub-⨾ _ S S′ σ τ d dτ)
          (Comp.sY-⨾ σ τ (egoal t))

------------------------------------------------------------------------
-- The context-variable clause, and the templates satisfy it.
--
-- An entry is well sorted for S when its base profile (xs ▸ z) either
-- has a non-representable output whose head variable (if any) is
-- data-sorted, or has a representable output and only representable
-- inputs (F.7.4 §2).

isRep : Fm → Bool
isRep (rep _) = true
isRep _       = false

headIn : List Nat → Maybe Nat → Bool
headIn S nothing  = true
headIn S (just i) = elem i S

sortedM : List Nat → MTy → Bool
sortedM S (xs ▸ z) = if nonRep z then headIn S (headVar z) else all isRep xs

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

∈-++ : ∀ {A : Set} {x : A} xs ys → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
∈-++ []       ys p          = inr p
∈-++ (y ∷ xs) ys here!      = inl here!
∈-++ (y ∷ xs) ys (there! p) with ∈-++ xs ys p
... | inl q = inl (there! q)
... | inr q = inr q

module Sorted (t : Tmpl) where
  private ρ = row t

  baseM-tyU : ∀ j → baseM (tyU t j) ≡ H ρ
  baseM-tyU zero    = refl
  baseM-tyU (suc j) = baseM-tyU j

  baseM-tyB : ∀ j → baseM (tyB t j) ≡ B ρ
  baseM-tyB zero    = refl
  baseM-tyB (suc j) = baseM-tyB j

  baseM-tyRU : ∀ j → baseM (tyRU t j) ≡ B ρ
  baseM-tyRU zero    = refl
  baseM-tyRU (suc j) = baseM-tyRU j

  HB : CTy → Set
  HB A = (baseM A ≡ H ρ) ⊎ (baseM A ≡ B ρ)

  block-HB : ∀ j A → A ∈ block t j → HB A
  block-HB j A here!                                         = inl (baseM-tyU j)
  block-HB j A (there! here!)                                = inl (baseM-tyU j)
  block-HB j A (there! (there! here!))                       = inr (baseM-tyB j)
  block-HB j A (there! (there! (there! here!)))              = inr (baseM-tyB j)
  block-HB j A (there! (there! (there! (there! here!))))     = inr (baseM-tyRU j)
  block-HB j A (there! (there! (there! (there! (there! here!))))) = inr (baseM-tyRU j)
  block-HB j A (there! (there! (there! (there! (there! (there! ()))))))

  levels-HB : ∀ j A → A ∈ levels t j → HB A
  levels-HB zero    A ()
  levels-HB (suc j) A p with ∈-++ (levels t j) (block t j) p
  ... | inl q = levels-HB j A q
  ... | inr q = block-HB j A q

  ctx-HB : ∀ A → A ∈ ctx t → HB A
  ctx-HB A p with ∈-++ (levels t (dimn t)) (tyB t (dimn t) ∷ []) p
  ... | inl q     = levels-HB (dimn t) A q
  ... | inr here! = inr (baseM-tyB (dimn t))
  ... | inr (there! ())

  T→≡′ : ∀ {b} → T b → b ≡ true
  T→≡′ {true} _ = refl

  outOK : ∀ xs z → T (isObj z) → T (sortedM (fromMaybe (headVar z)) (xs ▸ z))
  outOK xs (obj i) _ rewrite T→≡′ (==ℕ-refl i) = tt

  canon-obj : T (okT t) → T (isObj (outOf ρ))
  canon-obj ok = canonObj (row t) (okCanon t ok)
    where
      okCanon : ∀ t → T (okT t) → T (canon (row t))
      okCanon (tmpl ρ g m zero)    ok = ∧-fst ok
      okCanon (tmpl ρ g m (suc n)) ok = ∧-fst ok
      canonObj : ∀ ρ → T (canon ρ) → T (isObj (outOf ρ))
      canonObj ρ c = ∧-snd {_} c

  H-sorted : T (okT t) → T (sortedM (tmplData t) (H ρ))
  H-sorted ok = go ρ (canon-obj ok)
    where
      go : ∀ ρ′ → T (isObj (outOf ρ′)) → T (sortedM (fromMaybe (headVar (outOf ρ′))) (H ρ′))
      go (pairR L U V R Z)  o = outOK (L ++ (U ⊗ V) ∷ R) Z o
      go (probeR L Δ Θ R Z) o = outOK (L ++ rep (Δ ⊠ Θ) ∷ R) Z o
      go (unitR L R Z)      o = outOK (L ++ rep (disk 0) ∷ R) Z o
      go (shapeR L Θ R Z)   o = outOK (L ++ shp Θ ∷ R) Z o
      go (evLR Φ A C)       o = tt
      go (evRR Φ A C)       o = tt

  B-sorted : T (okT t) → T (sortedM (tmplData t) (B ρ))
  B-sorted ok = go ρ (canon-obj ok)
    where
      go : ∀ ρ′ → T (isObj (outOf ρ′)) → T (sortedM (fromMaybe (headVar (outOf ρ′))) (B ρ′))
      go (pairR L U V R Z)  o = outOK (L ++ U ∷ V ∷ R) Z o
      go (probeR L Δ Θ R Z) o = outOK (L ++ rep Δ ∷ rep Θ ∷ R) Z o
      go (unitR L R Z)      o = outOK (L ++ R) Z o
      go (shapeR L Θ R Z)   o = outOK (L ++ rep Θ ∷ R) Z o
      go (evLR Φ A C)       o = outOK (A ∷ Φ) C o
      go (evRR Φ A C)       o = outOK (Φ ++ A ∷ []) C o

-- every entry of every template context is well sorted for the
-- template's data variable
templates-sorted : ∀ t → T (okT t) → ∀ A → A ∈ ctx t →
                   T (sortedM (tmplData t) (baseM A))
templates-sorted t ok A p with Sorted.ctx-HB t A p
... | inl e rewrite e = Sorted.H-sorted t ok
... | inr e rewrite e = Sorted.B-sorted t ok

------------------------------------------------------------------------
-- The context-variable clause is preserved by data-sorted substitution

elem→∈ : ∀ i S → T (elem i S) → i ∈ S
elem→∈ i []       ()
elem→∈ i (k ∷ S) p with i ==ℕ k in e
... | true  = subst (λ j → i ∈ (j ∷ S)) (==ℕ-sound i k (subst T (sym e) tt)) here!
... | false = there! (elem→∈ i S p)

T→≡″ : ∀ {b} → T b → b ≡ true
T→≡″ {true} _ = refl

∈→elem : ∀ i S → i ∈ S → T (elem i S)
∈→elem i (k ∷ S) here! rewrite T→≡″ (==ℕ-refl i) = tt
∈→elem i (k ∷ S) (there! p) with i ==ℕ k
... | true  = tt
... | false = ∈→elem i S p

allRep-sFs : ∀ φ xs → T (all isRep xs) → T (all isRep (sFs φ xs))
allRep-sFs φ []            _ = tt
allRep-sFs φ (rep s ∷ xs)  p = allRep-sFs φ xs p
allRep-sFs φ (obj _ ∷ xs)  ()
allRep-sFs φ ((_ ⊗ _) ∷ xs)  ()
allRep-sFs φ (shp _ ∷ xs)  ()
allRep-sFs φ ((_ \\ _) ∷ xs) ()
allRep-sFs φ ((_ // _) ∷ xs) ()

sorted-sub : ∀ S S′ τ M → DSub S S′ τ → T (sortedM S M) → T (sortedM S′ (sM (fo τ) M))
sorted-sub S S′ τ (xs ▸ obj i) d p =
  let r = d i (elem→∈ i S p) in
  go (fo τ i) (fst r) (snd r)
  where
    go : ∀ f → T (nonRep f) → (∀ j → headVar f ≡ just j → j ∈ S′) →
         T (sortedM S′ (sFs (fo τ) xs ▸ f))
    go (obj j)  _  h = ∈→elem j S′ (h j refl)
    go (rep _)  () h
    go (shp _)  _  h = tt
    go (a ⊗ b)  _  h = tt
    go (a \\ b) _  h = tt
    go (a // b) _  h = tt
sorted-sub S S′ τ (xs ▸ rep s)  d p = allRep-sFs (fo τ) xs p
sorted-sub S S′ τ (xs ▸ shp s)  d p = p
sorted-sub S S′ τ (xs ▸ (a ⊗ b))  d p = tt
sorted-sub S S′ τ (xs ▸ (a \\ b)) d p = tt
sorted-sub S S′ τ (xs ▸ (a // b)) d p = tt

SortedCtx : List Nat → Ctx → Set
SortedCtx S Γ = ∀ A → A ∈ Γ → T (sortedM S (baseM A))

private
  mapL : ∀ {A B : Set} → (A → B) → List A → List B
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

  ∈-map : ∀ {A B : Set} (f : A → B) {y} xs → y ∈ mapL f xs →
          Σ A (λ x → x ∈ xs × y ≡ f x)
  ∈-map f (x ∷ xs) here!      = x , here! , refl
  ∈-map f (x ∷ xs) (there! p) with ∈-map f xs p
  ... | z , q , e = z , there! q , e

-- substituting a well-sorted context by a data-sorted τ gives a
-- well-sorted context
sortedCtx-sub : ∀ S S′ τ Γ → DSub S S′ τ → SortedCtx S Γ →
                SortedCtx S′ (mapL (sY τ) Γ)
sortedCtx-sub S S′ τ Γ d s B p with ∈-map (sY τ) Γ p
... | A , q , refl rewrite Ops.baseM-sY τ A =
  sorted-sub S S′ τ (baseM A) d (s A q)

-- the template contexts are well sorted for their data variable
templates-sortedCtx : ∀ t → T (okT t) → SortedCtx (tmplData t) (ctx t)
templates-sortedCtx = templates-sorted
