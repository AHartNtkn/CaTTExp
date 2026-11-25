------------------------------------------------------------------------
-- The local checks of the DAG checker, relative to
--
--   K : Nat                        the ids below K are the variables:
--                                  R i = just (V i) for i < K (checked
--                                  once, by varsOK), so instantiation
--                                  recognises a variable without a lookup
--   R : Nat → Maybe Item           the table (CaTTExp.Dag.Table)
--   J : Nat → Nat → Maybe RTy      typing claims: J c n = just A claims
--                                  ⟦ c ⟧c ⊢ ⟦ n ⟧ ∶ ⟦ A ⟧ty
--   F : Nat → Maybe (List Nat)     free-variable claims for the terms
--                                  that coherence side conditions read
--
-- Each check looks only at one item or claim and at the claims of its
-- immediate parts, so a whole certificate is checked in time linear in
-- the number of distinct items (times lookup cost), whatever the size
-- of the unfolded terms. Every claim is untrusted: CaTTExp.Dag.Sound
-- shows that if all local checks pass, every claim holds.
--
-- Instantiation (the type A[σ] of a coh) is checked against the claimed
-- result id by id, with a memo table, so a head type with sharing is
-- walked once per use, not as a tree.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Dag.Table
open import CaTTExp.Dag.Trie

module CaTTExp.Dag.Check
  (K : Nat)
  (R : Nat → Maybe Item)
  (J : Nat → Nat → Maybe RTy)
  (F : Nat → Maybe (List Nat))
  where

open import CaTTExp.Dag.Unfold R

------------------------------------------------------------------------
-- Small helpers

eqM : Maybe Nat → Nat → Bool
eqM (just a) m = a ==ℕ m
eqM nothing  m = false

eqRM : Maybe RTy → RTy → Bool
eqRM (just A) B = A ==R B
eqRM nothing  B = false

isHead : Maybe Item → Bool
isHead (just (H _ _)) = true
isHead _              = false

isCtx : Maybe Item → Bool
isCtx (just E)       = true
isCtx (just (S _ _)) = true
isCtx _              = false

isE : Maybe Item → Bool
isE (just E) = true
isE _        = false

eqL : List Nat → List Nat → Bool
eqL []       []       = true
eqL (x ∷ xs) (y ∷ ys) = (x ==ℕ y) ∧ eqL xs ys
eqL _        _        = false

------------------------------------------------------------------------
-- Instantiation: inst f s m M succeeds when ⟦ s ⟧ [ σ ] = ⟦ m ⟧, where
-- σ maps levels below b to ids. M memoizes pairs (s , m) already
-- established.

module Inst (σ : Trie Nat) (b : Nat) where
  instV : Nat → Nat → Trie Nat → Maybe (Trie Nat)
  instV i m M = if (i <ℕ b) ∧ eqM (lookupT i σ) m then just M else nothing

  mutual
    inst : Nat → Nat → Nat → Trie Nat → Maybe (Trie Nat)
    inst zero    s m M = nothing
    inst (suc f) s m M = if s <ℕ K then instV s m M else instHit f s m M (lookupT s M)

    instHit : Nat → Nat → Nat → Trie Nat → Maybe Nat → Maybe (Trie Nat)
    instHit f s m M (just m') = if m' ==ℕ m then just M else nothing
    instHit f s m M nothing   = instI f s m M (R s) (R m)

    instI : Nat → Nat → Nat → Trie Nat → Maybe Item → Maybe Item → Maybe (Trie Nat)
    instI f s m M (just (V i)) _ = instV i m M
    instI f s m M (just (C h as)) (just (C h' as')) =
      if (h ==ℕ h') ∧ isHead (R h) then instC s m (instL f as as' M) else nothing
    instI f s m M _ _ = nothing

    instC : Nat → Nat → Maybe (Trie Nat) → Maybe (Trie Nat)
    instC s m (just M) = just (insert s m M)
    instC s m nothing  = nothing

    instL : Nat → List Nat → List Nat → Trie Nat → Maybe (Trie Nat)
    instL f []       []         M = just M
    instL f (a ∷ as) (a' ∷ as') M = instL₂ f as as' (inst f a a' M)
    instL f _        _          M = nothing

    instL₂ : Nat → List Nat → List Nat → Maybe (Trie Nat) → Maybe (Trie Nat)
    instL₂ f as as' (just M) = instL f as as' M
    instL₂ f as as' nothing  = nothing

  instR₃ : Nat → Nat → Maybe (Trie Nat) → Maybe (Trie Nat)
  instR₃ t t' (just M) = inst (suc t) t t' M
  instR₃ t t' nothing  = nothing

  instR₂ : Nat → Nat → Nat → Nat → Maybe (Trie Nat) → Maybe (Trie Nat)
  instR₂ s t s' t' (just M) = instR₃ t t' (inst (suc s) s s' M)
  instR₂ s t s' t' nothing  = nothing

  instR : RTy → RTy → Trie Nat → Maybe (Trie Nat)
  instR ⋆ᵣ           ⋆ᵣ              M = just M
  instR (arrᵣ A s t) (arrᵣ A' s' t') M = instR₂ s t s' t' (instR A A' M)
  instR _            _               M = nothing

-- The type B [ σ ] is A, for σ with b levels.
instOK : Trie Nat → Nat → RTy → RTy → Bool
instOK σ b B A = is-just (Inst.instR σ b B A tleaf)

------------------------------------------------------------------------
-- Substitutions: the argument list (last argument first) as a trie
-- from levels to ids, with its length.

sigT₂ : Nat → Σ Nat (λ _ → Trie Nat) → Σ Nat (λ _ → Trie Nat)
sigT₂ a (L , σ) = suc L , insert L a σ

sigT : List Nat → Σ Nat (λ _ → Trie Nat)
sigT []       = 0 , tleaf
sigT (a ∷ as) = sigT₂ a (sigT as)

------------------------------------------------------------------------
-- Contexts

ctxLenS : Maybe Nat → Maybe Nat
ctxLenS (just L) = just (suc L)
ctxLenS nothing  = nothing

mutual
  ctxLen : Nat → Nat → Maybe Nat
  ctxLen zero    c = nothing
  ctxLen (suc f) c = ctxLenI f (R c)

  ctxLenI : Nat → Maybe Item → Maybe Nat
  ctxLenI f (just E)        = just 0
  ctxLenI f (just (S c' _)) = ctxLenS (ctxLen f c')
  ctxLenI f _               = nothing

-- The type of level i in the context c of length L.
mutual
  lookupCtx : Nat → Nat → Nat → Maybe RTy
  lookupCtx zero    c i = nothing
  lookupCtx (suc L) c i = lookupCtxI L i (R c)

  lookupCtxI : Nat → Nat → Maybe Item → Maybe RTy
  lookupCtxI L i (just (S c' B)) = if i ==ℕ L then just B else lookupCtx L c' i
  lookupCtxI L i _               = nothing

------------------------------------------------------------------------
-- Typing claims

-- Every component of a type is claimed at the type below it.
tyOK : Nat → RTy → Bool
tyOK c ⋆ᵣ           = true
tyOK c (arrᵣ A s t) = tyOK c A ∧ (eqRM (J c s) A ∧ eqRM (J c t) A)

-- Claims about one context c are checked against the claims Jc for c
-- (the block of c, looked up once), so an argument costs one lookup.

-- The arguments as (last first, L of them) fit the context ch, each
-- claimed in Jc at the substituted type of its slot.
mutual
  argsOK : (Nat → Maybe RTy) → Trie Nat → Nat → List Nat → Nat → Bool
  argsOK Jc σ ch []       zero    = isE (R ch)
  argsOK Jc σ ch (a ∷ as) (suc L) = argOK Jc σ as L (R ch) (Jc a)
  argsOK Jc σ ch _        _       = false

  argOK : (Nat → Maybe RTy) → Trie Nat → List Nat → Nat → Maybe Item → Maybe RTy → Bool
  argOK Jc σ as L (just (S ch' B)) (just Ta) = instOK σ L B Ta ∧ argsOK Jc σ ch' as L
  argOK Jc σ as L _                _         = false

judgC₂ : (Nat → Maybe RTy) → RTy → List Nat → Nat → RTy → Σ Nat (λ _ → Trie Nat) → Bool
judgC₂ Jc A as ch B (L , σ) = argsOK Jc σ ch as L ∧ instOK σ L B A

judgC : (Nat → Maybe RTy) → RTy → List Nat → Maybe Item → Bool
judgC Jc A as (just (H ch B)) = judgC₂ Jc A as ch B (sigT as)
judgC Jc A as _               = false

judgV : Nat → RTy → Nat → Maybe Nat → Bool
judgV c A i (just L) = eqRM (lookupCtx L c i) A
judgV c A i nothing  = false

judgI : Nat → (Nat → Maybe RTy) → RTy → Maybe Item → Bool
judgI c Jc A (just (V i))    = judgV c A i (ctxLen (suc c) c)
judgI c Jc A (just (C h as)) = judgC Jc A as (R h)
judgI c Jc A _               = false

-- The claim Jc n = just A, for the context c.
judgOK : Nat → (Nat → Maybe RTy) → Nat → RTy → Bool
judgOK c Jc n A = judgI c Jc A (R n)

------------------------------------------------------------------------
-- Free variables (as finite sets of levels)

merge : List Nat → List Nat → List Nat
merge []       ys       = ys
merge (x ∷ xs) []       = x ∷ xs
merge (x ∷ xs) (y ∷ ys) =
  if x <ℕ y then (x ∷ merge xs (y ∷ ys))
  else (if y <ℕ x then (y ∷ merge (x ∷ xs) ys)
  else (x ∷ merge xs ys))

mergeF₂ : Maybe (List Nat) → Maybe (List Nat) → Maybe (List Nat)
mergeF₂ (just xs) (just ys) = just (merge ys xs)
mergeF₂ _         _         = nothing

mergeF : List Nat → Maybe (List Nat)
mergeF []       = just []
mergeF (a ∷ as) = mergeF₂ (F a) (mergeF as)

fOKM : List Nat → Maybe (List Nat) → Bool
fOKM xs (just ys) = eqL xs ys
fOKM xs nothing   = false

fOKI : List Nat → Maybe Item → Bool
fOKI xs (just (V i))    = eqL xs (i ∷ [])
fOKI xs (just (C h as)) = isHead (R h) ∧ fOKM xs (mergeF as)
fOKI xs _               = false

fOK : Nat → List Nat → Bool
fOK n xs = fOKI xs (R n)

fvR₂ : Maybe (List Nat) → Maybe (List Nat) → Maybe (List Nat) → Maybe (List Nat)
fvR₂ (just a) (just x) (just y) = just (merge a (merge x y))
fvR₂ _        _        _        = nothing

fvR : RTy → Maybe (List Nat)
fvR ⋆ᵣ           = just []
fvR (arrᵣ A s t) = fvR₂ (fvR A) (F s) (F t)

-- The coh side condition (CaTTExp.Typing.cattSide), on free-variable
-- claims instead of unfolded terms.
sideF : Ctx → List Nat → List Nat → Bool
sideF Δ us ut = (≈? us (varsCtx Δ) ∧ ≈? ut (varsCtx Δ)) ∨ (≈? us (∂⁻ Δ) ∧ ≈? ut (∂⁺ Δ))

sideD₂ : Ctx → Maybe (List Nat) → Maybe (List Nat) → Maybe (List Nat) → Bool
sideD₂ Δ (just a) (just x) (just y) = sideF Δ (merge x a) (merge y a)
sideD₂ Δ _        _        _        = false

sideD : Ctx → RTy → Nat → Nat → Bool
sideD Δ A s t = sideD₂ Δ (fvR A) (F s) (F t)

------------------------------------------------------------------------
-- Items

headΔ : RTy → Nat → Nat → Ctx → Bool
headΔ A s t Δ = is-just (checkPs Δ) ∧ sideD Δ A s t

headOK : Nat → RTy → Bool
headOK c ⋆ᵣ           = false
headOK c (arrᵣ A s t) = isCtx (R c) ∧ (tyOK c (arrᵣ A s t) ∧ headΔ A s t ⟦ c ⟧c)

itemOK′ : Item → Bool
itemOK′ (C h _) = isHead (R h)
itemOK′ (S c A) = isCtx (R c) ∧ tyOK c A
itemOK′ (H c A) = headOK c A
itemOK′ _       = true

isV : Nat → Maybe Item → Bool
isV i (just (V j)) = i ==ℕ j
isV i _            = false

-- The ids below k are the variables of the same level.
varsOK : Nat → Bool
varsOK zero    = true
varsOK (suc k) = isV k (R k) ∧ varsOK k

itemOK : Nat → Item → Bool
itemOK k it = decItem k it ∧ itemOK′ it
