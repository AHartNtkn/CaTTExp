------------------------------------------------------------------------
-- Invertibility and pseudo marks for two-tier L
-- (notes/invertibility-markings.md §1.2), as decision procedures.
--
-- A marked context is a context Γ together with a list of marks on
-- its variables: inv, ps, or grpd_k (objects). The judgments
--     Γ ⊢ t inv        Γ ⊢ t ps
-- are syntax-directed on coh, with these rules:
--   (MARK)     a marked variable has its mark
--   (COH-inv)  coherence-case coh                               ⇒ inv
--   (OP-inv)   op-case coh, every top generator g has g[γ] inv  ⇒ inv
--   (OP-ps)    op-case coh, every top g: g[γ] inv, or some xⱼ in g
--              with dⱼ ≥ 1 and xⱼ[γ] ps*                        ⇒ ps
--   (INV-fac)  some i, dᵢ ≥ 1, xᵢ[γ] inv                        ⇒ g[γ] inv
--   (INV-obj)  all dᵢ = 0 and all xᵢ[γ] inv                     ⇒ g[γ] inv
--   (PS-fac)   some j, dⱼ ≥ 1, xⱼ[γ] ps*, some i < j, dᵢ ≥ 1     ⇒ g[γ] inv
--   (INV⇒PS)   t inv and hd(t) ≥ 1                              ⇒ t ps
--   (PS*)      hd(t) = 0, or t ps and (hd(t) = 1, or s ps* and
--              u ps* for t : s → u)                             ⇒ t ps*
--   (OBJ-k)    the 0-target of t is marked grpd_k, hd(t) ≥ k     ⇒ t inv
-- g ranges over the top-dimensional generators of the coh's own
-- unfolding K(Θ) (tuples), and g[γ] is the Gray cell of g at γ.
--
-- Not encoded: ICaTT's destructors t⁻ˡ, t⁻ʳ, λₜ, ρₜ (DES). They are
-- new term formers, which the core syntax does not have. Nothing
-- below derives a term; the judgments only classify existing terms.
--
-- (PS-fac) and (OP-ps) take ps* premises, as in the revised §1.2; the
-- variant with plain ps premises is Conjecture 2.2′ and is not encoded.
--
-- Encoding choices: `inv`, `ps` and `ps*` are computed together on raw terms
-- (`judge`), with the type of a term read off syntactically (lookup
-- for variables, A[γ] for coh). On derivable terms that is the derived
-- type (`typeOf-sound`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Marks (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Typing 𝕊

data Mark : Set where
  minv mps : Mark
  mgrpd    : Nat → Mark

Marks : Set
Marks = List (Nat × Mark)

isInvM isPsM : Mark → Bool
isInvM minv = true
isInvM _    = false
isPsM mps = true
isPsM _   = false

-- grpd_k with k ≤ h
grpdLe : Nat → Mark → Bool
grpdLe h (mgrpd k) = k <ℕ suc h
grpdLe h _         = false

hasMark : (Mark → Bool) → Marks → Nat → Bool
hasMark p ms x = any (λ m → (fst m ==ℕ x) ∧ p (snd m)) ms

------------------------------------------------------------------------
-- Syntactic type of a term.

typeOf : Ctx → Tm → Maybe Ty
typeOf Γ (var i)     = lookup Γ i
typeOf Γ (coh Θ A γ) = just (A [ γ ]ty)
typeOf Γ (cst k)     = just (ty k)

typeOf-sound : ∀ {Γ t A} → Γ ⊢tm t ∶ A → typeOf Γ t ≡ just A
typeOf-sound (var-wf _ eq)      = eq
typeOf-sound (coh-wf _ _ _ _ _) = refl
typeOf-sound (cst-wf _ _)       = refl

-- hd(t) = dim t − 1, and whether it is ≥ n (objects: never).
hdAtLeast : Nat → Maybe Ty → Bool
hdAtLeast n (just A) = n <ℕ dim A
hdAtLeast n nothing  = false

-- (OBJ-k): the 0-target of t is marked grpd_k with k ≤ hd(t), given
-- the dimension and ⋆-endpoints of t's type.
objAt : Marks → Nat → Maybe (Tm × Tm) → Bool
objAt ms n (just (_ , var C)) = hasMark (grpdLe (n ∸ 1)) ms C ∧ (1 <ℕ n)
objAt ms n _                  = false

objRule : Marks → Maybe Ty → Bool
objRule ms nothing  = false
objRule ms (just A) = objAt ms (dim A) (endsTy A)

------------------------------------------------------------------------
-- The judgments.

record IP : Set where
  constructor ip
  field
    jinv jps jpss : Bool      -- inv, ps, ps*
open IP public

nthIP : Nat → List IP → IP
nthIP _       []       = ip false false false
nthIP zero    (x ∷ _)  = x
nthIP (suc n) (_ ∷ xs) = nthIP n xs

dimOf : List El → Nat → Nat
dimOf []       w = 0
dimOf (c ∷ cs) w = if lvl c ==ℕ w then hdim c else dimOf cs w

pos : Nat → Bool
pos zero    = false
pos (suc _) = true

-- (PS-fac): scanning left to right, `seen` records a positive factor.
psFac : Bool → List (Nat × IP) → Bool
psFac seen []             = false
psFac seen ((d , j) ∷ xs) = (seen ∧ pos d ∧ jpss j) ∨ psFac (seen ∨ pos d) xs

-- g[γ] inv, from the dimensions and judgments of its factors.
grayInv : List (Nat × IP) → Bool
grayInv xs =
     any (λ x → pos (fst x) ∧ jinv (snd x)) xs                 -- INV-fac
  ∨ all (λ x → not (pos (fst x)) ∧ jinv (snd x)) xs            -- INV-obj
  ∨ psFac false xs                                            -- PS-fac

-- The premise of (OP-ps) for one top generator.
grayPs : List (Nat × IP) → Bool
grayPs xs = grayInv xs ∨ any (λ x → pos (fst x) ∧ jpss (snd x)) xs

-- The factors of a generator: dimension and judgment of each image.
facOf : List El → List IP → Tuple → List (Nat × IP)
facOf cs comps g = map (λ w → dimOf cs w , nthIP w comps) g

-- (COH-inv) and (OP-inv); (OP-ps). `comps` are the judgments of γ.
invC psC : Ctx → Ty → Tm → Tm → List IP → Bool
invC Θ A t u comps =
  cohCase Θ A t u ∨ (opCase Θ A t u ∧ all (λ g → grayInv (facOf (cells Θ) comps g)) (topT (homs Θ)))
psC Θ A t u comps =
  opCase Θ A t u ∧ all (λ g → grayPs (facOf (cells Θ) comps g)) (topT (homs Θ))

-- `judge n` computes all three judgments; n is fuel for the descent
-- into boundaries that (PS*) needs, and n = dim t suffices (`judgeT`).
mutual
  judge : Nat → Marks → Ctx → Tm → IP
  judge n ms Γ (var x) =
    let i = hasMark isInvM ms x ∨ objRule ms (lookup Γ x)
        p = hasMark isPsM ms x ∨ (i ∧ hdAtLeast 1 (lookup Γ x))
    in ip i p (star n ms Γ (lookup Γ x) p)
  judge n ms Γ (cst k) =
    let i = objRule ms (just (ty k))
        p = i ∧ hdAtLeast 1 (just (ty k))
    in ip i p (star n ms Γ (just (ty k)) p)
  judge n ms Γ (coh Θ ⋆ γ) = ip false false false
  judge n ms Γ (coh Θ (arr A t u) γ) =
    let comps = judgeSub n ms Γ γ
        ty'   = just (arr A t u [ γ ]ty)
        i     = invC Θ A t u comps ∨ objRule ms ty'
        p     = psC Θ A t u comps ∨ (i ∧ hdAtLeast 1 ty')
    in ip i p (star n ms Γ ty' p)

  judgeSub : Nat → Marks → Ctx → Sub → List IP
  judgeSub n ms Γ ⟨⟩       = []
  judgeSub n ms Γ (γ ,ₛ t) = judgeSub n ms Γ γ ++ (judge n ms Γ t ∷ [])

  -- (PS*) for a term of the given type that is ps iff p.
  star : Nat → Marks → Ctx → Maybe Ty → Bool → Bool
  star n ms Γ nothing  p = false
  star n ms Γ (just A) p = (dim A ==ℕ 1) ∨ (p ∧ ((dim A ==ℕ 2) ∨ bdStar n ms Γ A))

  bdStar : Nat → Marks → Ctx → Ty → Bool
  bdStar zero    ms Γ A           = false
  bdStar (suc n) ms Γ ⋆           = false
  bdStar (suc n) ms Γ (arr A s u) = jpss (judge n ms Γ s) ∧ jpss (judge n ms Γ u)

fuelOf : Ctx → Tm → Nat
fuelOf Γ t with typeOf Γ t
... | just A  = dim A
... | nothing = 0

judgeT : Marks → Ctx → Tm → IP
judgeT ms Γ t = judge (fuelOf Γ t) ms Γ t

_⊢_inv _⊢_ps _⊢_ps* : Marks × Ctx → Tm → Bool
(ms , Γ) ⊢ t inv = jinv (judgeT ms Γ t)
(ms , Γ) ⊢ t ps  = jps (judgeT ms Γ t)
(ms , Γ) ⊢ t ps* = jpss (judgeT ms Γ t)
