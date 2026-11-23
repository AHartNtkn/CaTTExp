------------------------------------------------------------------------
-- DES satisfies the presupposition law (CaTTExp.Binder.Presup,
-- `PresupLaws`), over any binder-free signature 𝕊₀, any mark judgment
-- for which substitution is admissible, and any coh side condition
-- that accepts the two coherences DES's result types use: the
-- composite of n-cells over Dⁿ⁺¹ ∨ Dⁿ⁺¹ (`compPC`) and the identity
-- over Dⁿ (`diskD`), for every n.
--
-- Opening the argument telescope Dⁿ⁺¹ after Γ (|Γ| = g) gives the disk
-- whose boundary variables are var g, …: `argsG g n`, with types
-- `tyG g m`. In it the cell t : u → v is typed, the destructors t⁻ˡ,
-- t⁻ʳ : v → u are typed by the binder rule (the inv premise on t by
-- MarkVar), and the composites and identities of the unit laws by
-- the coh rule, with the pasting contexts proved pasting for every n
-- through the pure pasting judgment.
--
-- The side-condition hypotheses (`side-comp`, `side-id`) hold for
-- plain CaTT for every n (CaTTExp.Binder.DesSideCatt, which also gives
-- unconditional presupposition `catt-tm-ty`); for L's side condition
-- they are MARK's (ledger S26i). `des-tm-ty` is presupposition for
-- 𝕊₀ + DES under these hypotheses.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.Des
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Pure as P
import CaTTExp.Pasting

module CaTTExp.Binder.DesPresup (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (desBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open DesConstruction K DesF (λ b → b)
open import CaTTExp.Binder.SyntaxLemmas K B

------------------------------------------------------------------------
-- Disks with free variables from g.

tyG : Nat → Nat → Ty
tyG g zero    = ⋆
tyG g (suc n) = arr (tyG g n) (var (g + (n + n))) (var (g + suc (n + n)))

diskG : Nat → Nat → Ctx
diskG g zero    = ε ▸ ⋆
diskG g (suc n) = diskG g n ▸ tyG g n ▸ tyG g (suc n)

argsG : Nat → Nat → Ctx
argsG g n = diskG g n ▸ tyG g n ▸[ minv ∷ [] ] tyG g (suc n)

------------------------------------------------------------------------
-- Arithmetic.

dd-suc : ∀ n → suc n + suc n ≡ suc (suc (n + n))
dd-suc n = cong suc (+-suc n n)

<dd : ∀ i n → T (i <ℕ n + n) → T (i <ℕ suc n + suc n)
<dd i n p = <-suc i (n + suc n) (<-trans i (n + n) (n + suc n) p (+-<suc n n))

dd< : ∀ n → T ((n + n) <ℕ suc n + suc n)
dd< n = <-suc (n + n) (n + suc n) (+-<suc n n)

sdd< : ∀ n → T (suc (n + n) <ℕ suc n + suc n)
sdd< n = +-<suc n n

lenG : ∀ g n → len (diskG g n) ≡ suc (n + n)
lenG g zero    = refl
lenG g (suc n) rewrite lenG g n | +-suc n n = refl

lenB : ∀ n → len (diskB n) ≡ suc (n + n)
lenB zero    = refl
lenB (suc n) rewrite lenB n | +-suc n n = refl

------------------------------------------------------------------------
-- Opening and substituting disks.

pick-fresh : ∀ g j i d → T (i <ℕ j) → pickOr (fresh g j) i d ≡ var (g + i)
pick-fresh g (suc j) i d p rewrite lenₛ-fresh g j with i ==ℕ j in e
... | true  = cong (λ x → var (g + x)) (sym (==→≡ i j e))
... | false = pick-fresh g j i d (<suc-≢ i j p e)

-- Opening by ts that sends the first m + m bound variables to var g, ….
module _ (g : Nat) (ts : Sub) where

  OpOK : Nat → Set
  OpOK m = ∀ i → T (i <ℕ m) → pickOr ts i (bvar 0 i) ≡ var (g + i)

  op-tyB : ∀ m → OpOK (m + m) → opTy 0 ts (tyB m) ≡ tyG g m
  op-tyB zero    _ = refl
  op-tyB (suc m) h =
    cong₃ arr (op-tyB m (λ i p → h i (<dd i m p)))
              (h (m + m) (dd< m)) (h (suc (m + m)) (sdd< m))
    where
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
            a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
    cong₃ f refl refl refl = refl

  op-bvs : ∀ k → OpOK k → opSub 0 ts (bvs k) ≡ fresh g k
  op-bvs zero    _ = refl
  op-bvs (suc k) h =
    cong₂ _,ₛ_ (op-bvs k (λ i p → h i (<-suc i k p))) (h k (<-self k))

opOK-fresh : ∀ g j m → T (m <ℕ suc j) → OpOK g (fresh g j) m
opOK-fresh g j m q i p = pick-fresh g j i (bvar 0 i) (<-≤ i m j p q)
  where
  <-≤ : ∀ i m j → T (i <ℕ m) → T (m <ℕ suc j) → T (i <ℕ j)
  <-≤ zero    (suc m) (suc j) _ _ = tt
  <-≤ (suc i) (suc m) (suc j) p q = <-≤ i m j p q
  <-≤ zero    (suc zero)    zero _ ()
  <-≤ zero    (suc (suc m)) zero _ ()
  <-≤ (suc i) (suc zero)    zero () _
  <-≤ (suc i) (suc (suc m)) zero _ ()

-- Opening the disk telescopes after g.
open-diskB : ∀ g m → openTel g (diskB m) ≡ diskG g m
open-diskB g zero    = refl
open-diskB g (suc m) rewrite lenB m | open-diskB g m =
  cong₂ (λ X Y → diskG g m ▸ X ▸ Y)
    (op-tyB g (fresh g (suc (m + m))) m
       (opOK-fresh g (suc (m + m)) (m + m) (<-suc (m + m) (suc (m + m)) (<-self (m + m)))))
    (op-tyB g (fresh g (suc (suc (m + m)))) (suc m)
       (opOK-fresh g (suc (suc (m + m))) (suc m + suc m)
          (subst (λ x → T (x <ℕ suc (suc (m + m)))) (sym (+-suc m m)) (<-self (suc (m + m))))))

open-argsD : ∀ g n → openTel g (argsD n) ≡ argsG g n
open-argsD g n rewrite lenB n | open-diskB g n =
  cong₂ (λ X Y → diskG g n ▸ X ▸[ minv ∷ [] ] Y)
    (op-tyB g (fresh g (suc (n + n))) n
       (opOK-fresh g (suc (n + n)) (n + n) (<-suc (n + n) (suc (n + n)) (<-self (n + n)))))
    (op-tyB g (fresh g (suc (suc (n + n)))) (suc n)
       (opOK-fresh g (suc (suc (n + n))) (suc n + suc n)
          (subst (λ x → T (x <ℕ suc (suc (n + n)))) (sym (+-suc n n)) (<-self (suc (n + n))))))

len-argsD : ∀ n → len (argsD n) ≡ 3 + (n + n)
len-argsD n rewrite lenB n = refl

------------------------------------------------------------------------
-- The pasting contexts, through the pure pasting judgment.

module PS where
  open CaTTExp.Pasting P.∅
  import CaTTExp.Binder.Pasting 𝕊 as BP
  open BP using (embTy; embCtx; toPure; toPure-ps)

  tyP : Nat → P.Ty
  tyP zero    = P.⋆
  tyP (suc n) = P.arr (tyP n) (P.var (n + n)) (P.var (suc (n + n)))

  diskP : Nat → P.Ctx
  diskP zero    = P.ε P.▸ P.⋆
  diskP (suc n) = diskP n P.▸ tyP n P.▸ tyP (suc n)

  compP : Nat → P.Ctx
  compP n = diskP (suc n) P.▸ tyP n P.▸ P.arr (tyP n) (P.var (suc (n + n))) (P.var (3 + (n + n)))

  lenP : ∀ n → P.len (diskP n) ≡ suc (n + n)
  lenP zero    = refl
  lenP (suc n) rewrite lenP n | +-suc n n = refl

  diskPs : ∀ n → diskP n ⊢ps (n + n) ∶ tyP n
  diskPs zero    = pss
  diskPs (suc n) =
    subst (λ x → diskP (suc n) ⊢ps x ∶ tyP (suc n)) (sym (dd-suc n))
      (subst (λ L → (diskP n P.▸ tyP n P.▸ P.arr (tyP n) (P.var (n + n)) (P.var L))
                      ⊢ps suc L ∶ P.arr (tyP n) (P.var (n + n)) (P.var L))
             (lenP n) (pse (diskPs n)))

  down : ∀ m {Γ x} → Γ ⊢ps x ∶ tyP m → Γ ⊢ps
  down zero    d = ps d
  down (suc m) d = down m (psd d)

  compPx : ∀ n → compP n ⊢ps suc (3 + (n + n)) ∶ P.arr (tyP n) (P.var (suc (n + n))) (P.var (3 + (n + n)))
  compPx n =
    subst (λ L → (diskP (suc n) P.▸ tyP n P.▸ P.arr (tyP n) (P.var (suc (n + n))) (P.var (suc (suc L))))
                   ⊢ps suc (suc (suc L)) ∶ P.arr (tyP n) (P.var (suc (n + n))) (P.var (suc (suc L))))
          (lenP n) (pse (psd (diskPs (suc n))))

  diskP-ps : ∀ n → diskP n ⊢ps
  diskP-ps n = down n (diskPs n)

  compP-ps : ∀ n → compP n ⊢ps
  compP-ps n = down n (psd (compPx n))

  emb-tyP : ∀ n → embTy (tyP n) ≡ tyD n
  emb-tyP zero    = refl
  emb-tyP (suc n) = cong (λ A → arr A (var (n + n)) (var (suc (n + n)))) (emb-tyP n)

  emb-diskP : ∀ n → embCtx (diskP n) ≡ diskD n
  emb-diskP zero    = refl
  emb-diskP (suc n) rewrite emb-diskP n | emb-tyP n | emb-tyP (suc n) = refl

  emb-compP : ∀ n → embCtx (compP n) ≡ compPC n
  emb-compP n rewrite emb-diskP (suc n) | emb-tyP n = refl

  diskD-ps : ∀ n → BP._⊢ps (diskD n)
  diskD-ps n = diskP n , subst (λ Δ → toPure Δ ≡ just (diskP n)) (emb-diskP n) (toPure-ps (diskPs n))
                       , diskP-ps n

  compPC-ps : ∀ n → BP._⊢ps (compPC n)
  compPC-ps n = compP n , subst (λ Δ → toPure Δ ≡ just (compP n)) (emb-compP n) (toPure-ps (compPx n))
                        , compP-ps n

------------------------------------------------------------------------
-- Substituting into disks with free variables.

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

tyD-sub : ∀ g m ρ → (∀ i → T (i <ℕ m + m) → lookupₛ ρ i ≡ var (g + i)) → tyD m [ ρ ]ty ≡ tyG g m
tyD-sub g zero    ρ h = refl
tyD-sub g (suc m) ρ h =
  cong₃ arr (tyD-sub g m ρ (λ i p → h i (<dd i m p)))
            (h (m + m) (dd< m)) (h (suc (m + m)) (sdd< m))

private
  ==+ : ∀ a i k → ((a + i) ==ℕ (a + k)) ≡ (i ==ℕ k)
  ==+ zero    i k = refl
  ==+ (suc a) i k = ==+ a i k

  <+ : ∀ a i k → T (i <ℕ k) → T ((a + i) <ℕ (a + k))
  <+ zero    i k p = p
  <+ (suc a) i k p = <+ a i k p

-- Looking up past σ in σ ++ τ.
lk-++ : ∀ σ τ j → T (j <ℕ lenₛ τ) → lookupₛ (σ ++ₛ τ) (lenₛ σ + j) ≡ lookupₛ τ j
lk-++ σ (τ ,ₛ t) j p
  rewrite lenₛ-++ σ τ | ==+ (lenₛ σ) j (lenₛ τ) with j ==ℕ lenₛ τ in e
... | true  = refl
... | false = lk-++ σ τ j (<suc-≢ j (lenₛ τ) p e)

-- Looking up below σ in σ ++ τ.
lk-++< : ∀ σ τ i → T (i <ℕ lenₛ σ) → lookupₛ (σ ++ₛ τ) i ≡ lookupₛ σ i
lk-++< σ ⟨⟩       i p = refl
lk-++< σ (τ ,ₛ t) i p
  rewrite <→≢ i (lenₛ (σ ++ₛ τ))
            (subst (λ x → T (i <ℕ x)) (sym (lenₛ-++ σ τ)) (<-+ i (lenₛ σ) (lenₛ τ) p))
  = lk-++< σ τ i p

lk-fresh : ∀ g K τ i → T (i <ℕ K) → lookupₛ (fresh g K ++ₛ τ) i ≡ var (g + i)
lk-fresh g K τ i p =
  trans (lk-++< (fresh g K) τ i (subst (λ x → T (i <ℕ x)) (sym (lenₛ-fresh g K)) p))
        (pick-like i p)
  where
  pick-like : ∀ i → T (i <ℕ K) → lookupₛ (fresh g K) i ≡ var (g + i)
  pick-like i p = subst (λ σ → lookupₛ σ i ≡ var (g + i)) (⟨⟩++′ (fresh g K)) (lookup-fresh ⟨⟩ g K i p)
    where
    ⟨⟩++′ : ∀ τ → ⟨⟩ ++ₛ τ ≡ τ
    ⟨⟩++′ ⟨⟩       = refl
    ⟨⟩++′ (τ ,ₛ t) = cong (_,ₛ t) (⟨⟩++′ τ)

lk-at : ∀ g K τ j → T (j <ℕ lenₛ τ) → lookupₛ (fresh g K ++ₛ τ) (K + j) ≡ lookupₛ τ j
lk-at g K τ j p = subst (λ x → lookupₛ (fresh g K ++ₛ τ) (x + j) ≡ lookupₛ τ j) (lenₛ-fresh g K)
                        (lk-++ (fresh g K) τ j p)

lk0 : ∀ g K τ → T (0 <ℕ lenₛ τ) → lookupₛ (fresh g K ++ₛ τ) K ≡ lookupₛ τ 0
lk0 g K τ p = subst (λ x → lookupₛ (fresh g K ++ₛ τ) x ≡ lookupₛ τ 0) (+-zero K) (lk-at g K τ 0 p)

lk1 : ∀ g K τ → T (1 <ℕ lenₛ τ) → lookupₛ (fresh g K ++ₛ τ) (suc K) ≡ lookupₛ τ 1
lk1 g K τ p = subst (λ x → lookupₛ (fresh g K ++ₛ τ) x ≡ lookupₛ τ 1)
                    (trans (+-suc K 0) (cong suc (+-zero K))) (lk-at g K τ 1 p)

lk3 : ∀ g K τ → T (3 <ℕ lenₛ τ) → lookupₛ (fresh g K ++ₛ τ) (3 + K) ≡ lookupₛ τ 3
lk3 g K τ p = subst (λ x → lookupₛ (fresh g K ++ₛ τ) x ≡ lookupₛ τ 3) (+3 K) (lk-at g K τ 3 p)
  where
  +3 : ∀ K → K + 3 ≡ 3 + K
  +3 zero    = refl
  +3 (suc K) = cong suc (+3 K)

-- tyD n under fresh g (n + n) ++ τ.
tyD-fresh : ∀ g n τ → tyD n [ fresh g (n + n) ++ₛ τ ]ty ≡ tyG g n
tyD-fresh g n τ = tyD-sub g n _ (λ i p → lk-fresh g (n + n) τ i p)

------------------------------------------------------------------------
-- Scoping: the argument telescope is closed.

sc-tyB : ∀ m n → T (scTy? m (tyB n))
sc-tyB m zero    = tt
sc-tyB m (suc n) = ∧T (sc-tyB m n) tt

sc-diskB : ∀ m n → T (scTel? m (diskB n))
sc-diskB m zero    = tt
sc-diskB m (suc n) = ∧T (∧T (sc-diskB m n) (sc-tyB m n)) (sc-tyB m (suc n))

sc-argsD : ∀ m n → T (scTel? m (argsD n))
sc-argsD m n = ∧T (∧T (sc-diskB m n) (sc-tyB m n)) (sc-tyB m (suc n))

------------------------------------------------------------------------
-- Typing.

tyG0 : ∀ n → tyG 0 n ≡ tyD n
tyG0 zero    = refl
tyG0 (suc n) = cong (λ A → arr A (var (n + n)) (var (suc (n + n)))) (tyG0 n)

diskG0 : ∀ n → diskG 0 n ≡ diskD n
diskG0 zero    = refl
diskG0 (suc n) rewrite diskG0 n | tyG0 n | tyG0 (suc n) = refl

ε⧺ : ∀ Ξ → ε ⧺ Ξ ≡ Ξ
ε⧺ ε             = refl
ε⧺ (Ξ ▸[ ms ] A) = cong (_▸[ ms ] A) (ε⧺ Ξ)

lenΞ : ∀ Γ n → len (Γ ⧺ diskG (len Γ) n) ≡ len Γ + suc (n + n)
lenΞ Γ n = trans (len-⧺ Γ (diskG (len Γ) n)) (cong (len Γ +_) (lenG (len Γ) n))

open import CaTTExp.Binder.DesLaws 𝕊₀ using (desLaws)

module Typed
  (side : Ctx → Ty → Tm → Tm → Bool)
  (mark : Ctx → BM.Mark → Tm → Bool)
  where

  open import CaTTExp.Binder.TypingWith 𝕊 side mark
  open import CaTTExp.Binder.Scoping 𝕊 side mark
  open import CaTTExp.Binder.Rename 𝕊 side mark
  open import CaTTExp.Binder.Subst 𝕊 side mark
  open import CaTTExp.Binder.Presup 𝕊 side mark
  open Laws 𝕊

  module _ (closed : Closed) (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar)
    (side-comp : ∀ n → T (side (compPC n) (tyD n) (var (n + n)) (var (3 + (n + n)))))
    (side-id   : ∀ n → T (side (diskD n) (tyD n) (var (n + n)) (var (n + n))))
    where

    private
      wkT : ∀ {Γ ms B t A} → Γ ⊢tm t ∶ A → (Γ ▸[ ms ] B) ⊢ctx → (Γ ▸[ ms ] B) ⊢tm t ∶ A
      wkT = wk-tm closed desLaws mren
      wkY : ∀ {Γ ms B A} → Γ ⊢ty A → (Γ ▸[ ms ] B) ⊢ctx → (Γ ▸[ ms ] B) ⊢ty A
      wkY = wk-ty closed desLaws mren
      lkY : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
      lkY = lookup-ty closed desLaws mren msub mvar
      tyOfVar : ∀ {Γ i A} → Γ ⊢tm var i ∶ A → Γ ⊢ty A
      tyOfVar (var-wf w eq) = lkY w eq

    ----------------------------------------------------------------------
    -- The disk after Γ.

    record Dk (Γ : Ctx) (n : Nat) : Set where
      field
        ctx : (Γ ⧺ diskG (len Γ) n) ⊢ctx
        ty  : (Γ ⧺ diskG (len Γ) n) ⊢ty tyG (len Γ) n
        top : (Γ ⧺ diskG (len Γ) n) ⊢tm var (len Γ + (n + n)) ∶ tyG (len Γ) n

    -- One more dimension, the new top entry marked ms.
    record Step (Γ : Ctx) (ms : List Mark) (n : Nat) : Set where
      C2 = (Γ ⧺ diskG (len Γ) n) ▸ tyG (len Γ) n ▸[ ms ] tyG (len Γ) (suc n)
      field
        ctx : C2 ⊢ctx
        ty  : C2 ⊢ty tyG (len Γ) (suc n)
        top : C2 ⊢tm var (len Γ + (suc n + suc n)) ∶ tyG (len Γ) (suc n)
        tyn : C2 ⊢ty tyG (len Γ) n
        u   : C2 ⊢tm var (len Γ + (n + n)) ∶ tyG (len Γ) n
        v   : C2 ⊢tm var (len Γ + suc (n + n)) ∶ tyG (len Γ) n

    dk0 : ∀ {Γ} → Γ ⊢ctx → Dk Γ 0
    dk0 {Γ} w = record
      { ctx = c
      ; ty  = ⋆-wf c
      ; top = var-wf c (lookup-top Γ {[]} ⋆ (len Γ + 0) (==-self (+-zero (len Γ))))
      }
      where c = ▸-wf w (⋆-wf w)

    step : ∀ {Γ} ms n → Dk Γ n → Step Γ ms n
    step {Γ} ms n d = record
      { ctx = c2 ; ty = wkY tyS c2 ; top = top2 ; tyn = wkY (wkY (Dk.ty d) c1) c2
      ; u = wkT uS c2 ; v = wkT vS c2 }
      where
      g  = len Γ
      Ξ  = Γ ⧺ diskG g n
      c1 = ▸-wf (Dk.ctx d) (Dk.ty d)
      vS : (Ξ ▸ tyG g n) ⊢tm var (g + suc (n + n)) ∶ tyG g n
      vS = var-wf c1 (lookup-top Ξ {[]} (tyG g n) (g + suc (n + n)) (==-self (sym (lenΞ Γ n))))
      uS : (Ξ ▸ tyG g n) ⊢tm var (g + (n + n)) ∶ tyG g n
      uS = wkT (Dk.top d) c1
      tyS : (Ξ ▸ tyG g n) ⊢ty tyG g (suc n)
      tyS = arr-wf uS vS
      c2 = ▸-wf {ms = ms} c1 tyS
      eq2 : (g + (suc n + suc n)) ≡ len (Ξ ▸ tyG g n)
      eq2 = trans (cong (g +_) (dd-suc n)) (trans (+-suc g (suc (n + n))) (cong suc (sym (lenΞ Γ n))))
      top2 = var-wf c2 (lookup-top (Ξ ▸ tyG g n) {ms} (tyG g (suc n)) (g + (suc n + suc n)) (==-self eq2))

    dk : ∀ {Γ} n → Γ ⊢ctx → Dk Γ n
    dk zero    w = dk0 w
    dk (suc n) w = let s = step [] n (dk n w) in
      record { ctx = Step.ctx s ; ty = Step.ty s ; top = Step.top s }

    ----------------------------------------------------------------------
    -- Substitutions into disks.

    subDisk : ∀ {Δ} g m s → Δ ⊢ty tyG g m → Δ ⊢tm s ∶ tyG g m →
              Δ ⊢sub fresh g (m + m) ,ₛ s ∶ diskD m
    subDisk g zero    s _ d = ,-wf (⟨⟩-wf (tm-ctx d)) d tt
    subDisk {Δ} g (suc k) s (arr-wf du dv) d =
      subst (λ x → Δ ⊢sub fresh g x ,ₛ s ∶ diskD (suc k)) (sym (dd-suc k))
        (,-wf (,-wf (subDisk g k _ (tyOfVar du) du)
                    (subst (Δ ⊢tm var (g + suc (k + k)) ∶_)
                           (sym (tyD-fresh g k (⟨⟩ ,ₛ var (g + (k + k))))) dv)
                    tt)
              (subst (Δ ⊢tm s ∶_)
                     (sym (tyD-sub g (suc k) (fresh g (suc (suc (k + k))))
                       (λ i p → lk-fresh g (suc (suc (k + k))) ⟨⟩ i
                                  (subst (λ x → T (i <ℕ x)) (dd-suc k) p))))
                     d)
              tt)

    subDisk′ : ∀ {Δ} g m s t x → Δ ⊢ty tyG g m → Δ ⊢tm s ∶ tyG g m → Δ ⊢tm t ∶ tyG g m →
               Δ ⊢tm x ∶ arr (tyG g m) s t →
               Δ ⊢sub fresh g (m + m) ,ₛ s ,ₛ t ,ₛ x ∶ diskD (suc m)
    subDisk′ {Δ} g m s t x a ds dt dx =
      ,-wf (,-wf (subDisk g m s a ds)
                 (subst (Δ ⊢tm t ∶_) (sym (tyD-fresh g m (⟨⟩ ,ₛ s))) dt) tt)
           (subst (Δ ⊢tm x ∶_)
                  (sym (cong₃ arr (tyD-fresh g m (⟨⟩ ,ₛ s ,ₛ t))
                                  (lk0 g (m + m) (⟨⟩ ,ₛ s ,ₛ t) tt)
                                  (lk1 g (m + m) (⟨⟩ ,ₛ s ,ₛ t) tt)))
                  dx)
           tt

    ----------------------------------------------------------------------
    -- The pasting contexts are well formed.

    private
      dkε : ∀ n → Dk ε n
      dkε n = dk n ε-wf

      stε : ∀ n → Step ε [] n
      stε n = step [] n (dkε n)

    private
      trY : ∀ {Γ Γ′ A A′} → Γ ≡ Γ′ → A ≡ A′ → Γ ⊢ty A → Γ′ ⊢ty A′
      trY refl refl a = a

      G0 : ∀ n → ε ⧺ diskG 0 n ≡ diskD n
      G0 n = trans (ε⧺ (diskG 0 n)) (diskG0 n)

    diskD-ctx : ∀ n → diskD n ⊢ctx
    diskD-ctx n = subst _⊢ctx (G0 n) (Dk.ctx (dkε n))

    idTy-wf : ∀ n → diskD n ⊢ty arr (tyD n) (var (n + n)) (var (n + n))
    idTy-wf n = trY (G0 n) (cong (λ A → arr A (var (n + n)) (var (n + n))) (tyG0 n))
                    (arr-wf (Dk.top (dkε n)) (Dk.top (dkε n)))

    private
      C3 : Nat → Ctx
      C3 n = (ε ⧺ diskG 0 (suc n)) ▸ tyG 0 n

      c3 : ∀ n → C3 n ⊢ctx
      c3 n = ▸-wf (Step.ctx (stε n)) (Step.tyn (stε n))

      h3 : ∀ n → C3 n ⊢tm var (3 + (n + n)) ∶ tyG 0 n
      h3 n = var-wf (c3 n) (lookup-top (ε ⧺ diskG 0 (suc n)) {[]} (tyG 0 n) (3 + (n + n))
                              (==-self (cong (λ x → suc (suc x)) (sym (lenΞ ε n)))))

      βTy : ∀ n → C3 n ⊢ty arr (tyG 0 n) (var (suc (n + n))) (var (3 + (n + n)))
      βTy n = arr-wf (wkT (Step.v (stε n)) (c3 n)) (h3 n)

      c4 : ∀ n → ((C3 n) ▸ arr (tyG 0 n) (var (suc (n + n))) (var (3 + (n + n)))) ⊢ctx
      c4 n = ▸-wf (c3 n) (βTy n)

      cmpTyε : ∀ n → ((C3 n) ▸ arr (tyG 0 n) (var (suc (n + n))) (var (3 + (n + n))))
                     ⊢ty arr (tyG 0 n) (var (n + n)) (var (3 + (n + n)))
      cmpTyε n = arr-wf (wkT (wkT (Step.u (stε n)) (c3 n)) (c4 n)) (wkT (h3 n) (c4 n))

      compPC-eq : ∀ n → (C3 n) ▸ arr (tyG 0 n) (var (suc (n + n))) (var (3 + (n + n))) ≡ compPC n
      compPC-eq n rewrite G0 (suc n) | tyG0 n = refl

    compPC-ctx : ∀ n → compPC n ⊢ctx
    compPC-ctx n = subst _⊢ctx (compPC-eq n) (c4 n)

    cmpTy-wf : ∀ n → compPC n ⊢ty arr (tyD n) (var (n + n)) (var (3 + (n + n)))
    cmpTy-wf n = trY (compPC-eq n) (cong (λ A → arr A (var (n + n)) (var (3 + (n + n)))) (tyG0 n))
                     (cmpTyε n)

    ----------------------------------------------------------------------
    -- Composites and identities with free variables.

    comp-wf : ∀ {Δ} g n f h₁ α h β → Δ ⊢ty tyG g n →
              Δ ⊢tm f ∶ tyG g n → Δ ⊢tm h₁ ∶ tyG g n → Δ ⊢tm α ∶ arr (tyG g n) f h₁ →
              Δ ⊢tm h ∶ tyG g n → Δ ⊢tm β ∶ arr (tyG g n) h₁ h →
              Δ ⊢tm comp n (fresh g (n + n)) f h₁ α h β ∶ arr (tyG g n) f h
    comp-wf {Δ} g n f h₁ α h β a df dg dα dh dβ =
      subst (Δ ⊢tm comp n (fresh g (n + n)) f h₁ α h β ∶_)
        (cong₃ arr (tyD-fresh g n τ) (lk0 g (n + n) τ tt) (lk3 g (n + n) τ tt))
        (coh-wf (PS.compPC-ps n) (compPC-ctx n) (cmpTy-wf n) (side-comp n)
          (,-wf (,-wf (subDisk′ g n f h₁ α a df dg dα)
                      (subst (Δ ⊢tm h ∶_) (sym (tyD-fresh g n (⟨⟩ ,ₛ f ,ₛ h₁ ,ₛ α))) dh) tt)
                (subst (Δ ⊢tm β ∶_)
                   (sym (cong₃ arr (tyD-fresh g n (⟨⟩ ,ₛ f ,ₛ h₁ ,ₛ α ,ₛ h))
                                   (lk1 g (n + n) (⟨⟩ ,ₛ f ,ₛ h₁ ,ₛ α ,ₛ h) tt)
                                   (lk3 g (n + n) (⟨⟩ ,ₛ f ,ₛ h₁ ,ₛ α ,ₛ h) tt)))
                   dβ)
                tt))
      where
      τ = ⟨⟩ ,ₛ f ,ₛ h₁ ,ₛ α ,ₛ h ,ₛ β

    idc-wf : ∀ {Δ} g n f → Δ ⊢ty tyG g n → Δ ⊢tm f ∶ tyG g n →
             Δ ⊢tm idc n (fresh g (n + n)) f ∶ arr (tyG g n) f f
    idc-wf {Δ} g n f a df =
      subst (Δ ⊢tm idc n (fresh g (n + n)) f ∶_)
        (cong₃ arr (tyD-fresh g n (⟨⟩ ,ₛ f)) (lk0 g (n + n) (⟨⟩ ,ₛ f) tt) (lk0 g (n + n) (⟨⟩ ,ₛ f) tt))
        (coh-wf (PS.diskD-ps n) (diskD-ctx n) (idTy-wf n) (side-id n) (subDisk g n f a df))

    ----------------------------------------------------------------------
    -- The result types.

    private
      trY′ : ∀ {Γ Γ′ A A′} → Γ ≡ Γ′ → A ≡ A′ → Γ ⊢ty A → Γ′ ⊢ty A′
      trY′ refl refl a = a

      trA : ∀ {Γ Γ′ ts ts′ Θ} → Γ ≡ Γ′ → ts ≡ ts′ → Γ ⊢args ts ∶ Θ → Γ′ ⊢args ts′ ∶ Θ
      trA refl refl a = a

    isInvK : DesKind → Bool
    isInvK linvK = true
    isInvK rinvK = true
    isInvK _     = false

    module Res {Γ : Ctx} (n : Nat) (w : Γ ⊢ctx) where
      g  = len Γ
      st = step (minv ∷ []) n (dk n w)
      Γ′ = Γ ⧺ argsG g n
      KK = 3 + (n + n)
      ts = fresh g KK

      okT : OpOK g ts KK
      okT = opOK-fresh g KK KK (<-self KK)

      okn : OpOK g ts (n + n)
      okn i p = okT i (<-suc i _ (<-suc i _ (<-suc i _ p)))

      pD = okT (n + n) (<-suc (n + n) _ (<-suc (n + n) _ (<-self (n + n))))
      pS = okT (suc (n + n)) (<-suc (n + n) _ (<-self (n + n)))
      pT = okT (suc (suc (n + n))) (<-self (n + n))

      ttyn = op-tyB g ts n okn
      bdEq = op-bvs g ts (n + n) okn
      allEq = op-bvs g ts KK okT

      u = var (g + (n + n))
      v = var (g + suc (n + n))
      t = var (g + suc (suc (n + n)))

      dt : Γ′ ⊢tm t ∶ arr (tyG g n) u v
      dt = subst (λ x → Γ′ ⊢tm var (g + x) ∶ tyG g (suc n)) (dd-suc n) (Step.top st)

      sf : DesKind → Tm
      sf k = bnd (des k (suc n)) 0 ε ts

      sfEq : ∀ k → opTm 0 ts (self k n) ≡ sf k
      sfEq k = cong (bnd (des k (suc n)) 0 ε) allEq

      dargs : Γ′ ⊢args ts ∶ argsD n
      dargs = trA (cong (Γ ⧺_) (open-argsD g n)) (cong (fresh g) (len-argsD n))
                 (fresh-args closed desLaws mren msub mvar (argsD n) (sc-argsD 0 n)
                    (subst _⊢ctx (cong (Γ ⧺_) (sym (open-argsD g n))) (Step.ctx st)))

      -- The destructors t⁻ˡ, t⁻ʳ : v → u.
      sf-wf : ∀ k → T (isInvK k) → Γ′ ⊢tm sf k ∶ arr (tyG g n) v u
      sf-wf linvK _ = subst (Γ′ ⊢tm sf linvK ∶_) (cong₃ arr ttyn pS pD)
                            (bnd-wf tt tt (Step.ctx st) tt dargs)
      sf-wf rinvK _ = subst (Γ′ ⊢tm sf rinvK ∶_) (cong₃ arr ttyn pS pD)
                            (bnd-wf tt tt (Step.ctx st) tt dargs)

      wf : ∀ k y Δ → Γ′ ⊢ty opTy 0 ts (res (des k (suc n)) y Δ)
      wf linvK y Δ = trY′ refl (sym (cong₃ arr ttyn pS pD)) (arr-wf (Step.v st) (Step.u st))
      wf rinvK y Δ = trY′ refl (sym (cong₃ arr ttyn pS pD)) (arr-wf (Step.v st) (Step.u st))
      wf unitLK y Δ =
        trY′ refl
          (sym (cong₃ arr (cong₃ arr ttyn pS pS)
             (cong (coh (compPC n) (arr (tyD n) (var (n + n)) (var (3 + (n + n)))))
               (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ bdEq pS) pD) (sfEq linvK)) pS) pT))
             (cong (coh (diskD n) (arr (tyD n) (var (n + n)) (var (n + n)))) (cong₂ _,ₛ_ bdEq pS))))
          (arr-wf (comp-wf g n v u (sf linvK) v t (Step.tyn st) (Step.v st) (Step.u st)
                           (sf-wf linvK tt) (Step.v st) dt)
                  (idc-wf g n v (Step.tyn st) (Step.v st)))
      wf unitRK y Δ =
        trY′ refl
          (sym (cong₃ arr (cong₃ arr ttyn pD pD)
             (cong (coh (compPC n) (arr (tyD n) (var (n + n)) (var (3 + (n + n)))))
               (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ (cong₂ _,ₛ_ bdEq pD) pS) pT) pD) (sfEq rinvK)))
             (cong (coh (diskD n) (arr (tyD n) (var (n + n)) (var (n + n)))) (cong₂ _,ₛ_ bdEq pD))))
          (arr-wf (comp-wf g n u v t u (sf rinvK) (Step.tyn st) (Step.u st) (Step.v st)
                           dt (Step.u st) (sf-wf rinvK tt))
                  (idc-wf g n u (Step.tyn st) (Step.u st)))

    res-wf : ∀ {Γ b y Δ} → T (scTel? (len Γ) Δ) → T (lcTel? 1 Δ) →
             (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → T (bside b y Δ) →
             (Γ ⧺ openTel (len Γ) (bargs b y Δ)) ⊢ty
               opTy 0 (fresh (len Γ) (len (bargs b y Δ))) (bres b y Δ)
    res-wf {b = des k zero} _ _ _ ()
    res-wf {Γ} {des k (suc n)} {y} {ε} _ _ w _ =
      trY′ (cong (Γ ⧺_) (sym (open-argsD (len Γ) n)))
           (cong (λ J → opTy 0 (fresh (len Γ) J) (res (des k (suc n)) y ε)) (sym (len-argsD n)))
           (Res.wf n w k y ε)
    res-wf {b = des k (suc n)} {y} {_ ▸[ _ ] _} _ _ _ ok = ⊥-elim (snd (T∧ {y ==ℕ 0} ok))

    desPresup : PresupLaws
    desPresup = record
      { bargs-sc = λ { (des _ zero) y Δ m _ _ → tt ; (des _ (suc n)) y Δ m _ _ → sc-argsD m n }
      ; res-wf   = res-wf
      }

    -- Presupposition for 𝕊₀ + DES.
    des-tm-ty : SigOK → ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
    des-tm-ty sig = tm-ty closed desLaws mren msub mvar sig desPresup
