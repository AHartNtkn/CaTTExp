------------------------------------------------------------------------
-- Presupposition for the cell heads (ledger S26j, step 2b).
--
-- For every valid head of CaTTExp.Binder.MultimapCells (a Gray object
-- former, or mmc_{k,Φ,t} with mmcTy defined), its type is well formed
-- over its arity (`HeadOK`), in the kernel with plain CaTT's side
-- condition and rule (MARK). Hence PresupLaws (`cells-presup`) and every
-- term of CaTT with ⊗, \, / and the cell heads has a well-formed type
-- (`cells-tm-ty`).
--
-- The arity of mmc_{k,Φ,t} is k objects followed by one kernel cell per
-- entry of Φ, entry j's type being the kernel image of Φ's entry j
-- (`trTy`), and its type is the image of t's type. Well-formedness is
-- by induction along Φ (`ctx-pre`): an image of a type is well formed
-- once the images of its boundaries are typed (`tyWf`), and a boundary
-- s that is not a variable is typed by rule (op) at its canonical head
-- c_s = canon k Φ s (`typTm`):
--
--  * c_s passes the side condition: its biclosed type is the renamed
--    type of s (CaTTExp.Binder.MultimapCellsWf, `sub-mmcTy`), and its
--    arity and type are scoped and locally closed
--    (CaTTExp.Binder.MultimapCellsScope), so honest;
--  * its arguments supArgs k c_s are well typed into its arity: each is
--    a variable of the prefix, whose type is the image of the matching
--    entry, and the image of the renamed entry, after the arguments,
--    is the image of the entry (CaTTExp.Binder.MultimapCellsComm);
--  * so it has type (image of the renamed type of s)[supArgs], which is
--    the image of the type of s, again by commutation.
--
-- No step recurses into the canonical heads' own presupposition: the
-- side condition of c_s is checked syntactically.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.Multimap using (MMI; mmi; atoms; mctx; mterm; atomFm; sortedT; sortedY)
import CaTTExp.Binder.HeadSpec as HS
import CaTTExp.Binder.Laws as BL
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT
open import CaTTExp.Gray.Biclosed.Strengthen using (Below; wf-deps; wf-scope; ∨-l; ∨-r; elem-++l; elem-++r)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_; Deps↓; lookup-some; elem-split)
import CaTTExp.Binder.MultimapCellsRen as MR
open import CaTTExp.Binder.MultimapCellsStrengthen using (nthY-just; upTo-elem; inl; inr)
open import CaTTExp.Binder.MultimapCellsCanon using (map-nthY-upTo; atY-concatAt; nthY-suc)
import CaTTExp.Binder.MultimapCellsWf as MW
import CaTTExp.Binder.MultimapCellsComm as CM
import CaTTExp.Binder.MultimapCellsScope as SC
open import CaTTExp.Binder.GrayForm using (GBKind)

module CaTTExp.Binder.MultimapCellsPresup where

open HS.Laws P.∅ (cellSpec P.K) using (𝕊; spec-honest; spec-head; spec-laws)
open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
open import CaTTExp.Binder.TypingWith 𝕊 cattSide varMark
open import CaTTExp.Binder.Scoping 𝕊 cattSide varMark using ()
open import CaTTExp.Binder.VarMark 𝕊 cattSide using (markVar; markRen; markSub)
open import CaTTExp.Binder.HonestHeads 𝕊 using (HonestAt; honest?)
open import CaTTExp.Binder.HonestHeads 𝕊 using (module Typed)
open Typed cattSide varMark using (op-intro; honest-ok)
import CaTTExp.Binder.Heads 𝕊 as Hd
open Hd.Typed cattSide varMark using (HeadOK; head-presup)
open BL 𝕊 using (Closed; BinderLaws)
open import CaTTExp.Binder.Presup 𝕊 cattSide varMark using (PresupLaws; tm-ty; tm-ctx)
open GCInterface K

closed : Closed
closed ()

laws : BinderLaws
laws = spec-laws

private
  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt
  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

  ==-+ : ∀ g i k → (g + i ==ℕ g + k) ≡ (i ==ℕ k)
  ==-+ zero    i k = refl
  ==-+ (suc g) i k = ==-+ g i k

  <-+l : ∀ k i j → T (i <ℕ j) → T (k + i <ℕ k + j)
  <-+l zero    i j p = p
  <-+l (suc k) i j p = <-+l k i j p

  lt-le : ∀ i j n → T (i <ℕ j) → T (j <ℕ suc n) → T (i <ℕ n)
  lt-le zero    (suc j) (suc n) _ _ = tt
  lt-le (suc i) (suc j) (suc n) p q = lt-le i j n p q
  lt-le zero    (suc j) zero    _ ()
  lt-le (suc i) (suc j) zero    _ ()

  concatAt-inv : ∀ (f : Nat → GB.CTy) xs x → In (concatAt (GT.map f xs)) x → Σ Nat (λ j → In xs j × In (atY (f j)) x)
  concatAt-inv f (y ∷ xs) x p with elem-split x (atY (f y)) (concatAt (GT.map f xs)) p
  ... | inl q = y , ∨-l (y ==ℕ y) _ (==ℕ-refl y) , q
  ... | inr q = let (j , jin , r) = concatAt-inv f xs x q in j , ∨-r (j ==ℕ y) _ jin , r

  is-just-inv : ∀ {X : Set} (m : Maybe X) → T (is-just m) → Σ X λ x → m ≡ just x
  is-just-inv (just x) _ = x , refl

------------------------------------------------------------------------
-- Lists.

takeN : Nat → List Nat → List Nat
takeN zero    xs       = []
takeN (suc n) []       = []
takeN (suc n) (x ∷ xs) = x ∷ takeN n xs

dropN : Nat → List Nat → List Nat
dropN zero    xs       = xs
dropN (suc n) []       = []
dropN (suc n) (x ∷ xs) = dropN n xs

take-drop : ∀ n xs → takeN n xs ++ dropN n xs ≡ xs
take-drop zero    xs       = refl
take-drop (suc n) []       = refl
take-drop (suc n) (x ∷ xs) = cong (x ∷_) (take-drop n xs)

take-snoc : ∀ xs p → T (p <ℕ GT.length xs) → takeN (suc p) xs ≡ takeN p xs ++ (MR.nth xs p ∷ [])
take-snoc (x ∷ xs) zero    _ = refl
take-snoc (x ∷ xs) (suc p) l = cong (x ∷_) (take-snoc xs p l)

take-all : ∀ xs → takeN (GT.length xs) xs ≡ xs
take-all []       = refl
take-all (x ∷ xs) = cong (x ∷_) (take-all xs)

length-take : ∀ xs p → T (p <ℕ suc (GT.length xs)) → GT.length (takeN p xs) ≡ p
length-take xs       zero    _ = refl
length-take (x ∷ xs) (suc p) l = cong suc (length-take xs p l)
length-take []       (suc zero) ()
length-take []       (suc (suc p)) ()

map-++′ : ∀ (f : Nat → Nat) xs ys → GT.map f (xs ++ ys) ≡ GT.map f xs ++ GT.map f ys
map-++′ f []       ys = refl
map-++′ f (x ∷ xs) ys = cong (f x ∷_) (map-++′ f xs ys)

dropC : Nat → GB.Ctx → GB.Ctx
dropC zero    Φ       = Φ
dropC (suc n) []      = []
dropC (suc n) (A ∷ Φ) = dropC n Φ

drop-step : ∀ Φ j → T (j <ℕ GT.length Φ) → dropC j Φ ≡ nthY Φ j ∷ dropC (suc j) Φ
drop-step (A ∷ Φ) zero    _ = refl
drop-step (A ∷ Φ) (suc j) l = trans (drop-step Φ j l) (cong (_∷ dropC (suc j) Φ) (sym (nthY-suc A Φ j)))

drop-all : ∀ Φ → dropC (GT.length Φ) Φ ≡ []
drop-all []      = refl
drop-all (A ∷ Φ) = drop-all Φ

------------------------------------------------------------------------
-- Substitutions of variables.

varsOf-snoc : ∀ ρ xs x → varsOf ρ (xs ++ (x ∷ [])) ≡ varsOf ρ xs ,ₛ var x
varsOf-snoc ρ []       x = refl
varsOf-snoc ρ (y ∷ xs) x = varsOf-snoc (ρ ,ₛ var y) xs x

varsOf-++ : ∀ ρ xs ys → varsOf ρ (xs ++ ys) ≡ varsOf (varsOf ρ xs) ys
varsOf-++ ρ []       ys = refl
varsOf-++ ρ (x ∷ xs) ys = varsOf-++ (ρ ,ₛ var x) xs ys

ext-varsOf : ∀ A σ js → T (scTy? (lenₛ σ) A) → A [ varsOf σ js ]ty ≡ A [ σ ]ty
ext-varsOf A σ []       p = refl
ext-varsOf A σ (j ∷ js) p = trans (ext-varsOf A (σ ,ₛ var j) js (scTy-suc A p)) (ext-ty A σ (var j) p)

lenₛ-varsOf : ∀ ρ js → lenₛ (varsOf ρ js) ≡ lenₛ ρ + GT.length js
lenₛ-varsOf = CM.lenₛ-varsOf K B gform mmc unit

------------------------------------------------------------------------
-- Prefixes of an arity, entry by entry.

pre : Nat → GB.Ctx → Nat → Ctx
pre k Φ zero    = atomsTel k
pre k Φ (suc j) = pre k Φ j ▸[ marksOf (nthY Φ j) ] trTy k Φ (nthY Φ j)

len-atomsTel : ∀ k → len (atomsTel k) ≡ k
len-atomsTel zero    = refl
len-atomsTel (suc k) = cong suc (len-atomsTel k)

len-pre : ∀ k Φ j → len (pre k Φ j) ≡ k + j
len-pre k Φ zero    = trans (len-atomsTel k) (sym (+-zero k))
len-pre k Φ (suc j) = trans (cong suc (len-pre k Φ j)) (sym (+-suc k j))

pre-cells : ∀ k Φ j → T (j <ℕ suc (GT.length Φ)) → cellsTel k Φ (pre k Φ j) (dropC j Φ) ≡ arity k Φ
pre-cells k Φ zero    _ = refl
pre-cells k Φ (suc j) l =
  trans (sym (cong (cellsTel k Φ (pre k Φ j)) (drop-step Φ j l)))
        (pre-cells k Φ j (<-suc j (GT.length Φ) l))

pre-arity : ∀ k Φ → pre k Φ (GT.length Φ) ≡ arity k Φ
pre-arity k Φ =
  trans (cong (cellsTel k Φ (pre k Φ (GT.length Φ))) (sym (drop-all Φ)))
        (pre-cells k Φ (GT.length Φ) (<-self (GT.length Φ)))

lookup-▸ : ∀ Γ ms A i → T (i <ℕ len Γ) → lookup (Γ ▸[ ms ] A) i ≡ lookup Γ i
lookup-▸ Γ ms A i p rewrite <→≢ i (len Γ) p = refl

marksAt-▸ : ∀ Γ ms A i → T (i <ℕ len Γ) → marksAt (Γ ▸[ ms ] A) i ≡ marksAt Γ i
marksAt-▸ Γ ms A i p rewrite <→≢ i (len Γ) p = refl

lookup-atoms : ∀ k i → T (i <ℕ k) → lookup (atomsTel k) i ≡ just ⋆
lookup-atoms (suc k) i p with i ==ℕ len (atomsTel k) in e
... | true  = refl
... | false = lookup-atoms k i (<suc-≢ i k p (trans (cong (i ==ℕ_) (sym (len-atomsTel k))) e))

lookup-pre-atom : ∀ k Φ j i → T (i <ℕ k) → lookup (pre k Φ j) i ≡ just ⋆
lookup-pre-atom k Φ zero    i p = lookup-atoms k i p
lookup-pre-atom k Φ (suc j) i p =
  trans (lookup-▸ (pre k Φ j) (marksOf (nthY Φ j)) (trTy k Φ (nthY Φ j)) i (subst (λ n → T (i <ℕ n)) (sym (len-pre k Φ j)) (<-+ i k j p)))
        (lookup-pre-atom k Φ j i p)

-- Entry v below j.
module _ (k : Nat) (Φ : GB.Ctx) where

  lookup-pre-cell : ∀ j v → T (v <ℕ j) → lookup (pre k Φ j) (k + v) ≡ just (trTy k Φ (nthY Φ v))
  lookup-pre-cell (suc j) v p with v ==ℕ j in e
  ... | true  rewrite len-pre k Φ j | ==-+ k v j | e | ==→≡ v j e = refl
  ... | false rewrite len-pre k Φ j | ==-+ k v j | e = lookup-pre-cell j v (<suc-≢ v j p e)

  marks-pre-cell : ∀ j v → T (v <ℕ j) → marksAt (pre k Φ j) (k + v) ≡ marksOf (nthY Φ v)
  marks-pre-cell (suc j) v p with v ==ℕ j in e
  ... | true  rewrite len-pre k Φ j | ==-+ k v j | e | ==→≡ v j e = refl
  ... | false rewrite len-pre k Φ j | ==-+ k v j | e = marks-pre-cell j v (<suc-≢ v j p e)

------------------------------------------------------------------------
-- Objects and formulas.

atoms-ctx : ∀ k → atomsTel k ⊢ctx
atoms-ctx zero    = ε-wf
atoms-ctx (suc k) = ▸-wf (atoms-ctx k) (⋆-wf (atoms-ctx k))

gbT : ∀ {Γ a c} kd → Γ ⊢tm a ∶ ⋆ → Γ ⊢tm c ∶ ⋆ → Γ ⊢tm gbApp kd a c ∶ ⋆
gbT kd da dc = bnd-wf tt tt w tt (,-a (,-a (⟨⟩-a w) da tt) dc tt)
  where w = tm-ctx da

-- The point object ⊤ (a head with lim_ε's rule).
top-wf : ∀ {Γ} → Γ ⊢ctx → Γ ⊢tm topT ∶ ⋆
top-wf w = bnd-wf tt tt w tt (⟨⟩-a w)

fm-ty : ∀ {Γ} k → Γ ⊢ctx → (∀ i → T (i <ℕ k) → lookup Γ i ≡ just ⋆) → ∀ x → T (atomFm k x) → Γ ⊢tm fmV x ∶ ⋆
fm-ty k w at (GB.obj i)  p = var-wf w (at i p)
fm-ty k w at (GB.rep _)  ()
fm-ty k w at (GB.shp _)  ()
fm-ty k w at (x GB.⊗ y)  p = gbT _ (fm-ty k w at x (∧-l _ _ p)) (fm-ty k w at y (∧-r _ _ p))
fm-ty k w at (x GB.\\ y) p = gbT _ (fm-ty k w at x (∧-l _ _ p)) (fm-ty k w at y (∧-r _ _ p))
fm-ty k w at (x GB.// y) p = gbT _ (fm-ty k w at x (∧-l _ _ p)) (fm-ty k w at y (∧-r _ _ p))

------------------------------------------------------------------------
-- Marks.

marksOf-sY : ∀ ρ C → marksOf (GT.sY ρ C) ≡ marksOf C
marksOf-sY ρ (GB.op _)              = refl
marksOf-sY ρ (GB.hom GB.inv _ _ _ _) = refl
marksOf-sY ρ (GB.hom GB.dir _ _ _ _) = refl

------------------------------------------------------------------------
-- Arities are honest.

eqMaybe-sound : ∀ m B → T (GT.eqMaybeTy m B) → m ≡ just B
eqMaybe-sound (just A) B p = cong just (GB.eqTy-sound A B p)

atomsTel-honest : ∀ k → T (honest? (atomsTel k))
atomsTel-honest zero    = tt
atomsTel-honest (suc k) = ∧T (atomsTel-honest k) tt

-- The facts about a context and its atoms used below.
record CtxOK (k : Nat) (Φ : GB.Ctx) : Set where
  field
    w   : T (GT.wfCtx Φ)
    oks : ∀ v {A} → GT.lookup Φ v ≡ just A → T (okTy k A)
    srt : ∀ v {A} → GT.lookup Φ v ≡ just A → T (sortedY k A)

module _ (k : Nat) (Φ : GB.Ctx) (V : CtxOK k Φ) where
  open CtxOK V

  dd : Deps↓ Φ
  dd j e = wf-deps Φ j w e

  entry : ∀ j → T (j <ℕ GT.length Φ) → T (okTy k (nthY Φ j)) × T (GT.wf Φ (nthY Φ j)) × Below j (varsY (nthY Φ j))
  entry j l =
    let (A , eA) = lookup-some Φ j l
        A≡ = nthY-just Φ j eA
    in subst (λ X → T (okTy k X)) (sym A≡) (oks j eA)
     , subst (λ X → T (GT.wf Φ X)) (sym A≡) (CM.wf-entry Φ j w eA)
     , subst (λ X → Below j (varsY X)) (sym A≡) (dd j eA)

  honest-pre : ∀ j → T (j <ℕ suc (GT.length Φ)) → T (honest? (pre k Φ j))
  honest-pre zero    _ = atomsTel-honest k
  honest-pre (suc j) l =
    let (ok , wj , bj) = entry j l in
    ∧T (honest-pre j (<-suc j (GT.length Φ) l))
       (∧T (subst (λ n → T (scTy? n (trTy k Φ (nthY Φ j)))) (sym (len-pre k Φ j))
              (SC.Sc.sc-trTy K B gform mmc unit k Φ dd j (nthY Φ j) ok wj bj))
           (SC.lc-trTy K B gform mmc unit k Φ (nthY Φ j)))

  honest-arity : T (honest? (arity k Φ))
  honest-arity = subst (λ G → T (honest? G)) (pre-arity k Φ) (honest-pre (GT.length Φ) (<-self (GT.length Φ)))

  len-arity : len (arity k Φ) ≡ k + GT.length Φ
  len-arity = trans (cong len (sym (pre-arity k Φ))) (len-pre k Φ (GT.length Φ))

------------------------------------------------------------------------
-- The type of a valid mmc head.

resC-just : ∀ h {A} → mmcTy h ≡ just A → resC h ≡ trTy (atoms h) (mctx h) A
resC-just h e with mmcTy h
resC-just h refl | just A = refl

record MmcOK (k : Nat) (Φ : GB.Ctx) (t : GB.Tm) (A : GB.CTy) : Set where
  field
    oks  : T (all (okTy k) Φ)
    w    : T (GT.wfCtx Φ)
    atb  : T (atomsBelow k Φ t)
    eA   : GT.infer Φ t ≡ just A
    okA  : T (okTy k A)
    wA   : T (GT.wf Φ A)
    atA  : T (all (λ i → i <ℕ k) (atY A))
    srtΦ : T (all (sortedY k) Φ)
    srtt : T (sortedT k t)
    srtA : T (sortedY k A)

if-T : ∀ {X : Set} b {x : Maybe X} {A} → (if b then x else nothing) ≡ just A → T b × (x ≡ just A)
if-T true  e = tt , e
if-T false ()

bind-just : ∀ {X Y : Set} (m : Maybe X) (f : X → Maybe Y) {y} → (m >>= f) ≡ just y → Σ X λ x → (m ≡ just x) × (f x ≡ just y)
bind-just (just x) f e = x , refl , e

mmcTy-inv : ∀ k Φ t {A} → mmcTy (mmi k Φ t) ≡ just A → MmcOK k Φ t A
mmcTy-inv k Φ t {A} e =
  let (c , e₁)       = if-T (isCanon (mmi k Φ t) ∧ all (okTy k) Φ ∧ GT.wfCtx Φ ∧ atomsBelow k Φ t ∧ all (sortedY k) Φ ∧ sortedT k t) e
      (A′ , eI , e₂) = bind-just (GT.infer Φ t) (λ A → if okTy k A ∧ GT.wf Φ A ∧ all (λ i → i <ℕ k) (atY A) ∧ sortedY k A
                                                       then just A else nothing) e₁
      (c₂ , e₃)      = if-T (okTy k A′ ∧ GT.wf Φ A′ ∧ all (λ i → i <ℕ k) (atY A′) ∧ sortedY k A′) e₂
  in go A′ eI c₂ (just-inj e₃) (∧-r (isCanon (mmi k Φ t)) _ c)
  where
  go : ∀ A′ → GT.infer Φ t ≡ just A′ → T (okTy k A′ ∧ GT.wf Φ A′ ∧ all (λ i → i <ℕ k) (atY A′) ∧ sortedY k A′) → A′ ≡ A →
       T (all (okTy k) Φ ∧ GT.wfCtx Φ ∧ atomsBelow k Φ t ∧ all (sortedY k) Φ ∧ sortedT k t) → MmcOK k Φ t A
  go A′ eI c₂ refl q₁ =
    let q₂ = ∧-r (all (okTy k) Φ) _ q₁
        q₃ = ∧-r (GT.wfCtx Φ) _ q₂
        q₄ = ∧-r (atomsBelow k Φ t) _ q₃
        r₁ = ∧-r (okTy k A′) _ c₂
        r₂ = ∧-r (GT.wf Φ A′) _ r₁
    in record { oks = ∧-l _ _ q₁ ; w = ∧-l _ _ q₂ ; atb = ∧-l _ _ q₃ ; eA = eI
              ; okA = ∧-l _ _ c₂ ; wA = ∧-l _ _ r₁ ; atA = ∧-l _ _ r₂ ; srtA = ∧-r (all (λ i → i <ℕ k) (atY A′)) _ r₂
              ; srtΦ = ∧-l _ _ q₄ ; srtt = ∧-r (all (sortedY k) Φ) _ q₄ }

all-elim : ∀ {X : Set} (P : X → Bool) (xs : List X) → T (all P xs) → ∀ p {x} → GT.lookup xs p ≡ just x → T (P x)
all-elim P (y ∷ xs) a zero    refl = ∧-l _ _ a
all-elim P (y ∷ xs) a (suc p) e    = all-elim P xs (∧-r (P y) _ a) p e

allN-elim : ∀ (P : Nat → Bool) xs → T (all P xs) → ∀ i → In xs i → T (P i)
allN-elim P (y ∷ xs) a i q with i ==ℕ y in e
... | true  rewrite ==→≡ i y e = ∧-l _ _ a
... | false = allN-elim P xs (∧-r (P y) _ a) i q

------------------------------------------------------------------------
-- Typing along a valid context.

module Along (k : Nat) (Φ : GB.Ctx) (V : CtxOK k Φ) (atΦ : ∀ i → In (concatAt Φ) i → T (i <ℕ k)) where
  open CtxOK V

  dd′ : Deps↓ Φ
  dd′ j e = wf-deps Φ j w e

  entry-at : ∀ v → T (v <ℕ GT.length Φ) → ∀ i → In (atY (nthY Φ v)) i → T (i <ℕ k)
  entry-at v l i q =
    atΦ i (subst (λ X → In (concatAt X) i) (map-nthY-upTo Φ)
            (atY-concatAt (nthY Φ) (upTo (GT.length Φ)) v (upTo-elem (GT.length Φ) v l) i q))

  module AtJ (j : Nat) (jl : T (j <ℕ suc (GT.length Φ))) (wj : pre k Φ j ⊢ctx) where

    Γ : Ctx
    Γ = pre k Φ j

    atoms-at : ∀ i → T (i <ℕ k) → lookup Γ i ≡ just ⋆
    atoms-at i p = lookup-pre-atom k Φ j i p

    v<Φ : ∀ v → T (v <ℕ j) → T (v <ℕ GT.length Φ)
    v<Φ v p = lt-le v j (GT.length Φ) p jl

    -- A boundary that is not a variable, at its canonical head.
    module Head (s : GB.Tm) {S : GB.CTy} (eS : GT.infer Φ s ≡ just S) (wS : T (GT.wf Φ S)) (okS : T (okTy k S))
                (bT : Below j (varsT s)) (bY : Below j (varsY S))
                (aT : ∀ i → In (atT s) i → T (i <ℕ k)) (aY : ∀ i → In (atY S) i → T (i <ℕ k))
                (srs : T (sortedT k s)) (srS : T (sortedY k S)) where

      ab : ∀ i → In (supAtomsOf Φ s) i → T (i <ℕ k)
      ab i p with elem-split i (concatAt (GT.map (nthY Φ) (supVars Φ s))) (atT s ++ atYM (GT.infer Φ s)) p
      ... | inr q with elem-split i (atT s) (atYM (GT.infer Φ s)) q
      ...   | inl r = aT i r
      ...   | inr r = aY i (subst (λ m → In (atYM m) i) eS r)
      ab i p | inl q =
        let (v , vin , r) = concatAt-inv (nthY Φ) (supVars Φ s) i q
            (_ , b) = MR.filter-In-inv _ (upTo (GT.length Φ)) v vin
        in entry-at v (MR.upTo-In-inv (GT.length Φ) v b) i r

      module A = CM.At K B gform mmc unit k Φ w s eS wS ab
      open A using (K′; σb; σb-rr)
      open A.CB using (asb; vs; ρ; rr; Φ′; m)

      h : MMI
      h = cidx (canon k Φ s)

      oksΦ : ∀ v {A} → GT.lookup Φ v ≡ just A → T (okTy k A)
      oksΦ = oks

      mmc-eq : mmcTy h ≡ just (GT.sY ρ S)
      mmc-eq = MW.SubWf.sub-mmcTy k Φ w s eS wS ab oksΦ okS srt srs srS

      res-eq : resC h ≡ trTy K′ Φ′ (GT.sY ρ S)
      res-eq = resC-just h mmc-eq

      okc : MmcOK K′ Φ′ (mterm h) (GT.sY ρ S)
      okc = mmcTy-inv K′ Φ′ (mterm h) mmc-eq

      Vc : CtxOK K′ Φ′
      Vc = record { w = MmcOK.w okc ; oks = all-elim (okTy K′) Φ′ (MmcOK.oks okc) ; srt = all-elim (sortedY K′) Φ′ (MmcOK.srtΦ okc) }

      ddc : Deps↓ Φ′
      ddc = dd K′ Φ′ Vc

      sc-res : T (scTy? (len (arity K′ Φ′)) (resC h))
      sc-res = subst (λ X → T (scTy? (len (arity K′ Φ′)) X)) (sym res-eq)
                 (subst (λ n → T (scTy? n (trTy K′ Φ′ (GT.sY ρ S)))) (sym (len-arity K′ Φ′ Vc))
                   (SC.Sc.sc-trTy K B gform mmc unit K′ Φ′ ddc (GT.length Φ′) (GT.sY ρ S) (MmcOK.okA okc) (MmcOK.wA okc)
                      (wf-scope Φ′ (GT.sY ρ S) (MmcOK.wA okc))))

      lc-res : T (lcTy? 0 (resC h))
      lc-res = subst (λ X → T (lcTy? 0 X)) (sym res-eq) (SC.lc-trTy K B gform mmc unit K′ Φ′ (GT.sY ρ S))

      ok : T (bside (mmc h) 0 ε)
      ok = ∧T (subst (λ m → T (is-just m)) (sym mmc-eq) tt)
              (∧T (honest-arity K′ Φ′ Vc) (∧T sc-res lc-res))

      -- The support, below j.
      vs<j : ∀ v → In vs v → T (v <ℕ j)
      vs<j = SC.Sc.sup-below K B gform mmc unit k Φ dd′ j s eS bT bY

      -- The arguments, a prefix at a time.
      σa : Sub
      σa = varsOf ⟨⟩ asb

      σp : Nat → Sub
      σp p = varsOf σa (GT.map (k +_) (takeN p vs))

      atoms-sub : ∀ a → T (a <ℕ suc K′) → Γ ⊢sub varsOf ⟨⟩ (takeN a asb) ∶ atomsTel a
      atoms-sub zero    _ = ⟨⟩-wf wj
      atoms-sub (suc a) l =
        subst (λ σ → Γ ⊢sub σ ∶ atomsTel (suc a))
          (sym (trans (cong (varsOf ⟨⟩) (take-snoc asb a l)) (varsOf-snoc ⟨⟩ (takeN a asb) (MR.nth asb a))))
          (,-wf (atoms-sub a (<-suc a K′ l))
                (var-wf wj (atoms-at (MR.nth asb a) (A.CB.asb-lt (MR.nth asb a) (MR.nth-In asb a l))))
                tt)

      σa-wf : Γ ⊢sub σa ∶ atomsTel K′
      σa-wf = subst (λ xs → Γ ⊢sub varsOf ⟨⟩ xs ∶ atomsTel K′) (take-all asb) (atoms-sub K′ (<-self K′))

      len-σp : ∀ p → T (p <ℕ suc m) → lenₛ (σp p) ≡ K′ + p
      len-σp p l =
        trans (lenₛ-varsOf σa (GT.map (k +_) (takeN p vs)))
          (cong₂ _+_ (lenₛ-varsOf ⟨⟩ asb)
            (trans (CM.length-map′ (k +_) (takeN p vs)) (length-take vs p l)))

      full : ∀ p → σb ≡ varsOf (σp p) (GT.map (k +_) (dropN p vs))
      full p =
        trans (cong (λ xs → varsOf σa (GT.map (k +_) xs)) (sym (take-drop p vs)))
          (trans (cong (varsOf σa) (map-++′ (k +_) (takeN p vs) (dropN p vs)))
                 (varsOf-++ σa (GT.map (k +_) (takeN p vs)) (GT.map (k +_) (dropN p vs))))

      cells-sub : ∀ p → T (p <ℕ suc m) → Γ ⊢sub σp p ∶ pre K′ Φ′ p
      cells-sub zero    _ = σa-wf
      cells-sub (suc p) l =
        subst (λ σ → Γ ⊢sub σ ∶ pre K′ Φ′ (suc p))
          (sym (trans (cong (λ xs → varsOf σa (GT.map (k +_) xs)) (take-snoc vs p l))
                 (trans (cong (varsOf σa) (map-++′ (k +_) (takeN p vs) (MR.nth vs p ∷ [])))
                        (varsOf-snoc σa (GT.map (k +_) (takeN p vs)) (k + MR.nth vs p)))))
          (,-wf (cells-sub p (<-suc p m l)) d mk)
        where
        v : Nat
        v = MR.nth vs p
        vin : In vs v
        vin = MR.nth-In vs p l
        Cp : GB.CTy
        Cp = nthY Φ′ p
        Cp≡ : Cp ≡ GT.sY ρ (nthY Φ v)
        Cp≡ = nthY-just Φ′ p (A.CB.lookup-Φ′ p l)
        lp : T (p <ℕ GT.length Φ′)
        lp = subst (λ n → T (p <ℕ n)) (sym A.CB.len-Φ′) l
        ep = entry K′ Φ′ Vc p lp
        scp : T (scTy? (lenₛ (σp p)) (trTy K′ Φ′ Cp))
        scp = subst (λ n → T (scTy? n (trTy K′ Φ′ Cp))) (sym (len-σp p (<-suc p m l)))
                (SC.Sc.sc-trTy K B gform mmc unit K′ Φ′ ddc p Cp (fst ep) (fst (snd ep)) (snd (snd ep)))
        okv : T (okTy k (nthY Φ v))
        okv = fst (entry k Φ V v (v<Φ v (vs<j v vin)))
        tyeq : trTy k Φ (nthY Φ v) ≡ trTy K′ Φ′ Cp [ σp p ]ty
        tyeq = sym (trans (sym (ext-varsOf (trTy K′ Φ′ Cp) (σp p) (GT.map (k +_) (dropN p vs)) scp))
                     (trans (cong (trTy K′ Φ′ Cp [_]ty) (sym (full p)))
                            (trans (cong (λ X → trTy K′ Φ′ X [ σb ]ty) Cp≡) (A.comm-entry v vin okv))))
        d : Γ ⊢tm var (k + v) ∶ trTy K′ Φ′ Cp [ σp p ]ty
        d = subst (Γ ⊢tm var (k + v) ∶_) tyeq (var-wf wj (lookup-pre-cell k Φ j v (vs<j v vin)))
        mk : T (marksOK Γ (marksOf Cp) (var (k + v)))
        mk = subst (λ ms → T (marksOK Γ ms (var (k + v))))
               (trans (marks-pre-cell k Φ j v (vs<j v vin))
                      (trans (sym (marksOf-sY ρ (nthY Φ v))) (cong marksOf (sym Cp≡))))
               (markVar wj (lookup-pre-cell k Φ j v (vs<j v vin)))

      args-wf : Γ ⊢sub supArgs k (canon k Φ s) ∶ arity K′ Φ′
      args-wf =
        subst₂ (λ σ G → Γ ⊢sub σ ∶ G)
          (cong (λ xs → varsOf σa (GT.map (k +_) xs)) (take-all vs))
          (trans (cong (pre K′ Φ′) (sym A.CB.len-Φ′)) (pre-arity K′ Φ′))
          (cells-sub m (<-self m))
        where
        subst₂ : ∀ {X Y : Set} (P : X → Y → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
        subst₂ P refl refl p = p

      typed : Γ ⊢tm trHead k Φ s ∶ trTy k Φ S
      typed =
        subst (Γ ⊢tm trHead k Φ s ∶_)
          (trans (cong (_[ σb ]ty) res-eq) (A.comm-res okS))
          (op-intro (spec-honest (mmc h) 0 ok) ok wj args-wf)

    typTm : ∀ s {S} → GT.infer Φ s ≡ just S → T (GT.wf Φ S) → T (okTy k S) →
            Below j (varsT s) → Below j (varsY S) →
            (∀ i → In (atT s) i → T (i <ℕ k)) → (∀ i → In (atY S) i → T (i <ℕ k)) →
            T (sortedT k s) → T (sortedY k S) →
            Γ ⊢tm trTm k Φ s ∶ trTy k Φ S
    typTm (GB.var v) {S} eS wS okS bT bY aT aY _ _ =
      let vj = bT v (∨-l (v ==ℕ v) _ (==ℕ-refl v)) in
      subst (λ X → Γ ⊢tm var (k + v) ∶ trTy k Φ X) (nthY-just Φ v eS) (var-wf wj (lookup-pre-cell k Φ j v vj))
    typTm s@(GB.mP _ _)       eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.eL _ _)       eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.eR _ _)       eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.pP _ _)       eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@GB.pt             eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.iP _)         eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.idt _)        eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.comp _ _)     eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.glue _ _ _)   eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS
    typTm s@(GB.here _ _ _ _) eS wS okS bT bY aT aY srs srS = Head.typed s eS wS okS bT bY aT aY srs srS

    tyWf : ∀ C → T (okTy k C) → T (GT.wf Φ C) → Below j (varsY C) → (∀ i → In (atY C) i → T (i <ℕ k)) →
           T (sortedY k C) → Γ ⊢ty trTy k Φ C
    tyWf (GB.op ((x ∷ []) GB.▸ z)) p _ _ _ _ =
      arr-wf (fm-ty k wj atoms-at x (∧-l _ _ p)) (fm-ty k wj atoms-at z (∧-r _ _ p))
    tyWf (GB.op ([] GB.▸ z)) p _ _ _ _ = arr-wf (top-wf wj) (fm-ty k wj atoms-at z p)
    tyWf (GB.op ((_ ∷ _ ∷ _) GB.▸ _)) () _ _ _ _
    tyWf (GB.hom d g A s t) p wC bC aC sC =
      let wA  = ∧-l _ _ wC
          wst = ∧-r (GT.wf Φ A) _ wC
          eS  = eqMaybe-sound (GT.infer Φ s) A (∧-l _ _ wst)
          eT  = eqMaybe-sound (GT.infer Φ t) A (∧-r (GT.eqMaybeTy (GT.infer Φ s) A) _ wst)
          okA = ∧-r (g ==ℕ inputs A) _ p
          bA  : Below j (varsY A)
          bA  = λ i q → bC i (elem-++l i (varsY A) (varsT s ++ varsT t) q)
          bs  : Below j (varsT s)
          bs  = λ i q → bC i (elem-++r i (varsY A) (varsT s ++ varsT t) (elem-++l i (varsT s) (varsT t) q))
          bt  : Below j (varsT t)
          bt  = λ i q → bC i (elem-++r i (varsY A) (varsT s ++ varsT t) (elem-++r i (varsT s) (varsT t) q))
          aA  = λ i q → aC i (elem-++l i (atY A) (atT s ++ atT t) q)
          as  = λ i q → aC i (elem-++r i (atY A) (atT s ++ atT t) (elem-++l i (atT s) (atT t) q))
          at′ = λ i q → aC i (elem-++r i (atY A) (atT s ++ atT t) (elem-++r i (atT s) (atT t) q))
          sA  = ∧-l _ _ sC
          sst = ∧-r (sortedY k A) _ sC
      in arr-wf (typTm s eS wA okA bs bA as aA (∧-l _ _ sst) sA)
                (typTm t eT wA okA bt bA at′ aA (∧-r (sortedT k s) _ sst) sA)

  -- Every prefix of the arity is well formed.
  ctx-pre : ∀ j → T (j <ℕ suc (GT.length Φ)) → pre k Φ j ⊢ctx
  ctx-pre zero    _ = atoms-ctx k
  ctx-pre (suc j) l =
    let wj = ctx-pre j (<-suc j (GT.length Φ) l)
        (ok , wC , bC) = entry k Φ V j l
        (A , eA) = lookup-some Φ j l
        sj = subst (λ X → T (sortedY k X)) (sym (nthY-just Φ j eA)) (srt j eA)
    in ▸-wf wj (AtJ.tyWf j (<-suc j (GT.length Φ) l) wj (nthY Φ j) ok wC bC (entry-at j l) sj)

------------------------------------------------------------------------
-- HeadOK for every head, and the presupposition law.

ok-all : ∀ b → HeadOK b
ok-all b y (_ ▸[ _ ] _) ()
ok-all (gform g) zero ε p = honest-ok (spec-honest (gform g) 0 p) (⋆-wf (atoms-ctx 2)) ε p
ok-all (gform g) (suc y) ε ()
ok-all (mmc h) (suc y) ε ()
ok-all unit zero ε p = honest-ok (spec-honest unit 0 p) (⋆-wf ε-wf) ε p
ok-all unit (suc y) ε ()
ok-all (mmc (mmi k Φ t)) zero ε p =
  honest-ok (spec-honest (mmc (mmi k Φ t)) 0 p) a ε p
  where
  ej = is-just-inv (mmcTy (mmi k Φ t)) (∧-l _ _ p)
  A  = fst ej
  o  = mmcTy-inv k Φ t (snd ej)
  V : CtxOK k Φ
  V = record { w = MmcOK.w o ; oks = all-elim (okTy k) Φ (MmcOK.oks o) ; srt = all-elim (sortedY k) Φ (MmcOK.srtΦ o) }
  atΦ : ∀ i → In (concatAt Φ) i → T (i <ℕ k)
  atΦ i q = allN-elim (λ i → i <ℕ k) (concatAt Φ ++ atT t) (MmcOK.atb o) i (elem-++l i (concatAt Φ) (atT t) q)
  open Along k Φ V atΦ
  n = GT.length Φ
  a : arity k Φ ⊢ty resC (mmi k Φ t)
  a = subst₂ (λ G X → G ⊢ty X) (pre-arity k Φ) (sym (resC-just (mmi k Φ t) (snd ej)))
        (AtJ.tyWf n (<-self n) (ctx-pre n (<-self n)) A (MmcOK.okA o) (MmcOK.wA o)
           (wf-scope Φ A (MmcOK.wA o)) (allN-elim _ (atY A) (MmcOK.atA o)) (MmcOK.srtA o))
    where
    subst₂ : ∀ {X Y : Set} (P : X → Y → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
    subst₂ P refl refl q = q

cells-presup : PresupLaws
cells-presup = head-presup closed spec-head ok-all markRen markSub markVar

-- Every term of CaTT with ⊗, \, / and the cell heads has a well-formed
-- type.
cells-tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
cells-tm-ty = tm-ty closed laws markRen markSub markVar (λ {_} {k} _ _ → ⊥-elim k) cells-presup
