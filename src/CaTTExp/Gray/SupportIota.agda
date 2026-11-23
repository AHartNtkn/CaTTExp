------------------------------------------------------------------------
-- Two-tier L's side condition does not see the signature on pure
-- syntax. For every signature 𝕊₀ and the inclusion ι of pure syntax
-- (CaTTExp.Pure, no constants) into 𝕊₀'s syntax,
--
--   graySide-ι : graySide_𝕊₀ (ι Θ) (ι A) (ι t) (ι u) ≡ graySide_∅ Θ A t u
--
-- Every function of Gray.Support commutes with ι: on cells and homs
-- through the field-wise copy of Support's records (cE, cH), on tuples
-- and the face order literally. So facts about two-tier L's side
-- condition proved over pure syntax (e.g. Gray.DesSideL) hold over
-- every signature.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Pure as P

module CaTTExp.Gray.SupportIota (𝕊₀ : Signature) where

open Signature 𝕊₀
import CaTTExp.Gray.Support 𝕊₀ as S
import CaTTExp.Gray.Support P.∅ as Z

------------------------------------------------------------------------
-- The inclusion.

mutual
  ιTy : P.Ty → Ty
  ιTy P.⋆           = ⋆
  ιTy (P.arr A t u) = arr (ιTy A) (ιTm t) (ιTm u)

  ιTm : P.Tm → Tm
  ιTm (P.var i)     = var i
  ιTm (P.coh Γ A σ) = coh (ιCtx Γ) (ιTy A) (ιSub σ)
  ιTm (P.cst ())

  ιCtx : P.Ctx → Ctx
  ιCtx P.ε       = ε
  ιCtx (Γ P.▸ A) = ιCtx Γ ▸ ιTy A

  ιSub : P.Sub → Sub
  ιSub P.⟨⟩       = ⟨⟩
  ιSub (σ P.,ₛ t) = ιSub σ ,ₛ ιTm t

len-ι : ∀ Γ → len (ιCtx Γ) ≡ P.len Γ
len-ι P.ε       = refl
len-ι (Γ P.▸ _) = cong suc (len-ι Γ)

dim-ι : ∀ A → dim (ιTy A) ≡ P.dim A
dim-ι P.⋆           = refl
dim-ι (P.arr A _ _) = cong suc (dim-ι A)

------------------------------------------------------------------------
-- The two copies of Support's list utilities agree.

private
  module L where
    map : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) xs → S.map f xs ≡ Z.map f xs
    map f []       = refl
    map f (x ∷ xs) = cong (f x ∷_) (map f xs)

    cm : ∀ {a b} {A : Set a} {B : Set b} (f g : A → List B) → (∀ x → f x ≡ g x) →
         ∀ xs → S.concatMap f xs ≡ Z.concatMap g xs
    cm f g e []       = refl
    cm f g e (x ∷ xs) = cong₂ _++_ (e x) (cm f g e xs)

    all-ext : ∀ {a} {A : Set a} (p q : A → Bool) → (∀ x → p x ≡ q x) → ∀ xs → all p xs ≡ all q xs
    all-ext p q e []       = refl
    all-ext p q e (x ∷ xs) = cong₂ _∧_ (e x) (all-ext p q e xs)

    any : ∀ {a} {A : Set a} (p q : A → Bool) → (∀ x → p x ≡ q x) → ∀ xs → S.any p xs ≡ Z.any q xs
    any p q e []       = refl
    any p q e (x ∷ xs) = cong₂ _∨_ (e x) (any p q e xs)

    upto : ∀ n → S.upto n ≡ Z.upto n
    upto zero    = refl
    upto (suc n) = cong (_++ (suc n ∷ [])) (upto n)

    sumL : ∀ xs → S.sumL xs ≡ Z.sumL xs
    sumL []       = refl
    sumL (x ∷ xs) = cong (x +_) (sumL xs)

    maxL : ∀ xs → S.maxL xs ≡ Z.maxL xs
    maxL []       = refl
    maxL (x ∷ xs) = cong (max x) (maxL xs)

    odd : ∀ n → S.odd n ≡ Z.odd n
    odd zero    = refl
    odd (suc n) = cong not (odd n)

    lengthN : ∀ xs → S.lengthN xs ≡ Z.lengthN xs
    lengthN []       = refl
    lengthN (_ ∷ xs) = cong suc (lengthN xs)

    dropLast : ∀ xs → S.dropLast xs ≡ Z.dropLast xs
    dropLast []           = refl
    dropLast (x ∷ [])     = refl
    dropLast (x ∷ y ∷ ys) = cong (x ∷_) (dropLast (y ∷ ys))

    drop1 : ∀ xs → S.drop1 xs ≡ Z.drop1 xs
    drop1 []       = refl
    drop1 (_ ∷ xs) = dropLast xs

    posOf : ∀ n xs → S.posOf n xs ≡ Z.posOf n xs
    posOf n []       = refl
    posOf n (m ∷ ms) rewrite posOf n ms = refl

    firstL : ∀ xs → S.firstL xs ≡ Z.firstL xs
    firstL []      = refl
    firstL (x ∷ _) = refl

    lastL : ∀ xs → S.lastL xs ≡ Z.lastL xs
    lastL []           = refl
    lastL (x ∷ [])     = refl
    lastL (_ ∷ y ∷ ys) = lastL (y ∷ ys)

    prod1 : ∀ xs ys → S.prod1 xs ys ≡ Z.prod1 xs ys
    prod1 xs ys = cm _ _ (λ x → map (x ∷_) ys) xs

    prodT : ∀ xs ys → S.prodT xs ys ≡ Z.prodT xs ys
    prodT xs ys = cm _ _ (λ x → map (x ++_) ys) xs

    nth : ∀ n xs → S.nth n xs ≡ Z.nth n xs
    nth _       []       = refl
    nth zero    (x ∷ _)  = refl
    nth (suc n) (_ ∷ xs) = nth n xs

    Ftuple : ∀ tops ws → S.Ftuple tops ws ≡ Z.Ftuple tops ws
    Ftuple tops []       = refl
    Ftuple tops (w ∷ ws) rewrite nth w tops | Ftuple tops ws = prodT (Z.nth w tops) (Z.Ftuple tops ws)

    applyF : ∀ tops C → S.applyF tops C ≡ Z.applyF tops C
    applyF tops C = cm _ _ (Ftuple tops) C

------------------------------------------------------------------------
-- Cells and homs.

cE : Z.El → S.El
cE e = S.el (Z.lvl e) (Z.hom e) (Z.hdim e) (Z.src e) (Z.tgt e)

cEs : List Z.El → List S.El
cEs []       = []
cEs (c ∷ cs) = cE c ∷ cEs cs

cH : Z.Hom → S.Hom
cH h = S.mkHom (Z.hd h) (cEs (Z.hcs h))

cHs : List Z.Hom → List S.Hom
cHs []       = []
cHs (h ∷ hs) = cH h ∷ cHs hs

ιE : Nat × P.Ty → Nat × Ty
ιE (v , A) = v , ιTy A

private
  map-++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) xs ys → S.map f (xs ++ ys) ≡ S.map f xs ++ S.map f ys
  map-++ f []       ys = refl
  map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

  if-≡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) c x y → f (if c then x else y) ≡ (if c then f x else f y)
  if-≡ f true  x y = refl
  if-≡ f false x y = refl

  lvl-cEs : ∀ cs → S.map S.lvl (cEs cs) ≡ Z.map Z.lvl cs
  lvl-cEs []       = refl
  lvl-cEs (c ∷ cs) = cong (Z.lvl c ∷_) (lvl-cEs cs)

  cEs-++ : ∀ xs ys → cEs (xs ++ ys) ≡ cEs xs ++ cEs ys
  cEs-++ []       ys = refl
  cEs-++ (x ∷ xs) ys = cong (cE x ∷_) (cEs-++ xs ys)

  mmT : Maybe (P.Tm × P.Tm) → Maybe (Tm × Tm)
  mmT nothing        = nothing
  mmT (just (a , b)) = just (ιTm a , ιTm b)

  endsTy-ι : ∀ A → S.endsTy (ιTy A) ≡ mmT (Z.endsTy A)
  endsTy-ι P.⋆                       = refl
  endsTy-ι (P.arr P.⋆ a b)           = refl
  endsTy-ι (P.arr (P.arr A s t) _ _) = endsTy-ι (P.arr A s t)

  varLvl-ι : ∀ t → S.varLvl (ιTm t) ≡ Z.varLvl t
  varLvl-ι (P.var i)     = refl
  varLvl-ι (P.coh _ _ _) = refl
  varLvl-ι (P.cst ())

  isVarAt-ι : ∀ t n → S.isVarAt (ιTm t) n ≡ Z.isVarAt t n
  isVarAt-ι (P.var i)     n = refl
  isVarAt-ι (P.coh _ _ _) n = refl
  isVarAt-ι (P.cst ())    n

  elBdry-ι : ∀ A → S.elBdry (ιTy A) ≡ Z.elBdry A
  elBdry-ι P.⋆                                         = refl
  elBdry-ι (P.arr P.⋆ _ _)                             = refl
  elBdry-ι (P.arr (P.arr _ _ _) (P.var s) (P.var t))     = refl
  elBdry-ι (P.arr (P.arr _ _ _) (P.var s) (P.coh _ _ _)) = refl
  elBdry-ι (P.arr (P.arr _ _ _) (P.var s) (P.cst ()))
  elBdry-ι (P.arr (P.arr _ _ _) (P.coh _ _ _) _)         = refl
  elBdry-ι (P.arr (P.arr _ _ _) (P.cst ()) _)

  isStar-ι : ∀ A → S.isStar (ιTy A) ≡ Z.isStar A
  isStar-ι P.⋆           = refl
  isStar-ι (P.arr _ _ _) = refl

entries-ι : ∀ Γ → S.entries (ιCtx Γ) ≡ S.map ιE (Z.entries Γ)
entries-ι P.ε       = refl
entries-ι (Γ P.▸ A) rewrite entries-ι Γ | len-ι Γ | map-++ ιE (Z.entries Γ) ((P.len Γ , A) ∷ []) = refl

objs-ι : ∀ Γ → S.objs (ιCtx Γ) ≡ Z.objs Γ
objs-ι Γ rewrite entries-ι Γ = go (Z.entries Γ)
  where
  go : ∀ es → S.map fst (filter (λ e → S.isStar (snd e)) (S.map ιE es))
            ≡ Z.map fst (filter (λ e → Z.isStar (snd e)) es)
  go []             = refl
  go ((v , A) ∷ es) rewrite isStar-ι A with Z.isStar A
  ... | true  = cong (v ∷_) (go es)
  ... | false = go es

private
  mkEl-ι : ∀ os e → S.mkEl os (ιE e) ≡ cEs (Z.mkEl os e)
  mkEl-ι os (v , A) with Z.endsTy A | endsTy-ι A
  ... | nothing      | e rewrite e = refl
  ... | just (a , b) | e rewrite e | varLvl-ι b with Z.varLvl b
  ...   | nothing = refl
  ...   | just b′ with S.posOf b′ os | Z.posOf b′ os | L.posOf b′ os
  ...     | nothing | .nothing | refl = refl
  ...     | just k  | .(just k) | refl rewrite dim-ι A | elBdry-ι A = refl

cells-ι : ∀ Γ → S.cells (ιCtx Γ) ≡ cEs (Z.cells Γ)
cells-ι Γ rewrite objs-ι Γ | entries-ι Γ = go (Z.entries Γ)
  where
  go : ∀ es → S.concatMap (S.mkEl (Z.objs Γ)) (S.map ιE es) ≡ cEs (Z.concatMap (Z.mkEl (Z.objs Γ)) es)
  go []       = refl
  go (e ∷ es) rewrite mkEl-ι (Z.objs Γ) e | go es
                    | cEs-++ (Z.mkEl (Z.objs Γ) e) (Z.concatMap (Z.mkEl (Z.objs Γ)) es) = refl

private
  filter-cE : ∀ (p : S.El → Bool) (q : Z.El → Bool) → (∀ c → p (cE c) ≡ q c) →
              ∀ cs → filter p (cEs cs) ≡ cEs (filter q cs)
  filter-cE p q e []       = refl
  filter-cE p q e (c ∷ cs) =
    trans (cong₂ (λ b X → if b then cE c ∷ X else X) (e c) (filter-cE p q e cs))
          (sym (if-≡ cEs (q c) (c ∷ filter q cs) (filter q cs)))

  maxL-cE : ∀ cs → S.maxL (S.map S.hdim (cEs cs)) ≡ Z.maxL (Z.map Z.hdim cs)
  maxL-cE []       = refl
  maxL-cE (c ∷ cs) = cong (max (Z.hdim c)) (maxL-cE cs)

  homAt-ι : ∀ Γ k → S.homAt (ιCtx Γ) k ≡ cH (Z.homAt Γ k)
  homAt-ι Γ k rewrite cells-ι Γ
                    | filter-cE (λ c → S.hom c ==ℕ k) (λ c → Z.hom c ==ℕ k) (λ _ → refl) (Z.cells Γ)
                    | maxL-cE (filter (λ c → Z.hom c ==ℕ k) (Z.cells Γ)) = refl

homs-ι : ∀ Γ → S.homs (ιCtx Γ) ≡ cHs (Z.homs Γ)
homs-ι Γ =
  trans (cong (λ os → S.map (S.homAt (ιCtx Γ)) (S.drop1 (S.upto (S.lengthN os)))) (objs-ι Γ))
        (trans (cong (S.map (S.homAt (ιCtx Γ))) idx) (go (Z.drop1 (Z.upto (Z.lengthN (Z.objs Γ))))))
  where
  go : ∀ ks → S.map (S.homAt (ιCtx Γ)) ks ≡ cHs (Z.map (Z.homAt Γ) ks)
  go []       = refl
  go (k ∷ ks) = cong₂ _∷_ (homAt-ι Γ k) (go ks)
  idx : S.drop1 (S.upto (S.lengthN (Z.objs Γ))) ≡ Z.drop1 (Z.upto (Z.lengthN (Z.objs Γ)))
  idx = trans (cong (λ n → S.drop1 (S.upto n)) (L.lengthN (Z.objs Γ)))
              (trans (cong S.drop1 (L.upto (Z.lengthN (Z.objs Γ)))) (L.drop1 (Z.upto (Z.lengthN (Z.objs Γ)))))

dimK-ι : ∀ hs → S.dimK (cHs hs) ≡ Z.dimK hs
dimK-ι []       = refl
dimK-ι (h ∷ hs) = cong (Z.hd h +_) (dimK-ι hs)

------------------------------------------------------------------------
-- Tables.

private
  any-hits : ∀ i sg c cs → S.any (S.hitsP i sg (cE c)) (cEs cs) ≡ Z.any (Z.hitsP i sg c) cs
  any-hits i sg c []       = refl
  any-hits i sg c (w ∷ ws) = cong (Z.hitsP i sg c w ∨_) (any-hits i sg c ws)

  lvl-filter : ∀ (p : S.El → Bool) (q : Z.El → Bool) → (∀ c → p (cE c) ≡ q c) →
               ∀ cs → S.map S.lvl (filter p (cEs cs)) ≡ Z.map Z.lvl (filter q cs)
  lvl-filter p q e cs = trans (cong (S.map S.lvl) (filter-cE p q e cs)) (lvl-cEs (filter q cs))

piece-ι : ∀ h i sg → S.piece (cH h) i sg ≡ Z.piece h i sg
piece-ι h i sg with i ==ℕ Z.hd h
... | true  = lvl-filter _ _ (λ _ → refl) (Z.hcs h)
... | false with i <ℕ Z.hd h
...   | true  = lvl-filter _ _ (λ c → cong (λ b → (Z.hdim c ==ℕ i) ∧ not b) (any-hits i sg c (Z.hcs h))) (Z.hcs h)
...   | false = refl

chainT-ι : ∀ sg k hs → S.chainT sg k (cHs hs) ≡ Z.chainT sg k hs
chainT-ι sg k []       = refl
chainT-ι sg k (h ∷ hs) rewrite L.upto k =
  L.cm _ _ (λ i → trans (cong₂ S.prod1 (piece-ι h i sg)
                                       (trans (cong (λ b → S.chainT (if b then not sg else sg) (k ∸ i) (cHs hs)) (L.odd i))
                                              (chainT-ι (if Z.odd i then not sg else sg) (k ∸ i) hs)))
                        (L.prod1 (Z.piece h i sg) (Z.chainT (if Z.odd i then not sg else sg) (k ∸ i) hs)))
       (filter (λ i → i <ℕ suc k) (Z.upto k))

lowerT-ι : ∀ m hs → S.lowerT m (cHs hs) ≡ Z.lowerT m hs
lowerT-ι zero    hs = refl
lowerT-ι (suc m) hs rewrite lowerT-ι m hs | chainT-ι false m hs | chainT-ι true m hs = refl

fullT-ι : ∀ hs → S.fullT (cHs hs) ≡ Z.fullT hs
fullT-ι hs rewrite dimK-ι hs | lowerT-ι (Z.dimK hs) hs | chainT-ι true (Z.dimK hs) hs = refl

bdryT-ι : ∀ sg hs → S.bdryT sg (cHs hs) ≡ Z.bdryT sg hs
bdryT-ι sg hs rewrite dimK-ι hs | lowerT-ι (Z.dimK hs ∸ 1) hs | chainT-ι sg (Z.dimK hs ∸ 1) hs = refl

topT-ι : ∀ hs → S.topT (cHs hs) ≡ Z.topT hs
topT-ι hs rewrite dimK-ι hs = chainT-ι true (Z.dimK hs) hs

------------------------------------------------------------------------
-- The face order and covers.

private
  mmE : Maybe Z.El → Maybe S.El
  mmE nothing  = nothing
  mmE (just c) = just (cE c)

  findEl-ι : ∀ n cs → S.findEl n (cEs cs) ≡ mmE (Z.findEl n cs)
  findEl-ι n []       = refl
  findEl-ι n (c ∷ cs) =
    trans (cong (λ X → if Z.lvl c ==ℕ n then just (cE c) else X) (findEl-ι n cs))
          (sym (if-≡ mmE (Z.lvl c ==ℕ n) (just c) (Z.findEl n cs)))

  bdEl-ι : ∀ cs w → S.bdEl (cEs cs) w ≡ Z.bdEl cs w
  bdEl-ι cs w rewrite findEl-ι w cs with Z.findEl w cs
  ... | nothing = refl
  ... | just c  = refl

  mutual
    leqL-ι : ∀ cs n a b → S.leqL (cEs cs) n a b ≡ Z.leqL cs n a b
    leqL-ι cs zero    a b = refl
    leqL-ι cs (suc n) a b rewrite bdEl-ι cs b = cong ((a ==ℕ b) ∨_) (leqAny-ι cs n a (Z.bdEl cs b))

    leqAny-ι : ∀ cs n a bs → S.leqAny (cEs cs) n a bs ≡ Z.leqAny cs n a bs
    leqAny-ι cs n a []       = refl
    leqAny-ι cs n a (c ∷ bs) = cong₂ _∨_ (leqL-ι cs n a c) (leqAny-ι cs n a bs)

  leqT-ι : ∀ cs n x r → S.leqT (cEs cs) n x r ≡ Z.leqT cs n x r
  leqT-ι cs n []      []      = refl
  leqT-ι cs n []      (_ ∷ _) = refl
  leqT-ι cs n (_ ∷ _) []      = refl
  leqT-ι cs n (a ∷ x) (b ∷ y) = cong₂ _∧_ (leqL-ι cs n a b) (leqT-ι cs n x y)

covers-ι : ∀ Γ X Y → S.covers (ιCtx Γ) X Y ≡ Z.covers Γ X Y
covers-ι Γ X Y =
  trans (cong₂ (λ cs N → all (λ s → S.any (S.leqT cs N s) Y) X)
               (cells-ι Γ) (trans (cong S.dimK (homs-ι Γ)) (dimK-ι (Z.homs Γ))))
        (L.all-ext _ _ (λ s → L.any _ _ (leqT-ι (Z.cells Γ) (Z.dimK (Z.homs Γ)) s) Y) X)

sameDown-ι : ∀ Γ X Y → S.sameDown (ιCtx Γ) X Y ≡ Z.sameDown Γ X Y
sameDown-ι Γ X Y = cong₂ _∧_ (covers-ι Γ X Y) (covers-ι Γ Y X)

endsOK-ι : ∀ Γ A → S.endsOK (ιCtx Γ) (ιTy A) ≡ Z.endsOK Γ A
endsOK-ι Γ A with Z.endsTy A | endsTy-ι A
... | nothing      | e rewrite e = refl
... | just (s , t) | e rewrite e = cong₂ _∧_ (end S.firstL Z.firstL L.firstL s) (end S.lastL Z.lastL L.lastL t)
  where
  end : (f : List Nat → Nat) (g : List Nat → Nat) → (∀ xs → f xs ≡ g xs) → ∀ x →
        S.isVarAt (ιTm x) (f (S.objs (ιCtx Γ))) ≡ Z.isVarAt x (g (Z.objs Γ))
  end f g fg x = trans (cong (λ os → S.isVarAt (ιTm x) (f os)) (objs-ι Γ))
                       (trans (cong (S.isVarAt (ιTm x)) (fg (Z.objs Γ))) (isVarAt-ι x (g (Z.objs Γ))))

------------------------------------------------------------------------
-- Supports and the side condition.

private
  dimKΓ : ∀ Γ → S.dimK (S.homs (ιCtx Γ)) ≡ Z.dimK (Z.homs Γ)
  dimKΓ Γ = trans (cong S.dimK (homs-ι Γ)) (dimK-ι (Z.homs Γ))

  topTΓ : ∀ Γ → S.topT (S.homs (ιCtx Γ)) ≡ Z.topT (Z.homs Γ)
  topTΓ Γ = trans (cong S.topT (homs-ι Γ)) (topT-ι (Z.homs Γ))

  objι : ∀ (f : List Nat → Nat) (g : List Nat → Nat) → (∀ xs → f xs ≡ g xs) → ∀ Γ x →
         S.isVarAt (ιTm x) (f (S.objs (ιCtx Γ))) ≡ Z.isVarAt x (g (Z.objs Γ))
  objι f g fg Γ x = trans (cong (λ os → S.isVarAt (ιTm x) (f os)) (objs-ι Γ))
                          (trans (cong (S.isVarAt (ιTm x)) (fg (Z.objs Γ))) (isVarAt-ι x (g (Z.objs Γ))))

  sdF : ∀ Θ {X X′} → X ≡ X′ →
        S.sameDown (ιCtx Θ) X (S.fullT (S.homs (ιCtx Θ))) ≡ Z.sameDown Θ X′ (Z.fullT (Z.homs Θ))
  sdF Θ {X′ = X′} e =
    trans (cong₂ (S.sameDown (ιCtx Θ)) e (trans (cong S.fullT (homs-ι Θ)) (fullT-ι (Z.homs Θ))))
          (sameDown-ι Θ X′ (Z.fullT (Z.homs Θ)))

  sdB : ∀ sg Θ {X X′} → X ≡ X′ →
        S.sameDown (ιCtx Θ) X (S.bdryT sg (S.homs (ιCtx Θ))) ≡ Z.sameDown Θ X′ (Z.bdryT sg (Z.homs Θ))
  sdB sg Θ {X′ = X′} e =
    trans (cong₂ (S.sameDown (ιCtx Θ)) e (trans (cong (S.bdryT sg) (homs-ι Θ)) (bdryT-ι sg (Z.homs Θ))))
          (sameDown-ι Θ X′ (Z.bdryT sg (Z.homs Θ)))

mutual
  topS-ι : ∀ t → S.topS (ιTm t) ≡ Z.topS t
  topS-ι (P.var v)                 = refl
  topS-ι (P.cst ())
  topS-ι (P.coh Θ P.⋆ ρ)           = refl
  topS-ι (P.coh Θ (P.arr A t u) ρ) =
    trans (cong₂ (λ tops b → S.applyF tops (if b then [] else S.topT (S.homs (ιCtx Θ))))
                 (topsSub-ι ρ) (cohCase-ι Θ A t u))
          (trans (cong (λ C → S.applyF (Z.topsSub ρ) (if Z.cohCase Θ A t u then [] else C)) (topTΓ Θ))
                 (L.applyF (Z.topsSub ρ) (if Z.cohCase Θ A t u then [] else Z.topT (Z.homs Θ))))

  topsSub-ι : ∀ ρ → S.topsSub (ιSub ρ) ≡ Z.topsSub ρ
  topsSub-ι P.⟨⟩       = refl
  topsSub-ι (ρ P.,ₛ t) = cong₂ (λ a b → a ++ (b ∷ [])) (topsSub-ι ρ) (topS-ι t)

  suppTy-ι : ∀ A → S.suppTy (ιTy A) ≡ Z.suppTy A
  suppTy-ι P.⋆                         = refl
  suppTy-ι (P.arr P.⋆ _ _)             = refl
  suppTy-ι (P.arr (P.arr B s s′) t u) =
    cong₂ _++_ (suppTy-ι (P.arr B s s′)) (cong₂ _++_ (topS-ι t) (topS-ι u))

  supp-ι : ∀ t A → S.supp (ιTm t) (ιTy A) ≡ Z.supp t A
  supp-ι t A = cong₂ _++_ (topS-ι t) (suppTy-ι A)

  cohCase-ι : ∀ Θ A t u → S.cohCase (ιCtx Θ) (ιTy A) (ιTm t) (ιTm u) ≡ Z.cohCase Θ A t u
  cohCase-ι Θ P.⋆ t u = refl
  cohCase-ι Θ (P.arr B a b) t u =
    cong₂ _∧_ (endsOK-ι Θ (P.arr B a b))
              (cong₂ _∧_ (sdF Θ (supp-ι t (P.arr B a b))) (sdF Θ (supp-ι u (P.arr B a b))))

opCase-ι : ∀ Θ A t u → S.opCase (ιCtx Θ) (ιTy A) (ιTm t) (ιTm u) ≡ Z.opCase Θ A t u
opCase-ι Θ P.⋆ t u =
  cong₂ _∧_ (cong (_==ℕ 0) (dimKΓ Θ))
            (cong₂ _∧_ (objι S.firstL Z.firstL L.firstL Θ t) (objι S.lastL Z.lastL L.lastL Θ u))
opCase-ι Θ (P.arr B a b) t u =
  cong₂ _∧_ (endsOK-ι Θ A)
            (cong₂ _∧_ (cong₂ _==ℕ_ (dim-ι A) (dimKΓ Θ))
                       (cong₂ _∧_ (sdB false Θ (supp-ι t A)) (sdB true Θ (supp-ι u A))))
  where A = P.arr B a b

graySide-ι : ∀ Θ A t u → S.graySide (ιCtx Θ) (ιTy A) (ιTm t) (ιTm u) ≡ Z.graySide Θ A t u
graySide-ι Θ A t u = cong₂ _∨_ (cohCase-ι Θ A t u) (opCase-ι Θ A t u)
