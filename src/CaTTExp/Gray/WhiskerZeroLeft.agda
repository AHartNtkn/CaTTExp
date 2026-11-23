------------------------------------------------------------------------
-- The context of the k = 0 left whisker heads, and the transfer of the
-- side condition onto it (step 2(d) of the two-tier L whiskering
-- interface, notes/surface-conservativity.md §7).
--
-- LK 0 j is not ΣΘ with something appended (as BK 0 j is, Gray.
-- WhiskerZero) but LW (Dsk j) (eqLW), where
--
--   LW Θ = x, y, h : x → y, z, then g(ΣA) for each A of Θ,
--
-- i.e. the disk ΣΘ moved over (y, z) = (1, 3), its levels relabelled by
-- g (0 ↦ 1, 1 ↦ 3, i ↦ i + 2 for i ≥ 2). For Θ whose cells are the
-- relabelled cells of ΣΘ (`good`; every disk, `goodD`):
--
--   homsLW     : homs (LW Θ) = (h) , g(hΣ Θ)
--   bdryLW     : bdryT sg (homs (LW Θ)) = map F (bdryT sg (homs ΣΘ))
--   sameDownLW : sameDown ΣΘ S R → sameDown (LW Θ) (map F S) (map F R)
--
-- with F x = (h) ++ g(x). g is injective, so findEl, bdEl, hitsP, the
-- tables and the face order commute with it.
------------------------------------------------------------------------
module CaTTExp.Gray.WhiskerZeroLeft where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Cover using (Any; here; there; any-witness; any-at; any-map⁻; any-map⁺; T-All; All-T; ∧-in; z≤n)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; anyS⇒; anyS⇐; map≡)
open import CaTTExp.Gray.DownAgree ∅ using () renaming (module Faces to DF)
open import CaTTExp.Suspension ∅ using (Σctx; Σty; Σtm; S; lenΣ; dimΣ)
open import CaTTExp.Gray.SingleHom ∅ using (mkC; hΣ; hcsΣ; homsΣ; cellsΣ; endsTyΣ)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
import CaTTExp.Derived as D
open D using (Sph; Dsk; LK; lK; bLK; tL; λsK; λtK; nB; zK)

------------------------------------------------------------------------
-- Generalities.

private
  ++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  ++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

  map-++ : ∀ {A B : Set} (g : A → B) xs ys → map g (xs ++ ys) ≡ map g xs ++ map g ys
  map-++ g []       ys = refl
  map-++ g (x ∷ xs) ys = cong (g x ∷_) (map-++ g xs ys)

  map-∘ : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (λ x → f (g x)) xs
  map-∘ f g []       = refl
  map-∘ f g (x ∷ xs) = cong (f (g x) ∷_) (map-∘ f g xs)

  map-cong : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
  map-cong e []       = refl
  map-cong e (x ∷ xs) = cong₂ _∷_ (e x) (map-cong e xs)

  filter-++ : ∀ {A : Set} (p : A → Bool) xs ys → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
  filter-++ p []       ys = refl
  filter-++ p (x ∷ xs) ys with p x
  ... | true  = cong (x ∷_) (filter-++ p xs ys)
  ... | false = filter-++ p xs ys

  cm-++ : ∀ {A B : Set} (g : A → List B) xs ys → concatMap g (xs ++ ys) ≡ concatMap g xs ++ concatMap g ys
  cm-++ g []       ys = refl
  cm-++ g (x ∷ xs) ys = trans (cong (g x ++_) (cm-++ g xs ys)) (sym (++-assoc (g x) (concatMap g xs) (concatMap g ys)))

  ==ℕ-≡ : ∀ n → (n ==ℕ n) ≡ true
  ==ℕ-≡ zero    = refl
  ==ℕ-≡ (suc n) = ==ℕ-≡ n

------------------------------------------------------------------------
-- The relabelling: the disk ΣΘ moves to the second hom, over (y, z) =
-- (1, 3), its cells shifted by 2.

g : Nat → Nat
g zero                = 1
g (suc zero)          = 3
g (suc (suc i))       = suc (suc (suc (suc i)))

g== : ∀ a b → (g a ==ℕ g b) ≡ (a ==ℕ b)
g== zero          zero          = refl
g== zero          (suc zero)    = refl
g== zero          (suc (suc b)) = refl
g== (suc zero)    zero          = refl
g== (suc zero)    (suc zero)    = refl
g== (suc zero)    (suc (suc b)) = refl
g== (suc (suc a)) zero          = refl
g== (suc (suc a)) (suc zero)    = refl
g== (suc (suc a)) (suc (suc b)) = refl

g≢2 : ∀ a → (2 ==ℕ g a) ≡ false
g≢2 zero          = refl
g≢2 (suc zero)    = refl
g≢2 (suc (suc a)) = refl

renTm : Tm → Tm
renTm (var i) = var (g i)
renTm t       = t

renTy : Ty → Ty
renTy ⋆           = ⋆
renTy (arr A t u) = arr (renTy A) (renTm t) (renTm u)

-- x, y, h : x → y, z, then the disk over (y, z).
hL : Ty
hL = arr ⋆ (var 0) (var 1)

LW : Ctx → Ctx
LW ε       = ε ▸ ⋆ ▸ ⋆ ▸ hL ▸ ⋆
LW (Θ ▸ A) = LW Θ ▸ renTy (Σty A)

-- The cell of h, the cells of the disk, and the relabelling of cells.
hcL : El
hcL = el 2 1 0 0 0

mkL : Nat × Ty → El
mkL (v , A) = el (S (S v)) 2 (dim A) (fst (elBdry (renTy (Σty A)))) (snd (elBdry (renTy (Σty A))))

rel : El → El
rel (el l k zero    s t) = el (g l) (suc k) zero s t
rel (el l k (suc d) s t) = el (g l) (suc k) (suc d) (g s) (g t)

F : Tuple → Tuple
F x = 2 ∷ map g x

------------------------------------------------------------------------
-- The cells of LW Θ.

private
  fL : Nat × Ty → Nat × Ty
  fL (v , A) = S (S v) , renTy (Σty A)

  isStarRΣ : ∀ A → isStar (renTy (Σty A)) ≡ false
  isStarRΣ ⋆           = refl
  isStarRΣ (arr A t u) = refl

  filter-starL : ∀ es → filter (λ e → isStar (snd e)) (map fL es) ≡ []
  filter-starL []            = refl
  filter-starL ((v , A) ∷ es) rewrite isStarRΣ A = filter-starL es

  endsRen : ∀ B {a b} → endsTy B ≡ just (var a , var b) → endsTy (renTy B) ≡ just (var (g a) , var (g b))
  endsRen ⋆                 ()
  endsRen (arr ⋆ _ _)       refl = refl
  endsRen (arr (arr B s t) _ _) e = endsRen (arr B s t) e

  dimRen : ∀ B → dim (renTy B) ≡ dim B
  dimRen ⋆           = refl
  dimRen (arr B _ _) = cong suc (dimRen B)

  mkEl-fL : ∀ v A → mkEl (0 ∷ 1 ∷ 3 ∷ []) (fL (v , A)) ≡ mkL (v , A) ∷ []
  mkEl-fL v A rewrite endsRen (Σty A) (endsTyΣ A) | dimRen (Σty A) | dimΣ A = refl

  cm-mkL : ∀ es → concatMap (mkEl (0 ∷ 1 ∷ 3 ∷ [])) (map fL es) ≡ map mkL es
  cm-mkL []             = refl
  cm-mkL ((v , A) ∷ es) rewrite mkEl-fL v A = cong (mkL (v , A) ∷_) (cm-mkL es)

module _ (Θ : Ctx) where

  lenLW : len (LW Θ) ≡ S (S (len Θ))
  lenLW = go Θ
    where
    go : ∀ Θ → len (LW Θ) ≡ S (S (len Θ))
    go ε       = refl
    go (Θ ▸ A) = cong suc (go Θ)

  entriesLW : entries (LW Θ) ≡ (0 , ⋆) ∷ (1 , ⋆) ∷ (2 , hL) ∷ (3 , ⋆) ∷ map fL (entries Θ)
  entriesLW = go Θ
    where
    go : ∀ Θ → entries (LW Θ) ≡ (0 , ⋆) ∷ (1 , ⋆) ∷ (2 , hL) ∷ (3 , ⋆) ∷ map fL (entries Θ)
    go ε       = refl
    go (Θ ▸ A) =
      trans (cong (λ X → X ++ ((len (LW Θ) , renTy (Σty A)) ∷ [])) (go Θ))
        (cong (λ X → (0 , ⋆) ∷ (1 , ⋆) ∷ (2 , hL) ∷ (3 , ⋆) ∷ X)
          (trans (cong (λ n → map fL (entries Θ) ++ ((n , renTy (Σty A)) ∷ [])) (lenLW′ Θ))
                 (sym (map-++ fL (entries Θ) ((len Θ , A) ∷ [])))))
      where
      lenLW′ : ∀ Θ → len (LW Θ) ≡ S (S (len Θ))
      lenLW′ ε       = refl
      lenLW′ (Θ ▸ A) = cong suc (lenLW′ Θ)

  objsLW : objs (LW Θ) ≡ 0 ∷ 1 ∷ 3 ∷ []
  objsLW = trans (cong (λ E → map fst (filter (λ e → isStar (snd e)) E)) entriesLW)
                 (cong (λ X → 0 ∷ 1 ∷ 3 ∷ map fst X) (filter-starL (entries Θ)))

  cellsLW : cells (LW Θ) ≡ hcL ∷ map mkL (entries Θ)
  cellsLW = trans (cong₂ (λ os E → concatMap (mkEl os) E) objsLW entriesLW)
                  (cong (hcL ∷_) (cm-mkL (entries Θ)))

------------------------------------------------------------------------
-- For disks, the cells of the second hom are the relabelled cells of
-- ΣΘ.

private
  ALs : List (Nat × Ty) → Set
  ALs []             = ⊤
  ALs ((v , A) ∷ es) = (Σ Nat λ k → A ≡ aL k) × ALs es

  ALs-++ : ∀ xs ys → ALs xs → ALs ys → ALs (xs ++ ys)
  ALs-++ []             ys _       q = q
  ALs-++ ((v , A) ∷ xs) ys (a , p) q = a , ALs-++ xs ys p q

  ALs-Sph : ∀ m → ALs (entries (Sph m))
  ALs-Sph zero    = tt
  ALs-Sph (suc k) =
    ALs-++ (entries (Sph k) ++ _) _ (ALs-++ (entries (Sph k)) _ (ALs-Sph k) ((k , refl) , tt)) ((k , refl) , tt)

  ALs-Dsk : ∀ m → ALs (entries (Dsk m))
  ALs-Dsk m = ALs-++ (entries (Sph m)) _ (ALs-Sph m) ((m , refl) , tt)

  mkL-aL : ∀ v k → mkL (v , aL k) ≡ rel (mkC (v , aL k))
  mkL-aL v zero          = refl
  mkL-aL v (suc zero)    = refl
  mkL-aL v (suc (suc k)) = refl

  good-ALs : ∀ es → ALs es → map mkL es ≡ map (λ e → rel (mkC e)) es
  good-ALs []             _                = refl
  good-ALs ((v , A) ∷ es) ((k , refl) , p) = cong₂ _∷_ (mkL-aL v k) (good-ALs es p)

goodD : ∀ m → map mkL (entries (Dsk m)) ≡ map rel (cells (Σctx (Dsk m)))
goodD m = trans (good-ALs (entries (Dsk m)) (ALs-Dsk m))
                (trans (sym (map-∘ rel mkC (entries (Dsk m)))) (cong (map rel) (sym (cellsΣ (Dsk m)))))

------------------------------------------------------------------------
-- The homs of LW Θ: (h), then the relabelled hom of ΣΘ.

hA : Hom
hA = mkHom 0 (hcL ∷ [])

relH : Hom → Hom
relH h = mkHom (hd h) (map rel (hcs h))

private
  hdim-rel : ∀ c → hdim (rel c) ≡ hdim c
  hdim-rel (el l k zero    s t) = refl
  hdim-rel (el l k (suc d) s t) = refl

  lvl-rel : ∀ c → lvl (rel c) ≡ g (lvl c)
  lvl-rel (el l k zero    s t) = refl
  lvl-rel (el l k (suc d) s t) = refl

  hom-rel : ∀ c → hom (rel c) ≡ suc (hom c)
  hom-rel (el l k zero    s t) = refl
  hom-rel (el l k (suc d) s t) = refl

  hom-mkL : ∀ e → hom (mkL e) ≡ 2
  hom-mkL (v , A) = refl

  filter-L2 : ∀ es → filter (λ c → hom c ==ℕ 2) (map mkL es) ≡ map mkL es
  filter-L2 []       = refl
  filter-L2 (e ∷ es) = cong (mkL e ∷_) (filter-L2 es)

  filter-L1 : ∀ es → filter (λ c → hom c ==ℕ 1) (map mkL es) ≡ []
  filter-L1 []       = refl
  filter-L1 (e ∷ es) = filter-L1 es

module _ (Θ : Ctx) (good : map mkL (entries Θ) ≡ map rel (cells (Σctx Θ))) where

  private
    es = entries Θ
    X  = hcs (hΣ Θ)
    hm : List El → Hom
    hm cs = mkHom (maxL (map hdim cs)) cs

  homsLW : homs (LW Θ) ≡ hA ∷ relH (hΣ Θ) ∷ []
  homsLW =
    trans (cong (λ os → map (homAt (LW Θ)) (drop1 (upto (lengthN os)))) (objsLW Θ))
          (cong₂ (λ a b → a ∷ b ∷ []) h1 h2)
    where
    h1 : homAt (LW Θ) 1 ≡ hA
    h1 = trans (cong (λ cs → hm (filter (λ c → hom c ==ℕ 1) cs)) (cellsLW Θ))
               (cong (λ L → hm (hcL ∷ L)) (filter-L1 es))
    Y≡ : map mkL es ≡ map rel X
    Y≡ = trans good (cong (map rel) (sym (hcsΣ Θ)))
    h2 : homAt (LW Θ) 2 ≡ relH (hΣ Θ)
    h2 = trans (cong (λ cs → hm (filter (λ c → hom c ==ℕ 2) cs)) (cellsLW Θ))
           (trans (cong hm (trans (filter-L2 es) Y≡))
                  (cong (λ n → mkHom n (map rel X))
                        (cong maxL (trans (map-∘ hdim rel X) (map-cong hdim-rel X)))))

------------------------------------------------------------------------
-- The tables of (h) ⊗ g(hΣ Θ) are those of hΣ Θ, relabelled, with h
-- prepended.

private
  cm-cong : ∀ {A B : Set} {f f′ : A → List B} → (∀ x → f x ≡ f′ x) → ∀ xs → concatMap f xs ≡ concatMap f′ xs
  cm-cong e []       = refl
  cm-cong e (x ∷ xs) = cong₂ _++_ (e x) (cm-cong e xs)

  cm-map : ∀ {A B C : Set} (m : B → C) (f : A → List B) xs →
           concatMap (λ x → map m (f x)) xs ≡ map m (concatMap f xs)
  cm-map m f []       = refl
  cm-map m f (x ∷ xs) = trans (cong (map m (f x) ++_) (cm-map m f xs)) (sym (map-++ m (f x) (concatMap f xs)))

  hitsP-rel : ∀ i sg c w → hitsP i sg (rel c) (rel w) ≡ hitsP i sg c w
  hitsP-rel i sg c (el l k zero    s t) = refl
  hitsP-rel i sg c (el l k (suc d) s t) rewrite lvl-rel c with sg
  ... | true  = cong ((suc d ==ℕ suc i) ∧_) (g== s (lvl c))
  ... | false = cong ((suc d ==ℕ suc i) ∧_) (g== t (lvl c))

  any-rel : ∀ i sg c cs → any (hitsP i sg (rel c)) (map rel cs) ≡ any (hitsP i sg c) cs
  any-rel i sg c []       = refl
  any-rel i sg c (w ∷ cs) = cong₂ _∨_ (hitsP-rel i sg c w) (any-rel i sg c cs)

  filter-rel : ∀ (p : El → Bool) (q : El → Bool) → (∀ c → p (rel c) ≡ q c) → ∀ cs →
               filter p (map rel cs) ≡ map rel (filter q cs)
  filter-rel p q e []       = refl
  filter-rel p q e (c ∷ cs) rewrite e c with q c
  ... | true  = cong (rel c ∷_) (filter-rel p q e cs)
  ... | false = filter-rel p q e cs

  lvls-rel : ∀ cs → map lvl (map rel cs) ≡ map g (map lvl cs)
  lvls-rel cs = trans (map-∘ lvl rel cs) (trans (map-cong lvl-rel cs) (sym (map-∘ g lvl cs)))

piece-rel : ∀ h i sg → piece (relH h) i sg ≡ map g (piece h i sg)
piece-rel h i sg with i ==ℕ hd h
... | true  = trans (cong (map lvl) (filter-rel _ _ (λ c → cong (_==ℕ i) (hdim-rel c)) (hcs h))) (lvls-rel _)
... | false with i <ℕ hd h
...   | true  = trans (cong (map lvl) (filter-rel _ _ (λ c → cong₂ (λ a b → (a ==ℕ i) ∧ not b) (hdim-rel c) (any-rel i sg c (hcs h))) (hcs h)))
                      (lvls-rel _)
...   | false = refl

private
  nil-fix : ∀ s r → map (map g) (chainT s r []) ≡ chainT s r []
  nil-fix s r with r ==ℕ 0
  ... | true  = refl
  ... | false = refl

  prod1-rel : ∀ P C → map (map g) C ≡ C → prod1 (map g P) C ≡ map (map g) (prod1 P C)
  prod1-rel []      C e = refl
  prod1-rel (x ∷ P) C e =
    trans (cong₂ _++_ step (prod1-rel P C e)) (sym (map-++ (map g) (map (x ∷_) C) (prod1 P C)))
    where
    step : map (g x ∷_) C ≡ map (map g) (map (x ∷_) C)
    step = trans (cong (map (g x ∷_)) (sym e))
                 (trans (map-∘ (g x ∷_) (map g) C) (sym (map-∘ (map g) (x ∷_) C)))

chain1-rel : ∀ h s k → chainT s k (relH h ∷ []) ≡ map (map g) (chainT s k (h ∷ []))
chain1-rel h s k =
  trans (cm-cong (λ i → trans (cong (λ P → prod1 P (chainT (if odd i then not s else s) (k ∸ i) [])) (piece-rel h i s))
                              (prod1-rel (piece h i s) (chainT (if odd i then not s else s) (k ∸ i) []) (nil-fix (if odd i then not s else s) (k ∸ i))))
                 (filter (λ i → i <ℕ suc k) (upto k)))
        (cm-map (map g) (λ i → prod1 (piece h i s) (chainT (if odd i then not s else s) (k ∸ i) [])) (filter (λ i → i <ℕ suc k) (upto k)))

private
  upto-suc : ∀ k → upto (suc k) ≡ 0 ∷ map suc (upto k)
  upto-suc zero    = refl
  upto-suc (suc k) =
    trans (cong (_++ (suc (suc k) ∷ [])) (upto-suc k)) (cong (0 ∷_) (sym (map-++ suc (upto k) (suc k ∷ []))))

  uptoP : Nat → List Nat
  uptoP zero    = []
  uptoP (suc k) = upto k

  uptoS : ∀ k → upto k ≡ 0 ∷ map suc (uptoP k)
  uptoS zero    = refl
  uptoS (suc k) = upto-suc k

chainA : ∀ hs s k → chainT s k (hA ∷ hs) ≡ map (2 ∷_) (chainT s k hs)
chainA hs s k rewrite uptoS k =
  trans (cong (prod1 (2 ∷ []) (chainT s k hs) ++_) (sucs (uptoP k)))
        (trans (++-[] _) (++-[] _))
  where
  f : Nat → TSet
  f i = prod1 (piece hA i s) (chainT (if odd i then not s else s) (k ∸ i) hs)
  sucs : ∀ U → concatMap f (filter (λ i → i <ℕ suc k) (map suc U)) ≡ []
  sucs []      = refl
  sucs (u ∷ U) with suc u <ℕ suc k
  ... | true  = sucs U
  ... | false = sucs U

chainAB : ∀ h s k → chainT s k (hA ∷ relH h ∷ []) ≡ map F (chainT s k (h ∷ []))
chainAB h s k =
  trans (chainA (relH h ∷ []) s k)
        (trans (cong (map (2 ∷_)) (chain1-rel h s k)) (map-∘ (2 ∷_) (map g) (chainT s k (h ∷ []))))

lowerAB : ∀ h m → lowerT m (hA ∷ relH h ∷ []) ≡ map F (lowerT m (h ∷ []))
lowerAB h zero    = refl
lowerAB h (suc m) rewrite lowerAB h m | chainAB h false m | chainAB h true m =
  sym (trans (map-++ F (lowerT m (h ∷ [])) (chainT false m (h ∷ []) ++ chainT true m (h ∷ [])))
             (cong (map F (lowerT m (h ∷ [])) ++_) (map-++ F (chainT false m (h ∷ [])) (chainT true m (h ∷ [])))))

module _ (Θ : Ctx) (good : map mkL (entries Θ) ≡ map rel (cells (Σctx Θ))) where

  bdryLW : ∀ sg → bdryT sg (homs (LW Θ)) ≡ map F (bdryT sg (homs (Σctx Θ)))
  bdryLW sg rewrite homsLW Θ good | homsΣ Θ =
    trans (cong₂ _++_ (lowerAB (hΣ Θ) (hd (hΣ Θ) + 0 ∸ 1)) (chainAB (hΣ Θ) sg (hd (hΣ Θ) + 0 ∸ 1)))
          (sym (map-++ F (lowerT (hd (hΣ Θ) + 0 ∸ 1) (hΣ Θ ∷ [])) (chainT sg (hd (hΣ Θ) + 0 ∸ 1) (hΣ Θ ∷ []))))

  topLW : topT (homs (LW Θ)) ≡ map F (topT (homs (Σctx Θ)))
  topLW rewrite homsLW Θ good | homsΣ Θ = chainAB (hΣ Θ) true (hd (hΣ Θ) + 0)

  dimKLW : dimK (homs (LW Θ)) ≡ dimK (homs (Σctx Θ))
  dimKLW rewrite homsLW Θ good | homsΣ Θ = refl

------------------------------------------------------------------------
-- The face order commutes with the relabelling.

private
  map⇒ : ∀ {A B : Set} (f : A → B) xs {y} → Any (y ≡_) (map f xs) → Σ A λ x → Any (x ≡_) xs × (y ≡ f x)
  map⇒ f xs m = any-witness (any-map⁻ f xs (subst (Any _) (map≡ f xs) m))

  map⇐ : ∀ {A B : Set} (f : A → B) xs {x} → Any (x ≡_) xs → Any (f x ≡_) (map f xs)
  map⇐ f xs {x} m = subst (Any (f x ≡_)) (sym (map≡ f xs)) (any-map⁺ f (any-at m refl))

  mapM : Maybe El → Maybe El
  mapM nothing  = nothing
  mapM (just c) = just (rel c)

  bdM : Maybe El → List Nat
  bdM nothing  = []
  bdM (just c) = if hdim c ==ℕ 0 then [] else (src c ∷ tgt c ∷ [])

  bdEl≡ : ∀ cs w → bdEl cs w ≡ bdM (findEl w cs)
  bdEl≡ cs w with findEl w cs
  ... | nothing = refl
  ... | just c  = refl

  bdM-rel : ∀ m → bdM (mapM m) ≡ map g (bdM m)
  bdM-rel nothing                   = refl
  bdM-rel (just (el l k zero s t))    = refl
  bdM-rel (just (el l k (suc d) s t)) = refl

  findEl-rel : ∀ w cs → findEl (g w) (map rel cs) ≡ mapM (findEl w cs)
  findEl-rel w []       = refl
  findEl-rel w (c ∷ cs) rewrite lvl-rel c | g== (lvl c) w with lvl c ==ℕ w
  ... | true  = refl
  ... | false = findEl-rel w cs

  findEl-h : ∀ w X → findEl (g w) (hcL ∷ X) ≡ findEl (g w) X
  findEl-h w X rewrite g≢2 w = refl

module _ (cs : List El) where

  private
    cs′ = hcL ∷ map rel cs

  bdEl-rel : ∀ w → bdEl cs′ (g w) ≡ map g (bdEl cs w)
  bdEl-rel w =
    trans (bdEl≡ cs′ (g w))
      (trans (cong bdM (trans (findEl-h w (map rel cs)) (findEl-rel w cs)))
             (trans (bdM-rel (findEl w cs)) (cong (map g) (sym (bdEl≡ cs w)))))

  private
    lr-rel : ∀ {k b a} → DF.LR cs k b a → DF.LR cs′ k (g b) (g a)
    lr-rel DF.lz                   = DF.lz
    lr-rel (DF.ls {b = b} {c} mc lr) =
      DF.ls (subst (λ L → g c ∈ᴺ L) (sym (bdEl-rel b)) (map⇐ g (bdEl cs b) mc)) (lr-rel lr)

    leqL-rel : ∀ n a b → T (leqL cs n a b) → T (leqL cs′ n (g a) (g b))
    leqL-rel n a b p with DF.leqL⇒ cs n a b p
    ... | k , l , lr = DF.leqL⇐ cs′ n l (lr-rel lr)

    leqT-map : ∀ n x r → T (leqT cs n x r) → T (leqT cs′ n (map g x) (map g r))
    leqT-map n []      []      _ = tt
    leqT-map n (a ∷ x) (b ∷ r) p =
      ∧-in (leqL-rel n a b (∧-fst {leqL cs n a b} p)) (leqT-map n x r (∧-snd {leqL cs n a b} p))
    leqT-map n []      (_ ∷ _) ()
    leqT-map n (_ ∷ _) []      ()

  leqT-F : ∀ n x r → T (leqT cs n x r) → T (leqT cs′ n (F x) (F r))
  leqT-F n x r p = ∧-in (DF.leqL⇐ cs′ n {a = 2} z≤n DF.lz) (leqT-map n x r p)

  covF : ∀ n S R → T (all (λ s → any (leqT cs n s) R) S) →
         T (all (λ s → any (leqT cs′ n s) (map F R)) (map F S))
  covF n S R p =
    T-All (λ s → any (leqT cs′ n s) (map F R)) (map F S) λ {s′} ms′ → go (map⇒ F S ms′)
    where
    go : ∀ {s′} → (Σ Tuple λ s → Any (s ≡_) S × (s′ ≡ F s)) → T (any (leqT cs′ n s′) (map F R))
    go (s , ms , refl) with any-witness (anyS⇒ (leqT cs n s) R (All-T (λ s → any (leqT cs n s) R) S p ms))
    ... | r , mr , q = anyS⇐ (leqT cs′ n (F s)) (map F R) (any-at (map⇐ F R mr) (leqT-F n s r q))

module _ (Θ : Ctx) (good : map mkL (entries Θ) ≡ map rel (cells (Σctx Θ))) where

  private
    N = dimK (homs (Σctx Θ))
    cs = cells (Σctx Θ)
    cellsLW′ : cells (LW Θ) ≡ hcL ∷ map rel cs
    cellsLW′ = trans (cellsLW Θ) (cong (hcL ∷_) good)

  coversLW : ∀ S R → T (covers (Σctx Θ) S R) → T (covers (LW Θ) (map F S) (map F R))
  coversLW S R p =
    subst (λ n → T (all (λ s → any (leqT (cells (LW Θ)) n s) (map F R)) (map F S))) (sym (dimKLW Θ good))
      (subst (λ c → T (all (λ s → any (leqT c N s) (map F R)) (map F S))) (sym cellsLW′)
        (covF cs N S R p))

  sameDownLW : ∀ S R → T (sameDown (Σctx Θ) S R) → T (sameDown (LW Θ) (map F S) (map F R))
  sameDownLW S R p =
    ∧-in (coversLW S R (∧-fst {covers (Σctx Θ) S R} p)) (coversLW R S (∧-snd {covers (Σctx Θ) S R} p))

------------------------------------------------------------------------
-- LK 0 j is LW (Dsk j).

bL≡ : ∀ i → bLK 0 (suc i) ≡ renTy (Σty (aL (i + 0)))
bL≡ zero    = refl
bL≡ (suc i) = cong (λ X → arr X (var (tL 0 i)) (var (suc (tL 0 i)))) (bL≡ i)

eqLW : ∀ j → LW (Dsk (j + 0)) ≡ LK 0 j
eqLW zero    = refl
eqLW (suc j) = sym (cong₂ (λ Γ (P : Ty × Ty) → Γ ▸ fst P ▸ snd P) (sym (eqLW j)) (cong₂ _,_ (bL≡ j) (bL≡ (suc j))))
