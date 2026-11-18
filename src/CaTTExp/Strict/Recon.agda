------------------------------------------------------------------------
-- Support determines cells (notes/conjectures/answered/
-- steiner-support-formalizable-2026-11-18.md, §§4–6), for cells of
-- K(Γ)(x, y), Γ a pasting context, without atoms.
--
-- The closed support of a cell X is D X: the tuples reached from a
-- tuple of X by at most dimK face steps (the closure `down` computes).
--
--   * lifting (§4): every tuple b of D X is in the top chain of a cell
--     whose source and target are those of the sub-cells of X of the
--     same dimension (`lift`), by cutting along a face path;
--   * (G) (§5): with (F2) (Strict.Rad), a tuple in both the source and
--     the target row of a sub-cell of X is a face of no tuple of D X;
--   * reconstruction (§6): the top chain of X is the set of tuples of
--     D X of degree dim X, and each lower row is determined by the row
--     above and D X (`uniq`).
--
-- So two n-cells with the same closed support are equal (`supp-det`),
-- which proves Strict.Hyp.BSupp and its instance BBdry.
------------------------------------------------------------------------
module CaTTExp.Strict.Recon where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Cut
open import CaTTExp.Strict.Rad using (∈L-count; pos-≤; cm-ge; cm-mem; consB-mem⇐; setTop-top; rad; hbound; f2⁺; f2⁻)
open import CaTTExp.Strict.Hyp using (SetEq; BSupp; BBdry; bsupp→bbdry; ⊆T-sound)
open import CaTTExp.Strict.TopCell using (Pos; _⊎_; inj₁; inj₂)
open import CaTTExp.Strict.CohCase using (count-∈L; All-∈L; ∈L-++r)
open import CaTTExp.Strict.Order using (OInv; oinv-⊢ps)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any; _≤_; z≤n; s≤s; ≤-trans; ≤-refl; ≤-step; n≤m+n; m≤m+n)
  renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_)
open import CaTTExp.Gray.DownAgree ∅ using (memT-sound; memT-complete; nub-sound; nub-complete)
  renaming (module Faces to DF)
import CaTTExp.Gray.Graded ∅ as Gr

------------------------------------------------------------------------
-- Lists and numbers.

∈L-++l : ∀ A B {x} → x ∈L A → x ∈L (A ++ B)
∈L-++l (a ∷ A) B (hereA e) = hereA e
∈L-++l (a ∷ A) B (thereA m) = thereA (∈L-++l A B m)

private
  suc-≰ : ∀ n → suc n ≤ n → ⊥
  suc-≰ zero    ()
  suc-≰ (suc n) (s≤s p) = suc-≰ n p

  ≤-split : ∀ {m n} → m ≤ n → (m ≡ n) ⊎ (suc m ≤ n)
  ≤-split {zero}  {zero}  _       = inj₁ refl
  ≤-split {zero}  {suc n} _       = inj₂ (s≤s z≤n)
  ≤-split {suc m} {suc n} (s≤s p) with ≤-split p
  ... | inj₁ e = inj₁ (cong suc e)
  ... | inj₂ q = inj₂ (s≤s q)

  ∸-suc : ∀ m n → m ≤ n → suc n ∸ m ≡ suc (n ∸ m)
  ∸-suc zero    n       _       = refl
  ∸-suc (suc m) (suc n) (s≤s p) = ∸-suc m n p

  ∸-self : ∀ n → n ∸ n ≡ 0
  ∸-self zero    = refl
  ∸-self (suc n) = ∸-self n

  ∸-zero : ∀ m n → m ≤ n → n ∸ m ≡ 0 → m ≡ n
  ∸-zero zero    zero    _       _ = refl
  ∸-zero (suc m) (suc n) (s≤s p) e = cong suc (∸-zero m n p e)

  flipN-invol : ∀ n b → flipN n (flipN n b) ≡ b
  flipN-invol zero    b = refl
  flipN-invol (suc n) b =
    trans (cong not (flipN-not n (flipN n b))) (trans (not-not (flipN n (flipN n b))) (flipN-invol n b))
    where
    not-not : ∀ b → not (not b) ≡ b
    not-not true  = refl
    not-not false = refl

------------------------------------------------------------------------
-- Gray face steps are boundary faces.

module _ {Γ : Ctx} (inv : PsInv Γ) where
  private
    module F = DF (cells Γ)

    bd-face : ∀ w b ws → b ∈ᴺ bdEl (cells Γ) w → Σ Bool λ σ → (b ∷ ws) ∈L ∂T Γ σ (w ∷ ws)
    bd-face w b ws mb = go (findEl w (cells Γ)) refl
      where
      R = consB w (∂T Γ (flipN (hdimV Γ w) false) ws)
      R' = consB w (∂T Γ (flipN (hdimV Γ w) true) ws)
      shape : ∀ A → lookup Γ w ≡ just A →
              b ∈ᴺ (if (dim A ∸ 1) ==ℕ 0 then [] else (fst (elBdry A) ∷ snd (elBdry A) ∷ [])) →
              Σ Bool λ σ → (b ∷ ws) ∈L ∂T Γ σ (w ∷ ws)
      shape ⋆ _ ()
      shape (arr ⋆ _ _) _ ()
      shape (arr (arr B a a') s t) eL m with inv w _ eL
      shape (arr (arr B a a') .(var i) .(var j)) eL (hereA refl) | i , j , refl , refl , _ =
        false , subst (λ L → (b ∷ ws) ∈L (here false (facesTy L) ws ++ R)) (sym eL) (hereA refl)
      shape (arr (arr B a a') .(var i) .(var j)) eL (thereA (hereA refl)) | i , j , refl , refl , _ =
        true , subst (λ L → (b ∷ ws) ∈L (here true (facesTy L) ws ++ R')) (sym eL) (hereA refl)
      go : ∀ m → findEl w (cells Γ) ≡ m → Σ Bool λ σ → (b ∷ ws) ∈L ∂T Γ σ (w ∷ ws)
      go nothing e = ⊥-elim (no (subst (b ∈ᴺ_) (bd-nothing e) mb))
        where
        no : b ∈ᴺ [] → ⊥
        no ()
        bd-nothing : findEl w (cells Γ) ≡ nothing → bdEl (cells Γ) w ≡ []
        bd-nothing e with findEl w (cells Γ)
        bd-nothing refl | nothing = refl
      go (just c) e with Gr.elAt-just (objs Γ) Γ w (trans (sym (Gr.findEl-cells (objs Γ) Γ w)) e)
      ... | A , eL , k , eH , refl = shape A eL (subst (b ∈ᴺ_) (Gr.bd-just (cells Γ) w e) mb)

  step-face : ∀ {t a} → F.Step t a → Σ Bool λ σ → a ∈L ∂T Γ σ t
  step-face (F.sh {w} {b} {ws} mb) = bd-face w b ws mb
  step-face (F.st {w} {ws} {ws'} s) with step-face s
  ... | τ , m =
    flipN (hdimV Γ w) τ ,
    ∈L-++r (here (flipN (hdimV Γ w) τ) (facesTy (lookup Γ w)) ws)
      (subst (λ σ → (w ∷ ws') ∈L consB w (∂T Γ σ ws)) (sym (flipN-invol (hdimV Γ w) τ)) (consB-mem⇐ w _ m))

  reach-last : ∀ {j t a} → F.Reach (suc j) t a → Σ Tuple λ z → F.Reach j t z × F.Step z a
  reach-last {zero}  (F.step s F.done) = _ , F.done , s
  reach-last {suc j} (F.step s r) with reach-last r
  ... | z , r' , s' = z , F.step s r' , s'

  -- Face paths from a basis element stay in the hom and lower the degree.
  reach-deg : ∀ x y {j t a} → WFT Γ x y t → F.Reach j t a → WFT Γ x y a × (deg Γ a + j ≡ deg Γ t)
  reach-deg x y wt F.done = wt , +-zero _
  reach-deg x y {t = t} wt (F.step {k} {_} {z} s r) with step-face s
  ... | σ , m with face-wft inv σ x y t wt m
  ...   | wz , dz with reach-deg x y wz r
  ...     | wa , da = wa , trans (+-suc _ k) (trans (cong suc da) dz)

------------------------------------------------------------------------
-- Sub-cells of a tower and globularity.

data SubT : Nat → Tower → Nat → Tower → Set where
  self : ∀ {n X} → SubT n X n X
  inS  : ∀ {n S U c m Z} → SubT n S m Z → SubT (suc n) (step S U c) m Z
  inU  : ∀ {n S U c m Z} → SubT n U m Z → SubT (suc n) (step S U c) m Z

Sub-le : ∀ {n X m Z} → SubT n X m Z → m ≤ n
Sub-le {n} self = ≤-refl n
Sub-le (inS p)  = ≤-step (Sub-le p)
Sub-le (inU p)  = ≤-step (Sub-le p)

Sub-self : ∀ {n X Z} → SubT n X n Z → Z ≡ X
Sub-self self        = refl
Sub-self {suc n} (inS p) = ⊥-elim (suc-≰ n (Sub-le p))
Sub-self {suc n} (inU p) = ⊥-elim (suc-≰ n (Sub-le p))

Sub-S : ∀ {n X m S U c} → SubT n X (suc m) (step S U c) → SubT n X m S
Sub-S self    = inS self
Sub-S (inS p) = inS (Sub-S p)
Sub-S (inU p) = inU (Sub-S p)

Sub-U : ∀ {n X m S U c} → SubT n X (suc m) (step S U c) → SubT n X m U
Sub-U self    = inU self
Sub-U (inS p) = inS (Sub-U p)
Sub-U (inU p) = inU (Sub-U p)

-- A sub-cell below the top has a parent one dimension up.
data Child (V : Tower) : Tower → Set where
  isS : ∀ {U c} → Child V (step V U c)
  isU : ∀ {S c} → Child V (step S V c)

parent : ∀ {n X m V} → SubT n X m V → suc m ≤ n → Σ Tower λ Z → SubT n X (suc m) Z × Child V Z
parent {n} self l = ⊥-elim (suc-≰ n l)
parent {suc n} {m = m} (inS p) (s≤s l) with ≤-split l
... | inj₁ refl rewrite Sub-self p = _ , self , isS
... | inj₂ l'   with parent p l'
...   | Z , q , ch = Z , inS q , ch
parent {suc n} {m = m} (inU p) (s≤s l) with ≤-split l
... | inj₁ refl rewrite Sub-self p = _ , self , isU
... | inj₂ l'   with parent p l'
...   | Z , q , ch = Z , inU q , ch

iterS : Nat → Tower → Tower
iterS zero    X            = X
iterS (suc j) (base c)     = base c
iterS (suc j) (step S _ _) = iterS j S

iterS-≈w : ∀ j X X' → X ≈w X' → iterS j X ≈w iterS j X'
iterS-≈w zero    X            X'              p           = p
iterS-≈w (suc j) (base c)     (base c')       p           = p
iterS-≈w (suc j) (step S U c) (step S' U' c') (p , _ , _) = iterS-≈w j S S' p

Par-refl : ∀ X → Par X X
Par-refl (base _)     = tt
Par-refl (step S U _) = ≈w-refl S , ≈w-refl U

Par-sym : ∀ X Y → Par X Y → Par Y X
Par-sym (base _)     (base _)       _       = tt
Par-sym (step S U _) (step S' U' _) (p , q) = ≈w-sym S S' p , ≈w-sym U U' q

Par-trans : ∀ X Y Z → Par X Y → Par Y Z → Par X Z
Par-trans (base _)     (base _)       (base _)         _       _         = tt
Par-trans (step S U _) (step S' U' _) (step S'' U'' _) (p , q) (p' , q') =
  ≈w-trans S S' S'' p p' , ≈w-trans U U' U'' q q'

Par-≈r : ∀ Z X X' → X ≈w X' → Par Z X → Par Z X'
Par-≈r Z X X' p = Par-≈ Z X Z X' (≈w-refl Z) p

Par-base : ∀ Z c c' → Par Z (base c) → Par Z (base c')
Par-base (base _) c c' _ = tt

Par-setTop : ∀ S SV w → S ≈w SV → Par (setTop S w) SV
Par-setTop (base _)       (base _)         w _           = tt
Par-setTop (step S₁ S₂ _) (step V₁ V₂ _)   w (p , q , _) = p , q

module _ {Γ : Ctx} (P : Γ ⊢ps) {x y : Nat} where
  private
    I   = oinv-⊢ps P
    inv = psInv P
    topBas = Cells.IsCell-top (∂T Γ) (Basis Γ x y)
    Cell = IsCellL Γ x y

  Sub-cell : ∀ {n X m Z} → Cell n X → SubT n X m Z → Cell m Z
  Sub-cell c self = c
  Sub-cell {X = step S U _} (cS , _ , _ , _ , _) (inS p) = Sub-cell cS p
  Sub-cell {X = step S U _} (_ , cU , _ , _ , _) (inU p) = Sub-cell cU p

  -- All sub-cells of dimension m have the boundary of the canonical one.
  glob : ∀ {n X m Z} → Cell n X → SubT n X m Z → Par Z (iterS (n ∸ m) X)
  glob {n} {X} c self = subst (λ j → Par X (iterS j X)) (sym (∸-self n)) (Par-refl X)
  glob {suc n} {step S U c} {m} {Z} (cS , cU , par , _) (inS p) =
    subst (λ j → Par Z (iterS j (step S U c))) (sym (∸-suc m n (Sub-le p))) (glob cS p)
  glob {suc n} {step S U c} {m} {Z} (cS , cU , par , _) (inU p) =
    subst (λ j → Par Z (iterS j (step S U c))) (sym (∸-suc m n (Sub-le p)))
      (swap (n ∸ m) refl S U refl refl par (glob cU p))
    where
    swap : ∀ j → n ∸ m ≡ j → ∀ S' U' → S' ≡ S → U' ≡ U → Par S' U' → Par Z (iterS j U') → Par Z (iterS j S')
    swap zero e S' U' refl refl par _ rewrite Sub-self (subst (λ k → SubT k U m Z) (sym (∸-zero m n (Sub-le p) e)) p) =
      Par-sym S U par
    swap (suc j) e (base _)       (base _)       _ _ _       q = Par-base Z _ _ q
    swap (suc j) e (step S₁ S₂ _) (step U₁ U₂ _) _ _ (a , b) q =
      Par-≈r Z (iterS j U₁) (iterS j S₁) (iterS-≈w j U₁ S₁ (≈w-sym S₁ U₁ a)) q

  ----------------------------------------------------------------------
  -- Tuples of a tower.

  flat-sub : ∀ n X → Cell n X → ∀ {t} → t ∈L flat X → Σ Nat λ m → Σ Tower λ V → SubT n X m V × t ∈L top V
  flat-sub zero (base c) _ m = 0 , base c , self , m
  flat-sub (suc n) (step S U c) (cS , cU , _) {t} m with ∈L-++ (flat S) m
  ... | inj₁ a with flat-sub n S cS a
  ...   | k , V , p , q = k , V , inS p , q
  flat-sub (suc n) (step S U c) (cS , cU , _) m | inj₂ b with ∈L-++ (flat U) b
  ... | inj₁ a with flat-sub n U cU a
  ...   | k , V , p , q = k , V , inU p , q
  flat-sub (suc n) (step S U c) _ m | inj₂ b | inj₂ d = suc n , step S U c , self , d

  flat-mono : ∀ {n X m Z t} → SubT n X m Z → t ∈L flat Z → t ∈L flat X
  flat-mono self m = m
  flat-mono {X = step S U c} (inS p) m = ∈L-++l (flat S) _ (flat-mono p m)
  flat-mono {X = step S U c} (inU p) m = ∈L-++r (flat S) (∈L-++l (flat U) c (flat-mono p m))

  top-flat : ∀ Z {t} → t ∈L top Z → t ∈L flat Z
  top-flat (base _)     m = m
  top-flat (step S U c) m = ∈L-++r (flat S) (∈L-++r (flat U) m)

  topdeg : ∀ m Z → Cell m Z → ∀ {t} → t ∈L top Z → Basis Γ x y m t
  topdeg m Z c mt = All-∈L (top Z) (topBas m Z c) mt

  ----------------------------------------------------------------------
  -- The closed support.

  private
    module F = DF (cells Γ)
    N = dimK (homs Γ)

  D : Tower → Tuple → Set
  D X a = F.InClo N (flat X) a

  D-flat : ∀ X {t} → t ∈L flat X → D X t
  D-flat X {t} m = t , m , 0 , z≤n , F.done

  ----------------------------------------------------------------------
  -- Lifting (§4).

  LInv : Nat → Tower → Nat → Tower → Set
  LInv n X m Z = Cell m Z × Σ Tower λ V → SubT n X m V × Par Z V

  lift-step : ∀ {n X m Z t t'} → LInv n X m Z → t ∈L top Z → F.Step t t' →
              Σ Nat λ m' → Σ Tower λ Z' → LInv n X m' Z' × t' ∈L top Z'
  lift-step {m = zero} {base c} {t} (cZ , _) mt sp with step-face inv sp
  ... | σ , mσ = ⊥-elim (none (subst (λ B → _ ∈L B) (∂-deg0 t (topdeg 0 (base c) cZ mt) σ) mσ))
    where
    none : ∀ {z} → z ∈L [] → ⊥
    none ()
  lift-step {m = suc q} {step S U c} {t} {t'} ((cS , cU , par , ch , ac) , step SV UV cV , sub , pS , pU) mt sp
    with step-face inv sp
  ... | σ , mσ =
    q , setTop S w , (cut-cell I inv q t' S (top U) c cS (topBas q U cU) ac ch , SV , Sub-S sub , Par-setTop S SV w pS) ,
    subst (t' ∈L_) (sym (setTop-top S w)) (count-∈L t' w (subst Pos (sym (cut-at I t' (top S) (top U) c)) (pos σ mσ)))
    where
    w = cut I t' (top S) (top U) c
    ge : ∀ σ → t' ∈L ∂T Γ σ t → Pos (count t' (∂B Γ σ c))
    ge σ m = pos-≤ (∈L-count t c mt) (cm-ge (∂T Γ σ) c t t' (∈L-count t' _ m))
    pos : ∀ σ → t' ∈L ∂T Γ σ t → Pos (count t' (top S) + count t' (∂B Γ true c))
    pos true  m = pos-≤ (ge true m) (n≤m+n (count t' (top S)) _)
    pos false m =
      subst Pos (trans (+-comm (count t' (top U)) _)
                (trans (sym (count-++ t' (∂B Γ false c) (top U)))
                (trans (sym (at ch t'))
                (trans (count-++ t' (∂B Γ true c) (top S)) (+-comm _ (count t' (top S)))))))
        (pos-≤ (ge false m) (n≤m+n (count t' (top U)) _))

  lift* : ∀ {n X m Z t j b} → LInv n X m Z → t ∈L top Z → F.Reach j t b →
          Σ Nat λ m' → Σ Tower λ Z' → LInv n X m' Z' × b ∈L top Z'
  lift* li mt F.done = _ , _ , li , mt
  lift* li mt (F.step s r) with lift-step li mt s
  ... | m' , Z' , li' , mt' = lift* li' mt' r

  lift : ∀ {n X b} → Cell n X → D X b → Σ Nat λ m → Σ Tower λ Z → LInv n X m Z × b ∈L top Z
  lift {n} {X} cX (t , mt , j , _ , r) with flat-sub n X cX mt
  ... | m , V , sub , mv = lift* (Sub-cell cX sub , V , sub , Par-refl V) mv r

  ----------------------------------------------------------------------
  -- The two conditions at a sub-cell step S U c of dimension k + 1.

  -- (B) A tuple of D X of degree k is in a row of the sub-cell or a
  -- face of a tuple of D X.
  NodeB : (Tuple → Set) → Nat → Tower → Tower → Set
  NodeB D' k S U = ∀ a → D' a → deg Γ a ≡ k →
    (Pos (count a (top S)) ⊎ Pos (count a (top U))) ⊎ (Σ Tuple λ b → Σ Bool λ σ → D' b × a ∈L ∂T Γ σ b)

  -- (G) A tuple in both rows is a face of no tuple of D X.
  NodeG : (Tuple → Set) → Tower → Tower → Set
  NodeG D' S U = ∀ a b σ → Pos (count a (top S)) → Pos (count a (top U)) → D' b → a ∈L ∂T Γ σ b → ⊥

  nodeB : ∀ {n X k S U c} → Cell n X → SubT n X (suc k) (step S U c) → NodeB (D X) k S U
  nodeB {n} {X} {k} {S} {U} {c} cX sub a (t , mt , zero , le , F.done) da with flat-sub n X cX mt
  ... | m , V , subV , mv = go m V (trans (sym (snd (topdeg m V (Sub-cell cX subV) mv))) da) subV mv
    where
    go : ∀ m V → m ≡ k → SubT n X m V → a ∈L top V →
         (Pos (count a (top S)) ⊎ Pos (count a (top U))) ⊎ (Σ Tuple λ b → Σ Bool λ σ → D X b × a ∈L ∂T Γ σ b)
    go .k V refl subV mv with parent subV (Sub-le sub)
    ... | Z₂ , sub₂ , ch = inj₁ (side ch (Par-trans Z₂ W (step S U c) (glob cX sub₂) (Par-sym (step S U c) W (glob cX sub))))
      where
      W = iterS (n ∸ suc k) X
      side : ∀ {Z₂} → Child V Z₂ → Par Z₂ (step S U c) → Pos (count a (top S)) ⊎ Pos (count a (top U))
      side isS (p , _) = inj₁ (subst Pos (at (≈w-top V S p) a) (∈L-count a _ mv))
      side isU (_ , q) = inj₂ (subst Pos (at (≈w-top V U q) a) (∈L-count a _ mv))
  nodeB cX sub a (t , mt , suc j , le , r) da with reach-last inv r
  ... | z , r' , sp with step-face inv sp
  ...   | σ , ma = inj₂ (z , σ , (t , mt , j , ≤-trans (≤-step (≤-refl j)) le , r') , ma)

  nodeG : ∀ {n X k S U c} → Cell n X → SubT n X (suc k) (step S U c) → NodeG (D X) S U
  nodeG {n} {X} {k} {S} {U} {c} cX sub a b σ qs pu db ma with lift cX db
  ... | m' , Z' , (cZ' , V , subV , pZ'V) , mb = go m' Z' em cZ' subV pZ'V mb
    where
    cS = fst (Sub-cell cX sub)
    ba = topdeg k S cS (count-∈L a _ qs)
    em : m' ≡ suc k
    em = trans (sym (snd (topdeg m' Z' cZ' mb)))
               (trans (sym (snd (face-wft inv σ x y b (fst (topdeg m' Z' cZ' mb)) ma))) (cong suc (snd ba)))
    go : ∀ m' Z' → m' ≡ suc k → Cell m' Z' → SubT n X m' V → Par Z' V → b ∈L top Z' → ⊥
    go .(suc k) (step S' U' c') refl cZ' subV pZ'V mb = fin σ ma
      where
      W = iterS (n ∸ suc k) X
      pZV : Par (step S U c) V
      pZV = Par-trans (step S U c) W V (glob cX sub) (Par-sym V W (glob cX subV))
      pZZ : Par (step S U c) (step S' U' c')
      pZZ = Par-trans (step S U c) V (step S' U' c') pZV (Par-sym (step S' U' c') V pZ'V)
      zpos : ∀ {n} → n ≡ 0 → Pos n → ⊥
      zpos refl ()
      fin : ∀ σ → a ∈L ∂T Γ σ b → ⊥
      fin true  m = zpos (trans (at (≈w-top S S' (fst pZZ)) a) (f2⁺ P k S' U' c' cZ' b a mb m)) qs
      fin false m = zpos (trans (at (≈w-top U U' (snd pZZ)) a) (f2⁻ P k S' U' c' cZ' b a mb m)) pu

  ----------------------------------------------------------------------
  -- The conditions at every sub-cell.

  Good : (Tuple → Set) → Nat → Tower → Set
  Good D' zero    (base _)     = ⊤
  Good D' (suc k) (step S U c) =
    NodeB D' k S U × NodeG D' S U × (∀ a → a ∈L top S → D' a) × (∀ b → b ∈L c → D' b) ×
    Good D' k S × Good D' k U
  Good D' _       _            = ⊥

  Good-iff : ∀ {D₁ D₂} → (∀ a → D₁ a → D₂ a) → (∀ a → D₂ a → D₁ a) → ∀ m Z → Good D₁ m Z → Good D₂ m Z
  Good-iff f g zero    (base _)     _ = tt
  Good-iff {D₁} {D₂} f g (suc k) (step S U c) (gB , gG , gS , gc , goS , goU) =
    (λ a d da → mapB (gB a (g a d) da)) ,
    (λ a b σ qs pu db m → gG a b σ qs pu (g b db) m) ,
    (λ a m → f a (gS a m)) , (λ b m → f b (gc b m)) ,
    Good-iff f g k S goS , Good-iff f g k U goU
    where
    mapB : ∀ {A a} → A ⊎ (Σ Tuple λ b → Σ Bool λ σ → D₁ b × a ∈L ∂T Γ σ b) →
           A ⊎ (Σ Tuple λ b → Σ Bool λ σ → D₂ b × a ∈L ∂T Γ σ b)
    mapB (inj₁ p)                 = inj₁ p
    mapB (inj₂ (b , σ , db , m)) = inj₂ (b , σ , f b db , m)

  goodX : ∀ {n X} → Cell n X → ∀ m Z → SubT n X m Z → Cell m Z → Good (D X) m Z
  goodX cX zero    (base c)     sub _ = tt
  goodX {X = X} cX (suc k) (step S U c) sub (cS , cU , _) =
    nodeB cX sub , nodeG cX sub ,
    (λ a m → D-flat X (flat-mono sub (∈L-++l (flat S) _ (top-flat S m)))) ,
    (λ b m → D-flat X (flat-mono sub (top-flat (step S U c) m))) ,
    goodX cX k S (Sub-S sub) cS , goodX cX k U (Sub-U sub) cU

  ----------------------------------------------------------------------
  -- Reconstruction (§6): a cell is determined by its top chain and the
  -- conditions.

  private
    cross : ∀ p n s u s' u' → p + s ≡ n + u → p + s' ≡ n + u' → s + u' ≡ s' + u
    cross p n s u s' u' e₁ e₂ = +-cancelˡ (p + n) (s + u') (s' + u)
      (trans (sym (+-interchange p s n u'))
      (trans (cong₂ _+_ e₁ (sym e₂))
      (trans (+-interchange n u p s') (cong₂ _+_ (+-comm n p) (+-comm u s')))))

    nat4' : ∀ {s u s' u'} → s ≤ 1 → u ≤ 1 → s' ≤ 1 → u' ≤ 1 → s + u' ≡ s' + u →
            (Pos s → Pos u → Pos s' × Pos u') → (Pos s' → Pos u' → Pos s × Pos u) → (s ≡ s') × (u ≡ u')
    nat4' z≤n z≤n z≤n z≤n _ _ _ = refl , refl
    nat4' z≤n z≤n z≤n (s≤s z≤n) () _ _
    nat4' z≤n z≤n (s≤s z≤n) z≤n () _ _
    nat4' z≤n z≤n (s≤s z≤n) (s≤s z≤n) _ _ g = ⊥-elim (fst (g tt tt))
    nat4' z≤n (s≤s z≤n) z≤n z≤n () _ _
    nat4' z≤n (s≤s z≤n) z≤n (s≤s z≤n) _ _ _ = refl , refl
    nat4' z≤n (s≤s z≤n) (s≤s z≤n) z≤n () _ _
    nat4' z≤n (s≤s z≤n) (s≤s z≤n) (s≤s z≤n) _ _ g = ⊥-elim (fst (g tt tt))
    nat4' (s≤s z≤n) z≤n z≤n z≤n () _ _
    nat4' (s≤s z≤n) z≤n z≤n (s≤s z≤n) () _ _
    nat4' (s≤s z≤n) z≤n (s≤s z≤n) z≤n _ _ _ = refl , refl
    nat4' (s≤s z≤n) z≤n (s≤s z≤n) (s≤s z≤n) _ _ g = ⊥-elim (snd (g tt tt))
    nat4' (s≤s z≤n) (s≤s z≤n) z≤n z≤n _ f _ = ⊥-elim (fst (f tt tt))
    nat4' (s≤s z≤n) (s≤s z≤n) z≤n (s≤s z≤n) _ f _ = ⊥-elim (fst (f tt tt))
    nat4' (s≤s z≤n) (s≤s z≤n) (s≤s z≤n) z≤n _ f _ = ⊥-elim (snd (f tt tt))
    nat4' (s≤s z≤n) (s≤s z≤n) (s≤s z≤n) (s≤s z≤n) _ _ _ = refl , refl

  both : ∀ {D'} k S U c S' U' c' → Cell (suc k) (step S U c) → Cell (suc k) (step S' U' c') →
         Good D' (suc k) (step S U c) → Good D' (suc k) (step S' U' c') → c ≈ c' →
         ∀ a → Pos (count a (top S)) → Pos (count a (top U)) → Pos (count a (top S')) × Pos (count a (top U'))
  both {D'} k S U c S' U' c' (cS , _) (_ , _ , _ , ch' , _) (_ , gG , gS , gc , _) (gB' , _) pc a qs pu
    with gB' a da (snd (topdeg k S cS (count-∈L a _ qs)))
    where
    da = gS a (count-∈L a _ qs)
  ... | inj₂ (b , σ , db , m) = ⊥-elim (gG a b σ qs pu db m)
  ... | inj₁ side = sides side
    where
    no : ∀ σ → count a (∂B Γ σ c) ≡ 0
    no σ with count a (∂B Γ σ c) in e
    ... | zero  = refl
    ... | suc _ with cm-mem (∂T Γ σ) c a (subst Pos (sym e) tt)
    ...   | b , mb , q = ⊥-elim (gG a b σ qs pu (gc b mb) (count-∈L a _ q))
    no' : ∀ σ → count a (∂B Γ σ c') ≡ 0
    no' σ = trans (sym (at (cm-cong (∂T Γ σ) c c' pc) a)) (no σ)
    su : count a (top S') ≡ count a (top U')
    su = trans (cong (_+ count a (top S')) (sym (no' true)))
         (trans (sym (count-++ a (∂B Γ true c') (top S')))
         (trans (at ch' a)
         (trans (count-++ a (∂B Γ false c') (top U')) (cong (_+ count a (top U')) (no' false)))))
    sides : Pos (count a (top S')) ⊎ Pos (count a (top U')) → Pos (count a (top S')) × Pos (count a (top U'))
    sides (inj₁ p) = p , subst Pos su p
    sides (inj₂ q) = subst Pos (sym su) q , q

  uniq : ∀ {D'} m Z Z' → Cell m Z → Cell m Z' → Good D' m Z → Good D' m Z' → top Z ≈ top Z' → Z ≈w Z'
  uniq zero    (base c)     (base c')       _  _   _  _   p = p
  uniq (suc k) (step S U c) (step S' U' c') cZ cZ' gZ gZ' p =
    uniq k S S' (fst cZ) (fst cZ') (fst (snd (snd (snd (snd gZ))))) (fst (snd (snd (snd (snd gZ'))))) (mk≈ λ a → fst (row a)) ,
    uniq k U U' (fst (snd cZ)) (fst (snd cZ')) (snd (snd (snd (snd (snd gZ))))) (snd (snd (snd (snd (snd gZ'))))) (mk≈ λ a → snd (row a)) ,
    p
    where
    row : ∀ a → (count a (top S) ≡ count a (top S')) × (count a (top U) ≡ count a (top U'))
    row a = nat4' (rad P k S (fst cZ) a) (rad P k U (fst (snd cZ)) a)
                  (rad P k S' (fst cZ') a) (rad P k U' (fst (snd cZ')) a)
                  (cross (count a (∂B Γ true c)) (count a (∂B Γ false c)) _ _ _ _ e₁ e₂)
                  (both k S U c S' U' c' cZ cZ' gZ gZ' p a)
                  (both k S' U' c' S U c cZ' cZ gZ' gZ (≈-sym p) a)
      where
      ch  = fst (snd (snd (snd cZ)))
      ch' = fst (snd (snd (snd cZ')))
      e₁ : count a (∂B Γ true c) + count a (top S) ≡ count a (∂B Γ false c) + count a (top U)
      e₁ = trans (sym (count-++ a (∂B Γ true c) (top S))) (trans (at ch a) (count-++ a (∂B Γ false c) (top U)))
      e₂ : count a (∂B Γ true c) + count a (top S') ≡ count a (∂B Γ false c) + count a (top U')
      e₂ = trans (cong (_+ count a (top S')) (at (cm-cong (∂T Γ true) c c' p) a))
           (trans (sym (count-++ a (∂B Γ true c') (top S'))) (trans (at ch' a)
           (trans (count-++ a (∂B Γ false c') (top U')) (cong (_+ count a (top U')) (sym (at (cm-cong (∂T Γ false) c c' p) a))))))

  ----------------------------------------------------------------------
  -- The top chain is the set of tuples of D X of top degree.

  private
    nat2 : ∀ {s s'} → s ≤ 1 → s' ≤ 1 → (Pos s → Pos s') → (Pos s' → Pos s) → s ≡ s'
    nat2 z≤n       z≤n       f g = refl
    nat2 z≤n       (s≤s z≤n) f g = ⊥-elim (g tt)
    nat2 (s≤s z≤n) z≤n       f g = ⊥-elim (f tt)
    nat2 (s≤s z≤n) (s≤s z≤n) f g = refl

    over : ∀ n j m → n + suc j ≡ m → m ≤ n → ⊥
    over n j m e l = suc-≰ n (≤-trans (s≤s (m≤m+n n j)) (subst (_≤ n) (sym (trans (sym (+-suc n j)) e)) l))

  top⇒ : ∀ {n X a} → Cell n X → Pos (count a (top X)) → D X a × (deg Γ a ≡ n)
  top⇒ {n} {X} {a} cX p = D-flat X (top-flat X (count-∈L a _ p)) , snd (topdeg n X cX (count-∈L a _ p))

  top⇐ : ∀ {n X a} → Cell n X → D X a → deg Γ a ≡ n → Pos (count a (top X))
  top⇐ {n} {X} {a} cX (t , mt , j , _ , r) da with flat-sub n X cX mt
  ... | m , V , sub , mv = fin j r (trans (cong (_+ j) (sym da)) (snd (reach-deg inv x y (fst bt) r))) (trans (snd bt) refl)
    where
    bt = topdeg m V (Sub-cell cX sub) mv
    fin : ∀ j → F.Reach j t a → n + j ≡ deg Γ t → deg Γ t ≡ m → Pos (count a (top X))
    fin zero    F.done e em with Sub-self (subst (λ k → SubT n X k V) (sym (trans (sym (+-zero n)) (trans e em))) sub)
    ... | refl = ∈L-count a _ mv
    fin (suc j) r e em = ⊥-elim (over n j m (trans e em) (Sub-le sub))

  topEq : ∀ {n X Y} → Cell n X → Cell n Y → (∀ a → D X a → D Y a) → (∀ a → D Y a → D X a) → top X ≈ top Y
  topEq {n} {X} {Y} cX cY f g = mk≈ λ a →
    nat2 (rad P n X cX a) (rad P n Y cY a)
      (λ p → let (d , e) = top⇒ cX p in top⇐ cY (f a d) e)
      (λ p → let (d , e) = top⇒ cY p in top⇐ cX (g a d) e)

  -- Support determines the cell.
  supp-det : ∀ n X Y → Cell n X → Cell n Y → (∀ a → D X a → D Y a) → (∀ a → D Y a → D X a) → X ≈w Y
  supp-det n X Y cX cY f g =
    uniq n X Y cX cY (goodX cX n X self cX) (Good-iff g f n Y (goodX cY n Y self cY)) (topEq cX cY f g)

------------------------------------------------------------------------
-- The hypotheses of Strict.Soundness.

b-supp : BSupp
b-supp {Θ} P x y n X Y L M cX cY fX fY eq =
  supp-det P n X Y cX cY (move {X} {Y} {L} {M} fX fY (⊆T-sound (down Θ L) (down Θ M) (∧-fst eq)))
                         (move {Y} {X} {M} {L} fY fX (⊆T-sound (down Θ M) (down Θ L) (∧-snd {⊆T (down Θ L) (down Θ M)} eq)))
  where
  module F = DF (cells Θ)
  N = dimK (homs Θ)
  move : ∀ {X Y L M} → SetEq (flat X) L → SetEq (flat Y) M →
         (∀ a → T (memT a (down Θ L)) → T (memT a (down Θ M))) →
         ∀ a → D P {x} {y} X a → D P {x} {y} Y a
  move {X} {Y} {L} {M} fX fY h a (t , mt , j , le , r)
    with F.close⇒ N (nubT M) (memT-sound a _ (h a (memT-complete a _
           (F.close⇐ N (nubT L) (t , nub-complete L (memT-sound t L (subst T (fX t) (memT-complete t (flat X) mt))) , j , le , r)))))
  ... | t' , mt' , j' , le' , r' =
    t' , memT-sound t' (flat Y) (subst T (sym (fY t')) (memT-complete t' M (nub-sound M mt'))) , j' , le' , r'

b-bdry : BBdry
b-bdry = bsupp→bbdry b-supp
