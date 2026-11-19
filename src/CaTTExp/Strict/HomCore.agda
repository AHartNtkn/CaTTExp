------------------------------------------------------------------------
-- The coh case of single-hom agreement, hom by hom.
--
-- Let Δ be a pasting context with objects o₀ … oₙ and homs h₁ … hₙ,
-- and let a substitution send each object o to an object img o of a
-- target whose cells all go from 0 to 1. Each hom then lands either in
-- a hom x → x (flat) or in the hom 0 → 1 (a jump), and at most one hom
-- jumps. `walk` computes the image of T's top chain under the chain
-- map of the substitution:
--   * if no hom jumps, it is the unit when every hom has dimension 0,
--     and 0 otherwise;
--   * if hom J jumps, it is the image of J's top cells when every other
--     hom has dimension 0, and 0 otherwise.
-- The hypotheses `flatH`, `jumpH` say what the substitution does on
-- each cell, by whether its hom is flat or jumps.
------------------------------------------------------------------------
module CaTTExp.Strict.HomCore where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L using (==-true; ==→≡)
open import CaTTExp.Strict.Tensor
open import CaTTExp.Strict.TotalCell using (Ph; Ch; HC; sing)
open import CaTTExp.Strict.Subst using (Ftuple-cons; applyF-cm; cmF-prod)
open import CaTTExp.Strict.Pasting using (_∈_; hd∈; tl∈; objL; pairs)
open import CaTTExp.Strict.Bridge using (module OneHom; seq; lengthN-snoc)
open import CaTTExp.Strict.HomTops
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂; Any; here; there; _≤_; z≤n; s≤s; ≤-trans; ≤-refl; max-l; max-r)
open import CaTTExp.Strict.L using (PsInv; psInv; endsL-inv; <-suc; n<suc; lookup-lt)
open import CaTTExp.Strict.Pasting using (rng; Tb; memHom; homM; hitB) renaming (sel to selH)
open import CaTTExp.Strict.Bridge using (ends-just; objs-objL; drop1-upto; homCells)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Strict.PsFacts ∅ using (Wb; dimv; dimM) renaming (sel to selW)
open import CaTTExp.Strict.Pasting using (hom-ends)
open import CaTTExp.Gray.PsFacts ∅ using (ps-facts; PsFacts)
import CaTTExp.Gray.CohDim ∅ as CD

------------------------------------------------------------------------
-- Small facts.

private
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  0≢s : ∀ {a} → 0 ≡ suc a → ⊥
  0≢s ()

  1≢0 : 1 ≡ 0 → ⊥
  1≢0 ()

-- 0/1 bags.
U : Bool → Bag
U true  = [] ∷ []
U false = []

prod-U : ∀ a b → prod (U (a ==ℕ 0)) (U (b ==ℕ 0)) ≈ U ((a + b) ==ℕ 0)
prod-U zero    zero    = ≈-refl
prod-U zero    (suc b) = ≈-refl
prod-U (suc a) b       = ≈-refl

-- c ≤ b as a + d.
Le : Nat → Nat → Set
Le c b = Σ Nat λ d → c + d ≡ b

private
  no' : ∀ c m → suc (m + c) ≡ c → ⊥
  no' zero    m ()
  no' (suc c) m p = no' c m (trans (sym (+-suc m c)) (suc-inj p))

  ==-false : ∀ a c → Le c a → ∀ {e} → suc e + a ≡ c → ⊥
  ==-false a c (d , cd) {e} q = no' c (e + d) (trans (cong suc (sym step2)) step1)
    where
    step1 : suc (e + (c + d)) ≡ c
    step1 = subst (λ z → suc (e + z) ≡ c) (sym cd) q
    step2 : e + (c + d) ≡ (e + d) + c
    step2 = trans (cong (e +_) (+-comm c d)) (sym (+-assoc e d c))

  eqb-false : ∀ m n → (m ≡ n → ⊥) → (m ==ℕ n) ≡ false
  eqb-false m n ne with m ==ℕ n in e
  ... | true  = ⊥-elim (ne (==→≡ m n e))
  ... | false = refl

prod-U-sel : ∀ (X : Bag) a b c → Le c b →
             prod (U (a ==ℕ 0)) (if b ==ℕ c then X else []) ≈ (if (a + b) ==ℕ c then X else [])
prod-U-sel X zero    b c le = prod-unitˡ _
prod-U-sel X (suc a) b c le rewrite eqb-false (suc a + b) c (==-false b c le) = ≈-refl

prod-sel-U : ∀ (X : Bag) a b → prod X (U (b ==ℕ 0)) ≈ (if (a + b) ==ℕ a then X else [])
prod-sel-U X a zero    rewrite +-zero a | ==-true a = prod-unitʳ X
prod-sel-U X a (suc b) rewrite eqb-false (a + suc b) a (λ q → ==-false a a (0 , +-zero a) {b} (trans (+-comm (suc b) a) q)) =
  ≡→≈ (prod-nilʳ X)

------------------------------------------------------------------------
-- The walk along the homs.

module Core {Δ : Ctx} (P : Δ ⊢ps) (R : List TSet) (F : Nat → Bag) (img : Nat → Nat)
  (flatH : ∀ v a b → endsL (lookup Δ v) ≡ just (a , b) → img a ≡ img b →
           (F v ≈ []) × (nth v R ≈ U (hdimV Δ v ==ℕ 0)))
  (jumpH : ∀ v a b → endsL (lookup Δ v) ≡ just (a , b) → (img a ≡ img b → ⊥) →
           (img a ≡ 0) × (img b ≡ 1) × (nth v R ≈ F v)) where

  S : Hom → Bag
  S h = cm (Ftuple R) (topsH h)

  Fsing : ∀ c → Ftuple R (sing c) ≈ nth c R
  Fsing c = ≈-trans (≡→≈ (Ftuple-cons R c [])) (prod-unitʳ (nth c R))

  private
    IsSing : Tuple → Set
    IsSing w = Σ Nat λ c → w ≡ sing c

    All-sing : ∀ L → All IsSing (map sing L)
    All-sing []      = tt
    All-sing (c ∷ L) = (c , refl) , All-sing L

    All-× : ∀ {P Q : Tuple → Set} X → All P X → All Q X → All (λ x → P x × Q x) X
    All-× []      _        _        = tt
    All-× (x ∷ X) (p , pr) (q , qr) = (p , q) , All-× X pr qr

  basis-sing : ∀ {o o' i} c → Basis Δ o o' i (sing c) →
               (endsL (lookup Δ c) ≡ just (o , o')) × (hdimV Δ c ≡ i)
  basis-sing c ((z , e , refl) , d) = e , trans (sym (+-zero (hdimV Δ c))) d

  -- One hom, between consecutive objects o, o'.
  module H (pre : List Nat) (o o' : Nat) (rest : List Nat) (eq : objL Δ ≡ pre ++ o ∷ o' ∷ rest) where
    h : Hom
    h = homAt Δ (suc (lengthN pre))

    tc : TabCell Δ o o' (hd h) (Ph h)
    tc = OneHom.hom-cell P pre o o' rest eq

    Info : Nat → Tuple → Set
    Info i w = Σ Nat λ c → (w ≡ sing c) × (endsL (lookup Δ c) ≡ just (o , o')) × (hdimV Δ c ≡ i)

    info : ∀ b i → All (Info i) (Ph h b i)
    info b i = All-map (Ph h b i) (λ { w ((c , we) , bs) → c , we , basis-sing c (subst (Basis Δ o o' i) we bs) })
                 (All-× (Ph h b i) (All-sing (piece h i b)) (basis tc b i))

    one-cell : Σ Nat λ c → endsL (lookup Δ c) ≡ just (o , o')
    one-cell with aug tc true
    ... | w , pw with fst (All-≈ (Ph h true 0) (w ∷ []) pw (info true 0))
    ...   | c , _ , e , _ = c , e

    pair-jump : (img o ≡ img o' → ⊥) → (img o ≡ 0) × (img o' ≡ 1)
    pair-jump ne = fst (jumpH c o o' e ne) , fst (snd (jumpH c o o' e ne))
      where
      c = fst one-cell
      e = snd one-cell

    S-flat : img o ≡ img o' → S h ≈ U (hd h ==ℕ 0)
    S-flat fl with hd h ==ℕ 0 in z
    ... | true with aug tc true
    ...   | w , pw with fst (All-≈ (Ph h true 0) (w ∷ []) pw (info true 0))
    ...     | c , we , e , hc =
      ≈-trans (cm-cong (Ftuple R) (topsH h) (w ∷ []) X≈)
      (≈-trans (≡→≈ (++-[]L (Ftuple R w)))
      (≈-trans (≡→≈ (cong (Ftuple R) we))
      (≈-trans (Fsing c)
               (subst (λ k → nth c R ≈ U (k ==ℕ 0)) hc (snd (flatH c o o' e fl))))))
      where
      X≈ : topsH h ≈ w ∷ []
      X≈ = subst (λ k → Ph h true k ≈ w ∷ []) (sym (==→≡ (hd h) 0 z)) pw
    S-flat fl | false =
      ≈-trans (cm-ext (Ftuple R) (λ _ → []) (topsH h) (info true (hd h)) zero1) (≡→≈ (cm-nil (topsH h)))
      where
      zero1 : ∀ w → Info (hd h) w → Ftuple R w ≈ []
      zero1 w (c , we , e , hc) =
        ≈-trans (≡→≈ (cong (Ftuple R) we))
        (≈-trans (Fsing c)
        (≈-trans (snd (flatH c o o' e fl))
                 (≡→≈ (cong U (trans (cong (_==ℕ 0) hc) z)))))

  ----------------------------------------------------------------------
  -- Walking from object o to the last object.

  hsOf : List Nat → List Nat → List Hom
  hsOf pre rest = map (homAt Δ) (seq (suc (lengthN pre)) (lengthN rest))

  FlatSeg : Nat → List Nat → Set
  FlatSeg o rest = ∀ a b → (a , b) ∈ pairs (o ∷ rest) → img a ≡ img b

  record Jump (pre : List Nat) (o : Nat) (rest : List Nat) : Set where
    field
      pre'  : List Nat
      o₁ o₂ : Nat
      rest' : List Nat
      eqJ   : objL Δ ≡ pre' ++ o₁ ∷ o₂ ∷ rest'
      i₁    : img o₁ ≡ 0
      i₂    : img o₂ ≡ 1
      first0 : img o ≡ 0
      last1  : img (lastL (o ∷ rest)) ≡ 1
      others : ∀ a b → (a , b) ∈ pairs (o ∷ rest) → ((a ≡ o₁) × (b ≡ o₂) → ⊥) → img a ≡ img b
      hdJ≤  : Le (hd (homAt Δ (suc (lengthN pre')))) (dimK (hsOf pre rest))
      prodJ : prodL (map S (hsOf pre rest)) ≈
              (if dimK (hsOf pre rest) ==ℕ hd (homAt Δ (suc (lengthN pre'))) then S (homAt Δ (suc (lengthN pre'))) else [])

  FlatRes : List Nat → Nat → List Nat → Set
  FlatRes pre o rest = FlatSeg o rest × (prodL (map S (hsOf pre rest)) ≈ U (dimK (hsOf pre rest) ==ℕ 0))

  private
    tail-eq : ∀ pre o rest → map (homAt Δ) (seq (suc (suc (lengthN pre))) (lengthN rest)) ≡ hsOf (pre ++ o ∷ []) rest
    tail-eq pre o rest = cong (λ j → map (homAt Δ) (seq (suc j) (lengthN rest))) (sym (lengthN-snoc pre o))

    eqb : ∀ m n → (m ≡ n) ⊎ (m ≡ n → ⊥)
    eqb m n with m ==ℕ n in e
    ... | true  = inj₁ (==→≡ m n e)
    ... | false = inj₂ (λ q → bad (trans (sym (==-true m)) (subst (λ k → (m ==ℕ k) ≡ false) (sym q) e)))
      where
      bad : true ≡ false → ⊥
      bad ()

  walk : ∀ pre o rest → objL Δ ≡ pre ++ o ∷ rest →
         (img o ≡ img (lastL (o ∷ rest)) → FlatRes pre o rest) ×
         ((img o ≡ img (lastL (o ∷ rest)) → ⊥) → Jump pre o rest)
  walk pre o []          eq = (λ _ → (λ a b ()) , ≈-refl) , (λ ne → ⊥-elim (ne refl))
  walk pre o (o' ∷ rest) eq with walk (pre ++ o ∷ []) o' rest eq′ | eqb (img o) (img o')
    where
    eq′ : objL Δ ≡ (pre ++ o ∷ []) ++ o' ∷ rest
    eq′ = trans eq (sym (++-assocL pre (o ∷ []) (o' ∷ rest)))
  ... | (fl , jp) | inj₁ fp = flatPart , jumpPart
    where
    open H pre o o' rest eq
    tl = map (homAt Δ) (seq (suc (suc (lengthN pre))) (lengthN rest))
    te = tail-eq pre o rest
    flatPart : img o ≡ img (lastL (o' ∷ rest)) → FlatRes pre o (o' ∷ rest)
    flatPart e with fl (trans (sym fp) e)
    ... | fs , pr = fsg , pr′
      where
      fsg : FlatSeg o (o' ∷ rest)
      fsg a b hd∈     = fp
      fsg a b (tl∈ m) = fs a b m
      pr′ : prod (S h) (prodL (map S tl)) ≈ U ((hd h + dimK tl) ==ℕ 0)
      pr′ = ≈-trans (prod-congˡ (prodL (map S tl)) (S-flat fp))
            (≈-trans (prod-congʳ (U (hd h ==ℕ 0)) (subst (λ L → prodL (map S L) ≈ U (dimK L ==ℕ 0)) (sym te) pr))
                     (prod-U (hd h) (dimK tl)))
    jumpPart : (img o ≡ img (lastL (o' ∷ rest)) → ⊥) → Jump pre o (o' ∷ rest)
    jumpPart ne with jp (λ q → ne (trans fp q))
    ... | J = record
      { pre' = Jump.pre' J ; o₁ = Jump.o₁ J ; o₂ = Jump.o₂ J ; rest' = Jump.rest' J ; eqJ = Jump.eqJ J
      ; i₁ = Jump.i₁ J ; i₂ = Jump.i₂ J ; first0 = trans fp (Jump.first0 J) ; last1 = Jump.last1 J
      ; others = oth ; hdJ≤ = le ; prodJ = pj }
      where
      HJ = homAt Δ (suc (lengthN (Jump.pre' J)))
      oth : ∀ a b → (a , b) ∈ pairs (o ∷ o' ∷ rest) → ((a ≡ Jump.o₁ J) × (b ≡ Jump.o₂ J) → ⊥) → img a ≡ img b
      oth a b hd∈     _ = fp
      oth a b (tl∈ m) n = Jump.others J a b m n
      le0 : Le (hd HJ) (dimK tl)
      le0 = subst (λ L → Le (hd HJ) (dimK L)) (sym te) (Jump.hdJ≤ J)
      le : Le (hd HJ) (hd h + dimK tl)
      le = hd h + fst le0 , trans (+-comm (hd HJ) (hd h + fst le0))
             (trans (+-assoc (hd h) (fst le0) (hd HJ)) (cong (hd h +_) (trans (+-comm (fst le0) (hd HJ)) (snd le0))))
      pj : prod (S h) (prodL (map S tl)) ≈ (if (hd h + dimK tl) ==ℕ hd HJ then S HJ else [])
      pj = ≈-trans (prod-congˡ (prodL (map S tl)) (S-flat fp))
           (≈-trans (prod-congʳ (U (hd h ==ℕ 0)) (subst (λ L → prodL (map S L) ≈ (if dimK L ==ℕ hd HJ then S HJ else [])) (sym te) (Jump.prodJ J)))
                    (prod-U-sel (S HJ) (hd h) (dimK tl) (hd HJ) le0))
  ... | (fl , jp) | inj₂ nfp = flatPart , jumpPart
    where
    open H pre o o' rest eq
    tl = map (homAt Δ) (seq (suc (suc (lengthN pre))) (lengthN rest))
    te = tail-eq pre o rest
    pj = pair-jump nfp
    -- The rest, from o', is flat.
    restFlat : img o' ≡ img (lastL (o' ∷ rest))
    restFlat with eqb (img o') (img (lastL (o' ∷ rest)))
    ... | inj₁ q = q
    ... | inj₂ q = ⊥-elim (1≢0 (trans (sym (snd pj)) (Jump.first0 (jp q))))
    flatPart : img o ≡ img (lastL (o' ∷ rest)) → FlatRes pre o (o' ∷ rest)
    flatPart e = ⊥-elim (1≢0 (trans (sym (snd pj)) (trans restFlat (trans (sym e) (fst pj)))))
    jumpPart : (img o ≡ img (lastL (o' ∷ rest)) → ⊥) → Jump pre o (o' ∷ rest)
    jumpPart _ with fl restFlat
    ... | fs , pr = record
      { pre' = pre ; o₁ = o ; o₂ = o' ; rest' = rest ; eqJ = eq
      ; i₁ = fst pj ; i₂ = snd pj ; first0 = fst pj ; last1 = trans (sym restFlat) (snd pj)
      ; others = oth ; hdJ≤ = dimK tl , refl ; prodJ = pr′ }
      where
      oth : ∀ a b → (a , b) ∈ pairs (o ∷ o' ∷ rest) → ((a ≡ o) × (b ≡ o') → ⊥) → img a ≡ img b
      oth a b hd∈     n = ⊥-elim (n (refl , refl))
      oth a b (tl∈ m) n = fs a b m
      pr′ : prod (S h) (prodL (map S tl)) ≈ (if (hd h + dimK tl) ==ℕ hd h then S h else [])
      pr′ = ≈-trans (prod-congʳ (S h) (subst (λ L → prodL (map S L) ≈ U (dimK L ==ℕ 0)) (sym te) pr))
                    (prod-sel-U (S h) (hd h) (dimK tl))

  ----------------------------------------------------------------------
  -- The CaTT side: the composite of Δ, cell by cell.

  Fs : Tuple → Bag
  Fs (v ∷ []) = F v
  Fs _        = []

  sumN : (Nat → Bag) → List Nat → Bag
  sumN f []       = []
  sumN f (v ∷ vs) = f v ++ sumN f vs

  private
    sumN-++ : ∀ f xs ys → sumN f (xs ++ ys) ≡ sumN f xs ++ sumN f ys
    sumN-++ f []       ys = refl
    sumN-++ f (x ∷ xs) ys = trans (cong (f x ++_) (sumN-++ f xs ys)) (sym (++-assocL (f x) _ _))

    sumN-down : ∀ f n → sumN f (downFrom n) ≈ sumN f (rng n)
    sumN-down f zero    = ≈-refl
    sumN-down f (suc n) =
      ≈-trans (++-cong (≈-refl {f n}) (sumN-down f n))
      (≈-trans (++-comm (f n) (sumN f (rng n)))
      (≡→≈ (trans (cong (sumN f (rng n) ++_) (sym (++-[]L (f n)))) (sym (sumN-++ f (rng n) (n ∷ []))))))

    sumN-ext : ∀ f g n → (∀ v → T (v <ℕ n) → f v ≈ g v) → sumN f (rng n) ≈ sumN g (rng n)
    sumN-ext f g zero    h = ≈-refl
    sumN-ext f g (suc n) h =
      ≈-trans (≡→≈ (sumN-++ f (rng n) (n ∷ [])))
      (≈-trans (++-cong (sumN-ext f g n (λ v lt → h v (<-suc v n lt))) (++-cong (h n (n<suc n)) ≈-refl))
               (≡→≈ (sym (sumN-++ g (rng n) (n ∷ [])))))

    sumN-nil : ∀ xs → sumN (λ _ → []) xs ≡ []
    sumN-nil []       = refl
    sumN-nil (x ∷ xs) = sumN-nil xs

  Wb-sum : ∀ d xs → cm Fs (selW Δ d xs) ≡ sumN (λ v → if dimv Δ v ==ℕ d then F v else []) xs
  Wb-sum d []       = refl
  Wb-sum d (v ∷ xs) with dimv Δ v ==ℕ d
  ... | true  = cong (F v ++_) (Wb-sum d xs)
  ... | false = Wb-sum d xs

  Tb-sum : ∀ (p : Nat → Bool) xs →
           cm (Ftuple R) (map sing (filter p xs)) ≈ sumN (λ v → if p v then nth v R else []) xs
  Tb-sum p []       = ≈-refl
  Tb-sum p (v ∷ xs) with p v
  ... | true  = ++-cong (Fsing v) (Tb-sum p xs)
  ... | false = Tb-sum p xs

  -- The composite, as a sum over all variables below len Δ.
  CT : Nat → Bag
  CT d = cm Fs (Wb Δ d)

  CT-sum : ∀ d → CT d ≈ sumN (λ v → if dimv Δ v ==ℕ d then F v else []) (rng (len Δ))
  CT-sum d = ≈-trans (≡→≈ (Wb-sum d (downFrom (len Δ)))) (sumN-down _ (len Δ))

  ----------------------------------------------------------------------
  -- The variables of Δ.

  invΔ : PsInv Δ
  invΔ = psInv P

  data View (v : Nat) : Set where
    obj  : lookup Δ v ≡ just ⋆ → View v
    cell : ∀ B s t a b → lookup Δ v ≡ just (arr B s t) → endsV (arr B s t) ≡ just (a , b) →
           (a , b) ∈ pairs (objL Δ) → View v

  private
    lookup-just : ∀ Γ v → T (v <ℕ len Γ) → Σ Ty λ C → lookup Γ v ≡ just C
    lookup-just (Γ ▸ A) v lt with v ==ℕ len Γ in e
    ... | true  = A , refl
    ... | false = lookup-just Γ v (lt-ne v (len Γ) lt e)
      where
      lt-ne : ∀ v n → T (v <ℕ suc n) → (v ==ℕ n) ≡ false → T (v <ℕ n)
      lt-ne zero    zero    _ ()
      lt-ne zero    (suc n) _ _ = tt
      lt-ne (suc v) zero    () _
      lt-ne (suc v) (suc n) p q = lt-ne v n p q

  view : ∀ v → T (v <ℕ len Δ) → View v
  view v lt with lookup-just Δ v lt
  ... | ⋆ , lv         = obj lv
  ... | arr B s t , lv with ends-just invΔ v B s t lv
  ...   | (a , b) , ev = cell B s t a b lv ev (hom-ends P v (trans (cong endsL lv) ev))

  private
    T-true : ∀ b → T b → b ≡ true
    T-true true _ = refl

    if-nil : ∀ (b : Bool) (X : Bag) → X ≈ [] → (if b then X else []) ≈ []
    if-nil true  X p = p
    if-nil false X p = ≈-refl

    pair-dec : ∀ a b a' b' → ((a ≡ a') × (b ≡ b')) ⊎ ((a ≡ a') × (b ≡ b') → ⊥)
    pair-dec a b a' b' with a ==ℕ a' in e1 | b ==ℕ b' in e2
    ... | true  | true  = inj₁ (==→≡ a a' e1 , ==→≡ b b' e2)
    ... | false | _     = inj₂ (λ { (refl , _) → bad (trans (sym (==-true a)) e1) })
      where
      bad : true ≡ false → ⊥
      bad ()
    ... | true  | false = inj₂ (λ { (_ , refl) → bad (trans (sym (==-true b)) e2) })
      where
      bad : true ≡ false → ⊥
      bad ()

    homM-no : ∀ a b o₁ o₂ → ((a ≡ o₁) × (b ≡ o₂) → ⊥) → homM (o₁ , o₂) (just (a , b)) ≡ false
    homM-no a b o₁ o₂ ne with a ==ℕ o₁ in e1 | b ==ℕ o₂ in e2
    ... | true  | true  = ⊥-elim (ne (==→≡ a o₁ e1 , ==→≡ b o₂ e2))
    ... | true  | false = refl
    ... | false | _     = refl

    homM-yes : ∀ a b → homM (a , b) (just (a , b)) ≡ true
    homM-yes a b rewrite ==-true a | ==-true b = refl

  ----------------------------------------------------------------------
  -- Flat: every variable of positive dimension sits in a flat hom.

  CT-flat : ∀ o₀ rest → objL Δ ≡ o₀ ∷ rest → FlatSeg o₀ rest → ∀ d → CT (suc d) ≈ []
  CT-flat o₀ rest eo fs d =
    ≈-trans (CT-sum (suc d))
    (≈-trans (sumN-ext _ (λ _ → []) (len Δ) pt) (≡→≈ (sumN-nil (rng (len Δ)))))
    where
    pt : ∀ v → T (v <ℕ len Δ) → (if dimv Δ v ==ℕ suc d then F v else []) ≈ []
    pt v lt with view v lt
    ... | obj lv rewrite lv = ≈-refl
    ... | cell B s t a b lv ev mem =
      if-nil _ (F v) (fst (flatH v a b (trans (cong endsL lv) ev) (fs a b (subst (λ xs → (a , b) ∈ pairs xs) eo mem))))

  ----------------------------------------------------------------------
  -- Numbers.

  private
    ≤→Le : ∀ {a b} → a ≤ b → Le a b
    ≤→Le {zero}  {b} z≤n = b , refl
    ≤→Le (s≤s p) with ≤→Le p
    ... | x , e = x , cong suc e

    Le→≤ : ∀ a x → a ≤ a + x
    Le→≤ zero    x = z≤n
    Le→≤ (suc a) x = s≤s (Le→≤ a x)

    ≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
    ≤-antisym z≤n     z≤n     = refl
    ≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

    lt-false : ∀ m k x → T (m <ℕ suc k) → (m ==ℕ suc (k + x)) ≡ false
    lt-false zero    k       x _ = refl
    lt-false (suc m) zero    x ()
    lt-false (suc m) (suc k) x p = lt-false m k x p

    dim-le-ctx : ∀ Γ v {C} → lookup Γ v ≡ just C → dim C ≤ dimCtx Γ
    dim-le-ctx (Γ ▸ A) v e with v ==ℕ len Γ
    dim-le-ctx (Γ ▸ A) v refl | true  = max-l (dim A) (dimCtx Γ)
    ... | false = ≤-trans (dim-le-ctx Γ v e) (max-r (dim A) (dimCtx Γ))

    k<len : ∀ pre o₁ o₂ rest → T (suc (lengthN pre) <ℕ lengthN (pre ++ o₁ ∷ o₂ ∷ rest))
    k<len []        o₁ o₂ rest = tt
    k<len (x ∷ pre) o₁ o₂ rest = k<len pre o₁ o₂ rest

    All-at : ∀ {Pp : Tuple → Set} L {c} → All Pp (map sing L) → Any (c ≡_) L → Pp (sing c)
    All-at (x ∷ L) (p , _)  (here refl) = p
    All-at (x ∷ L) (_ , pr) (there m)   = All-at L pr m

    pf : ∀ {Γ} → Γ ⊢ps → PsFacts Γ
    pf (ps d) = fst (ps-facts d)

    pfOf : PsFacts Δ
    pfOf = pf P

  ----------------------------------------------------------------------
  -- The homs of Δ, as walked.

  homs-eq : ∀ o₀ rest → objL Δ ≡ o₀ ∷ rest → homs Δ ≡ hsOf [] rest
  homs-eq o₀ rest eo =
    cong (λ L → map (homAt Δ) (drop1 (upto (lengthN L)))) (trans (objs-objL Δ) eo) ∙ cong (map (homAt Δ)) (drop1-upto (lengthN rest))
    where
    _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    _∙_ = trans

  cm-prodL : ∀ hs → cm (Ftuple R) (prodL (map topsH hs)) ≈ prodL (map S hs)
  cm-prodL []       = ≡→≈ (++-[]L (Ftuple R []))
  cm-prodL (h ∷ hs) = ≈-trans (cmF-prod R (topsH h) (prodL (map topsH hs))) (prod-congʳ (S h) (cm-prodL hs))

  L-top : applyF R (topT (homs Δ)) ≈ prodL (map S (homs Δ))
  L-top = ≈-trans (≡→≈ (applyF-cm R (topT (homs Δ))))
          (≈-trans (cm-cong (Ftuple R) _ _ (topT-prod (objs Δ) (homs Δ) (homCells P) true)) (cm-prodL (homs Δ)))

  ----------------------------------------------------------------------
  -- One jumping hom.

  module JumpSide (o₀ : Nat) (rest : List Nat) (eo : objL Δ ≡ o₀ ∷ rest) (J : Jump [] o₀ rest) where
    open Jump J
    HJ : Hom
    HJ = homAt Δ (suc (lengthN pre'))
    module OH = OneHom P pre' o₁ o₂ rest' eqJ
    module HH = H pre' o₁ o₂ rest' eqJ

    others′ : ∀ a b → (a , b) ∈ pairs (objL Δ) → ((a ≡ o₁) × (b ≡ o₂) → ⊥) → img a ≡ img b
    others′ a b m = others a b (subst (λ xs → (a , b) ∈ pairs xs) eo m)

    jne : img o₁ ≡ img o₂ → ⊥
    jne q = 1≢0 (trans (sym i₂) (trans (sym q) i₁))

    nohit-of : ∀ v B s t → lookup Δ v ≡ just (arr B s t) → endsV (arr B s t) ≡ just (o₁ , o₂) →
               hd HJ ≡ dim B → any (hitB Δ true v) (rng (len Δ)) ≡ false
    nohit-of v B s t lv ev hb =
      trans (sym (OH.eq-hit (hd HJ) true v (arr B s t) 0 0 0 0 lv
                   (trans (OneHom.CellInfo.hom-eq ci) (cong just m≡k)) hb))
            (OH.no-hit (hd HJ) true (el v 0 0 0 0) (n<suc (hd HJ)))
      where
      ci = OH.cell-info v B s t lv
      m≡k : OneHom.CellInfo.m ci ≡ OH.k
      m≡k = ==→≡ _ _ (trans (OH.hom-sel v (arr B s t) ci) (trans (cong (homM (o₁ , o₂)) ev) (homM-yes o₁ o₂)))

    -- Above the top of the jumping hom, the composite has nothing.
    CT-above : ∀ x → CT (suc (suc (hd HJ + x))) ≈ []
    CT-above x =
      ≈-trans (CT-sum _)
      (≈-trans (sumN-ext _ (λ _ → []) (len Δ) pt) (≡→≈ (sumN-nil (rng (len Δ)))))
      where
      pt : ∀ v → T (v <ℕ len Δ) → (if dimv Δ v ==ℕ suc (suc (hd HJ + x)) then F v else []) ≈ []
      pt v lt with view v lt
      ... | obj lv rewrite lv = ≈-refl
      ... | cell B s t a b lv ev mem with pair-dec a b o₁ o₂
      ...   | inj₁ (refl , refl) rewrite lv | lt-false (dim B) (hd HJ) x (OH.v-bound v (arr B s t) lv ev) = ≈-refl
      ...   | inj₂ ne = if-nil _ (F v) (fst (flatH v a b (trans (cong endsL lv) ev) (others′ a b mem ne)))

    -- At the top of the jumping hom, the composite is the image of its top cells.
    CT-at : CT (suc (hd HJ)) ≈ S HJ
    CT-at =
      ≈-trans (CT-sum _)
      (≈-trans (sumN-ext _ _ (len Δ) pt)
      (≈-sym (≈-trans (cm-cong (Ftuple R) _ _ (OH.Ph-Tb true (hd HJ)))
                      (Tb-sum (selH Δ (o₁ , o₂) true (hd HJ)) (rng (len Δ))))))
      where
      pt : ∀ v → T (v <ℕ len Δ) →
           (if dimv Δ v ==ℕ suc (hd HJ) then F v else []) ≈ (if selH Δ (o₁ , o₂) true (hd HJ) v then nth v R else [])
      pt v lt with view v lt
      ... | obj lv rewrite lv = ≈-refl
      ... | cell B s t a b lv ev mem with pair-dec a b o₁ o₂
      ...   | inj₂ ne rewrite lv | ev | homM-no a b o₁ o₂ ne =
        if-nil _ (F v) (fst (flatH v a b (trans (cong endsL lv) ev) (others′ a b mem ne)))
      ...   | inj₁ (refl , refl) with dim B ==ℕ hd HJ in e
      ...     | false rewrite lv | ev | homM-yes a b | e = ≈-refl
      ...     | true  rewrite nohit-of v B s t lv ev (sym (==→≡ _ _ e)) | lv | ev | homM-yes a b | e =
        ≈-sym (snd (snd (jumpH v a b (trans (cong endsL lv) ev) jne)))

    -- The ambient dimension is at least one more than the jumping hom's.
    hd< : suc (hd HJ) ≤ dimCtx Δ
    hd< with CD.Cells.top-cell Δ pfOf (CD.Cells.homAt-in Δ pfOf (suc (lengthN pre')) tt
               (subst (λ L → T (suc (lengthN pre') <ℕ lengthN L)) (sym (trans (objs-objL Δ) eqJ)) (k<len pre' o₁ o₂ rest')))
    ... | c , mc with All-at (piece HJ (hd HJ) true) (HH.info true (hd HJ)) mc
    ...   | c' , refl , ec , hc with endsL-inv (lookup Δ c') ec
    ...     | ⋆ , lc , ()
    ...     | arr B s t , lc , _ = subst (λ k → suc k ≤ dimCtx Δ) hc′ (dim-le-ctx Δ c' lc)
      where
      hc′ : dim B ≡ hd HJ
      hc′ = trans (cong (λ m → hdimTy m) (sym lc)) hc

  ----------------------------------------------------------------------
  -- The coh case.

  cohTop′ : Ty → Bag
  cohTop′ A = if suc (dim A) ==ℕ dimCtx Δ then CT (dimCtx Δ) else []

  cohAgree : ∀ o₀ rest → objL Δ ≡ o₀ ∷ rest → ∀ (A : Ty) (cc : Bool) →
             (cc ≡ true → suc (dimK (homs Δ)) ≤ dim A) → (cc ≡ false → dim A ≡ dimK (homs Δ)) →
             (img o₀ ≡ img (lastL (o₀ ∷ rest)) → cohTop′ A ≈ []) ×
             ((img o₀ ≡ img (lastL (o₀ ∷ rest)) → ⊥) → applyF R (if cc then [] else topT (homs Δ)) ≈ cohTop′ A)
  cohAgree o₀ rest eo A cc hc ho = flatCase , jumpCase
    where
    N = dimK (homs Δ)
    flatCase : img o₀ ≡ img (lastL (o₀ ∷ rest)) → cohTop′ A ≈ []
    flatCase fl with suc (dim A) ==ℕ dimCtx Δ in e
    ... | false = ≈-refl
    ... | true  = subst (λ d → CT d ≈ []) (==→≡ _ _ e) (CT-flat o₀ rest eo (fst (fst (walk [] o₀ rest eo) fl)) (dim A))
    jumpCase : (img o₀ ≡ img (lastL (o₀ ∷ rest)) → ⊥) → applyF R (if cc then [] else topT (homs Δ)) ≈ cohTop′ A
    jumpCase ne = go cc refl
      where
      J = snd (walk [] o₀ rest eo) ne
      open JumpSide o₀ rest eo J
      hs≡ = homs-eq o₀ rest eo
      hdLe : Le (hd HJ) N
      hdLe = subst (λ L → Le (hd HJ) (dimK L)) (sym hs≡) (Jump.hdJ≤ J)
      abv : ∀ k → Le (suc (suc (hd HJ))) k → CT k ≈ []
      abv k (x , refl) = CT-above x
      go : ∀ b → cc ≡ b → applyF R (if cc then [] else topT (homs Δ)) ≈ cohTop′ A
      go true  refl with suc (dim A) ==ℕ dimCtx Δ in e
      ... | false = ≈-refl
      ... | true  = ≈-sym (subst (λ d → CT d ≈ []) (==→≡ _ _ e) (abv (suc (dim A)) le))
        where
        le : Le (suc (suc (hd HJ))) (suc (dim A))
        le = ≤→Le (s≤s (≤-trans (s≤s (subst (hd HJ ≤_) (snd hdLe) (Le→≤ (hd HJ) (fst hdLe)))) (hc refl)))
      go false refl with N ==ℕ hd HJ in e2
      ... | true = ≈-trans L-top (≈-trans (subst (λ L → prodL (map S L) ≈ (if dimK L ==ℕ hd HJ then S HJ else [])) (sym hs≡) (Jump.prodJ J))
                   (≈-trans (≡→≈ (cong (λ b → if b then S HJ else []) e2)) (≈-sym rhs)))
        where
        N≡ : N ≡ hd HJ
        N≡ = ==→≡ _ _ e2
        d≡ : dimCtx Δ ≡ suc (hd HJ)
        d≡ = ≤-antisym (subst (λ k → dimCtx Δ ≤ suc k) N≡ (CD.Cells.ctx-dim Δ pfOf)) hd<
        r2 : (if suc (dim A) ==ℕ suc (hd HJ) then CT (suc (hd HJ)) else []) ≈ S HJ
        r2 = subst (λ k → (if k ==ℕ hd HJ then CT (suc (hd HJ)) else []) ≈ S HJ) (sym (trans (ho refl) N≡))
               (subst (λ b → (if b then CT (suc (hd HJ)) else []) ≈ S HJ) (sym (==-true (hd HJ))) CT-at)
        rhs : cohTop′ A ≈ S HJ
        rhs = subst (λ d → (if suc (dim A) ==ℕ d then CT d else []) ≈ S HJ) (sym d≡) r2
      ... | false = ≈-trans L-top (≈-trans (subst (λ L → prodL (map S L) ≈ (if dimK L ==ℕ hd HJ then S HJ else [])) (sym hs≡) (Jump.prodJ J))
                    (≈-trans (≡→≈ (cong (λ b → if b then S HJ else []) e2)) (≈-sym rhs)))
        where
        rhs : cohTop′ A ≈ []
        rhs with suc (dim A) ==ℕ dimCtx Δ in e3
        ... | false = ≈-refl
        ... | true = subst (λ d → CT d ≈ []) (==→≡ _ _ e3) (abv (suc (dim A)) le)
          where
          nz : Σ Nat λ x → N ≡ suc (hd HJ + x)
          nz with hdLe
          ... | zero  , q = ⊥-elim (bad (subst (λ k → (k ==ℕ hd HJ) ≡ false) (trans (sym q) (+-zero (hd HJ))) e2))
            where
            bad : (hd HJ ==ℕ hd HJ) ≡ false → ⊥
            bad p = subst (λ b → b ≡ false → ⊥) (sym (==-true (hd HJ))) (λ ()) p
          ... | suc x , q = x , trans (sym q) (+-suc (hd HJ) x)
          le : Le (suc (suc (hd HJ))) (suc (dim A))
          le = fst nz , cong suc (trans (sym (snd nz)) (sym (ho refl)))
