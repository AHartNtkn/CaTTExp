------------------------------------------------------------------------
-- Face and collapse maps of globes (S5 of the 𝔖̂ instance).
--
-- A map sending each cell to one cell or to 0 (`funMap`) is a map of
-- complexes when it preserves degree, is defined on 0-cells, and
-- commutes with the (single-cell) boundaries; a cell sent to 0 must
-- have its two boundaries sent to the same place. The faces
-- δ^± : λDⁿ → λDⁿ⁺¹, the collapse σ : λDⁿ⁺¹ → λDⁿ and the isomorphism
-- [] ≅ λD⁰ are of this form, and σ ∘ δ^± = 1 (`σδ`).
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.GlobeMaps (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC; globe)
open import CaTTExp.Gray.Biclosed.Steiner.Globe
open import CaTTExp.Gray.Biclosed.Steiner.Maps nmFB

------------------------------------------------------------------------
-- Codes whose boundaries are single cells.

record SVB (K : Code) : Set where
  field
    bK    : Bool → El K → Maybe (El K)
    bK-ok : ∀ β x y → bd K β x y ≡ ind (enumEl K) (bK β x) y
open SVB

svb-[] : SVB []
svb-[] = record { bK = λ _ _ → nothing ; bK-ok = λ _ _ _ → refl }

G : Nat → Code
G n = globe n ∷ []

wrap : ∀ {n} → Maybe (GCell n) → Maybe (El (G n))
wrap = mapM (_, tt)

private
  ind-wrap : ∀ {n} (m : Maybe (GCell n)) (j : GCell n) → ind (enumG n) m j ≡ ind (enumEl (G n)) (wrap m) (j , tt)
  ind-wrap nothing  j = refl
  ind-wrap {n} (just c) j = sym (trans (δ× (enumG n) enum⊤ c tt j tt) (*-one (δ (enumG n) c j)))

svb-G : ∀ n → SVB (G n)
svb-G n = record { bK = λ β x → wrap (gb β (fst x)) ; bK-ok = ok }
  where
    ok : ∀ β x y → bd (G n) β x y ≡ ind (enumEl (G n)) (wrap (gb β (fst x))) y
    ok β (i , tt) (j , tt) =
      trans (cong₂ _+_ (*-one (gbd β i j)) (*-zero (δ (enumG n) i j)))
      (trans (+-zero (gbd β i j)) (ind-wrap (gb β i) j))

------------------------------------------------------------------------
-- Maps given by a partial function on cells.

caseM : ∀ {A : Set} → Maybe A → (A → Nat) → Nat
caseM nothing  f = 0
caseM (just a) f = f a

Σ-indM : ∀ {A : Set} (E : Enum A) (m : Maybe A) (f : A → Nat) → Σl (els E) (λ l → ind E m l * f l) ≡ caseM m f
Σ-indM E nothing  f = Σ-0 (els E)
Σ-indM E (just a) f = Σ-δ E a f

-- the indicator of a bind
ind-bind : ∀ {A B : Set} (EB : Enum B) (m : Maybe A) (φ : A → Maybe B) y → caseM m (λ a → ind EB (φ a) y) ≡ ind EB (m >>= φ) y
ind-bind EB nothing  φ y = refl
ind-bind EB (just a) φ y = refl

module _ {K L : Code} (sK : SVB K) (sL : SVB L) (φ : El K → Maybe (El L)) where

  ChainAt : El K → Set
  ChainAt x = ((φ x >>= bK sL true) ≡ (bK sK true x >>= φ) × (φ x >>= bK sL false) ≡ (bK sK false x >>= φ))
            ⊎ ((φ x ≡ nothing) × (bK sK true x >>= φ) ≡ (bK sK false x >>= φ))

  funMap : (∀ x z → φ x ≡ just z → deg L z ≡ deg K x) →
           (∀ x → deg K x ≡ 0 → Σ (El L) (λ z → φ x ≡ just z)) →
           (∀ x → ChainAt x) → Map K L
  funMap hd ha hc = record { mat = M ; mdeg = md ; maug = ma ; mchain = mc }
    where
      M : Mat K L
      M x = ind (enumEl L) (φ x)

      δcases : ∀ z y → δ (enumEl L) z y ≡ 0 ⊎ z ≡ y
      δcases z y = go (eqb (enumEl L) z y) refl
        where go : ∀ b → eqb (enumEl L) z y ≡ b → δ (enumEl L) z y ≡ 0 ⊎ z ≡ y
              go true  e = inj₂ (eqb-sound (enumEl L) (subst T (sym e) tt))
              go false e = inj₁ (cong (λ b → if b then 1 else 0) e)

      md : ∀ x y → M x y ≡ 0 ⊎ deg L y ≡ deg K x
      md x y with φ x | hd x
      ... | nothing | _ = inj₁ refl
      ... | just z  | h with δcases z y
      ...   | inj₁ e    = inj₁ e
      ...   | inj₂ refl = inj₂ (h z refl)

      ma : ∀ x → deg K x ≡ 0 → Σl (els′ L) (M x) ≡ 1
      ma x d with ha x d
      ... | z , e rewrite e = count (enumEl L) z

      -- (M · ∂L β) x n and (∂K β · M) x n as indicators
      Mb : ∀ β x n → (M · ∂ L β) x n ≡ ind (enumEl L) (φ x >>= bK sL β) n
      Mb β x n = trans (Σ-cong (els′ L) (λ l → cong (ind (enumEl L) (φ x) l *_) (bK-ok sL β l n)))
                 (trans (Σ-indM (enumEl L) (φ x) (λ l → ind (enumEl L) (bK sL β l) n))
                        (ind-bind (enumEl L) (φ x) (bK sL β) n))

      bM : ∀ β x n → (∂ K β · M) x n ≡ ind (enumEl L) (bK sK β x >>= φ) n
      bM β x n = trans (Σ-cong (els′ K) (λ l → cong (_* ind (enumEl L) (φ l) n) (bK-ok sK β x l)))
                 (trans (Σ-indM (enumEl K) (bK sK β x) (λ l → ind (enumEl L) (φ l) n))
                        (ind-bind (enumEl L) (bK sK β x) φ n))

      mc : ((M · ∂ L true) ⊕ (∂ K false · M)) ≐ ((M · ∂ L false) ⊕ (∂ K true · M))
      mc x n = trans (cong₂ _+_ (Mb true x n) (bM false x n))
               (trans (go (hc x)) (sym (cong₂ _+_ (Mb false x n) (bM true x n))))
        where
          I = ind (enumEl L)
          go : ChainAt x → I (φ x >>= bK sL true) n + I (bK sK false x >>= φ) n
                         ≡ I (φ x >>= bK sL false) n + I (bK sK true x >>= φ) n
          go (inj₁ (e₁ , e₂)) rewrite e₁ | e₂ = +-comm (I (bK sK true x >>= φ) n) (I (bK sK false x >>= φ) n)
          go (inj₂ (e₀ , e)) rewrite e₀ = cong (λ m → I m n) (sym e)

-- composites of functional maps
∘-ind : ∀ {K L M} (f : Map K L) (g : Map L M) (φ : El K → Maybe (El L)) (ψ : El L → Maybe (El M)) →
        (∀ x y → mat f x y ≡ ind (enumEl L) (φ x) y) → (∀ y z → mat g y z ≡ ind (enumEl M) (ψ y) z) →
        ∀ x z → mat (g ∘M f) x z ≡ ind (enumEl M) (φ x >>= ψ) z
∘-ind {K} {L} {M} f g φ ψ hf hg x z =
  trans (Σ-cong (els′ L) (λ y → cong₂ _*_ (hf x y) (hg y z)))
  (trans (Σ-indM (enumEl L) (φ x) (λ y → ind (enumEl M) (ψ y) z)) (ind-bind (enumEl M) (φ x) ψ z))

funMap-id : ∀ {K} → (f : Map K K) → (∀ x z → mat f x z ≡ ind (enumEl K) (just x) z) → f ≈M idMap K
funMap-id f h = ≈m (λ x z → h x z)

funMap-≈ : ∀ {K L} (f g : Map K L) (m : El K → Maybe (El L)) →
           (∀ x z → mat f x z ≡ ind (enumEl L) (m x) z) → (∀ x z → mat g x z ≡ ind (enumEl L) (m x) z) → f ≈M g
funMap-≈ f g m hf hg = ≈m (λ x z → trans (hf x z) (sym (hg x z)))

------------------------------------------------------------------------
-- Maps between single globes, from a partial function on cells.

private
  wrap-bind : ∀ {n m} (a : Maybe (GCell n)) (f : GCell n → Maybe (GCell m)) →
              (wrap a >>= (λ x → wrap (f (fst x)))) ≡ wrap (a >>= f)
  wrap-bind nothing  f = refl
  wrap-bind (just c) f = refl

module _ {n m : Nat} (φ : GCell n → Maybe (GCell m)) where

  GChain : GCell n → Set
  GChain i = ((φ i >>= gb true) ≡ (gb true i >>= φ) × (φ i >>= gb false) ≡ (gb false i >>= φ))
           ⊎ ((φ i ≡ nothing) × (gb true i >>= φ) ≡ (gb false i >>= φ))

  gMap : (∀ i j → φ i ≡ just j → gdeg j ≡ gdeg i) → (∀ i → gdeg i ≡ 0 → Σ (GCell m) (λ j → φ i ≡ just j)) →
         (∀ i → GChain i) → Map (G n) (G m)
  gMap hd ha hc = funMap (svb-G n) (svb-G m) Φ hd′ ha′ hc′
    where
      Φ : El (G n) → Maybe (El (G m))
      Φ x = wrap (φ (fst x))
      hd′ : ∀ x z → Φ x ≡ just z → deg (G m) z ≡ deg (G n) x
      hd′ (i , tt) (j , tt) e with φ i | hd i
      hd′ (i , tt) (j , tt) refl | just .j | h = cong (_+ 0) (h j refl)
      ha′ : ∀ x → deg (G n) x ≡ 0 → Σ (El (G m)) (λ z → Φ x ≡ just z)
      ha′ (i , tt) d with ha i (trans (sym (+-zero (gdeg i))) d)
      ... | j , e = (j , tt) , cong wrap e
      hc′ : ∀ x → ChainAt (svb-G n) (svb-G m) Φ x
      hc′ (i , tt) with hc i
      ... | inj₁ (e₁ , e₂) =
        inj₁ (trans (wrap-bind (φ i) gb₁) (trans (cong wrap e₁) (sym (wrap-bind (gb true i) φ))) ,
              trans (wrap-bind (φ i) gb₀) (trans (cong wrap e₂) (sym (wrap-bind (gb false i) φ))))
        where gb₁ = gb true ; gb₀ = gb false
      ... | inj₂ (e₀ , e) =
        inj₂ (cong wrap e₀ , trans (wrap-bind (gb true i) φ) (trans (cong wrap e) (sym (wrap-bind (gb false i) φ))))

------------------------------------------------------------------------
-- Faces δ^α : λDⁿ → λDⁿ⁺¹.

dl : ∀ {n} → Bool → GCell n → GCell (suc n)
dl {n} α top = side α (fromℕ n)
dl α (src j) = src (inject₁ j)
dl α (tgt j) = tgt (inject₁ j)

private
  gdeg-side : ∀ {n} β (j : Fin n) → gdeg (side β j) ≡ toℕ j
  gdeg-side true  j = refl
  gdeg-side false j = refl

  dl-deg : ∀ {n} α (i : GCell n) → gdeg (dl α i) ≡ gdeg i
  dl-deg {n} α top = trans (gdeg-side α (fromℕ n)) (toℕ-fromℕ n)
  dl-deg α (src j) = toℕ-inject₁ j
  dl-deg α (tgt j) = toℕ-inject₁ j

  dl-side : ∀ {n} α β (j : Fin n) → dl α (side β j) ≡ side β (inject₁ j)
  dl-side α true  j = refl
  dl-side α false j = refl

  gb-side-fz : ∀ {n} β α → gb {suc n} β (side α fz) ≡ nothing
  gb-side-fz β true  = refl
  gb-side-fz β false = refl

  gb-side-fs : ∀ {n} β α (j : Fin n) → gb β (side α (fs j)) ≡ just (side β (inject₁ j))
  gb-side-fs β true  j = refl
  gb-side-fs β false j = refl

  gb-dl : ∀ {n} β α (i : GCell n) → gb β (dl α i) ≡ (gb β i >>= λ c → just (dl α c))
  gb-dl {zero}  β α top = gb-side-fz β α
  gb-dl {suc n} β α top = trans (gb-side-fs β α (fromℕ n)) (cong just (sym (dl-side α β (fromℕ n))))
  gb-dl β α (src fz)     = refl
  gb-dl β α (src (fs j)) = cong just (sym (dl-side α β (inject₁ j)))
  gb-dl β α (tgt fz)     = refl
  gb-dl β α (tgt (fs j)) = cong just (sym (dl-side α β (inject₁ j)))

δmap : ∀ α n → Map (G n) (G (suc n))
δmap α n = gMap (λ i → just (dl α i))
  (λ i j e → trans (cong gdeg (sym (just-inj e))) (dl-deg α i))
  (λ i _ → dl α i , refl)
  (λ i → inj₁ (gb-dl true α i , gb-dl false α i))
  where just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
        just-inj refl = refl

------------------------------------------------------------------------
-- Collapse σ : λDⁿ⁺¹ → λDⁿ.

lowS : ∀ {n} → (Fin n → GCell n) → Fin (suc n) → GCell n
lowS s j with lower j
... | nothing = top
... | just k  = s k

sl : ∀ {n} → GCell (suc n) → Maybe (GCell n)
sl top     = nothing
sl (src j) = just (lowS src j)
sl (tgt j) = just (lowS tgt j)

private
  lowS-max : ∀ {n} (s : Fin n → GCell n) → lowS s (fromℕ n) ≡ top
  lowS-max {n} s rewrite lower-max n = refl

  lowS-inj : ∀ {n} (s : Fin n → GCell n) (k : Fin n) → lowS s (inject₁ k) ≡ s k
  lowS-inj s k rewrite lower-inj k = refl

  sl-side : ∀ {n} β (j : Fin (suc n)) → sl (side β j) ≡ just (lowS (side β) j)
  sl-side true  j = refl
  sl-side false j = refl

  lowS-deg : ∀ {n} (s : Fin n → GCell n) → (∀ k → gdeg (s k) ≡ toℕ k) → ∀ j → gdeg (lowS s j) ≡ toℕ j
  lowS-deg {n} s hs j with lv j
  ... | isMax   rewrite lowS-max s = sym (toℕ-fromℕ n)
  ... | isInj k rewrite lowS-inj s k = trans (hs k) (sym (toℕ-inject₁ k))

  sl-deg : ∀ {n} (i : GCell (suc n)) j → sl i ≡ just j → gdeg j ≡ gdeg i
  sl-deg top     j ()
  sl-deg (src i) .(lowS src i) refl = lowS-deg src (λ _ → refl) i
  sl-deg (tgt i) .(lowS tgt i) refl = lowS-deg tgt (λ _ → refl) i

  sl-aug : ∀ {n} (i : GCell (suc n)) → gdeg i ≡ 0 → Σ (GCell n) (λ j → sl i ≡ just j)
  sl-aug top     ()
  sl-aug (src i) _ = _ , refl
  sl-aug (tgt i) _ = _ , refl

  -- the two faces of the top cell collapse to the top cell
  sl-top : ∀ {n} β → (gb β (top {suc n}) >>= sl) ≡ just top
  sl-top {n} β = trans (sl-side β (fromℕ n)) (cong just (lowS-max (side β)))

  -- off the top cell, σ commutes with boundaries
  maxcase : ∀ n β σ′ → gb β (lowS (side σ′) (fromℕ n)) ≡ (gb β (side σ′ (fromℕ n)) >>= sl)
  maxcase zero    β σ′ = trans (cong (gb β) (lowS-max (side σ′))) (sym (cong (_>>= sl) (gb-side-fz β σ′)))
  maxcase (suc n) β σ′ =
    trans (cong (gb β) (lowS-max (side σ′)))
          (sym (trans (cong (_>>= sl) (gb-side-fs β σ′ (fromℕ n)))
               (trans (sl-side β (inject₁ (fromℕ n))) (cong just (lowS-inj (side β) (fromℕ n))))))

  injcase : ∀ {n} β σ′ (k : Fin n) → gb β (side σ′ k) ≡ (gb β (side σ′ (inject₁ k)) >>= sl)
  injcase β σ′ fz = trans (gb-side-fz β σ′) (sym (cong (_>>= sl) (gb-side-fz β σ′)))
  injcase β σ′ (fs k′) =
    trans (gb-side-fs β σ′ k′)
          (sym (trans (cong (_>>= sl) (gb-side-fs β σ′ (inject₁ k′)))
               (trans (sl-side β (inject₁ (inject₁ k′))) (cong just (lowS-inj (side β) (inject₁ k′))))))

  sl-gb-s : ∀ {n} β σ′ (j : Fin (suc n)) → gb β (lowS (side σ′) j) ≡ (gb β (side σ′ j) >>= sl)
  sl-gb-s {n} β σ′ j with lv j
  ... | isMax   = maxcase n β σ′
  ... | isInj k = trans (cong (gb β) (lowS-inj (side σ′) k)) (injcase β σ′ k)

σmap : ∀ n → Map (G (suc n)) (G n)
σmap n = gMap sl sl-deg sl-aug ch
  where
    ch : ∀ i → GChain sl i
    ch top     = inj₂ (refl , trans (sl-top true) (sym (sl-top false)))
    ch (src j) = inj₁ (sl-gb-s true false j , sl-gb-s false false j)
    ch (tgt j) = inj₁ (sl-gb-s true true j , sl-gb-s false true j)

------------------------------------------------------------------------
-- The point: [] ≅ λD⁰, and the two points of λD¹.

iso0 : Map [] (G 0)
iso0 = funMap svb-[] (svb-G 0) (λ _ → just (top , tt))
  (λ { tt (top , tt) refl → refl })
  (λ _ _ → (top , tt) , refl)
  (λ _ → inj₁ (refl , refl))

d0 : Bool → Map [] (G 1)
d0 α = funMap svb-[] (svb-G 1) (λ _ → just (side α fz , tt))
  (λ { tt _ refl → cong (_+ 0) (gdeg-side α fz) })
  (λ _ _ → _ , refl)
  (λ _ → inj₁ (cong wrap (gb-side-fz true α) , cong wrap (gb-side-fz false α)))

------------------------------------------------------------------------
-- σ ∘ δ^α = 1.

private
  sl-dl : ∀ {n} α (i : GCell n) → sl (dl α i) ≡ just i
  sl-dl {n} α top = trans (sl-side α (fromℕ n)) (cong just (lowS-max (side α)))
  sl-dl α (src j) = cong just (lowS-inj src j)
  sl-dl α (tgt j) = cong just (lowS-inj tgt j)

σδ : ∀ α n → (σmap n ∘M δmap α n) ≈M idMap (G n)
σδ α n = ≈m λ { (i , tt) z → trans (∘-ind (δmap α n) (σmap n) (λ x → wrap (just (dl α (fst x)))) (λ x → wrap (sl (fst x)))
                                               (λ _ _ → refl) (λ _ _ → refl) (i , tt) z) (cong (λ m → ind (enumEl (G n)) (wrap m) z) (sl-dl α i)) }

σδ0 : ∀ α → (σmap 0 ∘M d0 α) ≈M iso0
σδ0 α = ≈m λ { tt z → trans (∘-ind (d0 α) (σmap 0) (λ _ → just (side α fz , tt)) (λ x → wrap (sl (fst x)))
                                        (λ _ _ → refl) (λ _ _ → refl) tt z) (cong (λ m → ind (enumEl (G 0)) (wrap m) z) (sl-side α fz)) }
