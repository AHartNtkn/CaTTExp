------------------------------------------------------------------------
-- A model of T that separates grid paths (ledger S3c, converse).
--
-- GridLink proves that grid equality gives equality of the raw
-- T-translations. This module proves the converse: if the
-- translations of two valid grid paths are equal under T's equations
-- without the support equations plus the switched laws of setting sw,
-- then the paths are equal in Grid. So on suspended grids V + S adds
-- no equation beyond the splits, and Grid is exactly the grid layer
-- of the raw syntax.
--
-- The model. A 2-cell is read as "is an identity" (a Bool). A 3-term
-- is read as its word of letters (a ↦ true, b ↦ false; whiskers
-- forgotten), or junk (nothing) when it contains a χ with two
-- non-identity arguments. A 4-term is read as a raw path, or junk:
--   * id4 ↦ the empty path;
--   * ι(F, G) ↦ empty if either side is the empty word; the block
--     crossing ⟨0, |G| - 1, |F| - 1⟩ if F is all a's and G all b's;
--     junk otherwise;
--   * r(A, b), t(a, B) ↦ empty if A (B) is the empty word or a (b)
--     is an identity, junk otherwise;
--   * X · Y ↦ concatenation, strict in junk;
--   * ctx p X q ↦ X shifted right by |p| (empty stays empty);
--   * 2-whiskering is forgotten. There are no 1-cells or 4-cells.
-- Paths are compared up to the untyped split relation of Grid.
--
-- Proved here:
--   sem3-≈   every equation of T in dimension 3 holds on the nose;
--   sem-≈    every equation of T in dimension 4 except the support
--            equations holds on the nose;
--   sem-law  each switched law holds up to one split step;
--   sem-tr   the translation of a running path is that path;
--   ≈U→≈     untyped split equivalence from a valid path stays among
--            valid paths, so it is Grid's typed equality;
--   Converse.converse
--            sw ⊢ tr start p ≈S tr start q (p, q valid) implies
--            sw ⊢ p ≈ q.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂)
open import CaTTExp.Join.Finite using (_∈L_; here; there; lengthL)
open import CaTTExp.Join.SwitchLaws using (Switches; IsTrue; tt′)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Arith
open import CaTTExp.Uniform.Grid
open import CaTTExp.Uniform.GridLink

module CaTTExp.Uniform.GridSep where

open Switches

------------------------------------------------------------------------
-- Small facts.

private
  T-∧ˡ : ∀ a b → T (a ∧ b) → T a
  T-∧ˡ true b _ = tt

  T-∧ʳ : ∀ a b → T (a ∧ b) → T b
  T-∧ʳ true b h = h

  fromIsTrue : ∀ {b} → IsTrue b → T b
  fromIsTrue tt′ = tt

------------------------------------------------------------------------
-- The model in dimensions 2 and 3.

isId : T2 → Bool
isId (gen2 _)   = false
isId id2        = true
isId (x ∘₂ y)   = isId x ∧ isId y
isId (w1L₂ () _)
isId (w1R₂ _ ())

-- Strict concatenation.
infixr 5 _⊛_
_⊛_ : ∀ {A : Set} → Maybe (List A) → Maybe (List A) → Maybe (List A)
just xs ⊛ just ys = just (xs ++ ys)
just _  ⊛ nothing = nothing
nothing ⊛ _       = nothing

⊛-idˡ : ∀ {A : Set} (m : Maybe (List A)) → just [] ⊛ m ≡ m
⊛-idˡ nothing  = refl
⊛-idˡ (just _) = refl

⊛-idʳ : ∀ {A : Set} (m : Maybe (List A)) → m ⊛ just [] ≡ m
⊛-idʳ nothing   = refl
⊛-idʳ (just xs) = cong just (++-[] xs)

⊛-nothingʳ : ∀ {A : Set} (m : Maybe (List A)) → m ⊛ nothing ≡ nothing
⊛-nothingʳ nothing  = refl
⊛-nothingʳ (just _) = refl

⊛-assoc : ∀ {A : Set} (a b c : Maybe (List A)) → (a ⊛ b) ⊛ c ≡ a ⊛ (b ⊛ c)
⊛-assoc nothing   b         c         = refl
⊛-assoc (just xs) nothing   c         = refl
⊛-assoc (just xs) (just ys) nothing   = refl
⊛-assoc (just xs) (just ys) (just zs) = cong just (++-assoc xs ys zs)

-- χ(a, b) is the empty word when an argument is an identity.
chiV : Bool → Maybe Word
chiV true  = just []
chiV false = nothing

⟦_⟧3 : T3 → Maybe Word
⟦ gen3 (aa _) ⟧3 = just (true ∷ [])
⟦ gen3 (bb _) ⟧3 = just (false ∷ [])
⟦ id3 _ ⟧3       = just []
⟦ χ a b ⟧3       = chiV (isId a ∨ isId b)
⟦ F ⨾ G ⟧3       = ⟦ F ⟧3 ⊛ ⟦ G ⟧3
⟦ wl _ F ⟧3      = ⟦ F ⟧3
⟦ wr F _ ⟧3      = ⟦ F ⟧3
⟦ w1L₃ () _ ⟧3
⟦ w1R₃ _ () ⟧3

private
  ∨-true : ∀ x → x ∨ true ≡ true
  ∨-true true  = refl
  ∨-true false = refl

  chi-∘ˡ : ∀ x y z → chiV ((x ∧ y) ∨ z) ≡ chiV (x ∨ z) ⊛ chiV (y ∨ z)
  chi-∘ˡ true  true  z     = refl
  chi-∘ˡ true  false true  = refl
  chi-∘ˡ true  false false = refl
  chi-∘ˡ false y     true  rewrite ∨-true y = refl
  chi-∘ˡ false true  false = refl
  chi-∘ˡ false false false = refl

  chi-∘ʳ : ∀ x y z → chiV (x ∨ (y ∧ z)) ≡ chiV (x ∨ z) ⊛ chiV (x ∨ y)
  chi-∘ʳ true  y     z     = refl
  chi-∘ʳ false true  true  = refl
  chi-∘ʳ false true  false = refl
  chi-∘ʳ false false true  = refl
  chi-∘ʳ false false false = refl


sem3-≈ : ∀ {F G} → F ≈3 G → ⟦ F ⟧3 ≡ ⟦ G ⟧3
sem3-≈ rfl3                = refl
sem3-≈ (sym3 d)            = sym (sem3-≈ d)
sem3-≈ (trans3 d e)        = trans (sem3-≈ d) (sem3-≈ e)
sem3-≈ (⨾-cong d e)        = cong₂ _⊛_ (sem3-≈ d) (sem3-≈ e)
sem3-≈ (wl-cong z d)       = sem3-≈ d
sem3-≈ (wr-cong z d)       = sem3-≈ d
sem3-≈ (w1L-cong () d)
sem3-≈ (w1R-cong () d)
sem3-≈ (⨾-assoc F G H)     = ⊛-assoc ⟦ F ⟧3 ⟦ G ⟧3 ⟦ H ⟧3
sem3-≈ (⨾-idˡ u F)         = ⊛-idˡ ⟦ F ⟧3
sem3-≈ (⨾-idʳ u F)         = ⊛-idʳ ⟦ F ⟧3
sem3-≈ (wl-⨾ z F G)        = refl
sem3-≈ (wr-⨾ z F G)        = refl
sem3-≈ (wl-id z u)         = refl
sem3-≈ (wr-id z u)         = refl
sem3-≈ (wl-wl z z′ F)      = refl
sem3-≈ (wr-wr z z′ F)      = refl
sem3-≈ (wl-wr z z′ F)      = refl
sem3-≈ (wl-id2 F)          = refl
sem3-≈ (wr-id2 F)          = refl
sem3-≈ (w1L-⨾ () F G)
sem3-≈ (w1R-⨾ () F G)
sem3-≈ (w1L-id () u)
sem3-≈ (w1R-id () u)
sem3-≈ (w1L-wl () z F)
sem3-≈ (w1L-wr () z F)
sem3-≈ (w1R-wl () z F)
sem3-≈ (w1R-wr () z F)
sem3-≈ (χ-∘ˡ a₁ a₂ b)      = chi-∘ˡ (isId a₁) (isId a₂) (isId b)
sem3-≈ (χ-∘ʳ a b₁ b₂)      = chi-∘ʳ (isId a) (isId b₁) (isId b₂)
sem3-≈ (χ-w1L () x y)
sem3-≈ (χ-w1M () x y)
sem3-≈ (χ-w1R () x y)
sem3-≈ (χ-idˡ b)           = refl
sem3-≈ (χ-idʳ a)           = cong chiV (∨-true (isId a))

------------------------------------------------------------------------
-- The model in dimension 4.

allT allF : Word → Bool
allT []          = true
allT (true ∷ w)  = allT w
allT (false ∷ w) = false
allF []          = true
allF (true ∷ w)  = false
allF (false ∷ w) = allF w

edgeIf : Bool → Nat → Nat → Maybe RawPath
edgeIf true  p q = just (⟨ 0 , p , q ⟩ ∷ [])
edgeIf false p q = nothing

ιV : Maybe Word → Maybe Word → Maybe RawPath
ιV (just [])       _                 = just []
ιV _               (just [])         = just []
ιV (just (x ∷ xs)) (just (y ∷ ys))   = edgeIf (allT (x ∷ xs) ∧ allF (y ∷ ys)) (lengthL ys) (lengthL xs)
ιV (just (x ∷ xs)) nothing           = nothing
ιV nothing         (just (y ∷ ys))   = nothing
ιV nothing         nothing           = nothing

-- r and t: empty when the 3-cell argument is the empty word or the
-- 2-cell argument an identity.
nilOr : Maybe Word → Bool → Maybe RawPath
nilOr m         true  = just []
nilOr (just []) false = just []
nilOr (just (_ ∷ _)) false = nothing
nilOr nothing   false = nothing

shiftE : Nat → Edge → Edge
shiftE k ⟨ i , p , q ⟩ = ⟨ k + i , p , q ⟩

shift : Nat → RawPath → RawPath
shift k = mapK (shiftE k)

ctxV : Maybe Word → Maybe RawPath → Maybe RawPath
ctxV _         (just [])       = just []
ctxV (just w)  (just (e ∷ es)) = just (shift (lengthL w) (e ∷ es))
ctxV nothing   (just (e ∷ es)) = nothing
ctxV _         nothing         = nothing

⟦_⟧4 : T4 → Maybe RawPath
⟦ gen4 () ⟧4
⟦ id4 _ ⟧4       = just []
⟦ ι F G ⟧4       = ιV ⟦ F ⟧3 ⟦ G ⟧3
⟦ r A b ⟧4       = nilOr ⟦ A ⟧3 (isId b)
⟦ t a B ⟧4       = nilOr ⟦ B ⟧3 (isId a)
⟦ X · Y ⟧4       = ⟦ X ⟧4 ⊛ ⟦ Y ⟧4
⟦ ctx p X q ⟧4   = ctxV ⟦ p ⟧3 ⟦ X ⟧4
⟦ wl4 _ X ⟧4     = ⟦ X ⟧4
⟦ wr4 X _ ⟧4     = ⟦ X ⟧4
⟦ w1L₄ () _ ⟧4
⟦ w1R₄ _ () ⟧4

------------------------------------------------------------------------
-- Value lemmas.

private
  shift-0 : ∀ es → shift 0 es ≡ es
  shift-0 []                   = refl
  shift-0 (⟨ i , p , q ⟩ ∷ es) = cong (⟨ i , p , q ⟩ ∷_) (shift-0 es)

  shift-shift : ∀ k k′ es → shift k (shift k′ es) ≡ shift (k + k′) es
  shift-shift k k′ []                   = refl
  shift-shift k k′ (⟨ i , p , q ⟩ ∷ es) =
    cong₂ _∷_ (cong (λ n → ⟨ n , p , q ⟩) (sym (+-assoc k k′ i))) (shift-shift k k′ es)

  shift-++ : ∀ k xs ys → shift k (xs ++ ys) ≡ shift k xs ++ shift k ys
  shift-++ k xs ys = map-++ (shiftE k) xs ys

ιV-idʳ : ∀ m → ιV m (just []) ≡ just []
ιV-idʳ (just [])      = refl
ιV-idʳ (just (_ ∷ _)) = refl
ιV-idʳ nothing        = refl

ctxV-nilOr : ∀ P m b → ctxV P (nilOr m b) ≡ nilOr m b
ctxV-nilOr P m true                = refl
ctxV-nilOr P (just []) false       = refl
ctxV-nilOr P (just (_ ∷ _)) false  = refl
ctxV-nilOr P nothing false         = refl

nilOr-id : ∀ b → nilOr (just []) b ≡ just []
nilOr-id true  = refl
nilOr-id false = refl

-- ι with a χ argument.
ι-chiʳ : ∀ m c → ιV m (chiV c) ≡ nilOr m c
ι-chiʳ m true                 = ιV-idʳ m
ι-chiʳ (just []) false        = refl
ι-chiʳ (just (_ ∷ _)) false   = refl
ι-chiʳ nothing false          = refl

ι-chiˡ : ∀ m c → ιV (chiV c) m ≡ nilOr m c
ι-chiˡ m true                 = refl
ι-chiˡ (just []) false        = refl
ι-chiˡ (just (_ ∷ _)) false   = refl
ι-chiˡ nothing false          = refl

nilOr-⊛ : ∀ m m′ c → nilOr (m ⊛ m′) c ≡ nilOr m c ⊛ nilOr m′ c
nilOr-⊛ m m′ true = refl
nilOr-⊛ (just []) (just []) false = refl
nilOr-⊛ (just []) (just (_ ∷ _)) false = refl
nilOr-⊛ (just []) nothing false = refl
nilOr-⊛ (just (_ ∷ _)) (just _) false = refl
nilOr-⊛ (just (_ ∷ _)) nothing false = refl
nilOr-⊛ nothing m′ false = refl

nilOr-∧ : ∀ m b b′ → nilOr m (b ∧ b′) ≡ nilOr m b ⊛ nilOr m b′
nilOr-∧ m true  b′ = sym (⊛-idˡ (nilOr m b′))
nilOr-∧ m false true  = sym (⊛-idʳ (nilOr m false))
nilOr-∧ (just []) false false = refl
nilOr-∧ (just (_ ∷ _)) false false = refl
nilOr-∧ nothing false false = refl

-- nilOr m b ⊛ nilOr m (c ∨ b) and its mirror collapse to nilOr m b.
nilOr-absʳ : ∀ m b c → nilOr m b ⊛ nilOr m (c ∨ b) ≡ nilOr m b
nilOr-absʳ m true c rewrite ∨-true c = refl
nilOr-absʳ (just []) false c = trans (cong (just [] ⊛_) (nilOr-id (c ∨ false))) refl
nilOr-absʳ (just (_ ∷ _)) false c = refl
nilOr-absʳ nothing false c = refl

nilOr-absˡ : ∀ m b c → nilOr m (c ∨ b) ⊛ nilOr m b ≡ nilOr m b
nilOr-absˡ m true c rewrite ∨-true c = refl
nilOr-absˡ (just []) false c = cong (_⊛ just []) (nilOr-id (c ∨ false))
nilOr-absˡ (just (_ ∷ _)) false c = ⊛-nothingʳ (nilOr (just (_ ∷ _)) (c ∨ false))
nilOr-absˡ nothing false c = ⊛-nothingʳ (nilOr nothing (c ∨ false))

nilOr-absˡ′ : ∀ m b c → nilOr m (b ∨ c) ⊛ nilOr m b ≡ nilOr m b
nilOr-absˡ′ m true c = refl
nilOr-absˡ′ (just []) false c = cong (_⊛ just []) (nilOr-id c)
nilOr-absˡ′ (just (_ ∷ _)) false c = ⊛-nothingʳ (nilOr (just (_ ∷ _)) c)
nilOr-absˡ′ nothing false c = ⊛-nothingʳ (nilOr nothing c)

nilOr-absʳ′ : ∀ m b c → nilOr m b ⊛ nilOr m (b ∨ c) ≡ nilOr m b
nilOr-absʳ′ m true c = refl
nilOr-absʳ′ (just []) false c = cong (just [] ⊛_) (nilOr-id c)
nilOr-absʳ′ (just (_ ∷ _)) false c = refl
nilOr-absʳ′ nothing false c = refl

boolNil : Bool → Maybe RawPath
boolNil true  = just []
boolNil false = nothing

nilOr-chi : ∀ c d → nilOr (chiV c) d ≡ boolNil (c ∨ d)
nilOr-chi true  d     = nilOr-id d
nilOr-chi false true  = refl
nilOr-chi false false = refl

τ-bool : ∀ a b d → (a ∨ b) ∨ d ≡ (b ∨ d) ∨ a
τ-bool true  true  d     = refl
τ-bool true  false true  = refl
τ-bool true  false false = refl
τ-bool false true  d     = refl
τ-bool false false true  = refl
τ-bool false false false = refl

ctxV-id : ∀ m → ctxV (just []) m ≡ m
ctxV-id (just [])       = refl
ctxV-id (just (e ∷ es)) = cong just (shift-0 (e ∷ es))
ctxV-id nothing         = refl

ctxV-ctxV : ∀ P P′ m → ctxV P (ctxV P′ m) ≡ ctxV (P ⊛ P′) m
ctxV-ctxV P P′ (just []) = refl
ctxV-ctxV P P′ nothing = refl
ctxV-ctxV nothing nothing (just (e ∷ es)) = refl
ctxV-ctxV nothing (just w′) (just (e ∷ es)) = refl
ctxV-ctxV (just w) nothing (just (e ∷ es)) = refl
ctxV-ctxV (just w) (just w′) (just (e ∷ es)) =
  cong just (trans (shift-shift (lengthL w) (lengthL w′) (e ∷ es))
                   (cong (λ n → shift n (e ∷ es)) (sym (len-++ w w′))))

ctxV-⊛ : ∀ P m m′ → ctxV P (m ⊛ m′) ≡ ctxV P m ⊛ ctxV P m′
ctxV-⊛ P nothing m′ = refl
ctxV-⊛ P (just []) nothing = refl
ctxV-⊛ P (just []) (just ys) = sym (⊛-idˡ (ctxV P (just ys)))
ctxV-⊛ P (just (e ∷ es)) nothing = sym (⊛-nothingʳ (ctxV P (just (e ∷ es))))
ctxV-⊛ nothing (just (e ∷ es)) (just ys) = refl
ctxV-⊛ (just w) (just (e ∷ es)) (just []) =
  trans (cong (λ zs → just (shift (lengthL w) zs)) (++-[] (e ∷ es)))
        (sym (⊛-idʳ (just (shift (lengthL w) (e ∷ es)))))
ctxV-⊛ (just w) (just (e ∷ es)) (just (y ∷ ys)) =
  cong just (shift-++ (lengthL w) (e ∷ es) (y ∷ ys))

nilOr-⊛′ : ∀ m m′ c → nilOr (m ⊛ m′) c ≡ nilOr m′ c ⊛ nilOr m c
nilOr-⊛′ m m′ true = refl
nilOr-⊛′ (just []) (just []) false = refl
nilOr-⊛′ (just []) (just (_ ∷ _)) false = refl
nilOr-⊛′ (just []) nothing false = refl
nilOr-⊛′ (just (x ∷ xs)) (just ys) false = sym (⊛-nothingʳ (nilOr (just ys) false))
nilOr-⊛′ (just (_ ∷ _)) nothing false = refl
nilOr-⊛′ nothing m′ false = sym (⊛-nothingʳ (nilOr m′ false))

private
  cir : ∀ P m c → ctxV P (ιV m (chiV c)) ≡ nilOr m c
  cir P m c = trans (cong (ctxV P) (ι-chiʳ m c)) (ctxV-nilOr P m c)

  cil : ∀ P m c → ctxV P (ιV (chiV c) m) ≡ nilOr m c
  cil P m c = trans (cong (ctxV P) (ι-chiˡ m c)) (ctxV-nilOr P m c)

  cn2 : ∀ P P′ m m′ c c′ → ctxV P (nilOr m c) ⊛ ctxV P′ (nilOr m′ c′) ≡ nilOr m c ⊛ nilOr m′ c′
  cn2 P P′ m m′ c c′ = cong₂ _⊛_ (ctxV-nilOr P m c) (ctxV-nilOr P′ m′ c′)

------------------------------------------------------------------------
-- Every support-free equation of T holds in the model.

sem-≈ : ∀ {X Y} (d : X ≈ Y) → T (noSupp d) → ⟦ X ⟧4 ≡ ⟦ Y ⟧4
sem-≈ rfl _                     = refl
sem-≈ (sym≈ d) h                = sym (sem-≈ d h)
sem-≈ (trans≈ d e) h            = trans (sem-≈ d (T-∧ˡ (noSupp d) _ h)) (sem-≈ e (T-∧ʳ (noSupp d) _ h))
sem-≈ (id4-cong _) _            = refl
sem-≈ (ι-cong d e) _            = cong₂ ιV (sem3-≈ d) (sem3-≈ e)
sem-≈ (r-cong b d) _            = cong (λ m → nilOr m (isId b)) (sem3-≈ d)
sem-≈ (t-cong a d) _            = cong (λ m → nilOr m (isId a)) (sem3-≈ d)
sem-≈ (·-cong d e) h            = cong₂ _⊛_ (sem-≈ d (T-∧ˡ (noSupp d) _ h)) (sem-≈ e (T-∧ʳ (noSupp d) _ h))
sem-≈ (ctx-cong p d q) h        = cong₂ ctxV (sem3-≈ p) (sem-≈ d h)
sem-≈ (wl4-cong z d) h          = sem-≈ d h
sem-≈ (wr4-cong z d) h          = sem-≈ d h
sem-≈ (w1L-cong () d) h
sem-≈ (w1R-cong () d) h
sem-≈ (·-assoc X Y Z) _         = ⊛-assoc ⟦ X ⟧4 ⟦ Y ⟧4 ⟦ Z ⟧4
sem-≈ (·-idˡ F X) _             = ⊛-idˡ ⟦ X ⟧4
sem-≈ (·-idʳ F X) _             = ⊛-idʳ ⟦ X ⟧4
sem-≈ (ctx-id u v X) _          = ctxV-id ⟦ X ⟧4
sem-≈ (ctx-ctx p p′ X q′ q) _   = ctxV-ctxV ⟦ p ⟧3 ⟦ p′ ⟧3 ⟦ X ⟧4
sem-≈ (ctx-· p X Y q) _         = ctxV-⊛ ⟦ p ⟧3 ⟦ X ⟧4 ⟦ Y ⟧4
sem-≈ (ctx-id4 p F q) _         = refl
sem-≈ (wl4-· z X Y) _           = refl
sem-≈ (wr4-· z X Y) _           = refl
sem-≈ (wl4-ctx z p X q) _       = refl
sem-≈ (wr4-ctx z p X q) _       = refl
sem-≈ (wl4-id4 z F) _           = refl
sem-≈ (wr4-id4 z F) _           = refl
sem-≈ (wl4-wl4 z z′ X) _        = refl
sem-≈ (wr4-wr4 z z′ X) _        = refl
sem-≈ (wl4-wr4 z z′ X) _        = refl
sem-≈ (wl4-id2 X) _             = refl
sem-≈ (wr4-id2 X) _             = refl
sem-≈ (w1L-· () X Y) _
sem-≈ (w1R-· () X Y) _
sem-≈ (w1L-ctx () p X q) _
sem-≈ (w1R-ctx () p X q) _
sem-≈ (w1L-id4 () F) _
sem-≈ (w1R-id4 () F) _
sem-≈ (w1L-wl4 () z X) _
sem-≈ (w1L-wr4 () z X) _
sem-≈ (w1R-wl4 () z X) _
sem-≈ (w1R-wr4 () z X) _
sem-≈ (r-w1L () A y) _
sem-≈ (r-w1M () A y) _
sem-≈ (r-w1R () A y) _
sem-≈ (t-w1L () x B) _
sem-≈ (t-w1M () x B) _
sem-≈ (t-w1R () x B) _
sem-≈ (ι-w1L () F G) _
sem-≈ (ι-w1R () F G) _
sem-≈ (ι-wl z F G) _            = refl
sem-≈ (ι-wm z F G) _            = refl
sem-≈ (ι-wr z F G) _            = refl
sem-≈ (r-⨾ A A′ b e e′) _       =
  trans (nilOr-⊛ ⟦ A ⟧3 ⟦ A′ ⟧3 (isId b)) (sym (cn2 _ _ ⟦ A ⟧3 ⟦ A′ ⟧3 (isId b) (isId b)))
sem-≈ (t-⨾ a B B′ e e′) _       =
  trans (nilOr-⊛′ ⟦ B ⟧3 ⟦ B′ ⟧3 (isId a)) (sym (cn2 _ _ ⟦ B′ ⟧3 ⟦ B ⟧3 (isId a) (isId a)))
sem-≈ (r-∘ A a a′ b₁ b₂ e e′) _ =
  trans (nilOr-∧ ⟦ A ⟧3 (isId b₁) (isId b₂)) (sym (cn2 _ _ ⟦ A ⟧3 ⟦ A ⟧3 (isId b₁) (isId b₂)))
sem-≈ (t-∘ a₁ a₂ B b b′ e e′) _ =
  trans (nilOr-∧ ⟦ B ⟧3 (isId a₁) (isId a₂)) (sym (cn2 _ _ ⟦ B ⟧3 ⟦ B ⟧3 (isId a₁) (isId a₂)))
sem-≈ (r-wr A a a′ a₂ b e e′) _ =
  sym (trans (cong₂ _⊛_ (cir _ ⟦ A ⟧3 (isId a₂ ∨ isId b)) (ctxV-nilOr _ ⟦ A ⟧3 (isId b)))
             (nilOr-absˡ ⟦ A ⟧3 (isId b) (isId a₂)))
sem-≈ (r-wl A a a′ a₁ b e e′) _ =
  trans (cong (nilOr ⟦ A ⟧3 (isId b) ⊛_) (cil _ ⟦ A ⟧3 (isId a₁ ∨ isId b)))
        (trans (nilOr-absʳ ⟦ A ⟧3 (isId b) (isId a₁)) (sym (ctxV-nilOr _ ⟦ A ⟧3 (isId b))))
sem-≈ (t-wr B a b b′ b₂ e e′) _ =
  trans (cong (_⊛ nilOr ⟦ B ⟧3 (isId a)) (cir _ ⟦ B ⟧3 (isId a ∨ isId b₂)))
        (trans (nilOr-absˡ′ ⟦ B ⟧3 (isId a) (isId b₂)) (sym (ctxV-nilOr _ ⟦ B ⟧3 (isId a))))
sem-≈ (t-wl B a b b′ b₁ e e′) _ =
  sym (trans (cong₂ _⊛_ (ctxV-nilOr _ ⟦ B ⟧3 (isId a)) (cil _ ⟦ B ⟧3 (isId a ∨ isId b₁)))
             (nilOr-absʳ′ ⟦ B ⟧3 (isId a) (isId b₁)))
sem-≈ (τ-eq a b d) _            =
  trans (nilOr-chi (isId a ∨ isId b) (isId d))
        (trans (cong boolNil (τ-bool (isId a) (isId b) (isId d))) (sym (nilOr-chi (isId b ∨ isId d) (isId a))))
sem-≈ (ι-⨾ˡ F F′ a b v v′ e e′) _ =
  trans (ι-chiʳ (⟦ F ⟧3 ⊛ ⟦ F′ ⟧3) (isId a ∨ isId b))
        (trans (nilOr-⊛ ⟦ F ⟧3 ⟦ F′ ⟧3 (isId a ∨ isId b))
               (sym (cong₂ _⊛_ (cir _ ⟦ F ⟧3 (isId a ∨ isId b)) (cir _ ⟦ F′ ⟧3 (isId a ∨ isId b)))))
sem-≈ (ι-⨾ʳ G G′ a b u u′ e e′) _ =
  trans (ι-chiˡ (⟦ G ⟧3 ⊛ ⟦ G′ ⟧3) (isId a ∨ isId b))
        (trans (nilOr-⊛′ ⟦ G ⟧3 ⟦ G′ ⟧3 (isId a ∨ isId b))
               (sym (cong₂ _⊛_ (cil _ ⟦ G′ ⟧3 (isId a ∨ isId b)) (cil _ ⟦ G ⟧3 (isId a ∨ isId b)))))
sem-≈ (ι-idˡ u G F) _           = refl
sem-≈ (ι-idʳ u F H) _           = ιV-idʳ ⟦ F ⟧3
sem-≈ (r-idˡ u b F) _           = nilOr-id (isId b)
sem-≈ (r-idʳ A F) _             = refl
sem-≈ (t-idˡ B F) _             = refl
sem-≈ (t-idʳ a u F) _           = nilOr-id (isId a)
sem-≈ (supp _ _ _ _ _ _) ()

------------------------------------------------------------------------
-- Untyped split equivalence of raw paths, and the comparison of model
-- values up to it.

infix 3 _⊢_≈U_
data _⊢_≈U_ (sw : Switches) : RawPath → RawPath → Set where
  u-refl  : ∀ {p} → sw ⊢ p ≈U p
  u-step  : ∀ {p q} → Step sw p q → sw ⊢ p ≈U q
  u-sym   : ∀ {p q} → sw ⊢ p ≈U q → sw ⊢ q ≈U p
  u-trans : ∀ {p q r} → sw ⊢ p ≈U q → sw ⊢ q ≈U r → sw ⊢ p ≈U r

infix 3 _⊢_~_
data _⊢_~_ (sw : Switches) : Maybe RawPath → Maybe RawPath → Set where
  ~n : sw ⊢ nothing ~ nothing
  ~j : ∀ {p q} → sw ⊢ p ≈U q → sw ⊢ just p ~ just q

module _ {sw : Switches} where

  ~-refl : ∀ m → sw ⊢ m ~ m
  ~-refl nothing  = ~n
  ~-refl (just _) = ~j u-refl

  ~-≡ : ∀ {m m′} → m ≡ m′ → sw ⊢ m ~ m′
  ~-≡ {m} refl = ~-refl m

  ~-sym : ∀ {m m′} → sw ⊢ m ~ m′ → sw ⊢ m′ ~ m
  ~-sym ~n     = ~n
  ~-sym (~j d) = ~j (u-sym d)

  ~-trans : ∀ {m m′ m″} → sw ⊢ m ~ m′ → sw ⊢ m′ ~ m″ → sw ⊢ m ~ m″
  ~-trans ~n     ~n     = ~n
  ~-trans (~j d) (~j e) = ~j (u-trans d e)

  -- Steps in a larger path.
  step-++ʳ : ∀ {p p′} q → Step sw p p′ → Step sw (p ++ q) (p′ ++ q)
  step-++ʳ q (step pre e post {rr} m) =
    subst₂ (Step sw) (sym (++-assoc pre (e ∷ post) q))
           (sym (trans (++-assoc pre (rr ++ post) q) (cong (pre ++_) (++-assoc rr post q))))
           (step pre e (post ++ q) m)

  step-++ˡ : ∀ p {q q′} → Step sw q q′ → Step sw (p ++ q) (p ++ q′)
  step-++ˡ p (step pre e post {rr} m) =
    subst₂ (Step sw) (++-assoc p pre (e ∷ post)) (++-assoc p pre (rr ++ post))
           (step (p ++ pre) e post m)

  ≈U-++ʳ : ∀ {p p′} q → sw ⊢ p ≈U p′ → sw ⊢ p ++ q ≈U p′ ++ q
  ≈U-++ʳ q u-refl        = u-refl
  ≈U-++ʳ q (u-step s)    = u-step (step-++ʳ q s)
  ≈U-++ʳ q (u-sym d)     = u-sym (≈U-++ʳ q d)
  ≈U-++ʳ q (u-trans d e) = u-trans (≈U-++ʳ q d) (≈U-++ʳ q e)

  ≈U-++ˡ : ∀ p {q q′} → sw ⊢ q ≈U q′ → sw ⊢ p ++ q ≈U p ++ q′
  ≈U-++ˡ p u-refl        = u-refl
  ≈U-++ˡ p (u-step s)    = u-step (step-++ˡ p s)
  ≈U-++ˡ p (u-sym d)     = u-sym (≈U-++ˡ p d)
  ≈U-++ˡ p (u-trans d e) = u-trans (≈U-++ˡ p d) (≈U-++ˡ p e)

  ≈U-++ : ∀ {p p′ q q′} → sw ⊢ p ≈U p′ → sw ⊢ q ≈U q′ → sw ⊢ p ++ q ≈U p′ ++ q′
  ≈U-++ {p′ = p′} {q = q} d e = u-trans (≈U-++ʳ q d) (≈U-++ˡ p′ e)

  -- Steps shifted right.
  private
    whenE : ∀ {A : Set} b (xs : List A) {x} → x ∈L when b xs → T b × (x ∈L xs)
    whenE true xs m = tt , m

    whenI : ∀ {A : Set} b (xs : List A) {x} → T b → x ∈L xs → x ∈L when b xs
    whenI true xs _ m = m

  cuts-complete : ∀ a b → (a , b) ∈L cuts (a + suc b)
  cuts-complete zero    b = here
  cuts-complete (suc a) b = there (∈-map⁺ (λ ab → suc (fst ab) , snd ab) (cuts-complete a b))

  splits-shift : ∀ k e {r} → r ∈L splits sw e → shift k r ∈L splits sw (shiftE k e)
  splits-shift k ⟨ i , p , q ⟩ m with ∈-++⁻ (when (icc sw) (leftS ⟨ i , p , q ⟩)) m
  ... | inj₁ m′ with whenE (icc sw) _ m′
  ...   | on , m″ with ∈-map⁻ _ (cuts q) m″
  ...     | (a , b) , mc , refl =
    ∈-++ˡ (when (rsp sw) (rightS ⟨ k + i , p , q ⟩))
      (whenI (icc sw) _ on
        (subst (λ n → (⟨ k + i , p , a ⟩ ∷ ⟨ n , p , b ⟩ ∷ []) ∈L leftS ⟨ k + i , p , q ⟩)
               (+-assoc k i (suc a))
               (∈-map⁺ (λ ab → ⟨ k + i , p , fst ab ⟩ ∷ ⟨ (k + i) + suc (fst ab) , p , snd ab ⟩ ∷ []) mc)))
  splits-shift k ⟨ i , p , q ⟩ m | inj₂ m′ with whenE (rsp sw) _ m′
  ...   | on , m″ with ∈-map⁻ _ (cuts p) m″
  ...     | (a , b) , mc , refl =
    ∈-++ʳ (when (icc sw) (leftS ⟨ k + i , p , q ⟩))
      (whenI (rsp sw) _ on
        (subst (λ n → (⟨ n , b , q ⟩ ∷ ⟨ k + i , a , q ⟩ ∷ []) ∈L rightS ⟨ k + i , p , q ⟩)
               (+-assoc k i (suc a))
               (∈-map⁺ (λ ab → ⟨ (k + i) + suc (fst ab) , snd ab , q ⟩ ∷ ⟨ k + i , fst ab , q ⟩ ∷ []) mc)))

  step-shift : ∀ k {p q} → Step sw p q → Step sw (shift k p) (shift k q)
  step-shift k (step pre e post {rr} m) =
    subst₂ (Step sw) (sym (shift-++′ k pre (e ∷ post)))
           (sym (trans (shift-++′ k pre (rr ++ post)) (cong (shift k pre ++_) (shift-++′ k rr post))))
           (step (shift k pre) (shiftE k e) (shift k post) (splits-shift k e m))
    where
    shift-++′ : ∀ k xs ys → shift k (xs ++ ys) ≡ shift k xs ++ shift k ys
    shift-++′ k xs ys = map-++ (shiftE k) xs ys

  ≈U-shift : ∀ k {p q} → sw ⊢ p ≈U q → sw ⊢ shift k p ≈U shift k q
  ≈U-shift k u-refl        = u-refl
  ≈U-shift k (u-step s)    = u-step (step-shift k s)
  ≈U-shift k (u-sym d)     = u-sym (≈U-shift k d)
  ≈U-shift k (u-trans d e) = u-trans (≈U-shift k d) (≈U-shift k e)

  -- The empty path is alone in its class.
  isNil : RawPath → Bool
  isNil []      = true
  isNil (_ ∷ _) = false

  private
    isNil-++ : ∀ xs ys → isNil (xs ++ ys) ≡ isNil xs ∧ isNil ys
    isNil-++ []       ys = refl
    isNil-++ (x ∷ xs) ys = refl

    split-nonnil : ∀ e {r} → r ∈L splits sw e → isNil r ≡ false
    split-nonnil e m with splits-shape sw e m
    ... | x , y , refl , _ = refl

    ∧-false : ∀ a → a ∧ false ≡ false
    ∧-false true  = refl
    ∧-false false = refl

  step-nil : ∀ {p q} → Step sw p q → (isNil p ≡ false) × (isNil q ≡ false)
  step-nil (step pre e post {rr} m) =
    trans (isNil-++ pre (e ∷ post)) (∧-false (isNil pre)) ,
    trans (isNil-++ pre (rr ++ post))
          (trans (cong (isNil pre ∧_) (trans (isNil-++ rr post) (cong (_∧ isNil post) (split-nonnil e m))))
                 (∧-false (isNil pre)))

  ≈U-nil : ∀ {p q} → sw ⊢ p ≈U q → isNil p ≡ isNil q
  ≈U-nil u-refl        = refl
  ≈U-nil (u-step s)    = trans (fst (step-nil s)) (sym (snd (step-nil s)))
  ≈U-nil (u-sym d)     = sym (≈U-nil d)
  ≈U-nil (u-trans d e) = trans (≈U-nil d) (≈U-nil e)

  -- Congruence of ~ for the model operations.
  ~-⊛ : ∀ {m m′ n n′} → sw ⊢ m ~ m′ → sw ⊢ n ~ n′ → sw ⊢ (m ⊛ n) ~ (m′ ⊛ n′)
  ~-⊛ ~n     _      = ~n
  ~-⊛ (~j d) ~n     = ~n
  ~-⊛ (~j d) (~j e) = ~j (≈U-++ d e)

  private
    ctx-j : ∀ P p q → sw ⊢ p ≈U q → sw ⊢ ctxV P (just p) ~ ctxV P (just q)
    ctx-j P [] [] d = ~j u-refl
    ctx-j P [] (_ ∷ _) d with ≈U-nil d
    ... | ()
    ctx-j P (_ ∷ _) [] d with ≈U-nil d
    ... | ()
    ctx-j nothing  (_ ∷ _) (_ ∷ _) d = ~n
    ctx-j (just w) (e ∷ es) (e′ ∷ es′) d = ~j (≈U-shift (lengthL w) d)

  ~-ctx : ∀ P {m m′} → sw ⊢ m ~ m′ → sw ⊢ ctxV P m ~ ctxV P m′
  ~-ctx P ~n     = ~n
  ~-ctx P (~j d) = ctx-j P _ _ d

  ----------------------------------------------------------------------
  -- The switched laws hold up to one split step.

  private
    allT-++ : ∀ xs ys → allT (xs ++ ys) ≡ allT xs ∧ allT ys
    allT-++ []           ys = refl
    allT-++ (true ∷ xs)  ys = allT-++ xs ys
    allT-++ (false ∷ xs) ys = refl

    allF-++ : ∀ xs ys → allF (xs ++ ys) ≡ allF xs ∧ allF ys
    allF-++ []           ys = refl
    allF-++ (true ∷ xs)  ys = refl
    allF-++ (false ∷ xs) ys = allF-++ xs ys

    cne : ∀ c p q → ctxV nothing (edgeIf c p q) ≡ nothing
    cne true  p q = refl
    cne false p q = refl

  leftStep : T (icc sw) → ∀ p a b →
             Step sw (⟨ 0 , p , a + suc b ⟩ ∷ []) (⟨ 0 , p , a ⟩ ∷ ⟨ suc a , p , b ⟩ ∷ [])
  leftStep on p a b =
    step [] ⟨ 0 , p , a + suc b ⟩ []
      (∈-++ˡ (when (rsp sw) (rightS ⟨ 0 , p , a + suc b ⟩))
        (whenI (icc sw) _ on
          (∈-map⁺ (λ ab → ⟨ 0 , p , fst ab ⟩ ∷ ⟨ 0 + suc (fst ab) , p , snd ab ⟩ ∷ []) (cuts-complete a b))))

  rightStep : T (rsp sw) → ∀ a b q →
              Step sw (⟨ 0 , a + suc b , q ⟩ ∷ []) (⟨ suc a , b , q ⟩ ∷ ⟨ 0 , a , q ⟩ ∷ [])
  rightStep on a b q =
    step [] ⟨ 0 , a + suc b , q ⟩ []
      (∈-++ʳ (when (icc sw) (leftS ⟨ 0 , a + suc b , q ⟩))
        (whenI (rsp sw) _ on
          (∈-map⁺ (λ ab → ⟨ 0 + suc (fst ab) , snd ab , q ⟩ ∷ ⟨ 0 , fst ab , q ⟩ ∷ []) (cuts-complete a b))))

  private
    mainL : T (icc sw) → ∀ tA tB f p a b w → lengthL w ≡ suc a →
            sw ⊢ edgeIf ((tA ∧ tB) ∧ f) p (a + suc b) ~
                 (ctxV (just []) (edgeIf (tA ∧ f) p a) ⊛ ctxV (just w) (edgeIf (tB ∧ f) p b))
    mainL on false tB    f     p a b w l = ~n
    mainL on true  false true  p a b w l = ~n
    mainL on true  false false p a b w l = ~n
    mainL on true  true  false p a b w l = ~n
    mainL on true  true  true  p a b w l =
      ~j (subst (λ n → sw ⊢ (⟨ 0 , p , a + suc b ⟩ ∷ []) ≈U (⟨ 0 , p , a ⟩ ∷ ⟨ n , p , b ⟩ ∷ []))
                (sym (trans (+-zero (lengthL w)) l)) (u-step (leftStep on p a b)))

    mainR : T (rsp sw) → ∀ t fA fB a b q w → lengthL w ≡ suc a →
            sw ⊢ edgeIf (t ∧ (fA ∧ fB)) (a + suc b) q ~
                 (ctxV (just w) (edgeIf (t ∧ fB) b q) ⊛ ctxV (just []) (edgeIf (t ∧ fA) a q))
    mainR on false fA    fB    a b q w l = ~n
    mainR on true  false true  a b q w l = ~n
    mainR on true  false false a b q w l = ~n
    mainR on true  true  false a b q w l = ~n
    mainR on true  true  true  a b q w l =
      ~j (subst (λ n → sw ⊢ (⟨ 0 , a + suc b , q ⟩ ∷ []) ≈U (⟨ n , b , q ⟩ ∷ ⟨ 0 , a , q ⟩ ∷ []))
                (sym (trans (+-zero (lengthL w)) l)) (u-step (rightStep on a b q)))

  splitL-v : T (icc sw) → ∀ mF mF′ mG →
             sw ⊢ ιV (mF ⊛ mF′) mG ~ (ctxV (just []) (ιV mF mG) ⊛ ctxV mF (ιV mF′ mG))
  splitL-v on mF mF′ (just []) =
    ~-≡ (trans (ιV-idʳ (mF ⊛ mF′))
               (sym (cong₂ (λ x y → ctxV (just []) x ⊛ ctxV mF y) (ιV-idʳ mF) (ιV-idʳ mF′))))
  splitL-v on (just []) mF′ mG =
    ~-≡ (trans (cong (λ x → ιV x mG) (⊛-idˡ mF′)) (sym (trans (⊛-idˡ _) (ctxV-id _))))
  splitL-v on nothing mF′ nothing = ~n
  splitL-v on nothing mF′ (just (y ∷ ys)) = ~n
  splitL-v on (just (x ∷ xs)) nothing nothing = ~n
  splitL-v on (just (x ∷ xs)) (just ys′) nothing = ~n
  splitL-v on (just (x ∷ xs)) nothing (just (y ∷ ys)) = ~-≡ (sym (⊛-nothingʳ _))
  splitL-v on (just (x ∷ xs)) (just []) (just (y ∷ ys)) =
    ~-≡ (trans (cong (λ zs → ιV (just (x ∷ zs)) (just (y ∷ ys))) (++-[] xs))
               (sym (trans (⊛-idʳ _) (ctxV-id _))))
  splitL-v on (just (x ∷ xs)) (just (x′ ∷ xs′)) (just (y ∷ ys)) =
    ~-trans (~-≡ (cong₂ (λ c n → edgeIf (c ∧ allF (y ∷ ys)) (lengthL ys) n)
                        (allT-++ (x ∷ xs) (x′ ∷ xs′)) (len-++ xs (x′ ∷ xs′))))
            (mainL on (allT (x ∷ xs)) (allT (x′ ∷ xs′)) (allF (y ∷ ys))
                   (lengthL ys) (lengthL xs) (lengthL xs′) (x ∷ xs) refl)

  splitR-v : T (rsp sw) → ∀ mF mG mG′ →
             sw ⊢ ιV mF (mG ⊛ mG′) ~ (ctxV mG (ιV mF mG′) ⊛ ctxV (just []) (ιV mF mG))
  splitR-v on (just []) mG mG′ = ~j u-refl
  splitR-v on mF (just []) mG′ =
    ~-≡ (trans (cong (ιV mF) (⊛-idˡ mG′))
               (sym (trans (cong (λ y → ctxV (just []) (ιV mF mG′) ⊛ ctxV (just []) y) (ιV-idʳ mF))
                           (trans (⊛-idʳ _) (ctxV-id _)))))
  splitR-v on mF mG (just []) =
    ~-≡ (trans (cong (ιV mF) (⊛-idʳ mG))
               (sym (trans (cong (λ y → ctxV mG y ⊛ ctxV (just []) (ιV mF mG)) (ιV-idʳ mF))
                           (trans (⊛-idˡ _) (ctxV-id _)))))
  splitR-v on nothing nothing nothing = ~n
  splitR-v on nothing nothing (just (y′ ∷ ys′)) = ~n
  splitR-v on nothing (just (y ∷ ys)) nothing = ~n
  splitR-v on nothing (just (y ∷ ys)) (just (y′ ∷ ys′)) = ~n
  splitR-v on (just (x ∷ xs)) nothing nothing = ~n
  splitR-v on (just (x ∷ xs)) nothing (just (y′ ∷ ys′)) =
    ~-≡ (sym (cong (_⊛ nothing) (cne (allT (x ∷ xs) ∧ allF (y′ ∷ ys′)) (lengthL ys′) (lengthL xs))))
  splitR-v on (just (x ∷ xs)) (just (y ∷ ys)) nothing = ~n
  splitR-v on (just (x ∷ xs)) (just (y ∷ ys)) (just (y′ ∷ ys′)) =
    ~-trans (~-≡ (cong₂ (λ c n → edgeIf (allT (x ∷ xs) ∧ c) n (lengthL xs))
                        (allF-++ (y ∷ ys) (y′ ∷ ys′)) (len-++ ys (y′ ∷ ys′))))
            (mainR on (allT (x ∷ xs)) (allF (y ∷ ys)) (allF (y′ ∷ ys′))
                   (lengthL ys) (lengthL ys′) (lengthL xs) (y ∷ ys) refl)

  sem-law : ∀ {X Y} → Law sw X Y → sw ⊢ ⟦ X ⟧4 ~ ⟦ Y ⟧4
  sem-law (splitL h F F′ G v v′ e e′) = splitL-v (fromIsTrue h) ⟦ F ⟧3 ⟦ F′ ⟧3 ⟦ G ⟧3
  sem-law (splitR h F G G′ u u′ e e′) = splitR-v (fromIsTrue h) ⟦ F ⟧3 ⟦ G ⟧3 ⟦ G′ ⟧3

  -- The model respects ≈S.
  sem-S : ∀ {X Y} → sw ⊢ X ≈S Y → sw ⊢ ⟦ X ⟧4 ~ ⟦ Y ⟧4
  sem-S (str d h)    = ~-≡ (sem-≈ d h)
  sem-S (law l)      = sem-law l
  sem-S (symS d)     = ~-sym (sem-S d)
  sem-S (transS d e) = ~-trans (sem-S d) (sem-S e)
  sem-S (·-c d e)    = ~-⊛ (sem-S d) (sem-S e)
  sem-S (ctx-c {p} {p′} {X} {X′} pe d qe) =
    subst (λ P → sw ⊢ ctxV ⟦ p ⟧3 ⟦ X ⟧4 ~ ctxV P ⟦ X′ ⟧4) (sem3-≈ pe) (~-ctx ⟦ p ⟧3 (sem-S d))

------------------------------------------------------------------------
-- The translation of a running path evaluates to that path.

private
  run-cons′ : ∀ x w L {t} → run w (x ∷ L) ≡ just t →
              Σ Word λ w′ → (cross x w ≡ just w′) × (run w′ L ≡ just t)
  run-cons′ x w L h with cross x w
  ... | just w′ = w′ , refl , h

  run-cons⁺ : ∀ x w L {w′ t} → cross x w ≡ just w′ → run w′ L ≡ just t → run w (x ∷ L) ≡ just t
  run-cons⁺ x w L c h rewrite c = h

  just-inj′ : ∀ {A : Set} {a b : A} → _≡_ {A = Maybe A} (just a) (just b) → a ≡ b
  just-inj′ refl = refl

  allT-rep : ∀ n → allT (rep n true) ≡ true
  allT-rep zero    = refl
  allT-rep (suc n) = allT-rep n

  allF-rep : ∀ n → allF (rep n false) ≡ true
  allF-rep zero    = refl
  allF-rep (suc n) = allF-rep n

sem-aRun : ∀ i k → ⟦ aRun i k ⟧3 ≡ just (rep (suc k) true)
sem-aRun i zero    = refl
sem-aRun i (suc k) = cong (just (true ∷ []) ⊛_) (sem-aRun (suc i) k)

sem-bRun : ∀ j k → ⟦ bRun j k ⟧3 ≡ just (rep (suc k) false)
sem-bRun j zero    = refl
sem-bRun j (suc k) = cong (just (false ∷ []) ⊛_) (sem-bRun (suc j) k)

private
  reify-split : ∀ x d xs → ⟦ d ⟧3 ≡ just [] → ⟦ reify x xs ⟧3 ≡ ⟦ x ⟧3 ⊛ ⟦ reify₀ d xs ⟧3
  reify-split x d []       hd rewrite hd = sym (⊛-idʳ ⟦ x ⟧3)
  reify-split x d (y ∷ ys) hd = refl

sem-w3 : ∀ i j w → ⟦ w3 i j w ⟧3 ≡ just w
sem-w3 i j []          = refl
sem-w3 i j (true ∷ w)  =
  trans (reify-split (l3 i j true) (id3 (gen2 (uu (suc i)) ∘₂ gen2 (vv j))) (lets (suc i) j w) refl)
        (cong (just (true ∷ []) ⊛_) (sem-w3 (suc i) j w))
sem-w3 i j (false ∷ w) =
  trans (reify-split (l3 i j false) (id3 (gen2 (uu i) ∘₂ gen2 (vv (suc j)))) (lets i (suc j) w) refl)
        (cong (just (false ∷ []) ⊛_) (sem-w3 i (suc j) w))

private
  ι-runs : ∀ p q → ιV (just (rep (suc q) true)) (just (rep (suc p) false)) ≡ just (⟨ 0 , p , q ⟩ ∷ [])
  ι-runs p q rewrite allT-rep q | allF-rep p | len-rep p false | len-rep q true = refl

sem-trE′ : ∀ pre p q post → ⟦ trE′ pre p q post ⟧4 ≡ just (⟨ lengthL pre , p , q ⟩ ∷ [])
sem-trE′ pre p q post =
  trans (cong₂ ctxV (sem-w3 0 0 pre)
                    (trans (cong₂ ιV (sem-aRun (cntA pre) q) (sem-bRun (cntB pre) p)) (ι-runs p q)))
        (cong (λ n → just (⟨ n , p , q ⟩ ∷ [])) (+-zero (lengthL pre)))

sem-trE : ∀ k p q w {w′} → cross ⟨ k , p , q ⟩ w ≡ just w′ → ⟦ trE ⟨ k , p , q ⟩ w ⟧4 ≡ just (⟨ k , p , q ⟩ ∷ [])
sem-trE k p q w c with cross-sound k p q w c
... | shape pre post refl refl _ = trans (cong ⟦_⟧4 (trE-shape pre p q post)) (sem-trE′ pre p q post)

sem-tr : ∀ w es {t} → run w es ≡ just t → ⟦ tr w es ⟧4 ≡ just es
sem-tr w [] h = refl
sem-tr w (⟨ k , p , q ⟩ ∷ es) h with run-cons′ ⟨ k , p , q ⟩ w es h
... | w′ , c , h′ =
  cong₂ _⊛_ (sem-trE k p q w c)
            (trans (cong (λ v → ⟦ tr v es ⟧4) (next-≡ ⟨ k , p , q ⟩ w c)) (sem-tr w′ es h′))

------------------------------------------------------------------------
-- Splits preserve running, in both directions.

private
  ∷-inj : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
  ∷-inj refl = refl , refl

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  ++-cancel : ∀ (xs xs′ : Word) {ys ys′ : Word} → lengthL xs ≡ lengthL xs′ →
              xs ++ ys ≡ xs′ ++ ys′ → (xs ≡ xs′) × (ys ≡ ys′)
  ++-cancel []       []         l e = refl , e
  ++-cancel []       (_ ∷ _)    () e
  ++-cancel (_ ∷ _)  []         () e
  ++-cancel (x ∷ xs) (x′ ∷ xs′) l e with ∷-inj e
  ... | refl , e′ with ++-cancel xs xs′ (suc-inj l) e′
  ...   | refl , e″ = refl , e″

  eqWT : ∀ a b (tl : Word) → rep (suc (a + suc b)) true ++ tl ≡ rep (suc a) true ++ (rep (suc b) true ++ tl)
  eqWT a b tl = trans (cong (_++ tl) (rep-+ (suc a) (suc b) true)) (++-assoc (rep (suc a) true) _ tl)

  eqWF : ∀ a b (tl : Word) → rep (suc (a + suc b)) false ++ tl ≡ rep (suc a) false ++ (rep (suc b) false ++ tl)
  eqWF a b tl = trans (cong (_++ tl) (rep-+ (suc a) (suc b) false)) (++-assoc (rep (suc a) false) _ tl)

  lenRep : ∀ (pre : Word) n x → lengthL (pre ++ rep n x) ≡ lengthL pre + n
  lenRep pre n x = trans (len-++ pre (rep n x)) (cong (lengthL pre +_) (len-rep n x))

  -- Left split.
  leftFwd : ∀ pre p a b post →
    run (pre ++ (rep (suc p) false ++ (rep (suc (a + suc b)) true ++ post)))
        (⟨ lengthL pre , p , a ⟩ ∷ ⟨ lengthL pre + suc a , p , b ⟩ ∷ []) ≡
    just (pre ++ (rep (suc (a + suc b)) true ++ (rep (suc p) false ++ post)))
  leftFwd pre p a b post =
    run-cons⁺ ⟨ lengthL pre , p , a ⟩ _ (⟨ lengthL pre + suc a , p , b ⟩ ∷ []) c1
      (run-cons⁺ ⟨ lengthL pre + suc a , p , b ⟩ w₁ [] c2 refl)
    where
    Bs = rep (suc p) false
    A₁ = rep (suc a) true
    A₂ = rep (suc b) true
    w₁ = pre ++ (A₁ ++ (Bs ++ (A₂ ++ post)))
    w′ = pre ++ (rep (suc (a + suc b)) true ++ (Bs ++ post))
    c1 : cross ⟨ lengthL pre , p , a ⟩ (pre ++ (Bs ++ (rep (suc (a + suc b)) true ++ post))) ≡ just w₁
    c1 = subst (λ ws → cross ⟨ lengthL pre , p , a ⟩ (pre ++ (Bs ++ ws)) ≡ just w₁) (sym (eqWT a b post))
               (cross-complete pre p a (A₂ ++ post))
    c2 : cross ⟨ lengthL pre + suc a , p , b ⟩ w₁ ≡ just w′
    c2 = subst₂ (λ n ws → cross ⟨ n , p , b ⟩ ws ≡ just w′) (lenRep pre (suc a) true)
                (++-assoc pre A₁ (Bs ++ (A₂ ++ post)))
                (trans (cross-complete (pre ++ A₁) p b post)
                       (cong just (trans (++-assoc pre A₁ (A₂ ++ (Bs ++ post)))
                                         (cong (pre ++_) (sym (eqWT a b (Bs ++ post)))))))

  leftF : ∀ i p a b w {w′} → cross ⟨ i , p , a + suc b ⟩ w ≡ just w′ →
          run w (⟨ i , p , a ⟩ ∷ ⟨ i + suc a , p , b ⟩ ∷ []) ≡ just w′
  leftF i p a b w c with cross-sound i p (a + suc b) w c
  ... | shape pre post refl refl refl = leftFwd pre p a b post

  leftBwd′ : ∀ pre p a b post₁ pre₂ post₂ → lengthL pre₂ ≡ lengthL pre + suc a →
    pre ++ (rep (suc a) true ++ (rep (suc p) false ++ post₁)) ≡
      pre₂ ++ (rep (suc p) false ++ (rep (suc b) true ++ post₂)) →
    cross ⟨ lengthL pre , p , a + suc b ⟩ (pre ++ (rep (suc p) false ++ (rep (suc a) true ++ post₁))) ≡
      just (pre₂ ++ (rep (suc b) true ++ (rep (suc p) false ++ post₂)))
  leftBwd′ pre p a b post₁ pre₂ post₂ l₂ s₂
    with ++-cancel (pre ++ rep (suc a) true) pre₂ (trans (lenRep pre (suc a) true) (sym l₂))
                   (trans (++-assoc pre (rep (suc a) true) _) s₂)
  ... | refl , er with snd (++-cancel (rep (suc p) false) (rep (suc p) false) refl er)
  ...   | refl =
    trans (cong (λ ws → cross ⟨ lengthL pre , p , a + suc b ⟩ (pre ++ (rep (suc p) false ++ ws)))
                (sym (eqWT a b post₂)))
          (trans (cross-complete pre p (a + suc b) post₂)
                 (cong just (trans (cong (pre ++_) (eqWT a b (rep (suc p) false ++ post₂)))
                                   (sym (++-assoc pre (rep (suc a) true) _)))))

  leftB : ∀ i p a b w w₁ w₂ → cross ⟨ i , p , a ⟩ w ≡ just w₁ → cross ⟨ i + suc a , p , b ⟩ w₁ ≡ just w₂ →
          cross ⟨ i , p , a + suc b ⟩ w ≡ just w₂
  leftB i p a b w w₁ w₂ c₁ c₂ with cross-sound i p a w c₁
  ... | shape pre post₁ refl refl refl with cross-sound (lengthL pre + suc a) p b _ c₂
  ...   | shape pre₂ post₂ l₂ s₂ refl = leftBwd′ pre p a b post₁ pre₂ post₂ l₂ s₂

  -- Right split.
  rightFwd : ∀ pre a b q post →
    run (pre ++ (rep (suc (a + suc b)) false ++ (rep (suc q) true ++ post)))
        (⟨ lengthL pre + suc a , b , q ⟩ ∷ ⟨ lengthL pre , a , q ⟩ ∷ []) ≡
    just (pre ++ (rep (suc q) true ++ (rep (suc (a + suc b)) false ++ post)))
  rightFwd pre a b q post =
    run-cons⁺ ⟨ lengthL pre + suc a , b , q ⟩ _ (⟨ lengthL pre , a , q ⟩ ∷ []) c1
      (run-cons⁺ ⟨ lengthL pre , a , q ⟩ w₁ [] c2 refl)
    where
    B₁ = rep (suc a) false
    B₂ = rep (suc b) false
    As = rep (suc q) true
    w₁ = pre ++ (B₁ ++ (As ++ (B₂ ++ post)))
    w′ = pre ++ (As ++ (rep (suc (a + suc b)) false ++ post))
    c1 : cross ⟨ lengthL pre + suc a , b , q ⟩ (pre ++ (rep (suc (a + suc b)) false ++ (As ++ post))) ≡ just w₁
    c1 = subst₂ (λ n ws → cross ⟨ n , b , q ⟩ ws ≡ just w₁) (lenRep pre (suc a) false)
                (trans (++-assoc pre B₁ (B₂ ++ (As ++ post))) (cong (pre ++_) (sym (eqWF a b (As ++ post)))))
                (trans (cross-complete (pre ++ B₁) b q post) (cong just (++-assoc pre B₁ (As ++ (B₂ ++ post)))))
    c2 : cross ⟨ lengthL pre , a , q ⟩ w₁ ≡ just w′
    c2 = trans (cross-complete pre a q (B₂ ++ post))
               (cong (λ ws → just (pre ++ (As ++ ws))) (sym (eqWF a b post)))

  rightF : ∀ i a b q w {w′} → cross ⟨ i , a + suc b , q ⟩ w ≡ just w′ →
           run w (⟨ i + suc a , b , q ⟩ ∷ ⟨ i , a , q ⟩ ∷ []) ≡ just w′
  rightF i a b q w c with cross-sound i (a + suc b) q w c
  ... | shape pre post refl refl refl = rightFwd pre a b q post

  rightBwd′ : ∀ pre a b q pre₁ post₁ post₂ → lengthL pre₁ ≡ lengthL pre + suc a →
    pre₁ ++ (rep (suc q) true ++ (rep (suc b) false ++ post₁)) ≡
      pre ++ (rep (suc a) false ++ (rep (suc q) true ++ post₂)) →
    cross ⟨ lengthL pre , a + suc b , q ⟩ (pre₁ ++ (rep (suc b) false ++ (rep (suc q) true ++ post₁))) ≡
      just (pre ++ (rep (suc q) true ++ (rep (suc a) false ++ post₂)))
  rightBwd′ pre a b q pre₁ post₁ post₂ l₁ s₂
    with ++-cancel pre₁ (pre ++ rep (suc a) false) (trans l₁ (sym (lenRep pre (suc a) false)))
                   (trans s₂ (sym (++-assoc pre (rep (suc a) false) _)))
  ... | refl , er with snd (++-cancel (rep (suc q) true) (rep (suc q) true) refl er)
  ...   | refl =
    trans (cong (cross ⟨ lengthL pre , a + suc b , q ⟩)
                (trans (++-assoc pre (rep (suc a) false) _)
                       (cong (pre ++_) (sym (eqWF a b (rep (suc q) true ++ post₁))))))
          (trans (cross-complete pre (a + suc b) q post₁)
                 (cong (λ ws → just (pre ++ (rep (suc q) true ++ ws))) (eqWF a b post₁)))

  rightB : ∀ i a b q w w₁ w₂ → cross ⟨ i + suc a , b , q ⟩ w ≡ just w₁ → cross ⟨ i , a , q ⟩ w₁ ≡ just w₂ →
           cross ⟨ i , a + suc b , q ⟩ w ≡ just w₂
  rightB i a b q w w₁ w₂ c₁ c₂ with cross-sound (i + suc a) b q w c₁
  ... | shape pre₁ post₁ l₁ refl refl with cross-sound i a q _ c₂
  ...   | shape pre post₂ refl s₂ refl = rightBwd′ pre a b q pre₁ post₁ post₂ l₁ s₂

module _ {sw : Switches} where

  private
    whenE′ : ∀ {A : Set} b (xs : List A) {x} → x ∈L when b xs → T b × (x ∈L xs)
    whenE′ true xs m = tt , m

    run-++⁺ : ∀ w xs ys {w′ t} → run w xs ≡ just w′ → run w′ ys ≡ just t → run w (xs ++ ys) ≡ just t
    run-++⁺ w []       ys refl h = h
    run-++⁺ w (x ∷ xs) ys h₁ h₂ with run-cons′ x w xs h₁
    ... | w₁ , c , h₁′ = run-cons⁺ x w (xs ++ ys) c (run-++⁺ w₁ xs ys h₁′ h₂)

    run-++⁻ : ∀ w xs ys {t} → run w (xs ++ ys) ≡ just t →
              Σ Word λ w′ → (run w xs ≡ just w′) × (run w′ ys ≡ just t)
    run-++⁻ w []       ys h = w , refl , h
    run-++⁻ w (x ∷ xs) ys h with run-cons′ x w (xs ++ ys) h
    ... | w₁ , c , h′ with run-++⁻ w₁ xs ys h′
    ...   | w′ , h₁ , h₂ = w′ , run-cons⁺ x w xs c h₁ , h₂

  -- A split path runs exactly where its edge does, to the same word.
  split-run : ∀ e {rr} → rr ∈L splits sw e → ∀ w {w′} →
              (cross e w ≡ just w′ → run w rr ≡ just w′) × (run w rr ≡ just w′ → cross e w ≡ just w′)
  split-run ⟨ i , p , q ⟩ m w {w′} with ∈-++⁻ (when (icc sw) (leftS ⟨ i , p , q ⟩)) m
  ... | inj₁ m′ with whenE′ (icc sw) _ m′
  ...   | _ , m″ with ∈-map⁻ _ (cuts q) m″
  ...     | (a , b) , mc , refl =
    subst (λ q′ → (cross ⟨ i , p , q′ ⟩ w ≡ just w′ → run w (⟨ i , p , a ⟩ ∷ ⟨ i + suc a , p , b ⟩ ∷ []) ≡ just w′) ×
                  (run w (⟨ i , p , a ⟩ ∷ ⟨ i + suc a , p , b ⟩ ∷ []) ≡ just w′ → cross ⟨ i , p , q′ ⟩ w ≡ just w′))
          (cuts-sound q mc)
          (leftF i p a b w , bwd)
    where
    bwd : run w (⟨ i , p , a ⟩ ∷ ⟨ i + suc a , p , b ⟩ ∷ []) ≡ just w′ → cross ⟨ i , p , a + suc b ⟩ w ≡ just w′
    bwd h with run-cons′ ⟨ i , p , a ⟩ w _ h
    ... | w₁ , c₁ , h₁ with run-cons′ ⟨ i + suc a , p , b ⟩ w₁ [] h₁
    ...   | w₂ , c₂ , h₂ = subst (λ v → cross ⟨ i , p , a + suc b ⟩ w ≡ just v) (just-inj′ h₂)
                                 (leftB i p a b w w₁ w₂ c₁ c₂)
  split-run ⟨ i , p , q ⟩ m w {w′} | inj₂ m′ with whenE′ (rsp sw) _ m′
  ...   | _ , m″ with ∈-map⁻ _ (cuts p) m″
  ...     | (a , b) , mc , refl =
    subst (λ p′ → (cross ⟨ i , p′ , q ⟩ w ≡ just w′ → run w (⟨ i + suc a , b , q ⟩ ∷ ⟨ i , a , q ⟩ ∷ []) ≡ just w′) ×
                  (run w (⟨ i + suc a , b , q ⟩ ∷ ⟨ i , a , q ⟩ ∷ []) ≡ just w′ → cross ⟨ i , p′ , q ⟩ w ≡ just w′))
          (cuts-sound p mc)
          (rightF i a b q w , bwd)
    where
    bwd : run w (⟨ i + suc a , b , q ⟩ ∷ ⟨ i , a , q ⟩ ∷ []) ≡ just w′ → cross ⟨ i , a + suc b , q ⟩ w ≡ just w′
    bwd h with run-cons′ ⟨ i + suc a , b , q ⟩ w _ h
    ... | w₁ , c₁ , h₁ with run-cons′ ⟨ i , a , q ⟩ w₁ [] h₁
    ...   | w₂ , c₂ , h₂ = subst (λ v → cross ⟨ i , a + suc b , q ⟩ w ≡ just v) (just-inj′ h₂)
                                 (rightB i a b q w w₁ w₂ c₁ c₂)

  -- A step preserves running from w to t, in both directions.
  step-run : ∀ {p q} → Step sw p q → ∀ w {t} →
             (run w p ≡ just t → run w q ≡ just t) × (run w q ≡ just t → run w p ≡ just t)
  step-run (step pre e post {rr} m) w = fwd , bwd
    where
    fwd : ∀ {t} → run w (pre ++ e ∷ post) ≡ just t → run w (pre ++ rr ++ post) ≡ just t
    fwd h with run-++⁻ w pre (e ∷ post) h
    ... | w₁ , h₁ , h₂ with run-cons′ e w₁ post h₂
    ...   | w₂ , c , h₃ = run-++⁺ w pre (rr ++ post) h₁ (run-++⁺ w₁ rr post (fst (split-run e m w₁) c) h₃)
    bwd : ∀ {t} → run w (pre ++ rr ++ post) ≡ just t → run w (pre ++ e ∷ post) ≡ just t
    bwd h with run-++⁻ w pre (rr ++ post) h
    ... | w₁ , h₁ , h₂ with run-++⁻ w₁ rr post h₂
    ...   | w₂ , h₃ , h₄ = run-++⁺ w pre (e ∷ post) h₁ (run-cons⁺ e w₁ post (snd (split-run e m w₁) h₃) h₄)

  ≈U-run : ∀ {p q} → sw ⊢ p ≈U q → ∀ w {t} →
           (run w p ≡ just t → run w q ≡ just t) × (run w q ≡ just t → run w p ≡ just t)
  ≈U-run u-refl w        = (λ h → h) , (λ h → h)
  ≈U-run (u-step s) w    = step-run s w
  ≈U-run (u-sym d) w     = snd (≈U-run d w) , fst (≈U-run d w)
  ≈U-run (u-trans d e) w = (λ h → fst (≈U-run e w) (fst (≈U-run d w) h)) ,
                           (λ h → snd (≈U-run d w) (snd (≈U-run e w) h))

------------------------------------------------------------------------
-- The converse of the link.

module Converse (m n : Nat) where
  open OnGrid m n
  open Link m n using (link)

  -- Untyped split equivalence from a valid path is Grid's equality.
  ≈U→≈ : ∀ {sw p q} → Valid p → sw ⊢ p ≈U q → sw ⊢ p ≈ q
  ≈U→≈ vp u-refl        = ≈-refl
  ≈U→≈ vp (u-step s)    = ≈-step vp (fst (step-run s start) vp) s
  ≈U→≈ vp (u-sym d)     = ≈-sym (≈U→≈ (snd (≈U-run d start) vp) d)
  ≈U→≈ vp (u-trans d e) = ≈-trans (≈U→≈ vp d) (≈U→≈ (fst (≈U-run d start) vp) e)

  private
    ~j⁻ : ∀ {sw p q} → sw ⊢ just p ~ just q → sw ⊢ p ≈U q
    ~j⁻ (~j d) = d

  converse : ∀ {sw p q} → Valid p → Valid q → sw ⊢ tr start p ≈S tr start q → sw ⊢ p ≈ q
  converse {sw} {p} {q} vp vq d =
    ≈U→≈ vp (~j⁻ (subst₂ (_⊢_~_ sw) (sem-tr start p vp) (sem-tr start q vq) (sem-S d)))

  -- Together: on valid paths, Grid's equality is exactly T-equality of
  -- the translations (without the support equations, with the
  -- switched laws).
  link-iff : ∀ {sw p q} → Valid p → Valid q →
             (sw ⊢ p ≈ q → sw ⊢ tr start p ≈S tr start q) × (sw ⊢ tr start p ≈S tr start q → sw ⊢ p ≈ q)
  link-iff vp vq = link , converse vp vq
