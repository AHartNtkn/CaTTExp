------------------------------------------------------------------------
-- Ledger F12c / F12d (notes/coinductive.md §2 and §4).
--
-- The terminal constant-arity machine, in the interface of
-- CaTTExp.Coinductive.DecidableDialgebra, so that the terminal
-- dialgebra of a decidable family there is unconditional.
--
-- A machine is (C, h : C → A, s : C × B → C).  With exponentials and
-- the list object L = μX. 1 + B × X (cons lists), the terminal machine
-- is A^L with
--   root  φ ↦ φ(nil),          step  (φ, b) ↦ λl. φ(cons(b, l)),
-- and the map from (C, h, s) is the transpose of r : L → A^C, defined by
-- recursion: r(nil) = h, r(cons(b, l)) = λx. r(l)(s(x, b)).  This is
-- Known 1 / notes/coinductive.md §2 in the cartesian case.
--
-- Machine-checked (no postulates):
--   * `terminal-machine` : TerminalMachine (existence and uniqueness);
--   * `Unconditional.terminal`, `Unconditional.unique`: the terminal
--     p-dialgebra of every decidable family χ : A × B → 2, from U-⊔ at
--     2, exponentials and the list object over B.
--
-- Scope and honesty notes.
--   * 1-categorical with strict equality of morphisms; cartesian.
--   * The list object is given by recursion without parameters plus
--     uniqueness (an initial algebra of 1 + B × X); parameters come
--     from the exponentials.
--   * For Fin → ℕ, B = ℕ and L = List ℕ.
------------------------------------------------------------------------
module CaTTExp.Coinductive.CartMachine where

open import CaTTExp.Prelude using (_≡_; refl; sym; trans; cong; cong₂)
open import CaTTExp.Descent.CocartLemmas using (_≡⟨_⟩_; _∎)
open import CaTTExp.Coinductive.DecidableDialgebra

record Closed (𝒞 : Cat⁺) (B : Cat⁺.Ob 𝒞) : Set₁ where
  open Cat⁺ 𝒞
  field
    Exp   : Ob → Ob → Ob        -- Exp X Z = Z^X
    ev    : ∀ {X Z} → Hom (Exp X Z × X) Z
    lam   : ∀ {W X Z} → Hom (W × X) Z → Hom W (Exp X Z)
    lam-β : ∀ {W X Z} (f : Hom (W × X) Z) → ev ∘ ⟨ lam f ∘ π₁ , π₂ ⟩ ≡ f
    lam-η : ∀ {W X Z} (g : Hom W (Exp X Z)) → lam (ev ∘ ⟨ g ∘ π₁ , π₂ ⟩) ≡ g

    L       : Ob
    nil     : Hom 𝟙 L
    cons    : Hom (B × L) L
    rec     : ∀ {Y} → Hom 𝟙 Y → Hom (B × Y) Y → Hom L Y
    rec-nil : ∀ {Y} (y : Hom 𝟙 Y) (k : Hom (B × Y) Y) → rec y k ∘ nil ≡ y
    rec-cons : ∀ {Y} (y : Hom 𝟙 Y) (k : Hom (B × Y) Y) →
               rec y k ∘ cons ≡ k ∘ ⟨ π₁ , rec y k ∘ π₂ ⟩
    rec-uni : ∀ {Y} (y : Hom 𝟙 Y) (k : Hom (B × Y) Y) (g : Hom L Y) →
              g ∘ nil ≡ y → g ∘ cons ≡ k ∘ ⟨ π₁ , g ∘ π₂ ⟩ → g ≡ rec y k

module Build (𝒞 : Cat⁺) {A B : Cat⁺.Ob 𝒞}
             (χ : Cat⁺.Hom 𝒞 (Cat⁺._×_ 𝒞 A B) (Cat⁺._+_ 𝒞 (Cat⁺.𝟙 𝒞) (Cat⁺.𝟙 𝒞)))
             (cl : Closed 𝒞 B) where
  open Cat⁺ 𝒞
  open Theory 𝒞
  open Family 𝒞 χ
  open Closed cl

  ----------------------------------------------------------------------
  -- application

  app : ∀ {W X Z} → Hom W (Exp X Z) → Hom W X → Hom W Z
  app φ a = ev ∘ ⟨ φ , a ⟩

  app≡ : ∀ {W X Z} {φ ψ : Hom W (Exp X Z)} (a : Hom W X) → φ ≡ ψ → app φ a ≡ app ψ a
  app≡ a refl = refl

  arg≡ : ∀ {W X Z} (φ : Hom W (Exp X Z)) {a b : Hom W X} → a ≡ b → app φ a ≡ app φ b
  arg≡ φ refl = refl

  app-∘ : ∀ {V W X Z} (φ : Hom W (Exp X Z)) (a : Hom W X) (k : Hom V W) →
          app φ a ∘ k ≡ app (φ ∘ k) (a ∘ k)
  app-∘ φ a k = trans (assoc _ _ _) (∘r ev (⟨⟩-∘ φ a k))

  app-lam : ∀ {V W X Z} (f : Hom (W × X) Z) (k : Hom V W) (a : Hom V X) →
            app (lam f ∘ k) a ≡ f ∘ ⟨ k , a ⟩
  app-lam f k a =
    ev ∘ ⟨ lam f ∘ k , a ⟩
      ≡⟨ ∘r ev (pair≡ (trans (∘r (lam f) (sym (π₁-β k a))) (sym (assoc _ _ _)))
                      (sym (π₂-β k a))) ⟩
    ev ∘ ⟨ (lam f ∘ π₁) ∘ ⟨ k , a ⟩ , π₂ ∘ ⟨ k , a ⟩ ⟩
      ≡⟨ ∘r ev (sym (⟨⟩-∘ _ _ _)) ⟩
    ev ∘ (⟨ lam f ∘ π₁ , π₂ ⟩ ∘ ⟨ k , a ⟩)
      ≡⟨ sym (assoc _ _ _) ⟩
    (ev ∘ ⟨ lam f ∘ π₁ , π₂ ⟩) ∘ ⟨ k , a ⟩
      ≡⟨ ∘l _ (lam-β f) ⟩
    f ∘ ⟨ k , a ⟩ ∎

  extE : ∀ {W X Z} (φ ψ : Hom W (Exp X Z)) →
        app (φ ∘ π₁) π₂ ≡ app (ψ ∘ π₁) π₂ → φ ≡ ψ
  extE φ ψ e = trans (sym (lam-η φ)) (trans (cong lam e) (lam-η ψ))

  pair-π : ∀ {X Y} → ⟨ π₁ {X} {Y} , π₂ ⟩ ≡ id
  pair-π = trans (pair≡ (sym (idr π₁)) (sym (idr π₂))) (⟨⟩-η id)

  -- swapping the arguments of a curried map
  sw : ∀ {X Y Z} → Hom X (Exp Y Z) → Hom Y (Exp X Z)
  sw f = lam (app (f ∘ π₂) π₁)

  app-sw : ∀ {W X Y Z} (f : Hom X (Exp Y Z)) (y : Hom W Y) (x : Hom W X) →
           app (sw f ∘ y) x ≡ app (f ∘ x) y
  app-sw f y x =
    trans (app-lam _ y x)
      (trans (app-∘ _ _ _)
        (cong₂ app (trans (assoc _ _ _) (∘r f (π₂-β y x))) (π₁-β y x)))

  ----------------------------------------------------------------------
  -- the terminal machine A^L

  Tc : Ob
  Tc = Exp L A

  hT : Hom Tc A
  hT = app id (nil ∘ !)

  sT : Hom (Tc × B) Tc
  sT = lam (app (π₁ ∘ π₁) (cons ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩))

  app-sT : ∀ {W} (φ : Hom W Tc) (b : Hom W B) (l : Hom W L) →
           app (sT ∘ ⟨ φ , b ⟩) l ≡ app φ (cons ∘ ⟨ b , l ⟩)
  app-sT φ b l =
    trans (app-lam _ _ _)
      (trans (app-∘ _ _ _)
        (cong₂ app
          (trans (assoc _ _ _) (trans (∘r π₁ (π₁-β _ _)) (π₁-β _ _)))
          (trans (assoc _ _ _)
            (∘r cons (trans (⟨⟩-∘ _ _ _)
              (pair≡ (trans (assoc _ _ _) (trans (∘r π₂ (π₁-β _ _)) (π₂-β _ _)))
                     (π₂-β _ _)))))))

  app-hT : ∀ {W} (φ : Hom W Tc) → hT ∘ φ ≡ app φ (nil ∘ !)
  app-hT φ =
    trans (app-∘ _ _ _)
      (cong₂ app (idl φ) (trans (assoc _ _ _) (∘r nil (!-uni _))))

  TM : Mach
  Mach.MC TM = Tc
  Mach.mh TM = hT
  Mach.s  TM = sT

  module ToT (M : Mach) where
    open Mach M renaming (MC to C; mh to h)

    EC : Ob
    EC = Exp C A

    y₀ : Hom 𝟙 EC
    y₀ = lam (h ∘ π₂)

    k : Hom (B × EC) EC
    k = lam (app (π₂ ∘ π₁) (s ∘ ⟨ π₂ , π₁ ∘ π₁ ⟩))

    app-k : ∀ {W} (b : Hom W B) (φ : Hom W EC) (x : Hom W C) →
            app (k ∘ ⟨ b , φ ⟩) x ≡ app φ (s ∘ ⟨ x , b ⟩)
    app-k b φ x =
      trans (app-lam _ _ _)
        (trans (app-∘ _ _ _)
          (cong₂ app
            (trans (assoc _ _ _) (trans (∘r π₂ (π₁-β _ _)) (π₂-β _ _)))
            (trans (assoc _ _ _)
              (∘r s (trans (⟨⟩-∘ _ _ _)
                (pair≡ (π₂-β _ _)
                       (trans (assoc _ _ _) (trans (∘r π₁ (π₁-β _ _)) (π₁-β _ _)))))))))

    app-y₀ : ∀ {W} (x : Hom W C) → app (y₀ ∘ !) x ≡ h ∘ x
    app-y₀ x = trans (app-lam _ _ _) (trans (assoc _ _ _) (∘r h (π₂-β _ _)))

    r : Hom L EC
    r = rec y₀ k

    ĝ : Hom C Tc
    ĝ = sw r

    root-ĝ : hT ∘ ĝ ≡ h
    root-ĝ =
      hT ∘ ĝ                         ≡⟨ app-hT ĝ ⟩
      app ĝ (nil ∘ !)                ≡⟨ app≡ _ (sym (idr ĝ)) ⟩
      app (ĝ ∘ id) (nil ∘ !)         ≡⟨ app-sw r id _ ⟩
      app (r ∘ (nil ∘ !)) id         ≡⟨ app≡ id (trans (sym (assoc _ _ _)) (∘l ! (rec-nil y₀ k))) ⟩
      app (y₀ ∘ !) id                ≡⟨ app-y₀ id ⟩
      h ∘ id                         ≡⟨ idr h ⟩
      h ∎

    r-cons : ∀ {W} (b : Hom W B) (l : Hom W L) (x : Hom W C) →
             app (r ∘ (cons ∘ ⟨ b , l ⟩)) x ≡ app (r ∘ l) (s ∘ ⟨ x , b ⟩)
    r-cons b l x =
      app (r ∘ (cons ∘ ⟨ b , l ⟩)) x
        ≡⟨ app≡ x (trans (sym (assoc _ _ _))
                    (trans (∘l _ (rec-cons y₀ k))
                      (trans (assoc _ _ _)
                        (∘r k (trans (⟨⟩-∘ _ _ _)
                          (pair≡ (π₁-β _ _) (trans (assoc _ _ _) (∘r r (π₂-β _ _))))))))) ⟩
      app (k ∘ ⟨ b , r ∘ l ⟩) x
        ≡⟨ app-k _ _ _ ⟩
      app (r ∘ l) (s ∘ ⟨ x , b ⟩) ∎

    step-ĝ : ĝ ∘ s ≡ sT ∘ (ĝ ⊠)
    step-ĝ = extE _ _
      (app ((ĝ ∘ s) ∘ π₁) π₂
         ≡⟨ app≡ π₂ (assoc _ _ _) ⟩
       app (ĝ ∘ (s ∘ π₁)) π₂
         ≡⟨ app-sw r _ _ ⟩
       app (r ∘ π₂) (s ∘ π₁)
         ≡⟨ arg≡ (r ∘ π₂) (∘r s (sym (trans (sym (⟨⟩-∘ π₁ π₂ π₁)) (trans (∘l π₁ pair-π) (idl π₁))))) ⟩
       app (r ∘ π₂) (s ∘ ⟨ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩)
         ≡⟨ sym (r-cons _ _ _) ⟩
       app (r ∘ (cons ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩)) (π₁ ∘ π₁)
         ≡⟨ sym (app-sw r _ _) ⟩
       app (ĝ ∘ (π₁ ∘ π₁)) (cons ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩)
         ≡⟨ sym (app-sT _ _ _) ⟩
       app (sT ∘ ⟨ ĝ ∘ (π₁ ∘ π₁) , π₂ ∘ π₁ ⟩) π₂
         ≡⟨ app≡ π₂ (∘r sT (sym (trans (⟨⟩-∘ _ _ _) (pair≡ (trans (assoc _ _ _) refl) refl)))) ⟩
       app (sT ∘ ((ĝ ⊠) ∘ π₁)) π₂
         ≡⟨ app≡ π₂ (sym (assoc _ _ _)) ⟩
       app ((sT ∘ (ĝ ⊠)) ∘ π₁) π₂ ∎)

    toT : MHom M TM
    MHom.mmap  toT = ĝ
    MHom.mroot toT = root-ĝ
    MHom.mstep toT = step-ĝ

    -- uniqueness: the swap of any machine map satisfies r's recursion
    uniq : (g : MHom M TM) → MHom.mmap g ≡ ĝ
    uniq g = extE _ _
      (app (g′ ∘ π₁) π₂             ≡⟨ sym (app-sw g′ _ _) ⟩
       app (ǧ ∘ π₂) π₁              ≡⟨ app≡ π₁ (∘l π₂ ǧ≡r) ⟩
       app (r ∘ π₂) π₁              ≡⟨ sym (app-sw r _ _) ⟩
       app (ĝ ∘ π₁) π₂ ∎)
      where
        g′ = MHom.mmap g
        ǧ : Hom L EC
        ǧ = sw g′

        nil-eq : ǧ ∘ nil ≡ y₀
        nil-eq = extE _ _
          (app ((ǧ ∘ nil) ∘ π₁) π₂            ≡⟨ app≡ π₂ (assoc _ _ _) ⟩
           app (ǧ ∘ (nil ∘ π₁)) π₂            ≡⟨ app-sw g′ _ _ ⟩
           app (g′ ∘ π₂) (nil ∘ π₁)           ≡⟨ arg≡ (g′ ∘ π₂) (trans (∘r nil (!-uni π₁))
                                                  (sym (trans (assoc _ _ _) (∘r nil (!-uni _))))) ⟩
           app (g′ ∘ π₂) ((nil ∘ !) ∘ (g′ ∘ π₂)) ≡⟨ sym (trans (app-∘ _ _ _) (app≡ _ (idl _))) ⟩
           app id (nil ∘ !) ∘ (g′ ∘ π₂)       ≡⟨ sym (assoc _ _ _) ⟩
           (hT ∘ g′) ∘ π₂                     ≡⟨ ∘l π₂ (MHom.mroot g) ⟩
           h ∘ π₂                             ≡⟨ sym (trans (app-lam _ _ _) (trans (∘r (h ∘ π₂) pair-π) (idr _))) ⟩
           app (y₀ ∘ π₁) π₂ ∎)

        cons-eq : ǧ ∘ cons ≡ k ∘ ⟨ π₁ , ǧ ∘ π₂ ⟩
        cons-eq = extE _ _
          (app ((ǧ ∘ cons) ∘ π₁) π₂
             ≡⟨ app≡ π₂ (assoc _ _ _) ⟩
           app (ǧ ∘ (cons ∘ π₁)) π₂
             ≡⟨ app-sw g′ _ _ ⟩
           app (g′ ∘ π₂) (cons ∘ π₁)
             ≡⟨ arg≡ (g′ ∘ π₂) (∘r cons (sym (trans (sym (⟨⟩-∘ π₁ π₂ π₁)) (trans (∘l π₁ pair-π) (idl π₁))))) ⟩
           app (g′ ∘ π₂) (cons ∘ ⟨ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩)
             ≡⟨ sym (app-sT _ _ _) ⟩
           app (sT ∘ ⟨ g′ ∘ π₂ , π₁ ∘ π₁ ⟩) (π₂ ∘ π₁)
             ≡⟨ app≡ _ (∘r sT (sym (trans (⟨⟩-∘ _ _ _)
                  (pair≡ (trans (assoc _ _ _) (∘r g′ (π₁-β _ _))) (π₂-β _ _))))) ⟩
           app (sT ∘ ((g′ ⊠) ∘ ⟨ π₂ , π₁ ∘ π₁ ⟩)) (π₂ ∘ π₁)
             ≡⟨ app≡ _ (trans (sym (assoc _ _ _))
                  (trans (∘l _ (sym (MHom.mstep g))) (assoc _ _ _))) ⟩
           app (g′ ∘ (s ∘ ⟨ π₂ , π₁ ∘ π₁ ⟩)) (π₂ ∘ π₁)
             ≡⟨ sym (app-sw g′ _ _) ⟩
           app (ǧ ∘ (π₂ ∘ π₁)) (s ∘ ⟨ π₂ , π₁ ∘ π₁ ⟩)
             ≡⟨ sym (app-k _ _ _) ⟩
           app (k ∘ ⟨ π₁ ∘ π₁ , ǧ ∘ (π₂ ∘ π₁) ⟩) π₂
             ≡⟨ app≡ π₂ (∘r k (sym (trans (⟨⟩-∘ _ _ _)
                  (pair≡ refl (assoc _ _ _))))) ⟩
           app (k ∘ (⟨ π₁ , ǧ ∘ π₂ ⟩ ∘ π₁)) π₂
             ≡⟨ app≡ π₂ (sym (assoc _ _ _)) ⟩
           app ((k ∘ ⟨ π₁ , ǧ ∘ π₂ ⟩) ∘ π₁) π₂ ∎)

        ǧ≡r : ǧ ≡ r
        ǧ≡r = rec-uni y₀ k ǧ nil-eq cons-eq

  terminal-machine : TerminalMachine
  TerminalMachine.T    terminal-machine = TM
  TerminalMachine.term terminal-machine M = ToT.toT M
  TerminalMachine.uni  terminal-machine M g = ToT.uniq M g

  -- the terminal dialgebra of the decidable family χ, unconditionally
  module Unconditional = Final terminal-machine
