------------------------------------------------------------------------
-- Ledger F10f, part 3, substantive version (notes/universe-free-
-- principles.md §6a steps 2–6), 1-truncated.
--
-- Encode–decode for the free category of a graph, with encode from
-- DJ-sec and step 5 from DJ (dj-ext), as §6a states it.
--
-- Setting: a graph (V, Ed), a vertex a, and a model Π of the path
-- context (Π_v, nil : Π_a, snoc_e : Π_v → Π_w) that is initial with
-- pointwise uniqueness (no function extensionality; equations strict,
-- with K, 1-truncated as in CocartLemmas).
--
-- What is machine-checked:
--   * the free category FΓ: objects V, arrows paths, composition by
--     concatenation, with its laws (`FΓ`);
--   * step 2, the covering family: Π extends to transport along paths
--     (`tr`, functorial: `tr-∘`), and its total space, the category of
--     elements E → FΓ, is an opfibration (`lift`), whose objects over
--     v are the elements of Π_v and whose chosen lift along an edge e
--     is snoc_e (by definition of `tr`);
--   * step 3, encode: DJ-sec (`DJOneTruncated.DJSec.dj-sec`) at the
--     point (a, Π.m) (the model's nil) gives a CF-morphism k : a ↓ FΓ → E over FΓ; enc reads
--     off its fibre component (`enc`), and it is a model morphism
--     (`encMor`), derived from k's laws (`enc-nil`, `enc-snoc`);
--   * step 4, decode: the model morphism Π → Hom(a, –) from initiality,
--     assembled into a functor Dec : E → a ↓ FΓ over FΓ from its
--     fibrewise components and their compatibility with transport
--     (`dec-tr`), i.e. DESC-uni's assembly in the 1-categorical case;
--   * step 5, dec ∘ enc = id: Dec ∘ k and the identity are CF-morphisms
--     a ↓ FΓ → a ↓ FΓ over FΓ; a map between them at ι over a gives,
--     by DJ (`dj-ext`), a natural transformation over FΓ whose
--     components force dec (enc p) ≡ p (`dec-enc`); only the existence
--     half of DJ-uni is used (`dj-ext-uni` is not);
--   * step 6, enc ∘ dec = id: enc is a model morphism, so by
--     uniqueness (INIT-J2) enc ∘ dec is the identity (`enc-dec`);
--   * so Hom_{FΓ}(a, v) ≅ Π_v (`hom≅Π`).
--
-- What is NOT machine-checked:
--   * the covering family is built directly as the category of
--     elements of Π, not glued by DESC-glue from collages over the
--     vertices and edges (G and G₁ are CaTTExp.Descent.Collage /
--     RelCollage's subject); DESC-uni is used only in its
--     1-categorical form (a functor from fibrewise maps compatible with
--     transport), not derived from a descent statement;
--   * FΓ's universal property as the free category (R-A); here FΓ is
--     the path category;
--   * that DJ is needed: dj-sec's section is the chosen lift, so
--     `enc v p` is definitionally `tr p Π.m` (the fold, as in
--     CaTTExp.Descent.EncodeDecode), and `dec-enc` also follows
--     directly from `dec-tr`, `f-nil` and `app-idr`.  Steps 3 and 5
--     are proved from the abstract interface of k and `dj-ext`, and
--     would go through unchanged for any such section, but they do not
--     show that the DJ route is essential;
--   * T-loc (inverted edges), homs over generalised points, and the
--     ω-categorical setting.
------------------------------------------------------------------------
module CaTTExp.Descent.EncodeDecodeDJ where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas
open import CaTTExp.Descent.DJOneTruncated

module _ (V : Set) (Ed : V → V → Set) where

  ----------------------------------------------------------------------
  -- The free category on the graph.

  data Path (u : V) : V → Set where
    nil  : Path u u
    snoc : ∀ {v w} → Path u v → Ed v w → Path u w

  app : ∀ {u v w} → Path v w → Path u v → Path u w
  app nil        p = p
  app (snoc q e) p = snoc (app q p) e

  app-idr : ∀ {u v} (q : Path u v) → app q nil ≡ q
  app-idr nil        = refl
  app-idr (snoc q e) = cong (λ r → snoc r e) (app-idr q)

  app-assoc : ∀ {t u v w} (r : Path v w) (q : Path u v) (p : Path t u)
            → app (app r q) p ≡ app r (app q p)
  app-assoc nil        q p = refl
  app-assoc (snoc r e) q p = cong (λ s → snoc s e) (app-assoc r q p)

  FΓ : Cat
  FΓ = record
    { Ob = V ; Hom = Path ; id = nil ; _∘_ = app
    ; idl = λ _ → refl ; idr = app-idr ; assoc = app-assoc }

  private
    uip′ : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
    uip′ refl refl = refl

  module _ (a : V) where

    -- Models and pointwise-initial models.
    record Model : Set₁ where
      field
        M  : V → Set
        m  : M a
        sn : ∀ {v w} → Ed v w → M v → M w

    record Mor (A B : Model) : Set where
      private
        module A = Model A
        module B = Model B
      field
        f      : ∀ v → A.M v → B.M v
        f-nil  : f a A.m ≡ B.m
        f-snoc : ∀ {v w} (e : Ed v w) (x : A.M v) → f w (A.sn e x) ≡ B.sn e (f v x)

    idMor : ∀ A → Mor A A
    idMor A = record { f = λ _ x → x ; f-nil = refl ; f-snoc = λ _ _ → refl }

    _∘M_ : ∀ {A B C} → Mor B C → Mor A B → Mor A C
    _∘M_ {A} {B} {C} g h = record
      { f      = λ v x → G.f v (H.f v x)
      ; f-nil  = trans (cong (G.f a) H.f-nil) G.f-nil
      ; f-snoc = λ e x → trans (cong (G.f _) (H.f-snoc e x)) (G.f-snoc e (H.f _ x)) }
      where
      module G = Mor g
      module H = Mor h

    record Initial (Π : Model) : Set₁ where
      field
        init : ∀ B → Mor Π B
        uniq : ∀ B (g h : Mor Π B) → ∀ v x → Mor.f g v x ≡ Mor.f h v x

    -- Hom_{FΓ}(a, –) is a model.
    HomModel : Model
    HomModel = record { M = Path a ; m = nil ; sn = λ e p → snoc p e }

    module _ (Π : Model) (ini : Initial Π) where
      private
        module Π = Model Π
        module I = Initial ini

      ------------------------------------------------------------------
      -- Step 2: the covering family, as the category of elements.

      tr : ∀ {u v} → Path u v → Π.M u → Π.M v
      tr nil        x = x
      tr (snoc q e) x = Π.sn e (tr q x)

      tr-∘ : ∀ {u v w} (q : Path v w) (p : Path u v) (x : Π.M u)
           → tr (app q p) x ≡ tr q (tr p x)
      tr-∘ nil        p x = refl
      tr-∘ (snoc q e) p x = cong (Π.sn e) (tr-∘ q p x)

      EOb : Set
      EOb = Σ V Π.M

      EHom : EOb → EOb → Set
      EHom (u , x) (v , y) = Σ (Path u v) (λ p → tr p x ≡ y)

      private
        E≡ : ∀ {s t : EOb} {f g : EHom s t} → fst f ≡ fst g → f ≡ g
        E≡ {f = p , e} {.p , e'} refl = cong (λ r → p , r) (uip′ e e')

        e∘ : ∀ {s t r : EOb} → EHom t r → EHom s t → EHom s r
        e∘ {u , x} {v , y} {w , z} (q , eq) (p , ep) =
          app q p , trans (tr-∘ q p x) (trans (cong (tr q) ep) eq)

      E : Cat
      E = record
        { Ob = EOb ; Hom = EHom
        ; id = λ {s} → nil , refl
        ; _∘_ = λ {s} {t} {r} g f → e∘ {s} {t} {r} g f
        ; idl = λ {s} {t} f → E≡ {s} {t} refl
        ; idr = λ {s} {t} f → E≡ {s} {t} (app-idr (fst f))
        ; assoc = λ {s} {t} {r} {q} h g f → E≡ {s} {q} (app-assoc (fst h) (fst g) (fst f)) }

      P : Functor E FΓ
      P = record { F₀ = fst ; F₁ = fst ; F-id = refl ; F-∘ = λ _ _ → refl }

      module OE = Over E FΓ P

      lift-cocart : ∀ {u v} (x : Π.M u) (p : Path u v)
                  → OE.IsCocart {u , x} {v , tr p x} (p , refl)
      lift-cocart {u} {v} x p = record
        { fact   = λ {t} τ γ q → fa {t} τ γ q
        ; fact-P = λ {t} τ γ q → fP {t} τ γ q
        ; fact-∘ = λ {t} τ γ q → E≡ {u , x} {t} (sym q)
        ; uniq   = λ {t} g g' q _ → E≡ {v , tr p x} {t} q }
        where
        fa : ∀ {t : EOb} (τ : EHom (u , x) t) (γ : Path v (fst t)) → fst τ ≡ app γ p
           → EHom (v , tr p x) t
        fa {w , z} (p' , ep') γ q =
          γ , trans (sym (tr-∘ γ p x)) (trans (cong (λ r → tr r x) (sym q)) ep')
        fP : ∀ {t : EOb} (τ : EHom (u , x) t) (γ : Path v (fst t)) (q : fst τ ≡ app γ p)
           → fst (fa {t} τ γ q) ≡ γ
        fP {w , z} (p' , ep') γ q = refl

      lift : OE.Opfib
      lift (u , x) {v} p = record
        { tgt = v , tr p x ; χ = p , refl ; cocart = lift-cocart x p
        ; θ = nil ; θ-iso = record { inv = nil ; left = refl ; right = refl } ; tri = refl }

      ------------------------------------------------------------------
      -- Step 3: encode, from DJ-sec at the point nil.

      module DS = DJSec E FΓ P lift (a , Π.m)
      open DS using (dj-sec)
      module D = DJ E FΓ P a
      module C = Comma FΓ a

      k : D.CFMor
      k = fst dj-sec
      module k = D.CFMor k

      enc : ∀ v → Path a v → Π.M v
      enc v p = tr (k.ζ (v , p)) (snd (k.h₀ (v , p)))

      private
        u   = fst (snd dj-sec)
        ζι  = k.ζ C.ι
        ytι = snd (k.h₀ C.ι)
        -- u : (a, m) → k(ι), with ζ_ι ∘ P u ≡ nil.
        u-tri : app ζι (fst u) ≡ nil
        u-tri = snd (snd (snd dj-sec))

      enc-nil : enc a nil ≡ Π.m
      enc-nil =
        tr ζι ytι                       ≡⟨ cong (tr ζι) (sym (snd u)) ⟩
        tr ζι (tr (fst u) Π.m)          ≡⟨ sym (tr-∘ ζι (fst u) Π.m) ⟩
        tr (app ζι (fst u)) Π.m         ≡⟨ cong (λ r → tr r Π.m) u-tri ⟩
        Π.m ∎

      -- The comma arrow (v, p) → (w, snoc p e) along the edge e.
      private
        edge : ∀ {v w} (p : Path a v) (e : Ed v w) → Cat.Hom C.aB (v , p) (w , snoc p e)
        edge p e = snoc nil e , refl

      enc-snoc : ∀ {v w} (e : Ed v w) (p : Path a v) → enc w (snoc p e) ≡ Π.sn e (enc v p)
      enc-snoc {v} {w} e p =
        tr ζy yy                                 ≡⟨ cong (tr ζy) (sym (snd g)) ⟩
        tr ζy (tr (fst g) yx)                    ≡⟨ sym (tr-∘ ζy (fst g) yx) ⟩
        tr (app ζy (fst g)) yx                   ≡⟨ cong (λ r → tr r yx) (k.ζ-nat (edge p e)) ⟩
        tr (snoc (app nil ζx) e) yx              ≡⟨ refl ⟩
        Π.sn e (tr ζx yx) ∎
        where
        g  = k.h₁ (edge p e)
        ζx = k.ζ (v , p)
        ζy = k.ζ (w , snoc p e)
        yx = snd (k.h₀ (v , p))
        yy = snd (k.h₀ (w , snoc p e))

      encMor : Mor HomModel Π
      encMor = record { f = enc ; f-nil = enc-nil ; f-snoc = λ e p → enc-snoc e p }

      ------------------------------------------------------------------
      -- Step 4: decode, and its assembly into a functor over FΓ.

      decMor : Mor Π HomModel
      decMor = I.init HomModel

      private
        dec = Mor.f decMor
        module dm = Mor decMor

      -- The fibrewise decode commutes with transport.
      dec-tr : ∀ {u v} (r : Path u v) (y : Π.M u) → dec v (tr r y) ≡ app r (dec u y)
      dec-tr nil        y = refl
      dec-tr (snoc r e) y = trans (dm.f-snoc e (tr r y)) (cong (λ s → snoc s e) (dec-tr r y))

      private
        C≡ : ∀ {s t : Cat.Ob C.aB} {f g : Cat.Hom C.aB s t} → fst f ≡ fst g → f ≡ g
        C≡ {f = p , e} {.p , e'} refl = cong (λ r → p , r) (uip′ e e')

        Dec₀ : EOb → Cat.Ob C.aB
        Dec₀ (v , y) = v , dec v y

        Dec₁ : ∀ {s t} → EHom s t → Cat.Hom C.aB (Dec₀ s) (Dec₀ t)
        Dec₁ {u , y} {v , y'} (r , er) = r , trans (sym (dec-tr r y)) (cong (dec v) er)

      Dec : Functor E C.aB
      Dec = record
        { F₀ = Dec₀ ; F₁ = λ {s} {t} → Dec₁ {s} {t}
        ; F-id = λ {s} → C≡ {Dec₀ s} {Dec₀ s} refl
        ; F-∘ = λ {s} {t} {r} g f → C≡ {Dec₀ s} {Dec₀ r} refl }

      ------------------------------------------------------------------
      -- Step 5: dec ∘ enc = id, by DJ for the comma over FΓ.

      module DC = DJ C.aB FΓ C.π a
      module CC = Over C.aB FΓ C.π

      private
        nil-iso : ∀ {v} → Cat.IsIso FΓ (nil {v})
        nil-iso = record { inv = nil ; left = refl ; right = refl }

      idCF : DC.CFMor
      idCF = record
        { h₀ = λ x → x ; h₁ = λ g → g ; h-id = refl ; h-∘ = λ _ _ → refl
        ; ζ = λ _ → nil ; ζ-iso = λ _ → nil-iso
        ; ζ-nat = λ g → sym (app-idr (fst g))
        ; cocart = C.dj-cocart }

      decCF : DC.CFMor
      decCF = record
        { h₀ = λ x → Dec₀ (k.h₀ x)
        ; h₁ = λ {x} {y} g → Dec₁ {k.h₀ x} {k.h₀ y} (k.h₁ {x} {y} g)
        ; h-id = λ {x} → trans (cong (Dec₁ {k.h₀ x} {k.h₀ x}) (k.h-id {x})) (Functor.F-id Dec {k.h₀ x})
        ; h-∘ = λ {x} {y} {z} g f → trans (cong (Dec₁ {k.h₀ x} {k.h₀ z}) (k.h-∘ {x} {y} {z} g f))
                  (Functor.F-∘ Dec {k.h₀ x} {k.h₀ y} {k.h₀ z} (k.h₁ {y} {z} g) (k.h₁ {x} {y} f))
        ; ζ = k.ζ ; ζ-iso = k.ζ-iso
        ; ζ-nat = k.ζ-nat
        ; cocart = λ {x} {y} g → C.dj-cocart (Dec₁ {k.h₀ x} {k.h₀ y} (k.h₁ {x} {y} g)) }

      private
        -- dec (k(ι)) ≡ fst u: dec y_ι = dec (tr (fst u) m) = fst u.
        dec-ι : dec _ ytι ≡ fst u
        dec-ι = trans (cong (dec _) (sym (snd u)))
                  (trans (dec-tr (fst u) Π.m) (trans (cong (app (fst u)) dm.f-nil) (app-idr (fst u))))

        ρ : Cat.Hom C.aB (DC.CFMor.h₀ decCF C.ι) C.ι
        ρ = ζι , trans (cong (app ζι) dec-ι) u-tri

      nat : DC.NatOver decCF idCF
      nat = fst (DC.dj-ext decCF idCF ρ refl)

      dec-enc : ∀ v (p : Path a v) → dec v (enc v p) ≡ p
      dec-enc v p =
        dec v (tr ζx yx)          ≡⟨ dec-tr ζx yx ⟩
        app ζx (dec _ yx)         ≡⟨ cong (λ r → app r (dec _ yx)) (sym (DC.NatOver.κ-over nat (v , p))) ⟩
        app (fst κ) (dec _ yx)    ≡⟨ snd κ ⟩
        p ∎
        where
        κ  = DC.NatOver.κ nat (v , p)
        ζx = k.ζ (v , p)
        yx = snd (k.h₀ (v , p))

      ------------------------------------------------------------------
      -- Step 6: enc ∘ dec = id, by uniqueness.

      enc-dec : ∀ v (x : Π.M v) → enc v (dec v x) ≡ x
      enc-dec v x = I.uniq Π (encMor ∘M decMor) (idMor Π) v x

      hom≅Π : ∀ v → Σ (Path a v → Π.M v) (λ en → Σ (Π.M v → Path a v) (λ de →
                (∀ p → de (en p) ≡ p) × (∀ x → en (de x) ≡ x)))
      hom≅Π v = enc v , dec v , dec-enc v , enc-dec v
