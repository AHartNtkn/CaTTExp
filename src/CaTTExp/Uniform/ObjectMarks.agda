------------------------------------------------------------------------
-- Object marks on object terms (ledger S36; notes/object-marks.md;
-- spec §3.2, §9.1).
--
-- Before S36 an object mark (`grpd_k`, `iord`, `ord`, `lsplit`,
-- `rsplit`) could only be sent by a substitution to an object
-- *variable* with the same mark, and constants carried none. Lemmas
-- over `C : ⋆ ord` therefore did not apply to ℕ, ℤ, limits, ⟦Γ⟧ or
-- ‖A‖_n. This module merges the h-levels of chapter 9 (`trunc n`, the
-- declaration mark ⋆^{≤n}) and the object marks of chapter 3 into one
-- family of atomic marks with an entailment relation, and gives one
-- decidable judgment `md ρ C m` on object terms, with a clause per
-- object former. It proves:
--   * entailment is reflexive and transitive         (ent-refl, ent-trans)
--   * the judgment is closed upward under entailment  (md-up)
--   * substitution: a variable declared with marks may be replaced by any
--     object term with those marks derivable, and every derived mark
--     survives                                       (md-subst)
--   * soundness in every strict model satisfying the per-former facts
--     listed in `Formers`                            (ent-sound, sound)
--   * examples by evaluation: ℕ, ⊤ ⊔ ⊤, ‖A‖₀, ‖A‖₁, ⟦Γ⟧ are `ord`; ‖A‖₂ and a
--     groupoid are not derivably `ord`; a groupoid is `iord`.
--
-- What is not checked here: the per-former facts themselves (fields of
-- `Base` and `Formers`). Those are the strict readings of the chapter 9
-- rules (T-lim, T-hom, T-coprod, T-graph, T-init, INIT's mark) and the
-- dimension count "inner letters have hom-dimension ≥ 2"; they are
-- proved on paper in notes/object-marks.md §3. The limit clause for the
-- inner marks (`lim-innId` etc.) uses the hypothesis (PW) of §3 there.
------------------------------------------------------------------------
module CaTTExp.Uniform.ObjectMarks where

open import CaTTExp.Prelude
open import CaTTExp.Uniform.Marks using (∨-introl; ∨-intror; ∨-elim; ∧-intro; fstT; sndT)

------------------------------------------------------------------------
-- Order on Nat, as a Boolean.

infix 4 _≤?_
_≤?_ : Nat → Nat → Bool
zero  ≤? _     = true
suc m ≤? zero  = false
suc m ≤? suc n = m ≤? n

≤?-refl : ∀ n → T (n ≤? n)
≤?-refl zero    = tt
≤?-refl (suc n) = ≤?-refl n

≤?-trans : ∀ a b c → T (a ≤? b) → T (b ≤? c) → T (a ≤? c)
≤?-trans zero    b       c       _ _ = tt
≤?-trans (suc a) zero    c       () _
≤?-trans (suc a) (suc b) zero    _ ()
≤?-trans (suc a) (suc b) (suc c) p q = ≤?-trans a b c p q

------------------------------------------------------------------------
-- Atomic object marks.
--
--   trunc t   `C trunc n` with t = n + 2   (n ≥ −2; also ⋆^{≤n})
--   grpd g    `C grpd_k`  with k = g + 1   (k ≥ 1)
--   iord      inner letters into C invertible
--   ord       inner letters into C trivial (with (COH-ord))
--   lsplit, rsplit   the split laws for inner crossings into C

data Mk : Set where
  trunc grpd : Nat → Mk
  iord ord lsplit rsplit : Mk

-- a ⊒ b : the mark a entails the mark b.
--   trunc n ⇒ trunc n′ (n ≤ n′);  trunc n ⇒ grpd_k (k ≥ n + 1);
--   trunc n ⇒ ord, iord, lsplit, rsplit (n ≤ 1);
--   grpd_k ⇒ grpd_k′ (k ≤ k′);  grpd_k ⇒ iord (k ≤ 2);
--   ord ⇒ iord, lsplit, rsplit.
infix 4 _⊒_
_⊒_ : Mk → Mk → Bool
trunc t ⊒ trunc t′ = t ≤? t′
trunc t ⊒ grpd g   = t ≤? suc (suc g)
trunc t ⊒ iord     = t ≤? 3
trunc t ⊒ ord      = t ≤? 3
trunc t ⊒ lsplit   = t ≤? 3
trunc t ⊒ rsplit   = t ≤? 3
grpd g  ⊒ grpd g′  = g ≤? g′
grpd g  ⊒ iord     = g ≤? 1
grpd _  ⊒ trunc _  = false
grpd _  ⊒ ord      = false
grpd _  ⊒ lsplit   = false
grpd _  ⊒ rsplit   = false
ord     ⊒ iord     = true
ord     ⊒ ord      = true
ord     ⊒ lsplit   = true
ord     ⊒ rsplit   = true
ord     ⊒ trunc _  = false
ord     ⊒ grpd _   = false
iord    ⊒ iord     = true
iord    ⊒ _        = false
lsplit  ⊒ lsplit   = true
lsplit  ⊒ _        = false
rsplit  ⊒ rsplit   = true
rsplit  ⊒ _        = false

ent-refl : ∀ a → T (a ⊒ a)
ent-refl (trunc t) = ≤?-refl t
ent-refl (grpd g)  = ≤?-refl g
ent-refl iord      = tt
ent-refl ord       = tt
ent-refl lsplit    = tt
ent-refl rsplit    = tt

ent-trans : ∀ a b c → T (a ⊒ b) → T (b ⊒ c) → T (a ⊒ c)
-- b = trunc
ent-trans (trunc a) (trunc b) (trunc c) p q = ≤?-trans a b c p q
ent-trans (trunc a) (trunc b) (grpd c)  p q = ≤?-trans a b _ p q
ent-trans (trunc a) (trunc b) iord      p q = ≤?-trans a b 3 p q
ent-trans (trunc a) (trunc b) ord       p q = ≤?-trans a b 3 p q
ent-trans (trunc a) (trunc b) lsplit    p q = ≤?-trans a b 3 p q
ent-trans (trunc a) (trunc b) rsplit    p q = ≤?-trans a b 3 p q
ent-trans (grpd _)  (trunc _) _ () _
ent-trans iord      (trunc _) _ () _
ent-trans ord       (trunc _) _ () _
ent-trans lsplit    (trunc _) _ () _
ent-trans rsplit    (trunc _) _ () _
-- b = grpd
ent-trans (trunc a) (grpd b) (grpd c) p q = ≤?-trans a (suc (suc b)) (suc (suc c)) p q
ent-trans (trunc a) (grpd b) iord     p q = ≤?-trans a (suc (suc b)) 3 p q
ent-trans (grpd a)  (grpd b) (grpd c) p q = ≤?-trans a b c p q
ent-trans (grpd a)  (grpd b) iord     p q = ≤?-trans a b 1 p q
ent-trans _ (grpd _) (trunc _) _ ()
ent-trans _ (grpd _) ord       _ ()
ent-trans _ (grpd _) lsplit    _ ()
ent-trans _ (grpd _) rsplit    _ ()
ent-trans iord   (grpd _) _ () _
ent-trans ord    (grpd _) _ () _
ent-trans lsplit (grpd _) _ () _
ent-trans rsplit (grpd _) _ () _
-- b = ord
ent-trans (trunc a) ord iord   p q = p
ent-trans (trunc a) ord ord    p q = p
ent-trans (trunc a) ord lsplit p q = p
ent-trans (trunc a) ord rsplit p q = p
ent-trans ord       ord c      p q = q
ent-trans _ ord (trunc _) _ ()
ent-trans _ ord (grpd _)  _ ()
ent-trans (grpd _) ord _ () _
ent-trans iord     ord _ () _
ent-trans lsplit   ord _ () _
ent-trans rsplit   ord _ () _
-- b = iord, lsplit, rsplit
ent-trans a iord   iord   p q = p
ent-trans _ iord   (trunc _) _ ()
ent-trans _ iord   (grpd _)  _ ()
ent-trans _ iord   ord       _ ()
ent-trans _ iord   lsplit    _ ()
ent-trans _ iord   rsplit    _ ()
ent-trans a lsplit lsplit p q = p
ent-trans _ lsplit (trunc _) _ ()
ent-trans _ lsplit (grpd _)  _ ()
ent-trans _ lsplit iord      _ ()
ent-trans _ lsplit ord       _ ()
ent-trans _ lsplit rsplit    _ ()
ent-trans a rsplit rsplit p q = p
ent-trans _ rsplit (trunc _) _ ()
ent-trans _ rsplit (grpd _)  _ ()
ent-trans _ rsplit iord      _ ()
ent-trans _ rsplit ord       _ ()
ent-trans _ rsplit lsplit    _ ()

-- A declared mark list entails m if one of its atoms does.
has : List Mk → Mk → Bool
has []       m = false
has (a ∷ as) m = (a ⊒ m) ∨ has as m

has-up : ∀ xs a m → T (a ⊒ m) → T (has xs a) → T (has xs m)
has-up []       a m e ()
has-up (x ∷ xs) a m e p =
  ∨-elim (x ⊒ a) (has xs a)
    (λ q → ∨-introl (has xs m) (ent-trans x a m q e))
    (λ q → ∨-intror (x ⊒ m) (has-up xs a m e q))
    p

------------------------------------------------------------------------
-- Object terms (the formers that produce objects; parameters of μΔ are
-- object terms, X itself is bound and only its marks matter here).

data Ob : Set where
  var             : Nat → Ob
  top bot graph   : Ob                       -- ⊤, ⊥, ⟦Γ⟧ (finite graph, possibly localised)
  lim             : List Ob → Ob             -- lim_{Γ^μ}[γ], by its object vertices
  trO             : Nat → Ob → Ob            -- ‖A‖_n, with t = n + 2
  hom             : Ob → Ob                  -- Hom_C(a, b)
  cop             : Ob → Ob → Ob             -- A ⊔ B
  mu              : List Mk → List Ob → Bool → Ob
                    -- μΔ: the marks of X in Δ, the parameters, and whether
                    -- Δ has T-init's shape (no cell variables, sources from
                    -- coproducts, finite products and parameters)

-- The largest h-level n ≥ 0 whose `trunc n` entails m (t = n + 2), used by
-- T-init and T-coprod, which conclude `trunc n` only for n ≥ 0.
tlevel : Mk → Maybe Nat
tlevel (trunc zero)          = nothing
tlevel (trunc (suc zero))    = nothing
tlevel (trunc (suc (suc n))) = just (suc (suc n))
tlevel (grpd g)              = just (suc (suc g))
tlevel iord                  = just 3
tlevel ord                   = just 3
tlevel lsplit                = just 3
tlevel rsplit                = just 3

tle : Maybe Nat → Maybe Nat → Bool
tle nothing  _        = true
tle (just x) nothing  = false
tle (just x) (just y) = x ≤? y

tlevel-mono : ∀ a m → T (a ⊒ m) → T (tle (tlevel a) (tlevel m))
tlevel-mono (trunc zero)          m _ = tt
tlevel-mono (trunc (suc zero))    m _ = tt
tlevel-mono (trunc (suc (suc n))) (trunc zero)          ()
tlevel-mono (trunc (suc (suc n))) (trunc (suc zero))    ()
tlevel-mono (trunc (suc (suc n))) (trunc (suc (suc k))) p = p
tlevel-mono (trunc (suc (suc n))) (grpd g) p = p
tlevel-mono (trunc (suc (suc n))) iord     p = p
tlevel-mono (trunc (suc (suc n))) ord      p = p
tlevel-mono (trunc (suc (suc n))) lsplit   p = p
tlevel-mono (trunc (suc (suc n))) rsplit   p = p
tlevel-mono (grpd g) (grpd g′) p = p
tlevel-mono (grpd g) iord      p = p
tlevel-mono (grpd g) (trunc _) ()
tlevel-mono (grpd g) ord       ()
tlevel-mono (grpd g) lsplit    ()
tlevel-mono (grpd g) rsplit    ()
tlevel-mono ord iord      _ = tt
tlevel-mono ord ord       _ = tt
tlevel-mono ord lsplit    _ = tt
tlevel-mono ord rsplit    _ = tt
tlevel-mono ord (trunc _) ()
tlevel-mono ord (grpd _)  ()
tlevel-mono iord   m p with m
... | iord = tt
... | trunc _ = ⊥-elim p
... | grpd _  = ⊥-elim p
... | ord     = ⊥-elim p
... | lsplit  = ⊥-elim p
... | rsplit  = ⊥-elim p
tlevel-mono lsplit m p with m
... | lsplit = tt
... | trunc _ = ⊥-elim p
... | grpd _  = ⊥-elim p
... | ord     = ⊥-elim p
... | iord    = ⊥-elim p
... | rsplit  = ⊥-elim p
tlevel-mono rsplit m p with m
... | rsplit = tt
... | trunc _ = ⊥-elim p
... | grpd _  = ⊥-elim p
... | ord     = ⊥-elim p
... | iord    = ⊥-elim p
... | lsplit  = ⊥-elim p

tlevel-sound : ∀ m t → tlevel m ≡ just t → T (2 ≤? t) × T (trunc t ⊒ m)
tlevel-sound (trunc zero)          t ()
tlevel-sound (trunc (suc zero))    t ()
tlevel-sound (trunc (suc (suc n))) _ refl = tt , ≤?-refl n
tlevel-sound (grpd g) _ refl = tt , ≤?-refl g
tlevel-sound iord     _ refl = tt , tt
tlevel-sound ord      _ refl = tt , tt
tlevel-sound lsplit   _ refl = tt , tt
tlevel-sound rsplit   _ refl = tt , tt

-- The query a mark on Hom_C(a, b) makes of C (T-hom: cells into the hom
-- of level h are cells into C of level h + 1).
homQ : Mk → Mk
homQ (trunc t) = trunc (suc t)
homQ (grpd g)  = grpd (suc g)
homQ iord      = grpd 2          -- C grpd_3 ⇒ Hom grpd_2 ⇒ iord
homQ ord       = trunc 4         -- C trunc 2 ⇒ Hom trunc 1 ⇒ ord
homQ lsplit    = trunc 4
homQ rsplit    = trunc 4

homQ-mono : ∀ a m → T (a ⊒ m) → T (homQ a ⊒ homQ m)
homQ-mono (trunc t) (trunc _) p = p
homQ-mono (trunc t) (grpd _)  p = p
homQ-mono (trunc t) iord      p = p
homQ-mono (trunc t) ord       p = p
homQ-mono (trunc t) lsplit    p = p
homQ-mono (trunc t) rsplit    p = p
homQ-mono (grpd g) (grpd _)  p = p
homQ-mono (grpd g) iord      p = p
homQ-mono (grpd g) (trunc _) ()
homQ-mono (grpd g) ord       ()
homQ-mono (grpd g) lsplit    ()
homQ-mono (grpd g) rsplit    ()
homQ-mono ord iord      _ = tt
homQ-mono ord ord       _ = tt
homQ-mono ord lsplit    _ = tt
homQ-mono ord rsplit    _ = tt
homQ-mono ord (trunc _) ()
homQ-mono ord (grpd _)  ()
homQ-mono iord m p with m
... | iord = tt
... | trunc _ = ⊥-elim p
... | grpd _  = ⊥-elim p
... | ord     = ⊥-elim p
... | lsplit  = ⊥-elim p
... | rsplit  = ⊥-elim p
homQ-mono lsplit m p with m
... | lsplit = tt
... | trunc _ = ⊥-elim p
... | grpd _  = ⊥-elim p
... | ord     = ⊥-elim p
... | iord    = ⊥-elim p
... | rsplit  = ⊥-elim p
homQ-mono rsplit m p with m
... | rsplit = tt
... | trunc _ = ⊥-elim p
... | grpd _  = ⊥-elim p
... | ord     = ⊥-elim p
... | iord    = ⊥-elim p
... | lsplit  = ⊥-elim p

------------------------------------------------------------------------
-- The judgment Γ ⊢ C m, decidable by construction. ρ gives the declared
-- marks of the object variables.

Env : Set
Env = Nat → List Mk

mutual
  md : Env → Ob → Mk → Bool
  md ρ (var i)       m = has (ρ i) m                       -- (mark)
  md ρ top           m = trunc 0 ⊒ m                       -- T-unit
  md ρ bot           m = trunc 1 ⊒ m                       -- T-unit
  md ρ graph         m = trunc 3 ⊒ m                       -- T-graph, T-loc
  md ρ (lim vs)      m = mdAll ρ vs m                      -- (O-lim)
  md ρ (trO t A)     m = trunc t ⊒ m                       -- T-trunc
  md ρ (hom C)       m = md ρ C (homQ m)                   -- T-hom
  md ρ (cop A B)     m = mdCop ρ A B (tlevel m)            -- T-coprod
  md ρ (mu xs ps ok) m = has xs m ∨ (ok ∧ mdMu ρ ps (tlevel m))
                                                           -- (O-init), T-init

  mdAll : Env → List Ob → Mk → Bool
  mdAll ρ []       m = true
  mdAll ρ (v ∷ vs) m = md ρ v m ∧ mdAll ρ vs m

  mdCop : Env → Ob → Ob → Maybe Nat → Bool
  mdCop ρ A B nothing  = false
  mdCop ρ A B (just t) = md ρ A (trunc t) ∧ md ρ B (trunc t)

  mdMu : Env → List Ob → Maybe Nat → Bool
  mdMu ρ ps nothing  = false
  mdMu ρ ps (just t) = mdAll ρ ps (trunc t)

------------------------------------------------------------------------
-- Upward closure under entailment.

private
  ∧-map : ∀ {a a′ b b′} → (T a → T a′) → (T b → T b′) → T (a ∧ b) → T (a′ ∧ b′)
  ∧-map {true} {a′} f g p = ∧-intro {a′} (f tt) (g p)

  ∨-map : ∀ {a a′ b b′} → (T a → T a′) → (T b → T b′) → T (a ∨ b) → T (a′ ∨ b′)
  ∨-map {a} {a′} {b} {b′} f g p =
    ∨-elim a b (λ x → ∨-introl b′ (f x)) (λ y → ∨-intror a′ (g y)) p

mutual
  md-up : ∀ ρ t a m → T (a ⊒ m) → T (md ρ t a) → T (md ρ t m)
  md-up ρ (var i)       a m e p = has-up (ρ i) a m e p
  md-up ρ top           a m e p = ent-trans (trunc 0) a m p e
  md-up ρ bot           a m e p = ent-trans (trunc 1) a m p e
  md-up ρ graph         a m e p = ent-trans (trunc 3) a m p e
  md-up ρ (lim vs)      a m e p = mdAll-up ρ vs a m e p
  md-up ρ (trO t A)     a m e p = ent-trans (trunc t) a m p e
  md-up ρ (hom C)       a m e p = md-up ρ C (homQ a) (homQ m) (homQ-mono a m e) p
  md-up ρ (cop A B)     a m e p = mdCop-up ρ A B (tlevel a) (tlevel m) (tlevel-mono a m e) p
  md-up ρ (mu xs ps ok) a m e p =
    ∨-map {has xs a} {has xs m} (has-up xs a m e)
      (∧-map {ok} {ok} (λ x → x) (mdMu-up ρ ps (tlevel a) (tlevel m) (tlevel-mono a m e)))
      p

  mdAll-up : ∀ ρ vs a m → T (a ⊒ m) → T (mdAll ρ vs a) → T (mdAll ρ vs m)
  mdAll-up ρ []       a m e p = tt
  mdAll-up ρ (v ∷ vs) a m e p =
    ∧-map {md ρ v a} {md ρ v m} (md-up ρ v a m e) (mdAll-up ρ vs a m e) p

  mdCop-up : ∀ ρ A B x y → T (tle x y) → T (mdCop ρ A B x) → T (mdCop ρ A B y)
  mdCop-up ρ A B nothing  y        _ ()
  mdCop-up ρ A B (just s) nothing  () _
  mdCop-up ρ A B (just s) (just t) l p =
    ∧-map {md ρ A (trunc s)} {md ρ A (trunc t)}
      (md-up ρ A (trunc s) (trunc t) l) (md-up ρ B (trunc s) (trunc t) l) p

  mdMu-up : ∀ ρ ps x y → T (tle x y) → T (mdMu ρ ps x) → T (mdMu ρ ps y)
  mdMu-up ρ ps nothing  y        _ ()
  mdMu-up ρ ps (just s) nothing  () _
  mdMu-up ρ ps (just s) (just t) l p = mdAll-up ρ ps (trunc s) (trunc t) l p

------------------------------------------------------------------------
-- Substitution. A substitution σ certifies the declared marks if every
-- declared atom of variable i is derivable for σ i; then every derived
-- mark survives. Object variables may now be sent to any object term.

mutual
  sub : (Nat → Ob) → Ob → Ob
  sub σ (var i)       = σ i
  sub σ top           = top
  sub σ bot           = bot
  sub σ graph         = graph
  sub σ (lim vs)      = lim (subAll σ vs)
  sub σ (trO t A)     = trO t (sub σ A)
  sub σ (hom C)       = hom (sub σ C)
  sub σ (cop A B)     = cop (sub σ A) (sub σ B)
  sub σ (mu xs ps ok) = mu xs (subAll σ ps) ok

  subAll : (Nat → Ob) → List Ob → List Ob
  subAll σ []       = []
  subAll σ (v ∷ vs) = sub σ v ∷ subAll σ vs

Cert : Env → Env → (Nat → Ob) → Set
Cert ρ ρ′ σ = ∀ i → T (all (λ a → md ρ′ (σ i) a) (ρ i))

has-cert : ∀ ρ′ t xs m → T (all (λ a → md ρ′ t a) xs) → T (has xs m) → T (md ρ′ t m)
has-cert ρ′ t []       m _ ()
has-cert ρ′ t (x ∷ xs) m c p =
  ∨-elim (x ⊒ m) (has xs m)
    (λ e → md-up ρ′ t x m e (fstT (md ρ′ t x) c))
    (has-cert ρ′ t xs m (sndT (md ρ′ t x) c))
    p

mutual
  md-subst : ∀ ρ ρ′ σ → Cert ρ ρ′ σ → ∀ t m → T (md ρ t m) → T (md ρ′ (sub σ t) m)
  md-subst ρ ρ′ σ c (var i)       m p = has-cert ρ′ (σ i) (ρ i) m (c i) p
  md-subst ρ ρ′ σ c top           m p = p
  md-subst ρ ρ′ σ c bot           m p = p
  md-subst ρ ρ′ σ c graph         m p = p
  md-subst ρ ρ′ σ c (lim vs)      m p = mdAll-subst ρ ρ′ σ c vs m p
  md-subst ρ ρ′ σ c (trO t A)     m p = p
  md-subst ρ ρ′ σ c (hom C)       m p = md-subst ρ ρ′ σ c C (homQ m) p
  md-subst ρ ρ′ σ c (cop A B)     m p = mdCop-subst ρ ρ′ σ c A B (tlevel m) p
  md-subst ρ ρ′ σ c (mu xs ps ok) m p =
    ∨-map {has xs m} {has xs m} (λ x → x)
      (∧-map {ok} {ok} (λ x → x) (mdMu-subst ρ ρ′ σ c ps (tlevel m))) p

  mdAll-subst : ∀ ρ ρ′ σ → Cert ρ ρ′ σ → ∀ vs m → T (mdAll ρ vs m) → T (mdAll ρ′ (subAll σ vs) m)
  mdAll-subst ρ ρ′ σ c []       m p = tt
  mdAll-subst ρ ρ′ σ c (v ∷ vs) m p =
    ∧-map {md ρ v m} {md ρ′ (sub σ v) m}
      (md-subst ρ ρ′ σ c v m) (mdAll-subst ρ ρ′ σ c vs m) p

  mdCop-subst : ∀ ρ ρ′ σ → Cert ρ ρ′ σ → ∀ A B x → T (mdCop ρ A B x) →
                T (mdCop ρ′ (sub σ A) (sub σ B) x)
  mdCop-subst ρ ρ′ σ c A B nothing  ()
  mdCop-subst ρ ρ′ σ c A B (just t) p =
    ∧-map {md ρ A (trunc t)} {md ρ′ (sub σ A) (trunc t)}
      (md-subst ρ ρ′ σ c A (trunc t)) (md-subst ρ ρ′ σ c B (trunc t)) p

  mdMu-subst : ∀ ρ ρ′ σ → Cert ρ ρ′ σ → ∀ ps x → T (mdMu ρ ps x) → T (mdMu ρ′ (subAll σ ps) x)
  mdMu-subst ρ ρ′ σ c ps nothing  ()
  mdMu-subst ρ ρ′ σ c ps (just t) p = mdAll-subst ρ ρ′ σ c ps (trunc t) p

------------------------------------------------------------------------
-- Semantics: strict models. `IdAt C j` says that every cell of level
-- j − 1 (hom-dimension j − 1) into C, in every hom 𝒦(X, C), is an
-- identity; `InvAt C j` that every such cell is invertible. Level −1 is
-- the hom itself, so `IdAt C 0` is contractibility of the homs.

record Base : Set₁ where
  field
    Obj                : Set
    IdAt InvAt         : Obj → Nat → Set
    InnId InnInv LS RS : Obj → Set
    id⇒inv     : ∀ C j → IdAt C j → InvAt C j
    -- every inner letter into C has hom-dimension ≥ 2 (notes §3, Lemma 3.1)
    inner-id   : ∀ C → (∀ j → T (3 ≤? j) → IdAt C j)  → InnId C
    inner-inv  : ∀ C → (∀ j → T (3 ≤? j) → InvAt C j) → InnInv C
    innId⇒inv  : ∀ C → InnId C → InnInv C
    innId⇒ls   : ∀ C → InnId C → LS C
    innId⇒rs   : ∀ C → InnId C → RS C

module Semantics (B : Base) where
  open Base B

  Holds : Obj → Mk → Set
  Holds C (trunc t) = ∀ j → T (t ≤? j) → IdAt C j
  Holds C (grpd g)  = ∀ j → T (suc (suc g) ≤? j) → InvAt C j
  Holds C iord      = InnInv C
  Holds C ord       = InnId C
  Holds C lsplit    = LS C
  Holds C rsplit    = RS C

  ent-sound : ∀ C a b → T (a ⊒ b) → Holds C a → Holds C b
  ent-sound C (trunc t) (trunc t′) p h = λ j q → h j (≤?-trans t t′ j p q)
  ent-sound C (trunc t) (grpd g)   p h =
    λ j q → id⇒inv C j (h j (≤?-trans t (suc (suc g)) j p q))
  ent-sound C (trunc t) ord    p h = inner-id C (λ j q → h j (≤?-trans t 3 j p q))
  ent-sound C (trunc t) iord   p h = innId⇒inv C (ent-sound C (trunc t) ord p h)
  ent-sound C (trunc t) lsplit p h = innId⇒ls C (ent-sound C (trunc t) ord p h)
  ent-sound C (trunc t) rsplit p h = innId⇒rs C (ent-sound C (trunc t) ord p h)
  ent-sound C (grpd g) (grpd g′) p h = λ j q → h j (≤?-trans (suc (suc g)) (suc (suc g′)) j p q)
  ent-sound C (grpd g) iord      p h = inner-inv C (λ j q → h j (≤?-trans (suc (suc g)) 3 j p q))
  ent-sound C (grpd g) (trunc _) ()
  ent-sound C (grpd g) ord       ()
  ent-sound C (grpd g) lsplit    ()
  ent-sound C (grpd g) rsplit    ()
  ent-sound C ord iord      _ h = innId⇒inv C h
  ent-sound C ord ord       _ h = h
  ent-sound C ord lsplit    _ h = innId⇒ls C h
  ent-sound C ord rsplit    _ h = innId⇒rs C h
  ent-sound C ord (trunc _) ()
  ent-sound C ord (grpd _)  ()
  ent-sound C iord m p h with m
  ... | iord    = h
  ... | trunc _ = ⊥-elim p
  ... | grpd _  = ⊥-elim p
  ... | ord     = ⊥-elim p
  ... | lsplit  = ⊥-elim p
  ... | rsplit  = ⊥-elim p
  ent-sound C lsplit m p h with m
  ... | lsplit  = h
  ... | trunc _ = ⊥-elim p
  ... | grpd _  = ⊥-elim p
  ... | ord     = ⊥-elim p
  ... | iord    = ⊥-elim p
  ... | rsplit  = ⊥-elim p
  ent-sound C rsplit m p h with m
  ... | rsplit  = h
  ... | trunc _ = ⊥-elim p
  ... | grpd _  = ⊥-elim p
  ... | ord     = ⊥-elim p
  ... | iord    = ⊥-elim p
  ... | lsplit  = ⊥-elim p

  AllH : Obj → List Mk → Set
  AllH C []       = ⊤
  AllH C (a ∷ as) = Holds C a × AllH C as

  has-sound : ∀ C xs m → AllH C xs → T (has xs m) → Holds C m
  has-sound C []       m _        ()
  has-sound C (x ∷ xs) m (h , hs) p =
    ∨-elim (x ⊒ m) (has xs m) (λ e → ent-sound C x m e h) (has-sound C xs m hs) p

  AllO : List Obj → (Obj → Set) → Set
  AllO []       P = ⊤
  AllO (v ∷ vs) P = P v × AllO vs P

  AllO-map : ∀ vs {P Q : Obj → Set} → (∀ v → P v → Q v) → AllO vs P → AllO vs Q
  AllO-map []       f _        = tt
  AllO-map (v ∷ vs) f (p , ps) = f v p , AllO-map vs f ps

-- The per-former facts, in the strict reading (notes/object-marks.md §3).
record Formers (B : Base) : Set₁ where
  open Base B
  open Semantics B
  field
    ⊤ₘ ⊥ₘ grₘ : Obj
    limₘ      : List Obj → Obj
    trₘ       : Nat → Obj → Obj
    homₘ      : Obj → Obj
    copₘ      : Obj → Obj → Obj
    muₘ       : List Mk → List Obj → Bool → Obj
    ⊤-id      : ∀ j → IdAt ⊤ₘ j                                    -- ⊤ trunc −2
    ⊥-id      : ∀ j → T (1 ≤? j) → IdAt ⊥ₘ j                       -- ⊥ trunc −1
    gr-id     : ∀ j → T (3 ≤? j) → IdAt grₘ j                      -- T-graph, T-loc
    tr-id     : ∀ t A j → T (t ≤? j) → IdAt (trₘ t A) j            -- T-trunc
    hom-id    : ∀ C j → IdAt C (suc j)  → IdAt (homₘ C) j          -- T-hom
    hom-inv   : ∀ C j → InvAt C (suc j) → InvAt (homₘ C) j
    lim-id    : ∀ vs j → AllO vs (λ v → IdAt v j)  → IdAt (limₘ vs) j    -- T-lim
    lim-inv   : ∀ vs j → AllO vs (λ v → InvAt v j) → InvAt (limₘ vs) j
    lim-innId  : ∀ vs → AllO vs InnId  → InnId (limₘ vs)            -- (PW)
    lim-innInv : ∀ vs → AllO vs InnInv → InnInv (limₘ vs)           -- (PW)
    lim-ls     : ∀ vs → AllO vs LS → LS (limₘ vs)                   -- (PW)
    lim-rs     : ∀ vs → AllO vs RS → RS (limₘ vs)                   -- (PW)
    cop-tr    : ∀ A B t → T (2 ≤? t) → Holds A (trunc t) → Holds B (trunc t) →
                Holds (copₘ A B) (trunc t)                           -- T-coprod
    mu-decl   : ∀ xs ps ok → AllH (muₘ xs ps ok) xs                  -- (O-init)
    mu-tinit  : ∀ xs ps ok t → T ok → T (2 ≤? t) →
                AllO ps (λ p → Holds p (trunc t)) → Holds (muₘ xs ps ok) (trunc t)  -- T-init

module Soundness (B : Base) (F : Formers B) where
  open Base B
  open Semantics B
  open Formers F

  mutual
    ⟦_⟧ : Ob → (Nat → Obj) → Obj
    ⟦ var i ⟧       η = η i
    ⟦ top ⟧         η = ⊤ₘ
    ⟦ bot ⟧         η = ⊥ₘ
    ⟦ graph ⟧       η = grₘ
    ⟦ lim vs ⟧      η = limₘ (⟦ vs ⟧* η)
    ⟦ trO t A ⟧     η = trₘ t (⟦ A ⟧ η)
    ⟦ hom C ⟧       η = homₘ (⟦ C ⟧ η)
    ⟦ cop A B ⟧     η = copₘ (⟦ A ⟧ η) (⟦ B ⟧ η)
    ⟦ mu xs ps ok ⟧ η = muₘ xs (⟦ ps ⟧* η) ok

    ⟦_⟧* : List Ob → (Nat → Obj) → List Obj
    ⟦ [] ⟧*     η = []
    ⟦ v ∷ vs ⟧* η = ⟦ v ⟧ η ∷ ⟦ vs ⟧* η

  lim-holds : ∀ vs m → AllO vs (λ v → Holds v m) → Holds (limₘ vs) m
  lim-holds vs (trunc t) h = λ j q → lim-id vs j (AllO-map vs (λ v hv → hv j q) h)
  lim-holds vs (grpd g)  h = λ j q → lim-inv vs j (AllO-map vs (λ v hv → hv j q) h)
  lim-holds vs iord      h = lim-innInv vs h
  lim-holds vs ord       h = lim-innId vs h
  lim-holds vs lsplit    h = lim-ls vs h
  lim-holds vs rsplit    h = lim-rs vs h

  hom-holds : ∀ C m → Holds C (homQ m) → Holds (homₘ C) m
  hom-holds C (trunc t) h = λ j q → hom-id C j (h (suc j) q)
  hom-holds C (grpd g)  h = λ j q → hom-inv C j (h (suc j) q)
  hom-holds C iord      h = ent-sound (homₘ C) (grpd 1) iord tt (hom-holds C (grpd 1) h)
  hom-holds C ord       h = ent-sound (homₘ C) (trunc 3) ord tt (hom-holds C (trunc 3) h)
  hom-holds C lsplit    h = ent-sound (homₘ C) (trunc 3) lsplit tt (hom-holds C (trunc 3) h)
  hom-holds C rsplit    h = ent-sound (homₘ C) (trunc 3) rsplit tt (hom-holds C (trunc 3) h)

  module _ (ρ : Env) (η : Nat → Obj) (ok : ∀ i → AllH (η i) (ρ i)) where
    mutual
      sound : ∀ t m → T (md ρ t m) → Holds (⟦ t ⟧ η) m
      sound (var i)  m p = has-sound (η i) (ρ i) m (ok i) p
      sound top      m p = ent-sound ⊤ₘ (trunc 0) m p (λ j _ → ⊤-id j)
      sound bot      m p = ent-sound ⊥ₘ (trunc 1) m p (λ j q → ⊥-id j q)
      sound graph    m p = ent-sound grₘ (trunc 3) m p (λ j q → gr-id j q)
      sound (lim vs) m p = lim-holds (⟦ vs ⟧* η) m (soundAll vs m p)
      sound (trO t A) m p =
        ent-sound (trₘ t (⟦ A ⟧ η)) (trunc t) m p (λ j q → tr-id t (⟦ A ⟧ η) j q)
      sound (hom C)  m p = hom-holds (⟦ C ⟧ η) m (sound C (homQ m) p)
      sound (cop A B) m p = soundCop A B m (tlevel m) refl p
      sound (mu xs ps ok′) m p =
        ∨-elim (has xs m) (ok′ ∧ mdMu ρ ps (tlevel m))
          (has-sound (muₘ xs (⟦ ps ⟧* η) ok′) xs m (mu-decl xs (⟦ ps ⟧* η) ok′))
          (λ q → soundMu xs ps ok′ m (tlevel m) refl (fstT ok′ q) (sndT ok′ q))
          p

      soundAll : ∀ vs m → T (mdAll ρ vs m) → AllO (⟦ vs ⟧* η) (λ v → Holds v m)
      soundAll []       m _ = tt
      soundAll (v ∷ vs) m p =
        sound v m (fstT (md ρ v m) p) , soundAll vs m (sndT (md ρ v m) p)

      soundCop : ∀ A B m x → tlevel m ≡ x → T (mdCop ρ A B x) → Holds (⟦ cop A B ⟧ η) m
      soundCop A B m nothing  _ ()
      soundCop A B m (just t) e p =
        ent-sound (copₘ (⟦ A ⟧ η) (⟦ B ⟧ η)) (trunc t) m (snd (tlevel-sound m t e))
          (cop-tr (⟦ A ⟧ η) (⟦ B ⟧ η) t (fst (tlevel-sound m t e))
             (sound A (trunc t) (fstT (md ρ A (trunc t)) p))
             (sound B (trunc t) (sndT (md ρ A (trunc t)) p)))

      soundMu : ∀ xs ps ok′ m x → tlevel m ≡ x → T ok′ → T (mdMu ρ ps x) →
                Holds (⟦ mu xs ps ok′ ⟧ η) m
      soundMu xs ps ok′ m nothing  _ _ ()
      soundMu xs ps ok′ m (just t) e o p =
        ent-sound (muₘ xs (⟦ ps ⟧* η) ok′) (trunc t) m (snd (tlevel-sound m t e))
          (mu-tinit xs (⟦ ps ⟧* η) ok′ t o (fst (tlevel-sound m t e)) (soundAll ps (trunc t) p))

------------------------------------------------------------------------
-- Examples, by evaluation. Variable 0 is a parameter A with no marks,
-- variable 1 a groupoid G, variable 2 an object C marked trunc 2.

private
  ρ₀ : Env
  ρ₀ zero                = []
  ρ₀ (suc zero)          = grpd 0 ∷ []          -- G grpd_1
  ρ₀ (suc (suc zero))    = trunc 4 ∷ []         -- C trunc 2
  ρ₀ (suc (suc (suc _))) = ord ∷ []

ℕ ℤ Two S¹ : Ob
ℕ    = mu [] [] true                 -- μ(X, z : ⊤ → X, s : X → X)
ℤ    = mu [] [] true                 -- μ(X, z, s inv by bi-invertibility data)
Two  = cop top top
S¹   = mu (grpd 0 ∷ []) [] false     -- μ(X : grpd, b, l : b → b)

ℕ-ord     : md ρ₀ ℕ ord ≡ true
ℕ-ord     = refl
ℕ-grpd₁   : md ρ₀ ℕ (grpd 0) ≡ true
ℕ-grpd₁   = refl
Two-ord   : md ρ₀ Two ord ≡ true
Two-ord   = refl
‖A‖₀-ord  : md ρ₀ (trO 2 (var 0)) ord ≡ true
‖A‖₀-ord  = refl
‖A‖₁-ord  : md ρ₀ (trO 3 (var 0)) ord ≡ true
‖A‖₁-ord  = refl
‖A‖₂-ord  : md ρ₀ (trO 4 (var 0)) ord ≡ false        -- not derivable
‖A‖₂-ord  = refl
graph-ord : md ρ₀ graph ord ≡ true
graph-ord = refl
S¹-grpd   : md ρ₀ S¹ (grpd 0) ≡ true                  -- read off Δ
S¹-grpd   = refl
S¹-iord   : md ρ₀ S¹ iord ≡ true
S¹-iord   = refl
S¹-ord    : md ρ₀ S¹ ord ≡ false
S¹-ord    = refl
G-iord    : md ρ₀ (var 1) iord ≡ true                 -- grpd_1 ⇒ iord
G-iord    = refl
G-ord     : md ρ₀ (var 1) ord ≡ false
G-ord     = refl
homC-ord  : md ρ₀ (hom (var 2)) ord ≡ true            -- C trunc 2 ⇒ Hom trunc 1
homC-ord  = refl
C-ord     : md ρ₀ (var 2) ord ≡ false
C-ord     = refl
lim-ord   : md ρ₀ (lim (ℕ ∷ hom (var 2) ∷ [])) ord ≡ true
lim-ord   = refl
lim-ord′  : md ρ₀ (lim (ℕ ∷ var 1 ∷ [])) ord ≡ false
lim-ord′  = refl
ℕA-trunc  : md ρ₀ (mu [] (var 0 ∷ []) true) (trunc 2) ≡ false   -- A unmarked
ℕA-trunc  = refl

-- A lemma over (C : ⋆)^ord applies to ℕ: σ sends its variable to ℕ, and
-- certifies the declaration.
private
  ρL : Env
  ρL _ = ord ∷ []

  σℕ : Nat → Ob
  σℕ _ = ℕ

cert-ℕ : Cert ρL ρ₀ σℕ
cert-ℕ _ = tt

lemma-at-ℕ : T (md ρ₀ (sub σℕ (var 0)) lsplit)
lemma-at-ℕ = md-subst ρL ρ₀ σℕ cert-ℕ (var 0) lsplit tt
