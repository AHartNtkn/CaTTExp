------------------------------------------------------------------------
-- D7g (notes/free-objects-proofs.md, Theorem D7g; open-issues D7g):
-- for every canonical row ρ, every gap g of H and every k ≥ 0, in the
-- generic context of the directed template tmpl ρ g dir (suc k) no
-- term of the kernel, of any shape, has the reversed goal type
-- u⁺ ⇒ u⁻ (Examples.reverseTop of the cell goal).
--
-- Proof: interpret the kernel in the poset model (PosetModel.agda),
-- which is sound by Theorem S (Soundness.agda), with the generic
-- context sent to a tower of monotone maps (DirEnv.agda):
--   uv α j : (pre, ⟦Dʲ⟧, post ▸ Z),  (…, d, …) ↦ e(lohi α j d)
-- where e : Bool → ⟦Z⟧ is a strict monotone embedding (Z is an object
-- variable or a closure into one, as in every canonical row), lohi
-- false j d says "d is above the interior of ⟦Dʲ⟧" and lohi true j d
-- "d is not below it".  A reverse cell x would have x∘δ⁻ = uv true k
-- and x∘δ⁺ = uv false k; at the interior, monotonicity of x in its
-- ⟦Dᵏ⁺¹⟧ argument gives e(true) ≤ e(false), which fails.
-- This is the formal side of D7g, under Theorem S's reading of inv as
-- flat (open-issues C5b).  No postulates.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.D7g where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.Gray.Biclosed.Rows
open import CaTTExp.Gray.Biclosed.ListLemmas
open import CaTTExp.Gray.Biclosed.Typing using (infer)
open import CaTTExp.Gray.Biclosed.Examples using (reverseTop)
open import CaTTExp.Gray.Biclosed.Model using (D; dsrc)
open import CaTTExp.Gray.Biclosed.Poset
open import CaTTExp.Gray.Biclosed.PosetModel
open import CaTTExp.Gray.Biclosed.RowSem posetModel using (CellAt; cellAt)
open import CaTTExp.Gray.Biclosed.DirEnv posetModel using (module Env)

------------------------------------------------------------------------
-- Strict embeddings of the two-element chain

bleq : Bool → Bool → Bool
bleq a b = not a ∨ b

ntC : Code → Bool
ntC (cnat b)    = leq 1 b
ntC (cpair a b) = ntC a
ntC (ctab a c)  = ntC c

embC : Code → Bool → U
embC (cnat b)    β = nat (if β then 1 else 0)
embC (cpair a b) β = pr (embC a β) (defC b)
embC (ctab a c)  β = tabF a (λ _ → embC c β)

emb-In : ∀ c β → T (ntC c) → In c (embC c β)
emb-In (cnat b)    true  h = h
emb-In (cnat b)    false h = tt
emb-In (cpair a b) β     h = ∧I (emb-In a β h) (inC-def b)
emb-In (ctab a c)  β     h =
  tabF-In a c (λ _ → embC c β) (λ _ _ → emb-In c β h) (λ _ _ _ _ _ → leC-refl c _ (emb-In c β h))

emb-mono : ∀ c β β′ → T (ntC c) → T (bleq β β′) → Le c (embC c β) (embC c β′)
emb-mono (cnat b)    false β′    h l = tt
emb-mono (cnat b)    true  true  h l = tt
emb-mono (cpair a b) β     β′    h l = ∧I (emb-mono a β β′ h l) (leC-refl b (defC b) (inC-def b))
emb-mono (ctab a c)  β     β′    h l = tabF-le a c _ _ (λ _ _ → emb-mono c β β′ h l)

private
  allZ-const : ∀ (r : U → U → Bool) u v {x : U} (es : List U) → x ∈ es →
               T (allZ r (map (λ _ → u) es) (map (λ _ → v) es)) → T (r u v)
  allZ-const r u v (e ∷ es) hd     q = ∧-fst q
  allZ-const r u v (e ∷ es) (tl m) q = allZ-const r u v es m (∧-snd {r u v} q)

emb-strict : ∀ c → T (ntC c) → Le c (embC c true) (embC c false) → ⊥
emb-strict (cnat b)    h ()
emb-strict (cpair a b) h l = emb-strict a h (∧-fst l)
emb-strict (ctab a c)  h l =
  emb-strict c h (allZ-const (leC c) _ _ (els a) (els-complete a (defC a) (inC-def a)) l)

-- the output of H is nontrivial in a canonical row
isObj-nt : ∀ Z → T (isObj Z) → T (ntC (fmC Z))
isObj-nt (obj _) _ = tt

canon-nt : ∀ ρ → T (canon ρ) → T (ntC (fmC (out (H ρ))))
canon-nt (pairR L U V R Z)  c = isObj-nt Z (∧-snd {canonFrom 0 (fmsOf (pairR L U V R Z))} c)
canon-nt (probeR L Δ Θ R Z) c = isObj-nt Z (∧-snd {canonFrom 0 (fmsOf (probeR L Δ Θ R Z))} c)
canon-nt (unitR L R Z)      c = isObj-nt Z (∧-snd {canonFrom 0 (fmsOf (unitR L R Z))} c)
canon-nt (evLR Φ A C)       c = isObj-nt C (∧-snd {canonFrom 0 (fmsOf (evLR Φ A C))} c)
canon-nt (evRR Φ A C)       c = isObj-nt C (∧-snd {canonFrom 0 (fmsOf (evRR Φ A C))} c)

------------------------------------------------------------------------
-- Where a point of ⟦Dʲ⟧ lies relative to the interior j

data Side : Set where
  Bl Ce Ab : Side

side : Nat → Nat → Side
side zero    zero    = Ce
side zero    (suc p) = Ab
side (suc j) zero    = Bl
side (suc j) (suc p) = side j p

rank : Side → Nat
rank Bl = 0
rank Ce = 1
rank Ab = 2

valS : Bool → Side → Bool
valS false Ab = true
valS false _  = false
valS true  Bl = false
valS true  _  = true

lohi : Bool → Nat → Nat → Bool
lohi α zero    p = α
lohi α (suc j) p = valS α (side (suc j) p)

shiftS : Bool → Side → Side
shiftS β Bl = Bl
shiftS β Ce = if β then Ab else Bl
shiftS β Ab = Ab

side-dl : ∀ β j p → side (suc j) (dl β j p) ≡ shiftS β (side j p)
side-dl true  zero    zero    = refl
side-dl false zero    zero    = refl
side-dl β     zero    (suc p) = refl
side-dl β     (suc j) zero    = refl
side-dl β     (suc j) (suc p) = side-dl β j p

valS-shift : ∀ α β s → valS α (shiftS β s) ≡ valS β s
valS-shift false false Bl = refl
valS-shift false false Ce = refl
valS-shift false false Ab = refl
valS-shift false true  Bl = refl
valS-shift false true  Ce = refl
valS-shift false true  Ab = refl
valS-shift true  false Bl = refl
valS-shift true  false Ce = refl
valS-shift true  false Ab = refl
valS-shift true  true  Bl = refl
valS-shift true  true  Ce = refl
valS-shift true  true  Ab = refl

-- the faces of the tower
lohi-face : ∀ α β j p → lohi α (suc (suc j)) (dl β (suc j) p) ≡ lohi β (suc j) p
lohi-face α β j p = trans (cong (valS α) (side-dl β (suc j) p)) (valS-shift α β (side (suc j) p))

lohi-face0 : ∀ α β → lohi α 1 (dl β 0 0) ≡ β
lohi-face0 false true  = refl
lohi-face0 true  true  = refl
lohi-face0 false false = refl
lohi-face0 true  false = refl

side-mono : ∀ j p q → T (leq p q) → T (leq (rank (side j p)) (rank (side j q)))
side-mono zero    zero    zero    _ = tt
side-mono zero    zero    (suc q) _ = tt
side-mono zero    (suc p) zero    ()
side-mono zero    (suc p) (suc q) _ = tt
side-mono (suc j) zero    q       _ = tt
side-mono (suc j) (suc p) zero    ()
side-mono (suc j) (suc p) (suc q) h = side-mono j p q h

valS-mono : ∀ α s s′ → T (leq (rank s) (rank s′)) → T (bleq (valS α s) (valS α s′))
valS-mono false Bl s′ _ = tt
valS-mono false Ce s′ _ = tt
valS-mono false Ab Bl ()
valS-mono false Ab Ce ()
valS-mono false Ab Ab _ = tt
valS-mono true  Bl s′ _ = tt
valS-mono true  Ce Bl ()
valS-mono true  Ce Ce _ = tt
valS-mono true  Ce Ab _ = tt
valS-mono true  Ab Bl ()
valS-mono true  Ab Ce _ = tt
valS-mono true  Ab Ab _ = tt

bleq-refl : ∀ a → T (bleq a a)
bleq-refl true  = tt
bleq-refl false = tt

lohi-mono : ∀ α j p q → T (leq p q) → T (bleq (lohi α j p) (lohi α j q))
lohi-mono α zero    p q h = bleq-refl α
lohi-mono α (suc j) p q h = valS-mono α (side (suc j) p) (side (suc j) q) (side-mono (suc j) p q h)

side-diag : ∀ j → side j j ≡ Ce
side-diag zero    = refl
side-diag (suc j) = side-diag j

valS-Ce : ∀ α → valS α Ce ≡ α
valS-Ce true  = refl
valS-Ce false = refl

------------------------------------------------------------------------
-- The tower, for a row ρ and a gap g

-- the input in ⟦Dᵏ⟧ at the interior (nothing at k = 0)
dsK : Nat → List U
dsK zero    = []
dsK (suc m) = nat (suc m) ∷ []

dsK-In : ∀ k → InL (dsrc k) (dsK k)
dsK-In zero    = []
dsK-In (suc m) = leq-wk m (dbl m) (leq-dbl m) ∷ []

lohi-ctr : ∀ α k cs → lohi α k (unNat (hdU (dsK k ++ cs))) ≡ α
lohi-ctr α zero    cs = refl
lohi-ctr α (suc m) cs = trans (cong (valS α) (side-diag m)) (valS-Ce α)

defL : List Fm → List U
defL = map (λ F → defC (fmC F))

defL-In : ∀ Fs → InL Fs (defL Fs)
defL-In []       = []
defL-In (F ∷ Fs) = inC-def (fmC F) ∷ defL-In Fs

module Tower (ρ : Row) (g : Nat) (bd : T (leq g (length (ins (H ρ))))) (nt : T (ntC (fmC (out (H ρ))))) where

  pre post : List Fm
  pre  = take g (ins (H ρ))
  post = drop g (ins (H ρ))
  Z : Fm
  Z = out (H ρ)

  lp : length pre ≡ g
  lp = length-take g (ins (H ρ)) bd

  e : Code
  e = fmC Z

  uv : Bool → Nat → Val
  uv α j = mk ((pre ++ dsrc j ++ post) ▸ Z) (λ us → embC e (lohi α j (unNat (hdU (drop g us)))))

  -- reading the time slot of a typed input
  slot : ∀ {as ds cs} → InL pre as → drop g (as ++ ds ++ cs) ≡ ds ++ cs
  slot {as} {ds} {cs} ia = subst (λ i → drop i (as ++ ds ++ cs) ≡ ds ++ cs) (trans (InL-len ia) lp) (drop-len as (ds ++ cs))

  T-uv : ∀ α j → uv α j ∶ᵥ ((pre ++ dsrc j ++ post) ▸ Z)
  T-uv α j = tyRaw (uv α j) refl (λ _ → emb-In e _ nt) mono
    where
    mono : ∀ {ws vs} → InL (pre ++ dsrc j ++ post) ws → InL (pre ++ dsrc j ++ post) vs →
           LeL (pre ++ dsrc j ++ post) ws vs → LF Z (raw (uv α j) ws) (raw (uv α j) vs)
    mono q q′ l with InL-split3 pre (dsrc j) post q | InL-split3 pre (dsrc j) post q′
    ... | sp3 a d c refl ia id ic | sp3 a′ d′ c′ refl ia′ id′ ic′ =
      subst₂′ (LF Z) (sym (cong rd (slot {ds = d} {cs = c} ia))) (sym (cong rd (slot {ds = d′} {cs = c′} ia′)))
        (emb-mono e _ _ nt (go j c c′ id id′ (fst (LeL-split id id′ (snd (LeL-split ia ia′ l))))))
      where
      rd : List U → U
      rd z = embC e (lohi α j (unNat (hdU z)))
      go : ∀ j {d d′} c c′ → InL (dsrc j) d → InL (dsrc j) d′ → LeL (dsrc j) d d′ →
           T (bleq (lohi α j (unNat (hdU (d ++ c)))) (lohi α j (unNat (hdU (d′ ++ c′)))))
      go zero    c c′ [] [] [] = bleq-refl α
      go (suc j) {u ∷ []} {u′ ∷ []} c c′ (qu ∷ []) (qu′ ∷ []) (lu ∷ []) with inC-nat _ u qu | inC-nat _ u′ qu′
      ... | p , refl , _ | p′ , refl , _ = lohi-mono α (suc j) p p′ lu

  uc : ∀ α j → CellAt j g (H ρ) (uv α j)
  uc α j = cellAt pre post (take-drop g (ins (H ρ))) lp (T-uv α j)

  uf : ∀ α β j → pcV (uv α (suc j)) g (δV β j) ≈ᵥ uv β j
  uf α β j = ≈-intro (trans (tprof tL) (sym (tprof (T-uv β j)))) fn
    where
    tL = T-pcV′ {P = pre} {Y = D (suc j)} {Q = post} (T-uv α (suc j)) (T-δV β j) (sym lp)
    fn : ∀ ws → InL (ins (prof (pcV (uv α (suc j)) g (δV β j)))) ws →
         ap (pcV (uv α (suc j)) g (δV β j)) ws ≡ ap (uv β j) ws
    fn ws q with InL-split3 pre (dsrc j) post (subst (λ M → InL (ins M) ws) (tprof tL) q)
    ... | sp3 a d c refl ia id ic =
      trans (evPC {P = pre} {Y = D (suc j)} {Q = post} (T-uv α (suc j)) (T-δV β j) (sym lp) ia id ic)
      (trans (ap-ty (uv α (suc j)) {a ++ ap (δV β j) d ∷ c} (InL-++ ia (tin (T-δV β j) id ∷ ic)))
      (trans (cong (λ z → embC e (lohi α (suc j) (unNat (hdU z)))) (slot {ds = ap (δV β j) d ∷ []} {cs = c} ia))
      (trans (cong (λ z → embC e (lohi α (suc j) (unNat z))) (ap-ty (δV β j) id))
      (trans (cong (embC e) (fc j id))
      (trans (cong (λ z → embC e (lohi β j (unNat (hdU z)))) (sym (slot {ds = d} {cs = c} ia)))
             (sym (ap-ty (uv β j) (InL-++ ia (InL-++ id ic)))))))))
      where
      fc : ∀ j {d} → InL (dsrc j) d → lohi α (suc j) (dl β j (unNat (hdU d))) ≡ lohi β j (unNat (hdU (d ++ c)))
      fc zero    []                     = lohi-face0 α β
      fc (suc j) {u ∷ []} (qu ∷ [])     with inC-nat _ u qu
      ... | p , refl , _ = lohi-face α β j p

------------------------------------------------------------------------
-- D7g

d7g : ∀ ρ g k → T (okT (tmpl ρ g dir (suc k))) → ∀ s →
      infer (ctx (tmpl ρ g dir (suc k))) s ≡ just (reverseTop (cgoal (tmpl ρ g dir (suc k)))) → ⊥
d7g ρ g k ok s es = main (Env.reverse-cell ρ g k uv uc uf s es)
  where
  open Tower ρ g (∧-snd {canon ρ} ok) (canon-nt ρ (∧-fst ok))
  main : ∀ {x} → CellAt (suc k) g (H ρ) x × (pcV x g (δV false k) ≈ᵥ uv true k) ×
                 (pcV x g (δV true k) ≈ᵥ uv false k) → ⊥
  main {x} (cellAt pre′ post′ sp len ty , m⁻ , m⁺) = go pre′ post′ e₁ e₂ ty
    where
    eu = split-unique pre′ post′ (ins (H ρ)) sp
    e₁ : pre′ ≡ pre
    e₁ = trans (fst eu) (cong (λ i → take i (ins (H ρ))) len)
    e₂ : post′ ≡ post
    e₂ = trans (snd eu) (cong (λ i → drop i (ins (H ρ))) len)
    go : ∀ P Q → P ≡ pre → Q ≡ post → x ∶ᵥ ((P ++ dsrc (suc k) ++ Q) ▸ Z) → ⊥
    go ._ ._ refl refl tx′ = emb-strict e (canon-nt ρ (∧-fst ok)) (subst₂′ (Le e) side⁻ side⁺ mon)
      where
      as = defL pre
      cs = defL post
      w  = as ++ dsK k ++ cs
      ia = defL-In pre
      ic = defL-In post
      L : Bool → List U
      L α = as ++ nat (dl α k k) ∷ cs
      ctr : ∀ α k → dl α k (unNat (hdU (dsK k))) ≡ dl α k k
      ctr α zero    = refl
      ctr α (suc m) = refl
      face : ∀ α → ap (pcV x g (δV α k)) w ≡ ap x (L α)
      face α = trans (evPC {P = pre} {Y = D (suc k)} {Q = post} tx′ (T-δV α k) (sym lp) ia (dsK-In k) ic)
                     (cong (λ z → ap x (as ++ z ∷ cs)) (trans (ap-ty (δV α k) (dsK-In k)) (cong nat (ctr α k))))
      mon : LF Z (ap x (L false)) (ap x (L true))
      mon = tmono tx′ {L false} {L true}
                  (InL-++ ia (dl-range false k k (leq-dbl k) ∷ ic)) (InL-++ ia (dl-range true k k (leq-dbl k) ∷ ic))
                  (LeL-++ (LeL-refl ia) (dl-ft k k ∷ LeL-refl ic))
      atU : ∀ α → ap (uv α k) w ≡ embC e α
      atU α = trans (ap-ty (uv α k) (InL-++ ia (InL-++ (dsK-In k) ic)))
                    (trans (cong (λ z → embC e (lohi α k (unNat (hdU z)))) (slot {ds = dsK k} {cs = cs} ia))
                           (cong (embC e) (lohi-ctr α k cs)))
      side⁻ : ap x (L false) ≡ embC e true
      side⁻ = trans (sym (face false)) (trans (efn m⁻ w) (atU true))
      side⁺ : ap x (L true) ≡ embC e false
      side⁺ = trans (sym (face true)) (trans (efn m⁺ w) (atU false))
