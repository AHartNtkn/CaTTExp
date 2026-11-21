------------------------------------------------------------------------
-- A concrete, nontrivial model of the biclosed kernel (Model.agda):
-- finite posets and monotone maps.
--
-- Formulas are finite posets (Poset.agda): object variables are the
-- chain 0 < 1, ⊗ and ⊠ are products, both closures A\C and C/A are the
-- poset of monotone maps A → C, a named shape is a point, and the
-- k-globe ⟦Dᵏ⟧ is the chain 0 < 1 < … < 2k whose middle element k is
-- its interior; the faces δ^±_k : ⟦Dᵏ⟧ → ⟦Dᵏ⁺¹⟧ send the interior to k
-- and to k + 2 and shift the points above it by 2, and σ_k collapses
-- k, k + 1, k + 2 back to k.
--
-- An operation (X₁, …, Xₙ ▸ Z) is a profile with a function on lists
-- of trees; applying it first coerces its inputs into the profile, so
-- ≈ is equality of the applied functions.  Typing asks that typed
-- inputs go to the output poset, monotonically.  Composition splices,
-- the corolla inverses unpair, the curries tabulate.  This is the
-- cartesian closed category of finite posets, so all Model laws hold;
-- monotonicity is what makes it directed: a cell from s to t has
-- s ≤ t pointwise.  No postulates.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.PosetModel where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.Gray.Biclosed.Rows using (leq)
open import CaTTExp.Gray.Biclosed.ListLemmas
open import CaTTExp.Gray.Biclosed.Poset
open import CaTTExp.Gray.Biclosed.Model

------------------------------------------------------------------------
-- Formulas as posets

dbl : Nat → Nat
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

shC : Shape → Code
shC (disk n)  = cnat (dbl n)
shC (named _) = cnat zero
shC (a ⊠ b)   = cpair (shC a) (shC b)

fmC : Fm → Code
fmC (obj _)  = cnat 1
fmC (rep s)  = shC s
fmC (a ⊗ b)  = cpair (fmC a) (fmC b)
fmC (a \\ c) = ctab (fmC a) (fmC c)
fmC (c // a) = ctab (fmC a) (fmC c)

IF : Fm → U → Set
IF F = In (fmC F)

LF : Fm → U → U → Set
LF F = Le (fmC F)

data InL : List Fm → List U → Set where
  []  : InL [] []
  _∷_ : ∀ {F Fs u us} → IF F u → InL Fs us → InL (F ∷ Fs) (u ∷ us)

data LeL : List Fm → List U → List U → Set where
  []  : LeL [] [] []
  _∷_ : ∀ {F Fs u us v vs} → LF F u v → LeL Fs us vs → LeL (F ∷ Fs) (u ∷ us) (v ∷ vs)

subst₂′ : ∀ {A : Set} (P : A → A → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
subst₂′ P refl refl p = p

------------------------------------------------------------------------
-- Typed lists

InL-len : ∀ {Fs us} → InL Fs us → length us ≡ length Fs
InL-len []       = refl
InL-len (_ ∷ qs) = cong suc (InL-len qs)

InL-++ : ∀ {A B as bs} → InL A as → InL B bs → InL (A ++ B) (as ++ bs)
InL-++ []       qb = qb
InL-++ (q ∷ qa) qb = q ∷ InL-++ qa qb

record Sp2 (A B : List Fm) (us : List U) : Set where
  constructor sp2
  field
    sa sb : List U
    seq2  : us ≡ sa ++ sb
    qa    : InL A sa
    qb    : InL B sb

InL-split : ∀ A {B us} → InL (A ++ B) us → Sp2 A B us
InL-split []      q        = sp2 [] _ refl [] q
InL-split (F ∷ A) (q ∷ qs) with InL-split A qs
... | sp2 a b refl qa qb = sp2 (_ ∷ a) b refl (q ∷ qa) qb

record Sp3 (A B C : List Fm) (us : List U) : Set where
  constructor sp3
  field
    xa xb xc : List U
    seq3     : us ≡ xa ++ xb ++ xc
    ia       : InL A xa
    ib       : InL B xb
    ic       : InL C xc

InL-split3 : ∀ A B C {us} → InL (A ++ B ++ C) us → Sp3 A B C us
InL-split3 A B C q with InL-split A q
... | sp2 a r refl qa qr with InL-split B qr
...   | sp2 b c refl qb qc = sp3 a b c refl qa qb qc

LeL-++ : ∀ {A B as as′ bs bs′} → LeL A as as′ → LeL B bs bs′ → LeL (A ++ B) (as ++ bs) (as′ ++ bs′)
LeL-++ []       lb = lb
LeL-++ (l ∷ la) lb = l ∷ LeL-++ la lb

LeL-split : ∀ {A B as as′ bs bs′} → InL A as → InL A as′ → LeL (A ++ B) (as ++ bs) (as′ ++ bs′) →
            LeL A as as′ × LeL B bs bs′
LeL-split []       []         l        = [] , l
LeL-split (q ∷ qa) (q′ ∷ qa′) (l ∷ ls) with LeL-split qa qa′ ls
... | la , lb = (l ∷ la) , lb

LeL-refl : ∀ {Fs us} → InL Fs us → LeL Fs us us
LeL-refl []                  = []
LeL-refl {F ∷ Fs} {u ∷ us} (q ∷ qs) = leC-refl (fmC F) u q ∷ LeL-refl qs

------------------------------------------------------------------------
-- Coercion into a profile

co : Fm → U → U
co F u = if inC (fmC F) u then u else defC (fmC F)

co-gen : ∀ c u b → inC c u ≡ b → In c (if b then u else defC c)
co-gen c u true  e = subst T (sym e) tt
co-gen c u false e = inC-def c

co-In : ∀ F u → IF F (co F u)
co-In F u = co-gen (fmC F) u (inC (fmC F) u) refl

co-id : ∀ F u → IF F u → co F u ≡ u
co-id F u q = cong (λ b → if b then u else defC (fmC F)) (T-≡ q)

hdU : List U → U
hdU []      = nat zero
hdU (u ∷ _) = u

tlU : List U → List U
tlU []       = []
tlU (_ ∷ us) = us

unNat : U → Nat
unNat (nat p) = p
unNat _       = zero

fstU sndU : U → U
fstU (pr a _) = a
fstU _        = nat zero
sndU (pr _ b) = b
sndU _        = nat zero

cA : List Fm → List U → List U
cA []       us = []
cA (F ∷ Fs) us = co F (hdU us) ∷ cA Fs (tlU us)

cA-In : ∀ Fs us → InL Fs (cA Fs us)
cA-In []       us = []
cA-In (F ∷ Fs) us = co-In F (hdU us) ∷ cA-In Fs (tlU us)

cA-id : ∀ {Fs us} → InL Fs us → cA Fs us ≡ us
cA-id []                          = refl
cA-id {F ∷ Fs} {u ∷ us} (q ∷ qs) = cong₂ _∷_ (co-id F u q) (cA-id qs)

------------------------------------------------------------------------
-- Operations

record Val : Set where
  constructor mk
  field
    prof : MTy
    raw  : List U → U
open Val public

ap : Val → List U → U
ap x us = raw x (cA (ins (prof x)) us)

ap-ty : ∀ v {ws} → InL (ins (prof v)) ws → ap v ws ≡ raw v ws
ap-ty v q = cong (raw v) (cA-id q)

infix 4 _≈ᵥ_ _∶ᵥ_

record _≈ᵥ_ (x y : Val) : Set where
  constructor ≈c
  field
    eprof : prof x ≡ prof y
    efn   : ∀ us → ap x us ≡ ap y us
open _≈ᵥ_ public

record _∶ᵥ_ (x : Val) (M : MTy) : Set where
  constructor tyd
  field
    tprof : prof x ≡ M
    tin   : ∀ {us} → InL (ins M) us → IF (out M) (ap x us)
    tmono : ∀ {us vs} → InL (ins M) us → InL (ins M) vs → LeL (ins M) us vs →
            LF (out M) (ap x us) (ap x vs)
open _∶ᵥ_ public

≈-intro : ∀ {x y} → prof x ≡ prof y → (∀ ws → InL (ins (prof x)) ws → ap x ws ≡ ap y ws) → x ≈ᵥ y
≈-intro {mk P rx} {mk .P ry} refl h =
  ≈c refl (λ us → trans (cong rx (sym (cA-id (cA-In (ins P) us))))
                  (trans (h (cA (ins P) us) (cA-In (ins P) us)) (cong ry (cA-id (cA-In (ins P) us)))))

tyRaw : ∀ v {M} → prof v ≡ M → (∀ {ws} → InL (ins M) ws → IF (out M) (raw v ws)) →
        (∀ {ws vs} → InL (ins M) ws → InL (ins M) vs → LeL (ins M) ws vs → LF (out M) (raw v ws) (raw v vs)) →
        v ∶ᵥ M
tyRaw (mk P r) refl hin hm =
  tyd refl (λ q → subst (IF (out P)) (sym (ap-ty (mk P r) q)) (hin q))
           (λ q q′ l → subst₂′ (LF (out P)) (sym (ap-ty (mk P r) q)) (sym (ap-ty (mk P r) q′)) (hm q q′ l))

retypeV : ∀ {x M N} → x ∶ᵥ M → M ≡ N → x ∶ᵥ N
retypeV p refl = p

≈ᵥ-refl : ∀ {x} → x ≈ᵥ x
≈ᵥ-refl = ≈c refl (λ _ → refl)

≈ᵥ-sym : ∀ {x y} → x ≈ᵥ y → y ≈ᵥ x
≈ᵥ-sym (≈c e f) = ≈c (sym e) (λ us → sym (f us))

≈ᵥ-trans : ∀ {x y z} → x ≈ᵥ y → y ≈ᵥ z → x ≈ᵥ z
≈ᵥ-trans (≈c e f) (≈c e′ f′) = ≈c (trans e e′) (λ us → trans (f us) (f′ us))

∶ᵥ-≈ : ∀ {x y M} → x ≈ᵥ y → x ∶ᵥ M → y ∶ᵥ M
∶ᵥ-≈ {M = M} (≈c e f) (tyd p i m) =
  tyd (trans (sym e) p) (λ q → subst (IF (out M)) (f _) (i q))
      (λ q q′ l → subst₂′ (LF (out M)) (f _) (f _) (m q q′ l))

-- one-place composition
pcProf : MTy → Nat → MTy → MTy
pcProf (Fs ▸ Z) i (Gs ▸ Y) = (take i Fs ++ Gs ++ drop (suc i) Fs) ▸ Z

pcV : Val → Nat → Val → Val
pcV f i g = mk (pcProf (prof f) i (prof g))
  (λ us → ap f (take i us ++ ap g (take (length (ins (prof g))) (drop i us))
                 ∷ drop (i + length (ins (prof g))) us))

idV : Fm → Val
idV A = mk ((A ∷ []) ▸ A) hdU

corV : Cor → Val
corV (cm U W) = mk ((U ∷ W ∷ []) ▸ (U ⊗ W)) (λ us → pr (hdU us) (hdU (tlU us)))
corV (cp Δ Θ) = mk ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) (λ us → pr (hdU us) (hdU (tlU us)))
corV cpt      = mk ([] ▸ D 0) (λ _ → nat zero)

evLV : Fm → Fm → Val
evLV A C = mk ((A ∷ (A \\ C) ∷ []) ▸ C) (λ us → app (fmC A) (hdU (tlU us)) (hdU us))

evRV : Fm → Fm → Val
evRV A C = mk (((C // A) ∷ A ∷ []) ▸ C) (λ us → app (fmC A) (hdU us) (hdU (tlU us)))

-- the faces and the degeneracy of the globes
dl : Bool → Nat → Nat → Nat
dl α zero    zero    = if α then 2 else 0
dl α zero    (suc p) = suc (suc (suc p))
dl α (suc n) zero    = zero
dl α (suc n) (suc p) = suc (dl α n p)

sg : Nat → Nat → Nat
sg zero    zero                = zero
sg zero    (suc zero)          = zero
sg zero    (suc (suc zero))    = zero
sg zero    (suc (suc (suc p))) = suc p
sg (suc n) zero                = zero
sg (suc n) (suc p)             = suc (sg n p)

δV : Bool → Nat → Val
δV α n = mk (dsrc n ▸ D (suc n)) (λ us → nat (dl α n (unNat (hdU us))))

σV : Nat → Val
σV n = mk ((D (suc n) ∷ []) ▸ D n) (λ us → nat (sg n (unNat (hdU us))))

-- the inverse of precomposition with a corolla
splitC : Cor → U → List U
splitC (cm _ _) u = fstU u ∷ sndU u ∷ []
splitC (cp _ _) u = fstU u ∷ sndU u ∷ []
splitC cpt      u = []

unProf : Cor → Nat → MTy → MTy
unProf c i (Ys ▸ Z) = (take i Ys ++ corOut c ∷ drop (i + length (corIns c)) Ys) ▸ Z

unCV : Cor → Nat → Val → Val
unCV c i y = mk (unProf c i (prof y))
  (λ us → ap y (take i us ++ splitC c (hdU (drop i us)) ++ drop (suc i) us))

-- the curries
init : List Fm → List Fm
init []           = []
init (x ∷ [])     = []
init (x ∷ y ∷ ys) = x ∷ init (y ∷ ys)

curLV : Fm → Fm → Val → Val
curLV A C y = mk (drop 1 (ins (prof y)) ▸ (A \\ C)) (λ us → tabF (fmC A) (λ a → ap y (a ∷ us)))

curRV : Fm → Fm → Val → Val
curRV A C y = mk (init (ins (prof y)) ▸ (C // A)) (λ us → tabF (fmC A) (λ a → ap y (us ++ a ∷ [])))

------------------------------------------------------------------------
-- List lemmas

take-len : ∀ {A : Set} (as ys : List A) → take (length as) (as ++ ys) ≡ as
take-len []       ys = refl
take-len (a ∷ as) ys = cong (a ∷_) (take-len as ys)

drop-len : ∀ {A : Set} (as ys : List A) → drop (length as) (as ++ ys) ≡ ys
drop-len []       ys = refl
drop-len (a ∷ as) ys = drop-len as ys

drop-suc-len : ∀ {A : Set} (as : List A) y ys → drop (suc (length as)) (as ++ y ∷ ys) ≡ ys
drop-suc-len []       y ys = refl
drop-suc-len (a ∷ as) y ys = drop-suc-len as y ys

init-snoc : ∀ Φ A → init (Φ ++ A ∷ []) ≡ Φ
init-snoc []          A = refl
init-snoc (x ∷ [])    A = refl
init-snoc (x ∷ y ∷ Φ) A = cong (x ∷_) (init-snoc (y ∷ Φ) A)

ra1 : ∀ {A : Set} (a b : List A) x (c d : List A) → (a ++ b) ++ x ∷ (c ++ d) ≡ a ++ (b ++ x ∷ c) ++ d
ra1 a b x c d = trans (++-assoc a b (x ∷ c ++ d)) (sym (cong (a ++_) (++-assoc b (x ∷ c) d)))

ra2 : ∀ {A : Set} (a b w c d : List A) → (a ++ b) ++ w ++ (c ++ d) ≡ a ++ (b ++ w ++ c) ++ d
ra2 a b w c d =
  trans (++-assoc a b (w ++ c ++ d))
        (cong (a ++_) (sym (trans (++-assoc b (w ++ c) d) (cong (b ++_) (++-assoc w c d)))))

ra3 : ∀ {A : Set} (p x m l : List A) → (p ++ x ++ m) ++ l ≡ p ++ x ++ m ++ l
ra3 p x m l = trans (++-assoc p (x ++ m) l) (cong (p ++_) (++-assoc x m l))

pcIns : ∀ (P : List Fm) Y Q Xs → take (length P) (P ++ Y ∷ Q) ++ Xs ++ drop (suc (length P)) (P ++ Y ∷ Q) ≡ P ++ Xs ++ Q
pcIns P Y Q Xs = cong₂ (λ a b → a ++ Xs ++ b) (take-len P (Y ∷ Q)) (drop-suc-len P Y Q)

pcProf-eq : ∀ {Pf Pg P Y Q Z Xs Y′} → Pf ≡ (P ++ Y ∷ Q) ▸ Z → Pg ≡ Xs ▸ Y′ →
            pcProf Pf (length P) Pg ≡ (P ++ Xs ++ Q) ▸ Z
pcProf-eq {P = P} {Y} {Q} {Z} {Xs} refl refl = cong (_▸ Z) (pcIns P Y Q Xs)

------------------------------------------------------------------------
-- Evaluating a composite

pc-ev : ∀ f g as bs cs → length bs ≡ length (ins (prof g)) →
        raw (pcV f (length as) g) (as ++ bs ++ cs) ≡ ap f (as ++ ap g bs ∷ cs)
pc-ev f g as bs cs lb
  rewrite take-len as (bs ++ cs) | drop-len as (bs ++ cs) | sym lb | take-len bs cs
        | drop-++ʳ as (length bs) (bs ++ cs) | drop-len bs cs = refl

evPC : ∀ {f g P Y Q Z Xs as bs cs i} → f ∶ᵥ ((P ++ Y ∷ Q) ▸ Z) → g ∶ᵥ (Xs ▸ Y) → i ≡ length P →
       InL P as → InL Xs bs → InL Q cs → ap (pcV f i g) (as ++ bs ++ cs) ≡ ap f (as ++ ap g bs ∷ cs)
evPC {f} {g} {P} {Y} {Q} {Z} {Xs} {as} {bs} {cs} tf tg refl ia ib ic =
  trans (ap-ty (pcV f (length P) g) typed)
        (subst (λ k → raw (pcV f k g) (as ++ bs ++ cs) ≡ ap f (as ++ ap g bs ∷ cs)) (InL-len ia)
               (pc-ev f g as bs cs (trans (InL-len ib) (cong (λ M → length (ins M)) (sym (tprof tg))))))
  where
  typed : InL (ins (prof (pcV f (length P) g))) (as ++ bs ++ cs)
  typed = subst (λ M → InL (ins M) (as ++ bs ++ cs)) (sym (pcProf-eq (tprof tf) (tprof tg)))
                (InL-++ ia (InL-++ ib ic))

T-pcV : ∀ {f g P Y Q Z Xs} → f ∶ᵥ ((P ++ Y ∷ Q) ▸ Z) → g ∶ᵥ (Xs ▸ Y) →
        pcV f (length P) g ∶ᵥ ((P ++ Xs ++ Q) ▸ Z)
T-pcV {f} {g} {P} {Y} {Q} {Z} {Xs} tf tg = tyd (pcProf-eq (tprof tf) (tprof tg)) tin′ tmono′
  where
  tin′ : ∀ {us} → InL (P ++ Xs ++ Q) us → IF Z (ap (pcV f (length P) g) us)
  tin′ q with InL-split3 P Xs Q q
  ... | sp3 a b c refl ia ib ic =
    subst (IF Z) (sym (evPC tf tg refl ia ib ic)) (tin tf (InL-++ ia (tin tg ib ∷ ic)))
  tmono′ : ∀ {us vs} → InL (P ++ Xs ++ Q) us → InL (P ++ Xs ++ Q) vs → LeL (P ++ Xs ++ Q) us vs →
           LF Z (ap (pcV f (length P) g) us) (ap (pcV f (length P) g) vs)
  tmono′ q q′ l with InL-split3 P Xs Q q | InL-split3 P Xs Q q′
  ... | sp3 a b c refl ia ib ic | sp3 a′ b′ c′ refl ia′ ib′ ic′ with LeL-split ia ia′ l
  ...   | la , lr with LeL-split ib ib′ lr
  ...     | lb , lc =
    subst₂′ (LF Z) (sym (evPC tf tg refl ia ib ic)) (sym (evPC tf tg refl ia′ ib′ ic′))
      (tmono tf (InL-++ ia (tin tg ib ∷ ic)) (InL-++ ia′ (tin tg ib′ ∷ ic′))
                (LeL-++ la (tmono tg ib ib′ lb ∷ lc)))

T-pcV′ : ∀ {f g P Y Q Z Xs i} → f ∶ᵥ ((P ++ Y ∷ Q) ▸ Z) → g ∶ᵥ (Xs ▸ Y) → i ≡ length P →
         pcV f i g ∶ᵥ ((P ++ Xs ++ Q) ▸ Z)
T-pcV′ tf tg refl = T-pcV tf tg

------------------------------------------------------------------------
-- Congruence

pc-congV : ∀ {f f′ g g′} i → f ≈ᵥ f′ → g ≈ᵥ g′ → pcV f i g ≈ᵥ pcV f′ i g′
pc-congV {mk P r} {mk .P r′} {mk Q s} {mk .Q s′} i (≈c refl ef) (≈c refl eg) =
  ≈c refl (λ us → let ws = cA (ins (pcProf P i Q)) us in
    trans (ef (take i ws ++ ap (mk Q s) (take (length (ins Q)) (drop i ws)) ∷ drop (i + length (ins Q)) ws))
          (cong (λ z → ap (mk P r′) (take i ws ++ z ∷ drop (i + length (ins Q)) ws)) (eg _)))

unC-congV : ∀ {y y′} c i → y ≈ᵥ y′ → unCV c i y ≈ᵥ unCV c i y′
unC-congV {mk P r} {mk .P r′} c i (≈c refl ey) = ≈c refl (λ us → ey _)

tabF-cong : ∀ a f g → (∀ x → In a x → f x ≡ g x) → tabF a f ≡ tabF a g
tabF-cong a f g h = cong tab (map-cong-∈ f g (els a) (λ m → h _ (els-sound a m)))

curL-congV : ∀ {y y′} A C → y ≈ᵥ y′ → curLV A C y ≈ᵥ curLV A C y′
curL-congV {mk P r} {mk .P r′} A C (≈c refl ey) = ≈c refl (λ us → tabF-cong (fmC A) _ _ (λ a _ → ey _))

curR-congV : ∀ {y y′} A C → y ≈ᵥ y′ → curRV A C y ≈ᵥ curRV A C y′
curR-congV {mk P r} {mk .P r′} A C (≈c refl ey) = ≈c refl (λ us → tabF-cong (fmC A) _ _ (λ a _ → ey _))

------------------------------------------------------------------------
-- Markl's laws

seqV : ∀ {f g h P Y Q Z P′ X Q′ Ws} →
       f ∶ᵥ ((P ++ Y ∷ Q) ▸ Z) → g ∶ᵥ ((P′ ++ X ∷ Q′) ▸ Y) → h ∶ᵥ (Ws ▸ X) →
       pcV (pcV f (length P) g) (length P + length P′) h ≈ᵥ pcV f (length P) (pcV g (length P′) h)
seqV {f} {g} {h} {P} {Y} {Q} {Z} {P′} {X} {Q′} {Ws} tf tg th =
  ≈-intro (trans (tprof tL) (trans (cong (_▸ Z) (ra2 P P′ Ws Q′ Q)) (sym (tprof tR)))) fn
  where
  fg  = pcV f (length P) g
  tfg : fg ∶ᵥ (((P ++ P′) ++ X ∷ (Q′ ++ Q)) ▸ Z)
  tfg = retypeV (T-pcV tf tg) (cong (_▸ Z) (sym (ra1 P P′ X Q′ Q)))
  pos : length P + length P′ ≡ length (P ++ P′)
  pos = sym (length-++ P P′)
  tL  = T-pcV′ tfg th pos
  tgh = T-pcV tg th
  tR  = T-pcV tf tgh
  fn : ∀ ws → InL (ins (prof (pcV fg (length P + length P′) h))) ws →
       ap (pcV fg (length P + length P′) h) ws ≡ ap (pcV f (length P) (pcV g (length P′) h)) ws
  fn ws q with InL-split3 (P ++ P′) Ws (Q′ ++ Q) (subst (λ M → InL (ins M) ws) (tprof tL) q)
  ... | sp3 a w c refl ia iw ic with InL-split P ia | InL-split Q′ ic
  ...   | sp2 ps ps′ refl ip ip′ | sp2 qs′ qs refl iq′ iq =
    trans (evPC tfg th pos (InL-++ ip ip′) iw (InL-++ iq′ iq))
    (trans (cong (ap fg) (ra1 ps ps′ (ap h w) qs′ qs))
    (trans (evPC tf tg refl ip (InL-++ ip′ (tin th iw ∷ iq′)) iq)
    (sym (trans (cong (ap (pcV f (length P) (pcV g (length P′) h))) (ra2 ps ps′ w qs′ qs))
         (trans (evPC tf tgh refl ip (InL-++ ip′ (InL-++ iw iq′)) iq)
                (cong (λ z → ap f (ps ++ z ∷ qs)) (evPC tg th refl ip′ iw iq′)))))))

parV : ∀ {f g h P Y M W Q Z Xs Ws} →
       f ∶ᵥ ((P ++ Y ∷ M ++ W ∷ Q) ▸ Z) → g ∶ᵥ (Xs ▸ Y) → h ∶ᵥ (Ws ▸ W) →
       pcV (pcV f (length P) g) (length P + length Xs + length M) h
         ≈ᵥ pcV (pcV f (length P + suc (length M)) h) (length P) g
parV {f} {g} {h} {P} {Y} {M} {W} {Q} {Z} {Xs} {Ws} tf tg th =
  ≈-intro (trans (tprof tL) (trans (cong (_▸ Z) (ra3 P Xs M (Ws ++ Q))) (sym (tprof tR)))) fn
  where
  fg = pcV f (length P) g
  tfg : fg ∶ᵥ (((P ++ Xs ++ M) ++ W ∷ Q) ▸ Z)
  tfg = retypeV (T-pcV tf tg) (cong (_▸ Z) (sym (ra3 P Xs M (W ∷ Q))))
  pos : length P + length Xs + length M ≡ length (P ++ Xs ++ M)
  pos = sym (trans (length-++ P (Xs ++ M))
                   (trans (cong (length P +_) (length-++ Xs M)) (sym (+-assoc (length P) (length Xs) (length M)))))
  tL = T-pcV′ tfg th pos
  fh = pcV f (length P + suc (length M)) h
  tf′ : f ∶ᵥ (((P ++ Y ∷ M) ++ W ∷ Q) ▸ Z)
  tf′ = retypeV tf (cong (_▸ Z) (sym (++-assoc P (Y ∷ M) (W ∷ Q))))
  pos′ : length P + suc (length M) ≡ length (P ++ Y ∷ M)
  pos′ = sym (length-++ P (Y ∷ M))
  tfh : fh ∶ᵥ ((P ++ Y ∷ (M ++ Ws ++ Q)) ▸ Z)
  tfh = retypeV (T-pcV′ tf′ th pos′) (cong (_▸ Z) (++-assoc P (Y ∷ M) (Ws ++ Q)))
  tR = T-pcV tfh tg
  fn : ∀ ws → InL (ins (prof (pcV fg (length P + length Xs + length M) h))) ws →
       ap (pcV fg (length P + length Xs + length M) h) ws ≡ ap (pcV fh (length P) g) ws
  fn ws q with InL-split3 (P ++ Xs ++ M) Ws Q (subst (λ N → InL (ins N) ws) (tprof tL) q)
  ... | sp3 a w c refl ia iw ic with InL-split3 P Xs M ia
  ...   | sp3 p x m refl ip ix im =
    trans (evPC tfg th pos (InL-++ ip (InL-++ ix im)) iw ic)
    (trans (cong (ap fg) (ra3 p x m (ap h w ∷ c)))
    (trans (evPC tf tg refl ip ix (InL-++ im (tin th iw ∷ ic)))
    (sym (trans (cong (ap (pcV fh (length P) g)) (ra3 p x m (w ++ c)))
         (trans (evPC tfh tg refl ip ix (InL-++ im (InL-++ iw ic)))
         (trans (cong (ap fh) (sym (++-assoc p (ap g x ∷ m) (w ++ c))))
         (trans (evPC tf′ th pos′ (InL-++ ip (tin tg ix ∷ im)) iw ic)
                (cong (ap f) (++-assoc p (ap g x ∷ m) (ap h w ∷ c))))))))))

unit-lV : ∀ {g Xs Y} → g ∶ᵥ (Xs ▸ Y) → pcV (idV Y) 0 g ≈ᵥ g
unit-lV {g} {Xs} {Y} tg =
  ≈-intro (trans (tprof tL) (trans (cong (_▸ Y) (++-[] Xs)) (sym (tprof tg)))) fn
  where
  tI : idV Y ∶ᵥ (([] ++ Y ∷ []) ▸ Y)
  tI = tyRaw (idV Y) refl (λ { (q ∷ []) → q }) (λ { (q ∷ []) (q′ ∷ []) (l ∷ []) → l })
  tL = T-pcV {P = []} {Q = []} tI tg
  fn : ∀ ws → InL (ins (prof (pcV (idV Y) 0 g))) ws → ap (pcV (idV Y) 0 g) ws ≡ ap g ws
  fn ws q =
    trans (cong (ap (pcV (idV Y) 0 g)) (sym (++-[] ws)))
    (trans (evPC {P = []} {Q = []} tI tg refl [] qx []) (ap-ty (idV Y) (tin tg qx ∷ [])))
    where
    qx : InL Xs ws
    qx = subst (λ L → InL L ws) (++-[] Xs) (subst (λ M → InL (ins M) ws) (tprof tL) q)

unit-rV : ∀ {f P Y Q Z} → f ∶ᵥ ((P ++ Y ∷ Q) ▸ Z) → pcV f (length P) (idV Y) ≈ᵥ f
unit-rV {f} {P} {Y} {Q} {Z} tf = ≈-intro (trans (tprof tL) (sym (tprof tf))) fn
  where
  tI : idV Y ∶ᵥ ((Y ∷ []) ▸ Y)
  tI = tyRaw (idV Y) refl (λ { (q ∷ []) → q }) (λ { (q ∷ []) (q′ ∷ []) (l ∷ []) → l })
  tL = T-pcV tf tI
  fn : ∀ ws → InL (ins (prof (pcV f (length P) (idV Y)))) ws → ap (pcV f (length P) (idV Y)) ws ≡ ap f ws
  fn ws q with InL-split3 P (Y ∷ []) Q (subst (λ M → InL (ins M) ws) (tprof tL) q)
  ... | sp3 a (y ∷ []) c refl ia (iy ∷ []) ic =
    trans (evPC tf tI refl ia (iy ∷ []) ic) (cong (λ z → ap f (a ++ z ∷ c)) (ap-ty (idV Y) (iy ∷ [])))

------------------------------------------------------------------------
-- Typing of the generators

T-idV : ∀ A → idV A ∶ᵥ ((A ∷ []) ▸ A)
T-idV A = tyRaw (idV A) refl (λ { (q ∷ []) → q }) (λ { (q ∷ []) (q′ ∷ []) (l ∷ []) → l })

T-corV : ∀ c → corV c ∶ᵥ (corIns c ▸ corOut c)
T-corV (cm U W) = tyRaw (corV (cm U W)) refl (λ { (qx ∷ qy ∷ []) → ∧I qx qy })
                    (λ { (_ ∷ _ ∷ []) (_ ∷ _ ∷ []) (lx ∷ ly ∷ []) → ∧I lx ly })
T-corV (cp Δ Θ) = tyRaw (corV (cp Δ Θ)) refl (λ { (qx ∷ qy ∷ []) → ∧I qx qy })
                    (λ { (_ ∷ _ ∷ []) (_ ∷ _ ∷ []) (lx ∷ ly ∷ []) → ∧I lx ly })
T-corV cpt      = tyRaw (corV cpt) refl (λ { [] → tt }) (λ { [] [] [] → tt })

T-evLV : ∀ A C → evLV A C ∶ᵥ ((A ∷ (A \\ C) ∷ []) ▸ C)
T-evLV A C = tyRaw (evLV A C) refl
  (λ { {a ∷ t ∷ []} (qa ∷ qt ∷ []) → app-In (fmC A) (fmC C) t a qt qa })
  (λ { {a ∷ t ∷ []} {a′ ∷ t′ ∷ []} (qa ∷ qt ∷ []) (qa′ ∷ qt′ ∷ []) (la ∷ lt ∷ []) →
         app-mono (fmC A) (fmC C) t t′ a a′ qt qt′ qa qa′ la lt })

T-evRV : ∀ A C → evRV A C ∶ᵥ (((C // A) ∷ A ∷ []) ▸ C)
T-evRV A C = tyRaw (evRV A C) refl
  (λ { {t ∷ a ∷ []} (qt ∷ qa ∷ []) → app-In (fmC A) (fmC C) t a qt qa })
  (λ { {t ∷ a ∷ []} {t′ ∷ a′ ∷ []} (qt ∷ qa ∷ []) (qt′ ∷ qa′ ∷ []) (lt ∷ la ∷ []) →
         app-mono (fmC A) (fmC C) t t′ a a′ qt qt′ qa qa′ la lt })

-- arithmetic of the globes
dl-le : ∀ α n p → T (leq (dl α n p) (suc (suc p)))
dl-le true  zero    zero    = tt
dl-le false zero    zero    = tt
dl-le α     zero    (suc p) = leq-refl p
dl-le α     (suc n) zero    = tt
dl-le α     (suc n) (suc p) = dl-le α n p

dl-range : ∀ α n p → T (leq p (dbl n)) → T (leq (dl α n p) (dbl (suc n)))
dl-range α n p h = leq-trans (dl α n p) (suc (suc p)) (dbl (suc n)) (dl-le α n p) h

dl-mono : ∀ α n p q → T (leq p q) → T (leq (dl α n p) (dl α n q))
dl-mono true  zero    zero    zero    _ = tt
dl-mono false zero    zero    zero    _ = tt
dl-mono true  zero    zero    (suc q) _ = tt
dl-mono false zero    zero    (suc q) _ = tt
dl-mono α     zero    (suc p) zero    ()
dl-mono α     zero    (suc p) (suc q) h = h
dl-mono α     (suc n) zero    q       _ = tt
dl-mono α     (suc n) (suc p) zero    ()
dl-mono α     (suc n) (suc p) (suc q) h = dl-mono α n p q h

-- the source face lies below the target face
dl-ft : ∀ n p → T (leq (dl false n p) (dl true n p))
dl-ft zero    zero    = tt
dl-ft zero    (suc p) = leq-refl p
dl-ft (suc n) zero    = tt
dl-ft (suc n) (suc p) = dl-ft n p

sg-dl : ∀ α n p → sg n (dl α n p) ≡ p
sg-dl true  zero    zero    = refl
sg-dl false zero    zero    = refl
sg-dl α     zero    (suc p) = refl
sg-dl α     (suc n) zero    = refl
sg-dl α     (suc n) (suc p) = cong suc (sg-dl α n p)

sg-le : ∀ n p q → T (leq p (suc (suc q))) → T (leq n q) → T (leq (sg n p) q)
sg-le zero    zero                q _ _ = tt
sg-le zero    (suc zero)          q _ _ = tt
sg-le zero    (suc (suc zero))    q _ _ = tt
sg-le zero    (suc (suc (suc p))) q h _ = h
sg-le (suc n) zero                q _ _ = tt
sg-le (suc n) (suc p)             zero    h ()
sg-le (suc n) (suc p)             (suc q) h l = sg-le n p q h l

leq-dbl : ∀ n → T (leq n (dbl n))
leq-dbl zero    = tt
leq-dbl (suc n) = leq-wk n (dbl n) (leq-dbl n)

sg-range : ∀ n p → T (leq p (dbl (suc n))) → T (leq (sg n p) (dbl n))
sg-range n p h = sg-le n p (dbl n) h (leq-dbl n)

sg-mono : ∀ n p q → T (leq p q) → T (leq (sg n p) (sg n q))
sg-mono zero    zero                q                   _ = tt
sg-mono zero    (suc zero)          q                   _ = tt
sg-mono zero    (suc (suc zero))    q                   _ = tt
sg-mono zero    (suc (suc (suc p))) zero                ()
sg-mono zero    (suc (suc (suc p))) (suc zero)          ()
sg-mono zero    (suc (suc (suc p))) (suc (suc zero))    ()
sg-mono zero    (suc (suc (suc p))) (suc (suc (suc q))) h = h
sg-mono (suc n) zero                q                   _ = tt
sg-mono (suc n) (suc p)             zero                ()
sg-mono (suc n) (suc p)             (suc q)             h = sg-mono n p q h

T-δV : ∀ α n → δV α n ∶ᵥ (dsrc n ▸ D (suc n))
T-δV true  zero    = tyRaw (δV true zero) refl (λ { [] → tt }) (λ { [] [] [] → tt })
T-δV false zero    = tyRaw (δV false zero) refl (λ { [] → tt }) (λ { [] [] [] → tt })
T-δV α     (suc n) = tyRaw (δV α (suc n)) refl
  (λ { {u ∷ []} (q ∷ []) → go u q })
  (λ { {u ∷ []} {v ∷ []} (q ∷ []) (q′ ∷ []) (l ∷ []) → mo u v q q′ l })
  where
  go : ∀ u → IF (D (suc n)) u → T (leq (dl α (suc n) (unNat u)) (dbl (suc (suc n))))
  go u q with inC-nat _ u q
  ... | p , refl , h = dl-range α (suc n) p h
  mo : ∀ u v → IF (D (suc n)) u → IF (D (suc n)) v → LF (D (suc n)) u v →
       T (leq (dl α (suc n) (unNat u)) (dl α (suc n) (unNat v)))
  mo u v q q′ l with inC-nat _ u q | inC-nat _ v q′
  ... | p , refl , _ | p′ , refl , _ = dl-mono α (suc n) p p′ l

T-σV : ∀ n → σV n ∶ᵥ ((D (suc n) ∷ []) ▸ D n)
T-σV n = tyRaw (σV n) refl
  (λ { {u ∷ []} (q ∷ []) → go u q })
  (λ { {u ∷ []} {v ∷ []} (q ∷ []) (q′ ∷ []) (l ∷ []) → mo u v q q′ l })
  where
  go : ∀ u → IF (D (suc n)) u → T (leq (sg n (unNat u)) (dbl n))
  go u q with inC-nat _ u q
  ... | p , refl , h = sg-range n p h
  mo : ∀ u v → IF (D (suc n)) u → IF (D (suc n)) v → LF (D (suc n)) u v →
       T (leq (sg n (unNat u)) (sg n (unNat v)))
  mo u v q q′ l with inC-nat _ u q | inC-nat _ v q′
  ... | p , refl , _ | p′ , refl , _ = sg-mono n p p′ l

------------------------------------------------------------------------
-- Globes: σ is a retraction of both faces

σδ-sucV : ∀ α n → pcV (σV (suc n)) 0 (δV α (suc n)) ≈ᵥ idV (D (suc n))
σδ-sucV α n = ≈-intro refl fn
  where
  fn : ∀ ws → InL (D (suc n) ∷ []) ws → ap (pcV (σV (suc n)) 0 (δV α (suc n))) ws ≡ ap (idV (D (suc n))) ws
  fn (u ∷ []) (q ∷ []) with inC-nat _ u q
  ... | p , refl , h =
    trans (evPC {P = []} {Y = D (suc (suc n))} {Q = []} {Z = D (suc n)} {Xs = D (suc n) ∷ []} {as = []} {bs = nat p ∷ []} {cs = []}
                 (T-σV (suc n)) (T-δV α (suc n)) refl [] (q ∷ []) [])
    (trans (cong (λ z → ap (σV (suc n)) (z ∷ [])) (ap-ty (δV α (suc n)) {nat p ∷ []} (q ∷ [])))
    (trans (ap-ty (σV (suc n)) {nat (dl α (suc n) p) ∷ []} (dl-range α (suc n) p h ∷ []))
    (trans (cong nat (sg-dl α (suc n) p)) (sym (ap-ty (idV (D (suc n))) {nat p ∷ []} (q ∷ []))))))

σδ-0V : ∀ α → pcV (σV 0) 0 (δV α 0) ≈ᵥ corV cpt
σδ-0V true  = ≈-intro refl (λ { [] [] → refl })
σδ-0V false = ≈-intro refl (λ { [] [] → refl })

------------------------------------------------------------------------
-- Representability

splitC-In : ∀ c {u} → IF (corOut c) u → InL (corIns c) (splitC c u)
splitC-In (cm U W) {u} q with inC-pair _ _ u q
... | x , y , refl , qx , qy = qx ∷ qy ∷ []
splitC-In (cp Δ Θ) {u} q with inC-pair _ _ u q
... | x , y , refl , qx , qy = qx ∷ qy ∷ []
splitC-In cpt      q = []

splitC-mono : ∀ c {u v} → IF (corOut c) u → IF (corOut c) v → LF (corOut c) u v →
              LeL (corIns c) (splitC c u) (splitC c v)
splitC-mono (cm U W) {u} {v} q q′ l with inC-pair _ _ u q | inC-pair _ _ v q′
... | x , y , refl , _ , _ | x′ , y′ , refl , _ , _ = ∧-fst l ∷ ∧-snd {leC (fmC U) x x′} l ∷ []
splitC-mono (cp Δ Θ) {u} {v} q q′ l with inC-pair _ _ u q | inC-pair _ _ v q′
... | x , y , refl , _ , _ | x′ , y′ , refl , _ , _ = ∧-fst l ∷ ∧-snd {leC (shC Δ) x x′} l ∷ []
splitC-mono cpt q q′ l = []

cor-split : ∀ c {u} → IF (corOut c) u → ap (corV c) (splitC c u) ≡ u
cor-split (cm U W) {u} q with inC-pair _ _ u q
... | x , y , refl , qx , qy = ap-ty (corV (cm U W)) (qx ∷ qy ∷ [])
cor-split (cp Δ Θ) {u} q with inC-pair _ _ u q
... | x , y , refl , qx , qy = ap-ty (corV (cp Δ Θ)) (qx ∷ qy ∷ [])
cor-split cpt      {u} q with inC-nat _ u q
cor-split cpt      {u} q | zero  , refl , _ = refl
cor-split cpt      {u} q | suc p , refl , ()

split-cor : ∀ c {bs} → InL (corIns c) bs → splitC c (ap (corV c) bs) ≡ bs
split-cor (cm U W) (qx ∷ qy ∷ []) = cong (splitC (cm U W)) (ap-ty (corV (cm U W)) (qx ∷ qy ∷ []))
split-cor (cp Δ Θ) (qx ∷ qy ∷ []) = cong (splitC (cp Δ Θ)) (ap-ty (corV (cp Δ Θ)) (qx ∷ qy ∷ []))
split-cor cpt      []              = refl

unProf-eq : ∀ c {Py P Q Z} → Py ≡ (P ++ corIns c ++ Q) ▸ Z → unProf c (length P) Py ≡ (P ++ corOut c ∷ Q) ▸ Z
unProf-eq c {P = P} {Q} {Z} refl =
  cong₂ (λ a b → (a ++ corOut c ∷ b) ▸ Z) (take-len P (corIns c ++ Q))
        (trans (drop-++ʳ P (length (corIns c)) (corIns c ++ Q)) (drop-len (corIns c) Q))

unC-ev : ∀ c y as u cs → raw (unCV c (length as) y) (as ++ u ∷ cs) ≡ ap y (as ++ splitC c u ++ cs)
unC-ev c y as u cs rewrite take-len as (u ∷ cs) | drop-len as (u ∷ cs) | drop-suc-len as u cs = refl

evUn : ∀ {c y P Q Z as u cs} → y ∶ᵥ ((P ++ corIns c ++ Q) ▸ Z) → InL P as → IF (corOut c) u → InL Q cs →
       ap (unCV c (length P) y) (as ++ u ∷ cs) ≡ ap y (as ++ splitC c u ++ cs)
evUn {c} {y} {P} {Q} {Z} {as} {u} {cs} ty ia iu ic =
  trans (ap-ty (unCV c (length P) y)
           (subst (λ M → InL (ins M) (as ++ u ∷ cs)) (sym (unProf-eq c (tprof ty))) (InL-++ ia (iu ∷ ic))))
        (subst (λ k → raw (unCV c k y) (as ++ u ∷ cs) ≡ ap y (as ++ splitC c u ++ cs)) (InL-len ia)
               (unC-ev c y as u cs))

T-unCV : ∀ {y P c Q Z} → y ∶ᵥ ((P ++ corIns c ++ Q) ▸ Z) → unCV c (length P) y ∶ᵥ ((P ++ corOut c ∷ Q) ▸ Z)
T-unCV {y} {P} {c} {Q} {Z} ty = tyd (unProf-eq c (tprof ty)) tin′ tmono′
  where
  tin′ : ∀ {us} → InL (P ++ corOut c ∷ Q) us → IF Z (ap (unCV c (length P) y) us)
  tin′ q with InL-split P q
  ... | sp2 a (u ∷ cs) refl ia (iu ∷ ic) =
    subst (IF Z) (sym (evUn {c = c} {P = P} {Q = Q} ty ia iu ic)) (tin ty (InL-++ ia (InL-++ (splitC-In c iu) ic)))
  tmono′ : ∀ {us vs} → InL (P ++ corOut c ∷ Q) us → InL (P ++ corOut c ∷ Q) vs →
           LeL (P ++ corOut c ∷ Q) us vs → LF Z (ap (unCV c (length P) y) us) (ap (unCV c (length P) y) vs)
  tmono′ q q′ l with InL-split P q | InL-split P q′
  ... | sp2 a (u ∷ cs) refl ia (iu ∷ ic) | sp2 a′ (u′ ∷ cs′) refl ia′ (iu′ ∷ ic′) with LeL-split ia ia′ l
  ...   | la , (lu ∷ lc) =
    subst₂′ (LF Z) (sym (evUn {c = c} {P = P} {Q = Q} ty ia iu ic)) (sym (evUn {c = c} {P = P} {Q = Q} ty ia′ iu′ ic′))
      (tmono ty (InL-++ ia (InL-++ (splitC-In c iu) ic)) (InL-++ ia′ (InL-++ (splitC-In c iu′) ic′))
                (LeL-++ la (LeL-++ (splitC-mono c iu iu′ lu) lc)))

unC-lV : ∀ {x P c Q Z} → x ∶ᵥ ((P ++ corOut c ∷ Q) ▸ Z) →
         unCV c (length P) (pcV x (length P) (corV c)) ≈ᵥ x
unC-lV {x} {P} {c} {Q} {Z} tx = ≈-intro (trans (tprof tL) (sym (tprof tx))) fn
  where
  tpc = T-pcV tx (T-corV c)
  tL  = T-unCV {P = P} {c = c} {Q = Q} tpc
  fn : ∀ ws → InL (ins (prof (unCV c (length P) (pcV x (length P) (corV c))))) ws →
       ap (unCV c (length P) (pcV x (length P) (corV c))) ws ≡ ap x ws
  fn ws q with InL-split P (subst (λ M → InL (ins M) ws) (tprof tL) q)
  ... | sp2 a (u ∷ cs) refl ia (iu ∷ ic) =
    trans (evUn {c = c} {P = P} {Q = Q} tpc ia iu ic)
    (trans (evPC {P = P} {Y = corOut c} {Q = Q} tx (T-corV c) refl ia (splitC-In c iu) ic)
           (cong (λ z → ap x (a ++ z ∷ cs)) (cor-split c iu)))

unC-rV : ∀ {y P c Q Z} → y ∶ᵥ ((P ++ corIns c ++ Q) ▸ Z) →
         pcV (unCV c (length P) y) (length P) (corV c) ≈ᵥ y
unC-rV {y} {P} {c} {Q} {Z} ty = ≈-intro (trans (tprof tL) (sym (tprof ty))) fn
  where
  tun = T-unCV {P = P} {c = c} {Q = Q} ty
  tL  = T-pcV tun (T-corV c)
  fn : ∀ ws → InL (ins (prof (pcV (unCV c (length P) y) (length P) (corV c)))) ws →
       ap (pcV (unCV c (length P) y) (length P) (corV c)) ws ≡ ap y ws
  fn ws q with InL-split3 P (corIns c) Q (subst (λ M → InL (ins M) ws) (tprof tL) q)
  ... | sp3 a b cs refl ia ib ic =
    trans (evPC {P = P} {Y = corOut c} {Q = Q} tun (T-corV c) refl ia ib ic)
    (trans (evUn {c = c} {P = P} {Q = Q} ty ia (tin (T-corV c) ib) ic)
           (cong (λ z → ap y (a ++ z ++ cs)) (split-cor c ib)))

------------------------------------------------------------------------
-- Closures

T-curLV : ∀ {y A Φ C} → y ∶ᵥ ((A ∷ Φ) ▸ C) → curLV A C y ∶ᵥ (Φ ▸ (A \\ C))
T-curLV {y} {A} {Φ} {C} ty =
  tyRaw (curLV A C y) (cong (λ M → drop 1 (ins M) ▸ (A \\ C)) (tprof ty))
    (λ {ws} q → tabF-In (fmC A) (fmC C) (λ a → ap y (a ∷ ws)) (λ a qa → tin ty (qa ∷ q))
                  (λ a b qa qb l → tmono ty (qa ∷ q) (qb ∷ q) (l ∷ LeL-refl q)))
    (λ {ws} {vs} q q′ l → tabF-le (fmC A) (fmC C) _ _
                  (λ a qa → tmono ty (qa ∷ q) (qa ∷ q′) (leC-refl (fmC A) a qa ∷ l)))

T-curRV : ∀ {y A Φ C} → y ∶ᵥ ((Φ ++ A ∷ []) ▸ C) → curRV A C y ∶ᵥ (Φ ▸ (C // A))
T-curRV {y} {A} {Φ} {C} ty =
  tyRaw (curRV A C y) (trans (cong (λ M → init (ins M) ▸ (C // A)) (tprof ty)) (cong (_▸ (C // A)) (init-snoc Φ A)))
    (λ {ws} q → tabF-In (fmC A) (fmC C) (λ a → ap y (ws ++ a ∷ [])) (λ a qa → tin ty (InL-++ q (qa ∷ [])))
                  (λ a b qa qb l → tmono ty (InL-++ q (qa ∷ [])) (InL-++ q (qb ∷ [])) (LeL-++ (LeL-refl q) (l ∷ []))))
    (λ {ws} {vs} q q′ l → tabF-le (fmC A) (fmC C) _ _
                  (λ a qa → tmono ty (InL-++ q (qa ∷ [])) (InL-++ q′ (qa ∷ []))
                                     (LeL-++ l (leC-refl (fmC A) a qa ∷ []))))

curL-lV : ∀ {x A Φ C} → x ∶ᵥ (Φ ▸ (A \\ C)) → curLV A C (pcV (evLV A C) 1 x) ≈ᵥ x
curL-lV {x} {A} {Φ} {C} tx = ≈-intro (trans (tprof tL) (trans (cong (_▸ (A \\ C)) (++-[] Φ)) (sym (tprof tx)))) fn
  where
  te = T-pcV {P = A ∷ []} {Y = A \\ C} {Q = []} (T-evLV A C) tx
  tL = T-curLV te
  fn : ∀ ws → InL (ins (prof (curLV A C (pcV (evLV A C) 1 x)))) ws →
       ap (curLV A C (pcV (evLV A C) 1 x)) ws ≡ ap x ws
  fn ws q =
    trans (ap-ty (curLV A C (pcV (evLV A C) 1 x)) q)
    (trans (tabF-cong (fmC A) _ _ (λ a qa →
              trans (cong (ap (pcV (evLV A C) 1 x)) (cong (a ∷_) (sym (++-[] ws))))
              (trans (evPC {P = A ∷ []} {Y = A \\ C} {Q = []} {Z = C} {Xs = Φ} (T-evLV A C) tx refl (qa ∷ []) qΦ [])
                     (ap-ty (evLV A C) {a ∷ ap x ws ∷ []} (qa ∷ tin tx qΦ ∷ [])))))
           (tab-eta (fmC A) (fmC C) (ap x ws) (tin tx qΦ)))
    where
    qΦ : InL Φ ws
    qΦ = subst (λ L → InL L ws) (++-[] Φ) (subst (λ M → InL (ins M) ws) (tprof tL) q)

curL-rV : ∀ {y A Φ C} → y ∶ᵥ ((A ∷ Φ) ▸ C) → pcV (evLV A C) 1 (curLV A C y) ≈ᵥ y
curL-rV {y} {A} {Φ} {C} ty = ≈-intro (trans (tprof tL) (trans (cong (λ L → (A ∷ L) ▸ C) (++-[] Φ)) (sym (tprof ty)))) fn
  where
  tc = T-curLV ty
  tL = T-pcV {P = A ∷ []} {Y = A \\ C} {Q = []} (T-evLV A C) tc
  fn : ∀ ws → InL (ins (prof (pcV (evLV A C) 1 (curLV A C y)))) ws →
       ap (pcV (evLV A C) 1 (curLV A C y)) ws ≡ ap y ws
  fn ws q with subst (λ M → InL (ins M) ws) (trans (tprof tL) (cong (λ L → (A ∷ L) ▸ C) (++-[] Φ))) q
  ... | _∷_ {u = a} {us = us} qa qΦ =
    trans (cong (ap (pcV (evLV A C) 1 (curLV A C y))) (cong (a ∷_) (sym (++-[] us))))
    (trans (evPC {P = A ∷ []} {Q = []} (T-evLV A C) tc refl (qa ∷ []) qΦ [])
    (trans (ap-ty (evLV A C) {a ∷ ap (curLV A C y) us ∷ []} (qa ∷ tin tc qΦ ∷ []))
    (trans (cong (λ z → app (fmC A) z a) (ap-ty (curLV A C y) qΦ′))
           (app-tab (fmC A) (λ b → ap y (b ∷ us)) a qa))))
    where
    qΦ′ : InL (ins (prof (curLV A C y))) us
    qΦ′ = subst (λ M → InL (ins M) us) (sym (tprof tc)) qΦ

curR-lV : ∀ {x A Φ C} → x ∶ᵥ (Φ ▸ (C // A)) → curRV A C (pcV (evRV A C) 0 x) ≈ᵥ x
curR-lV {x} {A} {Φ} {C} tx = ≈-intro (trans (tprof tL) (sym (tprof tx))) fn
  where
  te = T-pcV {P = []} {Y = C // A} {Q = A ∷ []} (T-evRV A C) tx
  tL = T-curRV {A = A} {Φ = Φ} te
  fn : ∀ ws → InL (ins (prof (curRV A C (pcV (evRV A C) 0 x)))) ws →
       ap (curRV A C (pcV (evRV A C) 0 x)) ws ≡ ap x ws
  fn ws q =
    trans (ap-ty (curRV A C (pcV (evRV A C) 0 x)) q)
    (trans (tabF-cong (fmC A) _ _ (λ a qa →
              trans (evPC {P = []} {Y = C // A} {Q = A ∷ []} {Z = C} {Xs = Φ} (T-evRV A C) tx refl [] qΦ (qa ∷ []))
                    (ap-ty (evRV A C) {ap x ws ∷ a ∷ []} (tin tx qΦ ∷ qa ∷ []))))
           (tab-eta (fmC A) (fmC C) (ap x ws) (tin tx qΦ)))
    where
    qΦ : InL Φ ws
    qΦ = subst (λ M → InL (ins M) ws) (tprof tL) q

curR-rV : ∀ {y A Φ C} → y ∶ᵥ ((Φ ++ A ∷ []) ▸ C) → pcV (evRV A C) 0 (curRV A C y) ≈ᵥ y
curR-rV {y} {A} {Φ} {C} ty = ≈-intro (trans (tprof tL) (sym (tprof ty))) fn
  where
  tc = T-curRV {A = A} {Φ = Φ} ty
  tL = T-pcV {P = []} {Y = C // A} {Q = A ∷ []} (T-evRV A C) tc
  fn : ∀ ws → InL (ins (prof (pcV (evRV A C) 0 (curRV A C y)))) ws →
       ap (pcV (evRV A C) 0 (curRV A C y)) ws ≡ ap y ws
  fn ws q with InL-split Φ (subst (λ M → InL (ins M) ws) (tprof tL) q)
  ... | sp2 us (a ∷ []) refl qΦ (qa ∷ []) =
    trans (evPC {P = []} {Q = A ∷ []} (T-evRV A C) tc refl [] qΦ (qa ∷ []))
    (trans (ap-ty (evRV A C) {ap (curRV A C y) us ∷ a ∷ []} (tin tc qΦ ∷ qa ∷ []))
    (trans (cong (λ z → app (fmC A) z a) (ap-ty (curRV A C y) (subst (λ M → InL (ins M) us) (sym (tprof tc)) qΦ)))
           (app-tab (fmC A) (λ b → ap y (us ++ b ∷ [])) a qa)))

------------------------------------------------------------------------
-- The model

posetModel : Model
posetModel = record
  { V = Val
  ; _≈_ = _≈ᵥ_
  ; ≈-refl = ≈ᵥ-refl
  ; ≈-sym = ≈ᵥ-sym
  ; ≈-trans = ≈ᵥ-trans
 
  ; _∶_ = _∶ᵥ_
  ; ∶-≈ = ∶ᵥ-≈
 
  ; pc = pcV
  ; idv = idV
  ; cor = corV
  ; evL = evLV
  ; evR = evRV
  ; δ = δV
  ; σ = σV
 
  ; unC = unCV
  ; curL = curLV
  ; curR = curRV
 
  ; T-pc = λ {f} {g} {P} {Y} {Q} {Z} {Xs} → T-pcV {f} {g} {P} {Y} {Q} {Z} {Xs}
  ; T-id = T-idV
  ; T-cor = T-corV
  ; T-evL = T-evLV
  ; T-evR = T-evRV
 
  ; T-δ = T-δV
  ; T-σ = T-σV
 
  ; pc-cong = pc-congV
  ; seq = λ {f} {g} {h} {P} {Y} {Q} {Z} {P′} {X} {Q′} {Ws} → seqV {f} {g} {h} {P} {Y} {Q} {Z} {P′} {X} {Q′} {Ws}
  ; par = λ {f} {g} {h} {P} {Y} {M} {W} {Q} {Z} {Xs} {Ws} → parV {f} {g} {h} {P} {Y} {M} {W} {Q} {Z} {Xs} {Ws}
  ; unit-l = λ {g} {Xs} {Y} → unit-lV {g} {Xs} {Y}
  ; unit-r = λ {f} {P} {Y} {Q} {Z} → unit-rV {f} {P} {Y} {Q} {Z}
 
  ; T-unC = λ {y} {P} {c} {Q} {Z} → T-unCV {y} {P} {c} {Q} {Z}
  ; unC-l = λ {x} {P} {c} {Q} {Z} → unC-lV {x} {P} {c} {Q} {Z}
  ; unC-r = λ {y} {P} {c} {Q} {Z} → unC-rV {y} {P} {c} {Q} {Z}
  ; unC-cong = unC-congV
 
  ; T-curL = λ {y} {A} {Φ} {C} → T-curLV {y} {A} {Φ} {C}
  ; curL-l = λ {x} {A} {Φ} {C} → curL-lV {x} {A} {Φ} {C}
  ; curL-r = λ {y} {A} {Φ} {C} → curL-rV {y} {A} {Φ} {C}
  ; curL-cong = curL-congV
 
  ; T-curR = λ {y} {A} {Φ} {C} → T-curRV {y} {A} {Φ} {C}
  ; curR-l = λ {x} {A} {Φ} {C} → curR-lV {x} {A} {Φ} {C}
  ; curR-r = λ {y} {A} {Φ} {C} → curR-rV {y} {A} {Φ} {C}
  ; curR-cong = curR-congV
 
  ; σδ-suc = σδ-sucV
  ; σδ-0 = σδ-0V
  }
