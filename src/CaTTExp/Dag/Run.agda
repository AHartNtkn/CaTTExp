------------------------------------------------------------------------
-- Running the DAG checker on a certificate written as strings
-- (tools/dag_cert.py). The decoder is untrusted plumbing: soundness
-- (CaTTExp.Dag.Sound) is about whatever tables it produces, and the
-- final statement only mentions the query, compared with the decoded
-- root inside the checked boolean.
--
-- Performance note: Agda does not memoize top-level definitions, so the
-- decoded tables are always passed as function arguments (shared thunks
-- under the call-by-need reduction machine), never referenced from a
-- top-level name inside the checks.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Dag.Table
open import CaTTExp.Dag.Trie
open import CaTTExp.Dag.NatMap
open import Agda.Builtin.String using (String; primStringToList)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Nat using (_*_; div-helper; mod-helper)
open import Agda.Builtin.Strict using (primForce)

module CaTTExp.Dag.Run where

------------------------------------------------------------------------
-- Decoding. Everything is forced as it is decoded (primForce): a lazy
-- number or list here would keep the rest of the input alive.

private
  digits : Nat → List Char → List Nat
  digits acc []       = []
  digits acc (c ∷ cs) = step (primCharToNat c)
    where
    step : Nat → List Nat
    step k = if k <ℕ 80 then primForce (acc * 32 + (k ∸ 48)) (λ v → v ∷ digits 0 cs)
                         else primForce (acc * 32 + (k ∸ 93)) (λ v → digits v cs)

  chars : List String → List Char
  chars []       = []
  chars (s ∷ ss) = primStringToList s ++ chars ss


big : Nat
big = 1000000000000

nums : List String → List Nat
nums ss = digits 0 (chars ss)

private
  -- A type: its dimension d, then d (source, target) pairs, bottom first.
  rtyGo : Nat → RTy → List Nat → Σ RTy (λ _ → List Nat)
  rtyGo zero    A xs           = A , xs
  rtyGo (suc d) A (s ∷ t ∷ xs) = primForce (arrᵣ A s t) (λ B → rtyGo d B xs)
  rtyGo (suc d) A xs           = A , xs

rty : List Nat → Σ RTy (λ _ → List Nat)
rty []       = ⋆ᵣ , []
rty (d ∷ xs) = rtyGo d ⋆ᵣ xs

------------------------------------------------------------------------
-- Packed entries. Every table entry (an item, a typing claim, a
-- free-variable list) is one number encoding a list of naturals, kept in
-- a bucket map (CaTTExp.Dag.NatMap); 0 means absent. Entries are
-- unpacked on every lookup. Unpacking takes fuel, which only bounds the
-- length: soundness is about whatever comes out.

packBase : Nat
packBase = 16777216

private
  unpackGo : Nat → Nat → List Nat
  unpackGo zero    n = []
  unpackGo (suc f) zero = []
  unpackGo (suc f) n@(suc _) =
    (mod-helper 0 (packBase ∸ 1) n (packBase ∸ 1) ∸ 1) ∷
    unpackGo f (div-helper 0 (packBase ∸ 1) n (packBase ∸ 1))

unpack : Nat → List Nat
unpack = unpackGo 100000

rtyL : RTy → List Nat → RTy
rtyL A (s ∷ t ∷ xs) = rtyL (arrᵣ A s t) xs
rtyL A _            = A

-- Items: [0, i] = V i; [1, h, args (last first)] = C h args; [2] = E;
-- [3, c, type] = S c A; [4, c, type] = H c A; a type as its (source,
-- target) pairs, bottom first.
parseI : List Nat → Maybe Item
parseI (0 ∷ i ∷ _)  = just (V i)
parseI (1 ∷ h ∷ as) = just (C h as)
parseI (2 ∷ _)      = just E
parseI (3 ∷ c ∷ xs) = just (S c (rtyL ⋆ᵣ xs))
parseI (4 ∷ c ∷ xs) = just (H c (rtyL ⋆ᵣ xs))
parseI _            = nothing

itemOf : Nat → Maybe Item
itemOf v = parseI (unpack v)

-- Claims and free-variable lists: a marker 1, then the type / the list.
parseJ : List Nat → Maybe RTy
parseJ (_ ∷ xs) = just (rtyL ⋆ᵣ xs)
parseJ []       = nothing

claimOf : Nat → Maybe RTy
claimOf v = parseJ (unpack v)

parseF : List Nat → Maybe (List Nat)
parseF (_ ∷ xs) = just xs
parseF []       = nothing

fvOf : Nat → Maybe (List Nat)
fvOf v = parseF (unpack v)

------------------------------------------------------------------------
-- Building the maps from the decoded streams: buckets "q v0 … v15".

private
  -- At most m buckets (and at most f steps of fuel).
  bucketsGo : Nat → Nat → NatMap → List Nat → Σ NatMap (λ _ → List Nat)
  bucketsGo zero    _       t xs = t , xs
  bucketsGo (suc f) zero    t xs = t , xs
  bucketsGo (suc f) (suc m) t (q ∷ v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ v5 ∷ v6 ∷ v7 ∷ v8 ∷ v9 ∷ v10 ∷ v11 ∷ v12 ∷ v13 ∷ v14 ∷ v15 ∷ xs) =
    primForce (bk v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) λ b →
    primForce (insert q b t) λ t' → bucketsGo f m t' xs
  bucketsGo (suc f) (suc m) t xs = t , xs

-- A whole stream of buckets (items, free variables, a query).
natmap : List Nat → NatMap
natmap xs = fst (bucketsGo big big tleaf xs)

-- Claims: blocks "c m (bucket)^m", one per context.
private
  claimsGo : Nat → Trie NatMap → List Nat → Trie NatMap
  claimsGo zero    t _            = t
  claimsGo (suc f) t (c ∷ m ∷ xs) = next (bucketsGo big m tleaf xs)
    where
    next : Σ NatMap (λ _ → List Nat) → Trie NatMap
    next (b , rest) = primForce (insert c b t) (λ t' → claimsGo f t' rest)
  claimsGo (suc f) t _            = t

claims : List Nat → Trie NatMap
claims = claimsGo big tleaf

------------------------------------------------------------------------
-- Lookup functions

blockOf : NatMap → Nat → Maybe RTy
blockOf t a = claimOf (lookupN a t)

lookJ₂ : Nat → Maybe NatMap → Maybe RTy
lookJ₂ n (just t) = blockOf t n
lookJ₂ n nothing  = nothing

lookJ : Trie NatMap → Nat → Nat → Maybe RTy
lookJ Jt c n = lookJ₂ n (lookupT c Jt)

------------------------------------------------------------------------
-- The whole check, on maps passed as arguments.

module _ (K : Nat) (Rt : NatMap) (Jt : Trie NatMap) (Ft : NatMap) where
  Rof : Nat → Maybe Item
  Rof k = itemOf (lookupN k Rt)
  Jof : Nat → Nat → Maybe RTy
  Jof = lookJ Jt
  Fof : Nat → Maybe (List Nat)
  Fof n = fvOf (lookupN n Ft)

  open import CaTTExp.Dag.Check K Rof Jof Fof
  open import CaTTExp.Dag.Unfold Rof

  okI : Nat → Maybe Item → Bool
  okI k (just it) = itemOK k it
  okI k nothing   = true

  okJ : Nat → (Nat → Maybe RTy) → Nat → Maybe RTy → Bool
  okJ c Jc n (just A) = judgOK c Jc n A
  okJ c Jc n nothing  = true

  okF : Nat → Maybe (List Nat) → Bool
  okF n (just xs) = fOK n xs
  okF n nothing   = true

  itemsOK claimsOK fvOK tablesOK : Bool
  itemsOK  = allN (λ k v → okI k (itemOf v)) Rt
  claimsOK = allT (λ c t → allN (λ n v → okJ c (blockOf t) n (claimOf v)) t) Jt
  fvOK     = allN (λ n v → okF n (fvOf v)) Ft
  tablesOK = varsOK K ∧ (itemsOK ∧ (claimsOK ∧ fvOK))

  -- The root claim, compared with a query in ordinary syntax.
  rootOK : Nat → Nat → RTy → Ctx → Ty → Bool
  rootOK g n A Γ B = isCtx (Rof g) ∧ (eqRM (Jof g n) A ∧ ((⟦ g ⟧c ==Ctx Γ) ∧ (⟦ A ⟧ty ==Ty B)))

  certOK : Nat → Nat → RTy → Ctx → Ty → Bool
  certOK g n A Γ B = rootOK g n A Γ B ∧ tablesOK

------------------------------------------------------------------------
-- Queries given as their own table (strings in the item format), for
-- queries too large to compare as trees. The query denotes the
-- unfolding of its table (queryCtxOf, queryTyOf); it is compared with
-- the certificate's root by ids (CaTTExp.Dag.QEq).

qtabOf : NatMap → Nat → Maybe Item
qtabOf Qt k = itemOf (lookupN k Qt)

ctxIn : NatMap → Nat → Ctx
ctxIn Qt = ⟦_⟧c where open import CaTTExp.Dag.Unfold (qtabOf Qt)

tyIn : NatMap → RTy → Ty
tyIn Qt = ⟦_⟧ty where open import CaTTExp.Dag.Unfold (qtabOf Qt)

queryCtxOf : List String → Nat → Ctx
queryCtxOf qs = ctxIn (natmap (nums qs))

queryTyOf : List String → List Nat → Ty
queryTyOf qs A = tyIn (natmap (nums qs)) (fst (rty A))

-- For queries small enough to write in ordinary syntax: the query table
-- unfolds to Γ and B (one decoding of the table, shared).
queryMatches : List String → Nat → List Nat → Ctx → Ty → Bool
queryMatches qs qg qA Γ B = go (natmap (nums qs))
  where
  go : NatMap → Bool
  go Qt = (ctxIn Qt qg ==Ctx Γ) ∧ (tyIn Qt (fst (rty qA)) ==Ty B)

module _ (K : Nat) (Rt : NatMap) (Jt : Trie NatMap) (Ft : NatMap) (Qt : NatMap) where
  Qof : Nat → Maybe Item
  Qof = qtabOf Qt

  open import CaTTExp.Dag.Check K (Rof K Rt Jt Ft) (Jof K Rt Jt Ft) (Fof K Rt Jt Ft)
  open import CaTTExp.Dag.QEq Qof (Rof K Rt Jt Ft)

  qfuel : Nat
  qfuel = big

  okD : Nat → Maybe Item → Bool
  okD k (just it) = decItem k it
  okD k nothing   = true

  qdecOK : Bool
  qdecOK = allN (λ k v → okD k (itemOf v)) Qt

  rootQOK : Nat → Nat → RTy → Nat → RTy → Bool
  rootQOK g n A qg qA =
    isCtx (Rof K Rt Jt Ft g) ∧ (eqRM (Jof K Rt Jt Ft g n) A ∧ (qdecOK ∧ qeqOK qfuel qg g qA A))

  certQOK : Nat → Nat → RTy → Nat → RTy → Bool
  certQOK g n A qg qA = rootQOK g n A qg qA ∧ tablesOK K Rt Jt Ft

------------------------------------------------------------------------
-- Entry points used by generated modules.

runCertQ : Nat → List String → List String → List String → List String →
           Nat → Nat → List Nat → Nat → List Nat → Bool
runCertQ K is cs fs qs g n A qg qA =
  go (natmap (nums is)) (claims (nums cs)) (natmap (nums fs)) (natmap (nums qs))
  where
  go : NatMap → Trie NatMap → NatMap → NatMap → Bool
  go Rt Jt Ft Qt = certQOK K Rt Jt Ft Qt g n (fst (rty A)) qg (fst (rty qA))

runCert : Nat → List String → List String → List String → Nat → Nat → List Nat → Ctx → Ty → Bool
runCert K is cs fs g n A Γ B = go (natmap (nums is)) (claims (nums cs)) (natmap (nums fs))
  where
  go : NatMap → Trie NatMap → NatMap → Bool
  go Rt Jt Ft = certOK K Rt Jt Ft g n (fst (rty A)) Γ B
