module DriftGraph where

open import Agda.Primitive                       using (Level; lzero)
open import FirstDifference                      using (Dist; D0)
open import Data.List                            using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat                             using (ℕ; suc)
open import Relation.Nullary.Negation            using (¬_)

------------------------------------------------------------------------
-- 1. DriftGraph als Record
------------------------------------------------------------------------

record DriftGraph : Set₁ where
  field
    ledger      : List Dist
    -- Driftkante, d.h. ∆(δ₁,δ₂) ∈ ledger
    driftEdge   : Dist → Dist → Set
    -- Aus einem irred-Beweis erzeugt drift die neue Distinktion
    drift       : ∀ (δ₁ δ₂ : Dist) → driftEdge δ₁ δ₂ → Dist
    -- Irreduzibilitäts-Predikat: δ ∉ prev
    irreducible : Dist → List Dist → Set

open DriftGraph public

------------------------------------------------------------------------
-- 2. Eine konkrete Instanz G
------------------------------------------------------------------------

postulate
  G : DriftGraph

-- projectioniert alle Felder auf G
open DriftGraph G public

------------------------------------------------------------------------
-- 3. Semantische Zeit T und ihre Axiome
------------------------------------------------------------------------

postulate
  T : List Dist → ℕ

postulate
  T-irreducible :
    ∀ {δ prev}
    → irreducible δ prev
    → T (δ ∷ prev) ≡ suc (T prev)

postulate
  T-reducible :
    ∀ {δ prev}
    → ¬ (irreducible δ prev)
    → T (δ ∷ prev) ≡ T prev
