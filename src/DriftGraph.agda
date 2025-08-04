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
    driftEdge   : Dist → Dist → Set
    drift       : ∀ (δ₁ δ₂ : Dist) → driftEdge δ₁ δ₂ → Dist
    irreducible : Dist → List Dist → Set

------------------------------------------------------------------------
-- 2. Eine konkrete Instanz G
------------------------------------------------------------------------

postulate
  G : DriftGraph

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
