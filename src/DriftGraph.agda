module DriftGraph where

open import Agda.Primitive                          using (Level; lzero)
open import FirstDifference                         using (Dist; D0)
open import Data.List                               using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality   using (_≡_; refl)
open import Data.Nat                                using (ℕ; suc)
open import Data.List.Membership.Propositional      using (_∈_; here; there)
open import Relation.Nullary.Negation               using (¬_)

------------------------------------------------------------------------
-- 1. Der DriftGraph-Typ (ledger + Drift–Felder)
------------------------------------------------------------------------

-- Wir heben die Universumsstufe an, damit Felder in Set₁ liegen dürfen.
record DriftGraph : Set₁ where
  field
    -- Chronologische Liste aller bisher erzeugten Distinktionen
    ledger      : List Dist

    -- Driftkante zwischen δ₁ und δ₂ genau dann, wenn ∆(δ₁,δ₂) ∈ ledger
    driftEdge   : Dist → Dist → Set₁

    -- Drift‐Operator: aus einem Irreduzibilitäts‐Beweis entsteht eine neue Distinktion
    drift       : (δ₁ δ₂ : Dist) → driftEdge δ₁ δ₂ → Dist

    -- Irreduzibilitäts‐Prädikat: δ ∉ previous ledger entries
    irreducible : Dist → List Dist → Set₁

open DriftGraph public

------------------------------------------------------------------------
-- 2. Ein konkreter DriftGraph  (Postulat)
------------------------------------------------------------------------

-- Wir definieren eine einzelne DriftGraph‐Instanz G, auf der alle
-- Postulate unten basieren.
postulate
  G : DriftGraph

open DriftGraph G public

------------------------------------------------------------------------
-- 3. Semantic Time T für G
------------------------------------------------------------------------

-- T zählt irreduzible Einträge in einer Ledger‐Liste
postulate
  T : List Dist → ℕ

-- Wenn ein neues δ irreduzibel ist, wächst T um genau 1
postulate
  T-irreducible :
    ∀ {δ prev}
    → irreducible δ prev
    → T (δ ∷ prev) ≡ suc (T prev)

-- Andernfalls bleibt T konstant
postulate
  T-reducible :
    ∀ {δ prev}
    → ¬ (irreducible δ prev)
    → T (δ ∷ prev) ≡ T prev
