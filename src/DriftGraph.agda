module DriftGraph where

open import Agda.Primitive               using (Level; lzero)
open import FirstDifference              using (Dist; D0)
open import Data.List                    using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat                     using (ℕ)
open import Data.List.Membership.DecPropositional using (_∈_; here; there)

-- A DriftGraph is a growing ledger of distinctions with drift edges
record DriftGraph : Set where
  field
    -- The chronological list of all distinctions created so far
    ledger       : List Dist
    -- A drift edge exists between δ₁ and δ₂ exactly when ∆(δ₁,δ₂) ∈ ledger
    driftEdge    : (δ₁ δ₂ : Dist) → Set
    -- The drift operator: given an irreducibility proof, produces the new distinction
    drift        : (δ₁ δ₂ : Dist) → driftEdge δ₁ δ₂ → Dist
    -- Irreducibility predicate: δ ∉ previous ledger entries
    irreducible  : (δ : Dist) → (prev : List Dist) → Set

open DriftGraph

-- Semantic time: count of irreducible entries
postulate
  T : List Dist → ℕ

-- We require that T grows by exactly 1 on each irreducible drift step
postulate
  T-irreducible :
    ∀ {δ : Dist} {prev : List Dist} →
    irreducible δ prev →
    T (δ ∷ prev) ≡ suc (T prev)

  T-reducible :
    ∀ {δ : Dist} {prev : List Dist} →
    (¬ irreducible δ prev) →
    T (δ ∷ prev) ≡ T prev
