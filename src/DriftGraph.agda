module DriftGraph where

open import Data.Bool using (Bool; _∧_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; zipWith)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (any?) -- statt any

------------------------------------------------------------------------
-- 1. Distinctions als Bool-Vektor
------------------------------------------------------------------------

record Dist (n : ℕ) : Set where
  constructor mkDist
  field poles : Vec Bool n
open Dist public

-- Drift = Boolesches UND der Vektoren
drift : ∀ {n} → Dist n → Dist n → Dist n
drift d1 d2 = mkDist (zipWith _∧_ (poles d1) (poles d2))

------------------------------------------------------------------------
-- 2. Boolesche Konjunktionen aller bisherigen Dists
------------------------------------------------------------------------

allConjunctions : ∀ {n} → List (Dist n) → List (Dist n)
allConjunctions []       = []
allConjunctions (x ∷ xs) =
  let rec = allConjunctions xs
  in  x ∷ rec ++ map (drift x) rec

------------------------------------------------------------------------
-- 3. Irreduzibilität
------------------------------------------------------------------------

irreducible : ∀ {n} → Dist n → List (Dist n) → Set
irreducible δ prev =
  ¬ (any? (λ d → poles d ≡ poles δ) (allConjunctions prev))

------------------------------------------------------------------------
-- 4. Semantische Zeit
------------------------------------------------------------------------

T : ∀ {n} → List (Dist n) → ℕ
T [] = zero
T (δ ∷ prev) with irreducible δ prev
... | irr = suc (T prev)
... | _   = T prev

------------------------------------------------------------------------
-- 5. Arrow of Time Lemma
------------------------------------------------------------------------

ArrowOfTime :
  ∀ {n} (δ : Dist n) (prev : List (Dist n)) →
  (T (δ ∷ prev) ≡ T prev) ⊎ (T (δ ∷ prev) ≡ suc (T prev))
ArrowOfTime δ prev with irreducible δ prev
... | irr = inj₂ refl
... | _   = inj₁ refl
