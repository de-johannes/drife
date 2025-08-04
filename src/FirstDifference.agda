module FirstDifference where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_)

-- 1. Pure potential (opaque type)
postulate
  P : Set

-- 2. Distinction as the fundamental cut (First Difference)
data Dist : Set where
  D0 : P → Dist

-- 3. Irreversibility axiom:
--    There is no global inverse g : Dist → P with g ∘ D0 ≡ idₚ
postulate
  irreversibility :
    {g : Dist → P} →
    ((p : P) → g (D0 p) ≡ p) →
    ⊥

-- 4. Token Principle (every syntactic token instantiates a distinction)
postulate
  Token        : Set
  instantiate  : Token → Dist
  tokenPrinciple :
    ∀ (t : Token) → Σ P (λ p → instantiate t ≡ D0 p)
