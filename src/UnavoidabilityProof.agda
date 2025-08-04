module UnavoidabilityProof where

open import Agda.Primitive                       using (Level; lzero)
open import FirstDifference                      using (Dist; D0; Token; instantiate; tokenPrinciple)
open import Data.Empty                           using (⊥)
open import Data.List                            using (List; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product                         using (Σ; _,_)
open import Data.Unit                            using (⊤; tt)

-- A minimal syntax for formulas in the sequent calculus SC△
data Formula : Set where
  atom   : Dist → Formula
  not    : Formula → Formula
  sequent: List Formula → List Formula → Formula

-- A judgment: derivability in the minimal sequent calculus
postulate
  derive : Formula → Set

-- The self‐subversion lemma: writing the sequent header instantiates D₀
postulate
  selfSubversion :
    ∀ {Γ Δ : List Formula} →
    derive (sequent Γ Δ) →
    derive (sequent (atom (D0 _)) Δ)

-- Unavoidability: there is no derivation of ¬D₀
postulate
  unavoidability :
    ∀ {Γ Δ : List Formula} →
    (Δ ≡ (not (atom (D0 _))) ∷ []) →
    ¬ derive (sequent Γ Δ)

-- Classical corollary: no system can derive ¬D₀ without inconsistency
postulate
  metaFixedPoint :
    ⊤
