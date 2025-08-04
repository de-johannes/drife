module UnavoidabilityProof where

open import Agda.Primitive                         using (Level; lzero)
open import FirstDifference                        using (Dist; D0; Token; instantiate; tokenPrinciple; P)
open import Data.Empty                             using (⊥)
open import Data.List                              using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality  using (_≡_; refl)
open import Data.Product                           using (Σ; _,_)
open import Data.Unit                              using (⊤; tt)
open import Relation.Nullary.Negation              using (¬_)

------------------------------------------------------------------------
-- 1. Syntax der minimalen Sequentenformeln
------------------------------------------------------------------------

data Formula : Set where
  atom    : Dist → Formula
  not     : Formula → Formula
  sequent : List Formula → List Formula → Formula

------------------------------------------------------------------------
-- 2. Ableitungs-Judgment im SC△
------------------------------------------------------------------------

postulate
  derive : Formula → Set

------------------------------------------------------------------------
-- 3. Self-Subversion Lemma
------------------------------------------------------------------------

postulate
  selfSubversion :
    ∀ {Γ Δ : List Formula} {p : P}
    → derive (sequent Γ Δ)
    → derive (sequent (atom (D0 p)) Δ)

------------------------------------------------------------------------
-- 4. Unavoidability Theorem
------------------------------------------------------------------------

postulate
  unavoidability :
    ∀ {Γ Δ : List Formula} {p : P}
    → Δ ≡ (not (atom (D0 p)) ∷ [])
    → ¬ derive (sequent Γ Δ)

------------------------------------------------------------------------
-- 5. Meta-logischer Fixed-Point (klassische Korollar)
------------------------------------------------------------------------

postulate
  metaFixedPoint : ⊤
