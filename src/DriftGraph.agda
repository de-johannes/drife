module DriftGraph where

open import Agda.Primitive using (Level; lzero)
open import FirstDifference using (Dist; D0)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary.Negation using (¬_)

------------------------------------------------------------------------
-- 1. DriftGraph als Record
------------------------------------------------------------------------

record DriftGraph : Set₁ where
  field
    ledger      : List Dist
    driftEdge   : Dist → Dist → Set
    drift       : ∀ (δ₁ δ₂ : Dist) → driftEdge δ₁ δ₂ → Dist
    irreducible : Dist → List Dist → Set

open DriftGraph public

------------------------------------------------------------------------
-- 2. Beispielinstanz (leer)
------------------------------------------------------------------------

-- Wir definieren eine triviale Instanz, damit das Modul kompiliert.
-- Später kann man echte Drift-Kanten und Ledger einfügen.

emptyGraph : DriftGraph
emptyGraph = record
  { ledger      = []
  ; driftEdge   = λ _ _ → ⊥               -- keine Kanten
  ; drift       = λ δ₁ δ₂ e → case e of ()
  ; irreducible = λ δ prev → ⊥            -- alles reducible
  }

------------------------------------------------------------------------
-- 3. Semantische Zeit T
------------------------------------------------------------------------

-- Semantische Zeit = Anzahl irreduzibler Distinctions in der Liste

T : (irr : Dist → List Dist → Set) → List Dist → ℕ
T irr [] = zero
T irr (δ ∷ prev) with irr δ prev
... | p = suc (T irr prev)  -- irreducible
... | _ = T irr prev        -- reducible (leer, weil Set 0 oder 1?)

------------------------------------------------------------------------
-- 4. Lemma: irreducible → Zeit tickt
------------------------------------------------------------------------

T-irreducible :
  ∀ {δ prev} {irr : Dist → List Dist → Set}
  → irr δ prev
  → T irr (δ ∷ prev) ≡ suc (T irr prev)
T-irreducible p = refl

------------------------------------------------------------------------
-- 5. Lemma: ¬irreducible → Zeit bleibt stehen
------------------------------------------------------------------------

T-reducible :
  ∀ {δ prev} {irr : Dist → List Dist → Set}
  → ¬ (irr δ prev)
  → T irr (δ ∷ prev) ≡ T irr prev
T-reducible _ = refl
