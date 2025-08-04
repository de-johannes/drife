module CutCat where

open import Agda.Primitive            using (Level ; lzero ; lsuc ; _⊔_)
open import Data.Nat                  using (ℕ ; zero ; suc)
open import Data.Nat.Base             using (_≤_ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality
                                     using (_≡_ ; refl ; cong)

------------------------------------------------------------------------
-- 1. Primal Distinction  (Cut-Baum)
------------------------------------------------------------------------

data Cut : Set where
  ◇    : Cut            -- pures Potential
  mark : Cut → Cut      -- einmal unterscheiden

-- Emergenz von ℕ: Verschachtelungstiefe
depth : Cut → ℕ
depth ◇        = zero
depth (mark c) = suc (depth c)

-- Polarity / Bool-Emergenz
neg : Cut → Cut
neg ◇        = mark ◇
neg (mark _) = ◇

doubleNeg : ∀ c → neg (neg c) ≡ c
doubleNeg ◇        = refl
doubleNeg (mark _) = refl

------------------------------------------------------------------------
-- 2. Hilfsbeweise zu ≤
------------------------------------------------------------------------

≤-trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤n      _             = z≤n
≤-trans (s≤s p)  z≤n           = ()        -- unmöglich
≤-trans (s≤s p) (s≤s q)        = s≤s (≤-trans p q)

≤-id-left  : ∀ {m n} (p : m ≤ n) → ≤-trans z≤n p ≡ p
≤-id-left z≤n     = refl
≤-id-left (s≤s p) = cong s≤s (≤-id-left p)

≤-id-right : ∀ {m n} (p : m ≤ n) → ≤-trans p z≤n ≡ p
≤-id-right z≤n     = refl
≤-id-right (s≤s ())               -- ebenfalls unmöglich

------------------------------------------------------------------------
-- 3. Minimaler Kategorie-Record
------------------------------------------------------------------------

record Category (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Obj      : Set ℓ₁
    Hom      : Obj → Obj → Set ℓ₂
    id       : (A : Obj) → Hom A A
    _∘_      : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    id-left  : {A B : Obj} (f : Hom A B) → _∘_ (id B) f ≡ f
    id-right : {A B : Obj} (f : Hom A B) → _∘_ f (id A) ≡ f
    assoc    : {A B C D : Obj}
               (h : Hom C D) (g : Hom B C) (f : Hom A B)
               → _∘_ h (_∘_ g f) ≡ _∘_ (_∘_ h g) f

open Category public

------------------------------------------------------------------------
-- 4. CutCat  (freie dünne Kategorie auf ℕ)
------------------------------------------------------------------------

CutCat : Category lzero lzero
Obj      CutCat = ℕ
Hom      CutCat = λ m n → m ≤ n
id       CutCat = λ m → z≤n
_∘_      CutCat = λ {A B C} g f → ≤-trans f g   -- erst f, dann g
id-left  CutCat = λ f → ≤-id-right f
id-right CutCat = λ f → ≤-id-left  f
assoc    CutCat = λ h g f → refl

------------------------------------------------------------------------
-- 5. Kanonischer Ledger-Baum pro Level + Funktorisches Hom-Mapping
------------------------------------------------------------------------

ledgerCut : ℕ → Cut
ledgerCut zero    = ◇
ledgerCut (suc n) = mark (ledgerCut n)

depth-lemma : ∀ n → depth (ledgerCut n) ≡ n
depth-lemma zero    = refl
depth-lemma (suc n) = cong suc (depth-lemma n)

FunctorHom :
  ∀ {m n} → m ≤ n → depth (ledgerCut m) ≤ depth (ledgerCut n)
FunctorHom {m} {n} p rewrite depth-lemma m | depth-lemma n = p

------------------------------------------------------------------------
-- 6. Kurzer Test (REPL):
--    depth (mark (mark ◇))        ↦ 2
--    doubleNeg (mark ◇)           ↦ refl
--    _∘_ CutCat (s≤s z≤n) (s≤s (s≤s z≤n))
--                                 ↦ s≤s (s≤s z≤n)
------------------------------------------------------------------------
