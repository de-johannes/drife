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
  ◇    : Cut
  mark : Cut → Cut

-- Tiefe  → ℕ
depth : Cut → ℕ
depth ◇        = zero
depth (mark c) = suc (depth c)

-- Polarity (einfaches Beispiel)
neg : Cut → Cut
neg ◇        = mark ◇
neg (mark _) = ◇
-- (kein involutions-Lemma mehr)

------------------------------------------------------------------------
-- 2. ≤-Hilfsbeweise
------------------------------------------------------------------------

refl≤ : (n : ℕ) → n ≤ n
refl≤ zero    = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

≤-trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤n       _             = z≤n
≤-trans (s≤s p)  (s≤s q)        = s≤s (≤-trans p q)

≤-id-left : ∀ {m n} (p : m ≤ n) → ≤-trans p (refl≤ n) ≡ p
≤-id-left z≤n     = refl
≤-id-left (s≤s p) = cong s≤s (≤-id-left p)

≤-id-right : ∀ {m n} (p : m ≤ n) → ≤-trans (refl≤ m) p ≡ p
≤-id-right z≤n     = refl
≤-id-right (s≤s p) = cong s≤s (≤-id-right p)

------------------------------------------------------------------------
-- 3. Kategorie-Record
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
-- 4. CutCat – freie dünne Kategorie auf ℕ
------------------------------------------------------------------------

CutCat : Category lzero lzero
Obj      CutCat = ℕ
Hom      CutCat = _≤_
id       CutCat = refl≤
_∘_      CutCat = λ {A B C} g f → ≤-trans f g
id-left  CutCat = ≤-id-left
id-right CutCat = ≤-id-right
assoc    CutCat = λ _ _ _ → refl

------------------------------------------------------------------------
-- 5. Kanonischer Ledger-Baum pro Level
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
