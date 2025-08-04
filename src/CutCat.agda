module CutCat where

open import Agda.Primitive using (Level; lzero)
open import Data.Nat         using (ℕ; suc)                          -- suc jetzt hier
open import Data.Nat.Properties
  using (_≤_; z≤n; s≤s; ≤-refl; ≤-trans)                             -- ≤-refl/≤-trans hier
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

-- Minimal Category record
record Category (ℓ₁ ℓ₂ : Level) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    Obj      : Set ℓ₁
    Hom      : Obj → Obj → Set ℓ₂
    id       : {A : Obj} → Hom A A
    _∘_      : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    id-left  : {A B : Obj}(f : Hom A B) → (_∘_ (id {B = B}) f) ≡ f
    id-right : {A B : Obj}(f : Hom A B) → (_∘_ f (id {A = A})) ≡ f
    assoc    : {A B C D : Obj}
               (h : Hom C D) (g : Hom B C) (f : Hom A B) →
               (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)

open Category

-- Die freie, dünne Kategorie auf ℕ mit Hom(m,n) ≡ (m ≤ n)
CutCat : Category lzero lzero
CutCat .Obj      = ℕ
CutCat .Hom      = λ m n → m ≤ n
CutCat .id       = λ {A} → ≤-refl {m = A}
CutCat ._∘_      = λ {A}{B}{C} f g → ≤-trans g f
CutCat .id-left  = λ f → refl
CutCat .id-right = λ f → refl
CutCat .assoc    = λ h g f → refl
