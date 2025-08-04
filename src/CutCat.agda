module CutCat where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat       using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat.Base  using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  ( ≤-refl
  ; ≤-trans
  ; ≤-identityˡ
  ; ≤-identityʳ
  )

record Category (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Obj      : Set ℓ₁
    Hom      : Obj → Obj → Set ℓ₂
    id       : (A : Obj) → Hom A A
    _∘_      : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    id-left  : {A B : Obj} (f : Hom A B) → _∘_ (id B) f ≡ f
    id-right : {A B : Obj} (f : Hom A B) → _∘_ f (id A) ≡ f
    assoc    : {A B C D : Obj}
               (h : Hom C D) (g : Hom B C) (f : Hom A B) →
               _∘_ h (_∘_ g f) ≡ _∘_ (_∘_ h g) f

open Category

CutCat : Category lzero lzero
Category.Obj CutCat      = ℕ
Category.Hom CutCat      = λ m n → m ≤ n
Category.id  CutCat      = λ m → ≤-refl
Category._∘_ CutCat      = λ f g → ≤-trans g f
Category.id-left  CutCat = λ f → ≤-identityʳ f
Category.id-right CutCat = λ f → ≤-identityˡ f
Category.assoc    CutCat = λ h g f → refl
