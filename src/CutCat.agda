module CutCat where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat       using (ℕ)
open import Data.Nat.Base  using (_≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Transitivity of ≤
≤-trans : ∀ {i j k : ℕ} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤n      _             = z≤n
≤-trans (s≤s p)  z≤n           = ()
≤-trans (s≤s p) (s≤s q)        = s≤s (≤-trans p q)

-- Left identity
≤-id-left : ∀ {m n} (p : m ≤ n) → ≤-trans z≤n p ≡ p
≤-id-left z≤n     = refl
≤-id-left (s≤s p) = cong s≤s (≤-id-left p)

-- Right identity (s≤s case is uninhabited)
≤-id-right : ∀ {m n} (p : m ≤ n) → ≤-trans p z≤n ≡ p
≤-id-right z≤n    = refl
≤-id-right (s≤s p) = ()

-- Category record
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

-- CutCat: free thin category on ℕ
CutCat : Category lzero lzero
Category.Obj CutCat      = ℕ
Category.Hom CutCat      = λ m n → m ≤ n
Category.id  CutCat      = λ m → z≤n
Category._∘_ CutCat      = λ f g → ≤-trans g f
Category.id-left  CutCat = λ f → ≤-id-right f
Category.id-right CutCat = λ f → ≤-id-left f
Category.assoc    CutCat = λ h g f → refl
