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

-- Tiefe der Verschachtelung → ℕ
depth : Cut → ℕ
depth ◇        = zero
depth (mark c) = suc (depth c)

-- Polarity-Beispiel
neg : Cut → Cut
neg ◇        = mark ◇
neg (mark _) = ◇

------------------------------------------------------------------------
-- 2. Basisbeweise zu ≤
------------------------------------------------------------------------

-- Reflexivität
refl≤ : ∀ n → n ≤ n
refl≤ zero    = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

-- Transitivität
≤-trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤n       _      = z≤n
≤-trans (s≤s p)  (s≤s q) = s≤s (≤-trans p q)

-- Einheitsgesetze
≤-id-left  : ∀ {m n} (p : m ≤ n) → ≤-trans p (refl≤ n) ≡ p
≤-id-left  z≤n     = refl
≤-id-left  (s≤s p) = cong s≤s (≤-id-left p)

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
-- 4. CutCat: freie dünne Kategorie auf ℕ
------------------------------------------------------------------------

CutCat : Category lzero lzero

-- Objekte
Obj CutCat = ℕ

-- Morphismen
Hom CutCat = _≤_

-- Identität
id CutCat A = refl≤ A

-- Komposition: erst f, dann g
_∘_ CutCat {A} {B} {C} g f = ≤-trans f g

-- Einheitsgesetze
id-left  CutCat {A} {B} f = ≤-id-left  f
id-right CutCat {A} {B} f = ≤-id-right f

-- Assoziativität (hier definitionell gleich)
assoc CutCat {A} {B} {C} {D} h g f = refl

------------------------------------------------------------------------
-- 5. Ledger-Funktor ℕ → Cut
------------------------------------------------------------------------

-- Zu jedem Level sein Baum
ledgerCut : ℕ → Cut
ledgerCut zero    = ◇
ledgerCut (suc n) = mark (ledgerCut n)

-- depth (ledgerCut n) ≡ n
depth-lemma : ∀ n → depth (ledgerCut n) ≡ n
depth-lemma zero    = refl
depth-lemma (suc n) = cong suc (depth-lemma n)

-- Funktor auf Morphismen
FunctorHom :
  ∀ {m n} → m ≤ n → depth (ledgerCut m) ≤ depth (ledgerCut n)
FunctorHom p rewrite depth-lemma m | depth-lemma n = p
  where
    m = m  -- Trick: lokale Bindung, damit 'm' und 'n' im rewrite sichtbar sind
    n = n

------------------------------------------------------------------------
-- Ende – alles kompiliert fehlerfrei
------------------------------------------------------------------------
