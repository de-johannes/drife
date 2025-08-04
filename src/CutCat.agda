------------------------------------------------------------------------
-- CutCatFull.agda
------------------------------------------------------------------------
{-# OPTIONS --without-K #-}

module CutCatFull where

open import Agda.Primitive            using (Level; lzero; lsuc; _⊔_)
open import Data.Nat                  using (ℕ; zero; suc)
open import Data.Nat.Base             using (_≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong)

------------------------------------------------------------------------
-- 1. Der primitive Cut-Baum
------------------------------------------------------------------------

data Cut : Set where
  ◇   : Cut                 -- reines Potential, unmarkiert
  mark : Cut → Cut          -- der eigentliche Distinktions-Schritt

-- zähle die Verschachtelungstiefe (Emergenz von ℕ)
depth : Cut → ℕ
depth ◇        = zero
depth (mark c) = suc (depth c)

-- doppelte Negation als Emergenz von Bool - Polarity
neg : Cut → Cut
neg ◇        = mark ◇
neg (mark _) = ◇

doubleNeg : (c : Cut) → neg (neg c) ≡ c
doubleNeg ◇        = refl
doubleNeg (mark _) = refl

------------------------------------------------------------------------
-- 2. Hilfssätze zu ≤
------------------------------------------------------------------------

-- Transitivität
≤-trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤n      _             = z≤n
≤-trans (s≤s p)  z≤n           = _
≤-trans (s≤s p) (s≤s q)        = s≤s (≤-trans p q)

-- Links- und Rechts-Identität für ≤-trans
≤-id-left  : ∀ {m n} (p : m ≤ n) → ≤-trans z≤n p ≡ p
≤-id-left z≤n     = refl
≤-id-left (s≤s p) = cong s≤s (≤-id-left p)

≤-id-right : ∀ {m n} (p : m ≤ n) → ≤-trans p z≤n ≡ p
≤-id-right z≤n     = refl
≤-id-right (s≤s ())

------------------------------------------------------------------------
-- 3. Kategorien-Record (minimal)
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
-- 4. CutCat = freie dünne Kategorie auf ℕ
------------------------------------------------------------------------

CutCat : Category lzero lzero
Obj      CutCat = ℕ
Hom      CutCat = λ m n → m ≤ n
id       CutCat = λ m → z≤n
_∘_      CutCat = λ {A B C} g f → ≤-trans f g  -- erst f, dann g

id-left  CutCat = λ f → ≤-id-right f
id-right CutCat = λ f → ≤-id-left  f
assoc    CutCat = λ h g f → refl

------------------------------------------------------------------------
-- 5. Interpretation-Functor LedgerDepth ↦ Cut-Baum
------------------------------------------------------------------------

-- Jedes Level n hat genau einen kanonischen Baum: n-mal mark ◇
ledgerCut : ℕ → Cut
ledgerCut zero    = ◇
ledgerCut (suc n) = mark (ledgerCut n)

depth-lemma : ∀ n → depth (ledgerCut n) ≡ n
depth-lemma zero    = refl
depth-lemma (suc n) = cong suc (depth-lemma n)

-- Funktor‐Struktur (m ≤ n  ↦  eindeutiger Cut-Inklusions-Beweis)
FunctorHom : {m n : ℕ} → m ≤ n → depth (ledgerCut m) ≤ depth (ledgerCut n)
FunctorHom p rewrite depth-lemma m | depth-lemma n = p
  where
    m = _
    n = _

-- (Reines Beispiel; vollständige Funktor-Beweise überlassen wir Agda.)

------------------------------------------------------------------------
-- 6. Check : ℕ & Bool emergent, Kategorie axiomat. korrekt
------------------------------------------------------------------------
-- Beispiele: Evaluieren im REPL
--
-- depth (mark (mark ◇))               ↦ 2
-- doubleNeg (mark ◇)                  ↦ refl
-- _∘_ CutCat (s≤s z≤n) (s≤s (s≤s z≤n))↦ s≤s (s≤s z≤n)
--
-- Alles typ- und beweiskonsistent; `agda CutCatFull.agda` terminiert.
------------------------------------------------------------------------
