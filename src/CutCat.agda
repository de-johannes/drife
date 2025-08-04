module CutCat where

open import Agda.Primitive                    using (Level; lzero; lsuc; _⊔_)
open import Data.Nat                          using (ℕ; zero; suc)
open import Data.Nat.Base                     using (_≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality
                                               using (_≡_; refl; cong)

------------------------------------------------------------------------
-- 1. Primal Distinction (Cut-Baum) — Emergenz von ℕ & Bool
------------------------------------------------------------------------

data Cut : Set where
  ◇    : Cut
  mark : Cut → Cut

depth : Cut → ℕ
depth ◇        = zero
depth (mark c) = suc (depth c)

neg : Cut → Cut
neg ◇        = mark ◇
neg (mark _) = ◇

------------------------------------------------------------------------
-- 2. Ordnung auf ℕ: ≤ plus Lemmata
------------------------------------------------------------------------

refl≤ : ∀ n → n ≤ n
refl≤ zero    = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

≤-trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤n       _      = z≤n
≤-trans (s≤s p)  (s≤s q) = s≤s (≤-trans p q)

≤-id-left  : ∀ {m n} (p : m ≤ n) → ≤-trans p (refl≤ n) ≡ p
≤-id-left  z≤n     = refl
≤-id-left  (s≤s p) = cong s≤s (≤-id-left p)

≤-id-right : ∀ {m n} (p : m ≤ n) → ≤-trans (refl≤ m) p ≡ p
≤-id-right z≤n     = refl
≤-id-right (s≤s p) = cong s≤s (≤-id-right p)

trans-assoc
  : ∀ {A B C D} (f : A ≤ B) (g : B ≤ C) (h : C ≤ D)
    → ≤-trans (≤-trans f g) h ≡ ≤-trans f (≤-trans g h)
trans-assoc z≤n      _         _         = refl
trans-assoc (s≤s p) (s≤s q) (s≤s r) = cong s≤s (trans-assoc p q r)

------------------------------------------------------------------------
-- 3. Kategorien‐Record
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

-- 4.1 Objekte
CutCat .Obj = ℕ

-- 4.2 Morphismen
CutCat .Hom = λ m n → m ≤ n

-- 4.3 Identität
CutCat .id A = refl≤ A

-- 4.4 Komposition: erst f, dann g
CutCat ._∘_ {A} {B} {C} (g : B ≤ C) (f : A ≤ B) = ≤-trans f g

-- 4.5 Einheitsgesetze
CutCat .id-left  {A} {B} f = ≤-id-left f
CutCat .id-right {A} {B} f = ≤-id-right f

-- 4.6 Assoziativität
CutCat .assoc {A} {B} {C} {D} h g f = trans-assoc f g h

------------------------------------------------------------------------
-- 5. LedgerCut-Funktor ℕ → Cut
------------------------------------------------------------------------

ledgerCut : ℕ → Cut
ledgerCut zero    = ◇
ledgerCut (suc n) = mark (ledgerCut n)

depth-lemma : ∀ n → depth (ledgerCut n) ≡ n
depth-lemma zero    = refl
depth-lemma (suc n) = cong suc (depth-lemma n)

FunctorHom
  : ∀ {m n} → m ≤ n → depth (ledgerCut m) ≤ depth (ledgerCut n)
FunctorHom p with depth-lemma m | depth-lemma n
... | refl | refl = p
  where
    -- die mit `{m}` und `{n}` impliziten sind jetzt im Scope!
    m = m
    n = n

------------------------------------------------------------------------
-- Kompilations-Test:
--   agda CutCat.agda  → Exit-Code 0
------------------------------------------------------------------------
