module Induct where

open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality

{- The downward closure of a set. -}
data downset : (ℕ → Set) → ℕ → Set where
  downset-lit : {φ : ℕ → Set} → {x : ℕ} → φ x → downset φ x
  downset-pred : {φ : ℕ → Set} → {x : ℕ} → downset φ (suc x) → downset φ x

{- Example 1: The downset of a downset is itself. Simple induction. -}
downset-downset : ∀ {φ} → ∀ {x} → downset (downset φ) x → downset φ x
downset-downset (downset-lit p) = p
downset-downset (downset-pred p) = downset-pred (downset-downset p)

{- Example 2: Downsets are downward closed. Needs lemmata. -}
lemma-larger : ∀ x y → x ≤ y → (suc x ≤ y) ⊎ (x ≡ y)
lemma-larger .0 zero z≤n = inj₂ refl
lemma-larger .0 (suc y) z≤n = inj₁ (s≤s z≤n)
lemma-larger (suc x) (suc y) (s≤s x-leq-y) with lemma-larger x y x-leq-y
lemma-larger (suc x) (suc y) (s≤s x-leq-y) | inj₁ sx-leq-y = inj₁ (s≤s sx-leq-y)
lemma-larger (suc x) (suc y) (s≤s x-leq-y) | inj₂ x-eq-y = inj₂ (cong suc x-eq-y)

downset-zero : ∀ {φ} → ∀ y → downset φ y → downset φ zero
downset-zero zero d-phi-y = d-phi-y
downset-zero (suc y) d-phi-y = downset-zero y (downset-pred d-phi-y)

downset-downward-closed : ∀ {φ} → ∀ x y → downset φ y → x ≤ y → downset φ x
downset-downward-closed zero y d-phi-y x-leq-y = downset-zero y d-phi-y
downset-downward-closed
  (suc x) (suc y) d-phi-y (s≤s x-leq-y) with lemma-larger x y x-leq-y
... | inj₁ sx-leq-y = downset-downward-closed (suc x) y (downset-pred d-phi-y) sx-leq-y
... | inj₂ refl = d-phi-y
