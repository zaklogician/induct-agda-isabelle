module Induct where

open import Data.Nat

{- The downward closure of a set. -}
data downset : (ℕ → Set) → ℕ → Set where
  downset-lit : {φ : ℕ → Set} → {x : ℕ} → φ x → downset φ x
  downset-pred : {φ : ℕ → Set} → {x : ℕ} → downset φ (suc x) → downset φ x

{- A very short proof by induction. -}
theorem : ∀ {φ} → ∀ {x} → downset (downset φ) x → downset φ x
theorem (downset-lit p) = p
theorem (downset-pred p) = downset-pred (theorem p)
