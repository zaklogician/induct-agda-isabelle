module Induct where

open import Data.Nat

{- The downward closure of a set. -}
data downset (φ : ℕ → Set) : ℕ → Set where
  downset-lit : {x : ℕ} → φ x → downset φ x
  downset-pred : {x : ℕ} → downset φ (suc x) → downset φ x

{- A very short proof by induction. -}
theorem : ∀ {φ} → ∀ {x} → downset (downset φ) x → downset φ x
theorem (downset-lit p) = p
theorem (downset-pred p) = downset-pred (theorem p)

{- The same proof in natural language. -}
theorem-full : ∀ φ → ∀ x → downset (downset φ) x → downset φ x
-- Take some predicate φ ⊂ ℕ and some x ∈ ℕ. Asssume that `downset (downset φ) x` holds.
-- We have to prove that `downset φ x` also holds. We proceed by structural induction
-- on `downset (downset φ) x`. There are two cases to consider.
--   Case downset-lit: in this case we immediately have `x ∈ downset φ x`, so we are done.
theorem-full φ x (downset-lit p) = qed where
  qed : downset φ x
  qed = p
--   Case downset-pred: in this case we have `downset (downset φ x) (suc x)`, and
theorem-full φ x (downset-pred p) = qed where
--   we can inductively assume `downset φ (suc x)`.
  inductive-hypothesis : downset φ (suc x)
  inductive-hypothesis = theorem-full φ (suc x) p 
--   We obtain `downset ϕ x` by invoking the downset-pred rule.
  qed : downset φ x
  qed = downset-pred inductive-hypothesis
