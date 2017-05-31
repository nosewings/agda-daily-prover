module Decreasing where

open import Base
open import Base.Equality
open import Base.Natural

Decreasing : (ℕ → ℕ) → Type₀
Decreasing f = ∀ n → f (succ n) ≤ f n

Decreasing-≤ : {f : ℕ → ℕ} → Decreasing f → {m n : ℕ} → m ≤ n → f n ≤ f m
Decreasing-≤ dec refl = refl
Decreasing-≤ dec {m = m} {n = succ n} (succ m≤n) =
  ≤-trans (dec n) (Decreasing-≤ dec m≤n)

Decreasing-+ : {f : ℕ → ℕ} → Decreasing f → (m n : ℕ) → f (m + n) ≤ f n
Decreasing-+ dec zero     n = refl
Decreasing-+ dec (succ m) n = ≤-trans (dec (m + n)) (Decreasing-+ dec m n)
