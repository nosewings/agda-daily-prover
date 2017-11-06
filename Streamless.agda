{-# OPTIONS --without-K --rewriting #-}

module Streamless where

open import Base
open import Base.Equality
open import Base.Natural

Streamless : ∀ {ℓ} → Type ℓ → Type ℓ
Streamless A = (f : ℕ → A) → Σ[ i ∶ ℕ ] Σ[ j ∶ ℕ ] (i ≢ j) × (f i ≡ f j)

Funext : (ℓ₁ ℓ₂ : Level) → Type (Level.succ (ℓ₁ ⊔ ℓ₂))
Funext ℓ₁ ℓ₂ = ∀ {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : Π A B} → (∀ a → f a ≡ g a) → f ≡ g

module _ {ℓ} {A : Type ℓ} where

  d : A → ℕ → A → (ℕ → A)
  d a i x j with ⌊ j ≟ i ⌋
  ... | true  = x
  ... | false = a

  d-elsewhere : ∀ a x {i j} → j ≢ i → d a i x j ≡ a
  d-elsewhere a x {i} {j} j≢i with j ≟ i
  ... | yes j≡i = j≡i ↯ j≢i
  ... | no  _   = refl

module _ {ℓ} (funext : Funext Level.zero ℓ) where

  -- Let h be a proof that A is streamless. That is, h is a function which,
  -- given some f : ℕ → ℕ, returns i : ℕ and j : ℕ such that i ≠ j and
  -- f(i) = f(j).
  --
  -- Now take x : A and y : A. Define k : ℕ → A to be the constant function at
  -- x. Then, h(k) gives us m₁ : ℕ and n₁ : ℕ such that m₁ ≠ n₁ and
  -- k(m₁) = k(n₁). Now let d : ℕ → A be defined by d(m₁) = y and d(i) = x for
  -- all i ≠ m₁. Then, h(k) gives us m₂ : ℕ and n₂ : ℕ such that m₂ ≠ n₂ and
  -- d(m₂) = d(n₂).
  -- 
  -- Now it can be determined whether m₁ and m₂ are equal.
  --
  -- If m₂ = m₁, then d(m₂) = d(m₁) = y. Since n₂ ≠ m₂, d(n₂) = x, and since
  -- d(n₂) = d(m₂), we have x = d(m₂) = d(m₁) = y.
  --
  -- If m₂ ≠ m₁, assume that x = y. Then d(m₂) = x and d(i) = x for all i ≠ m₂,
  -- so d is pointwise equal to k. By function extensionality, this means that
  -- d = k. But then h(d) = h(k). In particular, m₂ = m₁, a contradiction. Thus,
  -- x ≠ y.
  Funext⇒Streamless⇒Dec-≡ : {A : Type ℓ} → Streamless A → (x y : A) → Dec (x ≡ y)
  Funext⇒Streamless⇒Dec-≡ h x y
   with h (const x)         | inspect (π₁ ∘ h) (const x)
  ... | m₁ , n₁ , m₁≢n₁ , _ | [ π₁[h[k]]≡m₁ ]
   with h (d x m₁ y)              | inspect (π₁ ∘ h) (d x m₁ y)
  ... | m₂ , n₂ , m₂≢n₂ , x≡d[n₂] | [ π₁[h[d]]≡m₂ ] with m₂ ≟ m₁
  ... | yes refl  = yes (d-elsewhere x y (≢-inv m₂≢n₂) ⁻¹ ∙ x≡d[n₂] ⁻¹)
  ... | no  m₂≢m₁ = no  (λ x≡y → (π₁[h[d]]≡m₂ ⁻¹ ∙ ap (π₁ ∘ h) (d-connect x≡y) ⁻¹ ∙ π₁[h[k]]≡m₁) ↯ m₂≢m₁) where
    d-connect-pointwise : x ≡ y → ∀ z → const x z ≡ d x m₁ y z
    d-connect-pointwise x≡y z with ⌊ z ≟ m₁ ⌋
    ... | true  = x≡y
    ... | false = refl

    d-connect : x ≡ y → const x ≡ d x m₁ y
    d-connect x≡y = funext (d-connect-pointwise x≡y)
