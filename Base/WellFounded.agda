{-# OPTIONS --without-K --rewriting #-}

module Base.WellFounded where

open import Base

data Accessible {ℓ₁ ℓ₂} {A : Type ℓ₁} (_≺_ : A → A → Type ℓ₂) (x : A) : Type (ℓ₁ ⊔ ℓ₂) where
  accessible : ((y : A) → y ≺ x → Accessible _≺_ y) → Accessible _≺_ x

WellFounded : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
WellFounded _≺_ = ∀ x → Accessible _≺_ x

WellFounded-induction :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {_≺_ : A → A → Type ℓ₂}
  → WellFounded _≺_
  → (τ : A → Type ℓ₃)
  → ((x : A) → ((y : A) → y ≺ x → τ y) → τ x)
  → ((x : A) → τ x)
WellFounded-induction {_≺_ = _≺_} wf τ f x = rec x (wf x) where
  rec : ∀ x → Accessible _≺_ x → τ x
  rec x (accessible h) = f x (λ y y≺x → rec y (h y y≺x))

WellFounded-recursion :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {_≺_ : A → A → Type ℓ₂}
  → WellFounded _≺_
  → {τ : Type ℓ₃}
  → ((x : A) → ((y : A) → y ≺ x → τ) → τ)
  → ((x : A) → τ)
WellFounded-recursion wf = WellFounded-induction wf _

on-wf :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {_≺_ : B → B → Type ℓ₃}
  → WellFounded _≺_
  → (f : A → B)
  → WellFounded (_≺_ on f)
on-wf {_≺_ = _≺_} wf f = λ x → rec x (wf (f x)) where
  rec : ∀ x → Accessible _≺_ (f x) → Accessible (_≺_ on f) x
  rec x (accessible h) = accessible (λ y fy≺fx → rec y (h (f y) fy≺fx))
