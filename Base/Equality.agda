{-# OPTIONS --without-K --rewriting #-}

module Base.Equality where

open import Base

module _ {ℓ} {A : Type ℓ} where

  infix  3 _⁻¹
  infixr 2 _∙_

  _∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  refl ∙ refl = refl

  _⁻¹ : {x y : A} → x ≡ y → y ≡ x
  refl ⁻¹ = refl

module _ {ℓ} {A : Type ℓ} where

  infix  1 begin_
  infixr 2 step-≡ step-≡⁻¹ _≡⟨⟩_
  infix  3 _∎

  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin_ p = p

  step-≡ : ∀ x {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ refl refl = refl
  syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

  step-≡⁻¹ : ∀ x {y z : A} → y ≡ z → y ≡ x → x ≡ z
  step-≡⁻¹ _ refl refl = refl
  syntax step-≡⁻¹ x y≡z y≡x = x ≡⟨ y≡x ⟩⁻¹ y≡z

  _≡⟨⟩_ : ∀ x {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ p = p

  _∎ : (x : A) → x ≡ x
  _ ∎ = refl

ap : ∀ {ℓ₁ ℓ₂}
       {A : Type ℓ₁} {B : Type ℓ₂}
       (f : A → B)
     → {x y : A} → x ≡ y
     → f x ≡ f y
ap f refl = refl
syntax ap f p = p |in-ctx f
