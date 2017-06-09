{-# OPTIONS --without-K --rewriting #-}

module FiniteCancellativeSemigroup where

open import Base
open import Base.Equality
  hiding ( _∙_
         ; _⁻¹
         )

Injective : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)
Injective f = ∀ {a₁ a₂} → f a₁ ≡ f a₂ → a₁ ≡ a₂

Surjective : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)
Surjective f = Π[ b ∶ _ ] Σ[ a ∶ _ ] f a ≡ b

-- A type A is Dedekind-finite if every injective automorphism on A is a
-- surjection.

DedekindFinite : ∀ {ℓ} → Type ℓ → Type ℓ
DedekindFinite A = {f : A → A} → Injective f → Surjective f

module _ {ℓ}
         (A : Type ℓ)
         (a : A)
         (_∙_ : A → A → A) (let infixr 5 _∙_ ; _∙_ = _∙_)
         (inj⇒surj : DedekindFinite A)
         (assoc : ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)
         (cancel-l : ∀ {x y z} → x ∙ y ≡ x ∙ z → y ≡ z)
         (cancel-r : ∀ {x y z} → y ∙ x ≡ z ∙ x → y ≡ z)
         where

  -- The left and right cancellative properties tell us that the operations of
  -- right and left multiplication are injective. Sine A is Dedekind-finite,
  -- these operations are also surjective.

  ∙-r-surj : ∀ x → Surjective (_∙_ x)
  ∙-r-surj _ = inj⇒surj cancel-l

  ∙-l-surj : ∀ x → Surjective (flip _∙_ x)
  ∙-l-surj _ = inj⇒surj cancel-r

  -- This means that for any x : A and z : A, there exist yₗ : A and yᵣ : A
  -- such that yₗx = z and xyᵣ = z. This makes A a quasigroup, so we adopt
  -- quasigroup notation.

  _\\_ : A → A → A
  x \\ y = π₁ (∙-r-surj x y)

  _//_ : A → A → A
  x // y = π₁ (∙-l-surj y x)

  -- These operations function somewhat like division.

  \\-cancel : ∀ x y → x ∙ (x \\ y) ≡ y
  \\-cancel x y = π₂ (∙-r-surj x y)

  //-cancel : ∀ x y → (x // y) ∙ y ≡ x
  //-cancel x y = π₂ (∙-l-surj y x)

  -- If we set y = x, then we arrive at the important facts that
  -- x(x\x) = x and (x/x)x = x. This makes x\x and x/x what we might call a
  -- "local right identity" and "local left identity" respectively.

  module _ (x : A) where

    eᵣ : A
    eᵣ = x \\ x

    eᵣ-local-right-id : x ∙ eᵣ ≡ x
    eᵣ-local-right-id = \\-cancel x x

    eₗ : A
    eₗ = x // x

    eₗ-local-left-id : eₗ ∙ x ≡ x
    eₗ-local-left-id = //-cancel x x

    -- However, thanks to associativity, it turns out that these two objects are
    -- in fact identical.

    eₗ≡eᵣ : eₗ ≡ eᵣ
    eₗ≡eᵣ = cancel-l (cancel-r help) where
      help : (x ∙ eₗ) ∙ x ≡ (x ∙ eᵣ) ∙ x
      help = begin
        (x ∙ eₗ) ∙ x ≡⟨ assoc _ _ _ ⟩⁻¹
        x ∙ (eₗ ∙ x) ≡⟨ eₗ-local-left-id |in-ctx (_∙_ x) ⟩
        x ∙ x        ≡⟨ eᵣ-local-right-id |in-ctx (flip _∙_ x) ⟩⁻¹
        (x ∙ eᵣ) ∙ x ∎

    -- As expected, eᵣ is also a local left identity and eₗ is also a local
    -- right identity (and this can be proven even without substitution).

    eᵣ-local-left-id : eᵣ ∙ x ≡ x
    eᵣ-local-left-id = cancel-l help where
      help : x ∙ (eᵣ ∙ x) ≡ x ∙ x
      help = begin
        x ∙ (eᵣ ∙ x) ≡⟨ assoc _ _ _ ⟩
        (x ∙ eᵣ) ∙ x ≡⟨ eᵣ-local-right-id |in-ctx (flip _∙_ x) ⟩
        x ∙ x        ∎

    eₗ-local-right-id : x ∙ eₗ ≡ x
    eₗ-local-right-id = cancel-r help where
      help : (x ∙ eₗ) ∙ x ≡ x ∙ x
      help = begin
        (x ∙ eₗ) ∙ x ≡⟨ assoc _ _ _ ⟩⁻¹
        x ∙ (eₗ ∙ x) ≡⟨ eₗ-local-left-id |in-ctx (_∙_ x) ⟩
        x ∙ x        ∎

  -- In any case, since A is inhabited, we can obtain one of these local
  -- identities and show that it is in fact a global identity, using the same
  -- basic reasoning as above.

  e : A
  e = eᵣ a

  e-right-id : ∀ x → x ∙ e ≡ x
  e-right-id x = cancel-r help where
    help : (x ∙ e) ∙ a ≡ x ∙ a
    help = begin
      (x ∙ e) ∙ a    ≡⟨⟩
      (x ∙ eᵣ a) ∙ a ≡⟨ assoc _ _ _ ⟩⁻¹
      x ∙ (eᵣ a ∙ a) ≡⟨ eᵣ-local-left-id a |in-ctx (_∙_ x) ⟩
      x ∙ a          ∎

  e-left-id : ∀ x → e ∙ x ≡ x
  e-left-id x = cancel-l help where
    help : a ∙ (e ∙ x) ≡ a ∙ x
    help = begin
      a ∙ (e ∙ x)    ≡⟨⟩
      a ∙ (eᵣ a ∙ x) ≡⟨ assoc _ _ _ ⟩
      (a ∙ eᵣ a) ∙ x ≡⟨ eᵣ-local-right-id a |in-ctx (flip _∙_ x) ⟩
      a ∙ x          ∎

  -- x⁻¹ should satisfy the equations xx⁻¹ = e and x⁻¹x = e. It is easy to see
  -- that both x(x\e) = e and (e\x)x = e, and it is not hard to show that
  -- (x\e)x = e and x(e\x) = e.

  _⁻¹ : A → A
  x ⁻¹ = x \\ e

  ⁻¹-right-inv : ∀ x → x ∙ x ⁻¹ ≡ e
  ⁻¹-right-inv x = \\-cancel x e

  ⁻¹-left-inv : ∀ x → x ⁻¹ ∙ x ≡ e
  ⁻¹-left-inv x = cancel-r help where
    help : (x ⁻¹ ∙ x) ∙ x ⁻¹ ≡ e ∙ x ⁻¹
    help = begin
      (x ⁻¹ ∙ x) ∙ x ⁻¹ ≡⟨ assoc _ _ _ ⟩⁻¹
      x ⁻¹ ∙ (x ∙ x ⁻¹) ≡⟨ ⁻¹-right-inv x |in-ctx (_∙_ (x ⁻¹)) ⟩
      x ⁻¹ ∙ e          ≡⟨ e-right-id (x ⁻¹) ⟩
      x ⁻¹              ≡⟨ e-left-id (x ⁻¹) ⟩⁻¹
      e ∙ x ⁻¹          ∎
