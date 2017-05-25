{-# OPTIONS --without-K --rewriting #-}

module Base where

infixr 9 _∘_
infixl 1 _on_
infix  0 case_return_of_ case_of_

infix  4 _≢_
infix  3  ¬_
infix  2  Π Σ
infixr 1 _⊎_

infixr 4 _,_
infix  3 _↯_

open import Agda.Primitive
  public
  using ( Level
        )
module Level where
  open import Agda.Primitive
    public
    using (
          )
    renaming ( lzero to zero
             ; lsuc  to succ
             ; _⊔_   to max
             )

Type : (ℓ : Level) → Set (Level.succ ℓ)
Type ℓ = Set ℓ

Type₀ : Type (Level.succ Level.zero)
Type₀ = Type Level.zero

record Max {ℓ} (A : Type ℓ) : Type ℓ where
  infixl 6 _⊔_
  field
    _⊔_ : A → A → A
open Max ⦃...⦄ public

instance
  Max-Level#instance : Max Level
  Max-Level#instance = record { _⊔_ = Level.max }

Π : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
Π A B = (a : A) → B a
syntax Π A (λ x → B) = Π[ x ∶ A ] B

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
        {A : Type ℓ₁}
        {B : A → Type ℓ₂}
        {C : (a : A) → B a → Type ℓ₃}
      → ({a : A} → Π (B a) (C a))
      → (f : Π A B)
      → ((a : A) → C a (f a))
g ∘ f = λ a → g (f a)

_on_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
         {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → (B → B → C)
       → (A → B)
       → (A → A → C)
_∙_ on f = λ x y → f x ∙ f y

case_return_of_ :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} (x : A)
    (B : A → Type ℓ₂)
  → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A → (A → B) → B
case x of f = case x return _ of f

record Σ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open Σ public
syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

Σ-elim : ∀ {ℓ₁ ℓ₂ ℓ₃}
           {A : Type ℓ₁} {B : A → Type ℓ₂}
           (τ : Σ A B → Type ℓ₃)
         → ((a : A) (b : B a) → τ (a , b))
         → ((x : Σ A B) → τ x)
Σ-elim τ p (a , b) = p a b

Σ-rec : ∀ {ℓ₁ ℓ₂ ℓ₃}
          {A : Type ℓ₁} {B : A → Type ℓ₂}
          {τ : Type ℓ₃}
        → ((a : A) → B a → τ)
        → (Σ A B → τ)
Σ-rec = Σ-elim _

_×_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (λ _ → B)

×-elim : ∀ {ℓ₁ ℓ₂ ℓ₃}
           {A : Type ℓ₁} {B : Type ℓ₂}
           (τ : A × B → Type ℓ₃)
         → ((a : A) (b : B) → τ (a , b))
         → ((x : A × B) → τ x)
×-elim = Σ-elim

×-rec : ∀ {ℓ₁ ℓ₂ ℓ₃}
          {A : Type ℓ₁} {B : Type ℓ₂}
          {τ : Type ℓ₃}
        → (A → B → τ)
        → (A × B → τ)
×-rec = Σ-rec

data _⊎_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  i₁ : A → A ⊎ B
  i₂ : B → A ⊎ B

⊎-elim : ∀ {ℓ₁ ℓ₂ ℓ₃}
           {A : Type ℓ₁} {B : Type ℓ₂}
           (τ : A ⊎ B → Type ℓ₃)
         → ((a : A) → τ (i₁ a))
         → ((b : B) → τ (i₂ b))
         → ((x : A ⊎ B) → τ x)
⊎-elim τ l r (i₁ a) = l a
⊎-elim τ l r (i₂ b) = r b

⊎-rec : ∀ {ℓ₁ ℓ₂ ℓ₃}
          {A : Type ℓ₁} {B : Type ℓ₂}
          {τ : Type ℓ₃}
        → (A → τ)
        → (B → τ)
        → (A ⊎ B → τ)
⊎-rec = ⊎-elim _

data 𝟘 : Type₀ where

𝟘-elim : ∀ {ℓ} (τ : 𝟘 → Type ℓ) → (x : 𝟘) → τ x
𝟘-elim X ()

𝟘-rec : ∀ {ℓ} {τ : Type ℓ} → 𝟘 → τ
𝟘-rec = 𝟘-elim _

¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = A → 𝟘

_↯_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → A → ¬ A → {B : Type ℓ₂} → B
x ↯ f = 𝟘-rec (f x)

contrapositive : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → (¬ B → ¬ A)
contrapositive f = λ ¬b → λ a → ¬b (f a)

open import Agda.Builtin.Bool
  public
  renaming ( Bool  to 𝟚
           ; false to 0₂
           ; true  to 1₂
           )

𝟚-elim :
  ∀ {ℓ}
    (τ : 𝟚 → Type ℓ)
  → τ 0₂
  → τ 1₂
  → ((x : 𝟚) → τ x)
𝟚-elim τ f t 0₂ = f
𝟚-elim τ f t 1₂ = t

𝟚-rec :
  ∀ {ℓ}
    {τ : Type ℓ}
  → τ
  → τ
  → (𝟚 → τ)
𝟚-rec = 𝟚-elim _

not : 𝟚 → 𝟚
not 0₂ = 1₂
not 1₂ = 0₂

open import Agda.Builtin.Equality
  public
  using ( _≡_
        ; refl
        )

≡-elim :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {a : A}
    (τ : (x : A) → a ≡ x → Type ℓ₂)
  → τ a refl
  → ({x : A} (p : a ≡ x) → τ x p)
≡-elim τ r refl = r

≡-rec :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {a : A}
    (τ : A → Type ℓ₂)
  → τ a
  → ({x : A} → a ≡ x → τ x)
≡-rec τ r refl = r

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = ¬ (x ≡ y)

record DecEq {ℓ} (A : Type ℓ) : Type ℓ where
  field
    _≟_ : (x y : A) → x ≡ y ⊎ x ≢ y
open DecEq ⦃...⦄ public
