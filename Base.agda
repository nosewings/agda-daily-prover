{-# OPTIONS --without-K --rewriting #-}

module Base where

infixr 9 _∘_
infixl 9 _⨾_
infixl 1 _⟨_⟩_
infixl 1 _on_
infixl 0 _&_
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

_&_ : ∀ {ℓ₁ ℓ₂}
        {A : Type ℓ₁}
        {B : A → Type ℓ₂}
      → (a : A)
      → Π A B
      → B a
x & f = f x

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
        {A : Type ℓ₁}
        {B : A → Type ℓ₂}
        {C : (a : A) → B a → Type ℓ₃}
      → ({a : A} → Π (B a) (C a))
      → (f : Π A B)
      → ((a : A) → C a (f a))
g ∘ f = λ a → g (f a)

_⨾_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
        {A : Type ℓ₁}
        {B : A → Type ℓ₂}
        {C : (a : A) → B a → Type ℓ₃}
        (f : Π A B)
      → ({a : A} → Π (B a) (C a))
      → ((a : A) → C a (f a))
f ⨾ g = λ a → g (f a)

flip : ∀ {ℓ₁ ℓ₂ ℓ₃}
         {A : Type ℓ₁} {B : Type ℓ₂} {C : A → B → Type ℓ₃}
       → (∀ a b → C a b)
       → (∀ b a → C a b)
flip f = λ b a → f a b

_⟨_⟩_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
          {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
        → A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

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
         → Π (Σ A B) τ
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
         → Π (A × B) τ
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
         → Π (A ⊎ B) τ
⊎-elim τ l r (i₁ a) = l a
⊎-elim τ l r (i₂ b) = r b

⊎-rec : ∀ {ℓ₁ ℓ₂ ℓ₃}
          {A : Type ℓ₁} {B : Type ℓ₂}
          {τ : Type ℓ₃}
        → (A → τ)
        → (B → τ)
        → (A ⊎ B → τ)
⊎-rec = ⊎-elim _

data Tri {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃) : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  tri₁ : A → Tri A B C
  tri₂ : B → Tri A B C
  tri₃ : C → Tri A B C

Tri-elim : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
             {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
             (τ : Tri A B C → Type ℓ₄)
           → ((a : A) → τ (tri₁ a))
           → ((b : B) → τ (tri₂ b))
           → ((c : C) → τ (tri₃ c))
           → Π (Tri A B C) τ
Tri-elim τ t₁ t₂ t₃ (tri₁ a) = t₁ a
Tri-elim τ t₁ t₂ t₃ (tri₂ b) = t₂ b
Tri-elim τ t₁ t₂ t₃ (tri₃ c) = t₃ c

Tri-rec : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
            {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
            {τ : Type ℓ₄}
          → (A → τ)
          → (B → τ)
          → (C → τ)
          → (Tri A B C → τ)
Tri-rec = Tri-elim _

data 𝟘 : Type₀ where

𝟘-elim : ∀ {ℓ} (τ : 𝟘 → Type ℓ) → Π 𝟘 τ
𝟘-elim X ()

𝟘-rec : ∀ {ℓ} {τ : Type ℓ} → 𝟘 → τ
𝟘-rec = 𝟘-elim _

¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = A → 𝟘

_↯_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → A → ¬ A → {B : Type ℓ₂} → B
x ↯ f = 𝟘-rec (f x)

contrapositive : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → (¬ B → ¬ A)
contrapositive f = λ ¬b → λ a → ¬b (f a)

open import Agda.Builtin.Unit
  public
  renaming ( ⊤  to 𝟙
           ; tt to 0₁
           )

𝟙-elim :
  ∀ {ℓ}
    (τ : 𝟙 → Type ℓ)
  → τ 0₁
  → ((x : 𝟙) → τ x)
𝟙-elim τ z _ = z

𝟙-rec :
  ∀ {ℓ}
    {τ : Type ℓ}
  → τ
  → (𝟙 → τ)
𝟙-rec = 𝟙-elim _

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
  → Π 𝟚 τ
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

data 𝟛 : Type₀ where
  0₃ 1₃ 2₃ : 𝟛

𝟛-elim :
  ∀ {ℓ}
    (τ : 𝟛 → Type ℓ)
  → τ 0₃
  → τ 1₃
  → τ 2₃
  → Π 𝟛 τ
𝟛-elim τ z o t 0₃ = z
𝟛-elim τ z o t 1₃ = o
𝟛-elim τ z o t 2₃ = t

𝟛-rec :
  ∀ {ℓ}
    {τ : Type ℓ}
  → τ
  → τ
  → τ
  → (𝟛 → τ)
𝟛-rec = 𝟛-elim _

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

record Reveal_·_is_ {ℓ₁ ℓ₂}
                    {A : Type ℓ₁} {B : A → Type ℓ₂}
                    (f : Π A B) (x : A) (y : B x) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {ℓ₁ ℓ₂}
            {A : Type ℓ₁} {B : A → Type ℓ₂}
            (f : Π A B) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = ¬ (x ≡ y)

record DecEq {ℓ} (A : Type ℓ) : Type ℓ where
  field
    _≟_ : (x y : A) → x ≡ y ⊎ x ≢ y
open DecEq ⦃...⦄ public
