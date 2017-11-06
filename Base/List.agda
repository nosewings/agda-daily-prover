{-# OPTIONS --without-K --rewriting #-}

module Base.List where

open import Base
open import Base.Natural

infixr 5 _∷_ _++_

data List {ℓ} (A : Type ℓ) : Type ℓ where
  []  : List A
  _∷_ : A → List A → List A

foldr : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B → B) → B → List A → B
foldr _∙_ e []       = e
foldr _∙_ e (a ∷ as) = a ∙ foldr _∙_ e as

map : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → List A
xs ++ ys = foldr _∷_ ys xs
--[]       ++ ys = ys
--(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {ℓ} {A : Type ℓ} → List (List A) → List A
concat = foldr _++_ []
--concat []         = []
--concat (xs ∷ xss) = xs ++ concat xss

filter : ∀ {ℓ} {A : Type ℓ} → (A → 𝟚) → List A → List A
filter f = map (λ x → if f x then x ∷ [] else []) ⨾ concat
