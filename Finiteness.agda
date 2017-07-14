{-# OPTIONS --without-K --rewriting #-}

module Finiteness where

open import Base
open import Base.Equality
open import Base.Natural

-- Pointwise equality of functions.

infix 4 _≈_
_≈_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} → Π A B → Π A B → Type (ℓ₁ ⊔ ℓ₂)
f ≈ g = ∀ x → f x ≡ g x

-- Injectivity.

Injective : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)
Injective f = ∀ {a₁ a₂} → f a₁ ≡ f a₂ → a₁ ≡ a₂

-- If f and g are pointwise equal and f is injective, then g is also injective.

≈-Injective : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} → f ≈ g → Injective f → Injective g
≈-Injective p q {x} {y} r = q (p x ∙ r ∙ p y ⁻¹)

-- Surjectivity.

Surjective : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)
Surjective f = Π[ b ∶ _ ] Σ[ a ∶ _ ] f a ≡ b

-- Any surjection f has a right inverse defined by f(x) ↦ x, with the particular
-- x given by the surjectivity proof.

rinv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} → Surjective f → (B → A)
rinv {f = f} surj = π₁ ∘ surj

-- This right inverse is injective.

rinv-inj : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} (srj : Surjective f) → Injective (rinv srj)
rinv-inj {f = f} srj {x} {y} p = π₂ (srj x) ⁻¹ ∙ ap f p ∙ π₂ (srj y)

-- This is structurally identical to the usual formulation with zero and succ.

data Fin : ℕ → Type₀ where
  top : ∀ {n} → Fin (succ n)
  pred : ∀ {n} → Fin n → Fin (succ n)

-- `pred` is injective.

pred-inj : ∀ {n} → Injective (pred {n})
pred-inj refl = refl

-- Given an injective function f : [n+1] → [n+1], define lowerᶠ : [n] → [n] in
-- the following manner:
--
-- Take i ∈ [n]. If f(i) ≠ n+1, then return f(i). If f(i) = n+1, then the
-- injectivity of f means that f(n+1) ≠ n+1, so we can return f(n+1).
--
-- NB. The use of `inspect` here is somewhat unfortunate: since the function's
-- computational behavior depends on the result of `inspect`, applications of
-- this function will not reduce unless the appropriate `inspect` call is
-- invoked. This means that proofs about this function will usually need to call
-- `inspect`, even if they do not actually use the result.

lower : ∀ {n} {f : Fin (succ n) → Fin (succ n)} → Injective f → (Fin n → Fin n)
lower {f = f} inj i with f (pred i) | inspect f (pred i)
... | pred j | _ = j
... | top  | [ f[pi]≡top ] with f top | inspect f top
... | pred j | _ = j
... | top  | [ f[top]≡top ] = case inj (f[pi]≡top ∙ f[top]≡top ⁻¹) of λ ()

-- For any injective f : [n+1] → [n+1], lowerᶠ is also injective.

inj-lower : ∀ {n} {f : Fin (succ n) → Fin (succ n)} (inj : Injective f) → Injective (lower inj)
inj-lower {f = f} inj {i} {j} f[i]≡f[j] with f (pred i) | inspect f (pred i) | f (pred j) | inspect f (pred j)
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | pred k        | [ f[pi]≡pk  ]      | pred l     | [ f[pj]≡pl  ] = pred-inj (inj (f[pi]≡pk ∙ ap pred f[i]≡f[j] ∙ f[pj]≡pl ⁻¹))
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | top           | [ f[pi]≡top ]      | top        | [ f[pj]≡top ] with f top  | inspect f top
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | top           | [ f[pi]≡top ]      | top        | [ f[pj]≡top ]    | pred m | [ f[top]≡pm  ] = pred-inj (inj (f[pi]≡top ∙ f[pj]≡top ⁻¹))
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | top           | [ f[pi]≡top ]      | top        | [ f[pj]≡top ]    | top    | [ f[top]≡top ] = case inj (f[top]≡top ∙ f[pi]≡top ⁻¹) of λ ()
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | top           | [ f[pi]≡top ]      | pred l     | [ f[pj]≡pl  ] with f top  | inspect f top
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | top           | [ f[pi]≡top ]      | pred l     | [ f[pj]≡pl  ]    | pred m | [ f[top]≡pm  ] = case inj (f[top]≡pm ∙ ap pred f[i]≡f[j] ∙ f[pj]≡pl ⁻¹) of λ ()
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | top           | [ f[pi]≡top ]      | pred l     | [ f[pj]≡pl  ]    | top    | [ f[top]≡top ] = case inj (f[top]≡top ∙ f[pi]≡top ⁻¹) of λ ()
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | pred k        | [ f[pi]≡pk  ]      | top        | [ f[pj]≡top ] with f top  | inspect f top
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | pred k        | [ f[pi]≡pk  ]      | top        | [ f[pj]≡top ]    | pred m | [ f[top]≡pm  ] = case inj (f[pi]≡pk ∙ ap pred f[i]≡f[j] ∙ f[top]≡pm ⁻¹) of λ ()
inj-lower {f = f} inj {i} {j} f[i]≡f[j] | pred k        | [ f[pi]≡pk  ]      | top        | [ f[pj]≡top ]    | top    | [ f[top]≡top ] = case inj (f[top]≡top ∙ f[pj]≡top ⁻¹) of λ ()

-- Use induction. The inductive hypothesis is that all injections [n] → [n] are
-- surjective. From this, we derive that for any injective f : [n+1] → [n+1],
-- lowerᶠ is surjective. We then use this to show that f is surjective.

Injective⇒Surjective : ∀ {n} {f : Fin n → Fin n} → Injective f → Surjective f
Injective⇒Surjective {zero}   {f} inj ()
Injective⇒Surjective {succ n} {f} inj top
 with f top  | inspect f top
... | top    | [ f[top]≡top ] = top , f[top]≡top
... | pred i | [ f[top]≡pi  ]
 with Injective⇒Surjective (inj-lower inj) i
... | j , lowerᶠ[j]≡i -- lowerᶠ[j]≡i : (lower inj j | f (pred j) | [ refl ]) ≡ i
 with f (pred j)  | inspect f (pred j)
... | top         | [ f[pj]≡top ] = pred j , f[pj]≡top
... | pred k      | [ f[pj]≡pk  ] = case inj (f[pj]≡pk ∙ ap pred lowerᶠ[j]≡i ∙ f[top]≡pi ⁻¹) of λ () -- lowerᶠ[j]≡i : k ≡ i
Injective⇒Surjective {succ n} {f} inj (pred i)
 with Injective⇒Surjective (inj-lower inj) i
... | j , lowerᶠ[j]≡i -- lowerᶠ[j]≡i : (lower inj j | f (pred j) | [ refl ]) ≡ i
 with f (pred j) | inspect f (pred j)
... | pred k     | [ f[pj]≡pk  ] = pred j , (f[pj]≡pk ∙ ap pred lowerᶠ[j]≡i)
... | top        | [ f[pj]≡top ]
 with f top  | inspect f top
... | pred k | [ f[top]≡pk  ] = top , (f[top]≡pk ∙ ap pred lowerᶠ[j]≡i) -- lowerᶠ[j]≡i : k ≡ i
... | top    | [ f[top]≡top ] = case inj (f[top]≡top ∙ f[pj]≡top ⁻¹) of λ ()

-- The right inverse of any surjective automorphism on a finite set is itself
-- surjective.
 
rinv-srj : ∀ {n} {f : Fin n → Fin n} (srj : Surjective f) → Surjective (rinv srj)
rinv-srj srj = Injective⇒Surjective (rinv-inj srj)

-- For any surjective f : Fin n → Fin n, the right inverse of the right inverse
-- of f is pointwise equal to f.
--
-- NB. This is an extraordinarily ugly proof.

rinv-rinv : ∀ {n} {f : Fin n → Fin n} (srj : Surjective f) → rinv (rinv-srj srj) ≈ f
rinv-rinv {zero}   srj ()
rinv-rinv {succ n} {f} srj top
 with srj top             | inspect (rinv srj) top
... | top    , f[top]≡top | _ = f[top]≡top ⁻¹
... | pred i , f[pi]≡top  | _
 with Injective⇒Surjective (inj-lower (rinv-inj srj)) i
... | j , lower-rinv-f[j]≡i -- lower-rinv-f[j]≡i : (lower (rinv-inj srj) i | rinv srj (pred j) | [ refl ]) ≡ i
 with srj (pred j)       | inspect (rinv srj) (pred j)
... | top    , f[top]≡pj | _ = f[top]≡pj ⁻¹
... | pred k , f[pk]≡pj  | _ = case f[pk]≡pj ⁻¹ ∙ ap (f ∘ pred) lower-rinv-f[j]≡i ∙ f[pi]≡top of λ () -- lower-rinv-f[j]≡i : k ≡ i
rinv-rinv {succ n} {f} srj (pred i)
 with Injective⇒Surjective (inj-lower (rinv-inj srj)) i
... | j , lower-rinv-f[j]≡i -- lower-rinv-f[j]≡i : (lower (rinv-inj srj) i | rinv srj (pred j) | [ refl ]) ≡ i
 with srj (pred j)       | inspect (rinv srj) (pred j)
... | pred k , f[pk]≡pj  | _ = f[pk]≡pj ⁻¹ ∙ ap (f ∘ pred) lower-rinv-f[j]≡i -- lower-rinv-f[j]≡i : k ≡ i
... | top    , f[top]≡pj | [ rinv-srj[pj]≡top ]
 with srj top | inspect (rinv srj) top
... | pred l , f[pl]≡top  | _                     = f[pl]≡top ⁻¹ ∙ ap (f ∘ pred) lower-rinv-f[j]≡i
... | top    , _          | [ rinv-srj[top]≡top ] = case rinv-inj srj (rinv-srj[top]≡top ∙ rinv-srj[pj]≡top ⁻¹) of λ ()

-- For any surjective f : Fin n → Fin n, the right inverse of the right inverse
-- of f is injective (since all right inverses are injective). Furthermore, as
-- shown above, it is pointwise equal to f. Since pointwise equal functions
-- share injectivity, this means that f is injective.

Surjective⇒Injective : ∀ {n} {f : Fin n → Fin n} → Surjective f → Injective f
Surjective⇒Injective {f = f} srj = ≈-Injective (rinv-rinv srj) (rinv-inj (rinv-srj srj))
