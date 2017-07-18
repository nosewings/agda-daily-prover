{-# OPTIONS --without-K --rewriting #-}

module Valley where

open import Base
open import Base.Equality
open import Base.WellFounded
open import Base.Natural

open import Decreasing

Valley : (ℕ → ℕ) → ℕ → ℕ → Type₀
Valley f n x = ∀ y → x ≤ y → y ≤ (n + x) → f y ≡ f x

module Valley where

  -- `null f x` is the zero-length valley at x. This valley always exists.

  null : (f : ℕ → ℕ) (x : ℕ) → Valley f zero x
  null f x = λ _ x≤y y≤x → ap f (≤-antisym y≤x x≤y)

  -- Cons-like operations on valleys on both the left and right.

  cons-right : {f : ℕ → ℕ} (n : ℕ) {x : ℕ}
             → Valley f n x
             → f (succ (n + x)) ≡ f x
             → Valley f (succ n) x
  cons-right {f} n {x} v f[sn+x]≡f[x] = λ
    { _  _   refl           → f[sn+x]≡f[x]
    ; y  x≤y (succ y≤[n+x]) → v y x≤y y≤[n+x]
    }

  cons-left : {f : ℕ → ℕ} (n : ℕ) {x : ℕ}
            → f x ≡ f (succ x)
            → Valley f n (succ x)
            → Valley f (succ n) x
  cons-left {f} n {x} f[x]≡f[sx] v = λ
    { _        refl       _       → refl
    ; (succ y) (succ x≤y) sy≤sn+x →
        let sx≤sy       = m≤n⇒sm≤sn x≤y
            sn+x≡n+sx   = sm+n≡m+sn n x
            sy≤n+sx     = ≡-rec (_≤_ (succ y)) sy≤sn+x sn+x≡n+sx
            f[sy]≡f[sx] = v (succ y) sx≤sy sy≤n+sx
        in f[sy]≡f[sx] ∙ f[x]≡f[sx] ⁻¹
    }

  -- A valley is maximal if it is the largest valley at its location.

  Maximal : {f : ℕ → ℕ} (n : ℕ) {x : ℕ} → Valley f n x → Type₀
  Maximal {f} n {x} v = f (succ (n + x)) ≢ f x

  -- Attempts to find a maximal valley for a given function and position.
  
  seek-maximal : (f : ℕ → ℕ) (n x : ℕ)
               → Σ[ m ∶ ℕ ] Σ[ v ∶ Valley f m x ] (Maximal m v ⊎ m ≡ n)
  seek-maximal f zero     x = zero , null f x , i₂ refl
  seek-maximal f (succ n) x with f (succ x) ≟ f x
  ... | i₂ f[sx]≢fx = zero , null f x , i₁ f[sx]≢fx
  ... | i₁ f[sx]≡fx with seek-maximal f n (succ x)
  ... | m , v , i₂ m≡n =
      succ m
    , cons-left m (f[sx]≡fx ⁻¹) v
    , i₂ (ap succ m≡n)
  ... | m , v , i₁ f[s[m+sx]]≢f[sx] =
      succ m
    , cons-left m (f[sx]≡fx ⁻¹) v
    , i₁ (λ f[ssm+x]≡f[x] → f[s[m+sx]]≡f[sx] f[ssm+x]≡f[x] ↯ f[s[m+sx]]≢f[sx])
    where
    f[s[m+sx]]≡f[sx] : f (succ (succ (m + x))) ≡ f x
                     → f (succ (m + succ x)) ≡ f (succ x)
    f[s[m+sx]]≡f[sx] f[ssm+x]≡f[x] = begin
      f (succ (m + succ x)) ≡⟨ sm+n≡m+sn m x |in-ctx (f ∘ succ) ⟩⁻¹
      f (succ (succ m + x)) ≡⟨ f[ssm+x]≡f[x] ⟩
      f x                   ≡⟨ f[sx]≡fx ⟩⁻¹
      f (succ x)            ∎

decreasing-has-n-valleys : ∀ n f → Decreasing f → Σ ℕ (Valley f n)
decreasing-has-n-valleys n f dec =
    WellFounded-recursion (on-wf wf-< f) go zero
  where
  go : (x : ℕ) → ((y : ℕ) → f y < f x → Σ ℕ (Valley f n)) → Σ ℕ (Valley f n)
  go x rec with Valley.seek-maximal f n x
  ... | _ , v , i₂ refl         = x , v
  ... | m , v , i₁ f[s[m+x]]̄≢fx =
    rec (succ (m + x)) (m≤n⇒m≢n⇒m<n (Decreasing-+ dec (succ m) x) f[s[m+x]]̄≢fx)
