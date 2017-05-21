{-# OPTIONS --without-K --rewriting #-}

module Base.Natural where

open import Base
open import Base.Equality
open import Base.WellFounded

open import Agda.Builtin.Nat
  public
  using ( zero
        ; _+_
        ; _-_
        )
  renaming ( Nat to ℕ
           ; suc to succ
           )

ℕ-elim : ∀ {ℓ}
           (τ : ℕ → Type ℓ)
         → τ zero
         → ((n : ℕ) (x : τ n) → τ (succ n))
         → ((n : ℕ) → τ n)
ℕ-elim τ z s zero     = z
ℕ-elim τ z s (succ n) = s n (ℕ-elim τ z s n)

ℕ-rec : ∀ {ℓ}
          {τ : Type ℓ}
        → τ
        → (ℕ → τ → τ)
        → (ℕ → τ)
ℕ-rec = ℕ-elim _

zero≢succ : (x : ℕ) → zero ≢ succ x
zero≢succ x = λ ()

succ≢zero : (x : ℕ) → succ x ≢ zero
succ≢zero x = λ ()

succ-inj : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-inj refl = refl

instance
  DecEq-Nat#instance : DecEq ℕ
  DecEq-Nat#instance = record { _≟_ = _==_ } where
    _==_ : (x y : ℕ) → x ≡ y ⊎ x ≢ y
    zero   == zero   = i₁ refl
    zero   == succ y = i₂ (zero≢succ y)
    succ x == zero   = i₂ (succ≢zero x)
    succ x == succ y with x == y
    ... | i₁ x≡y = i₁ (ap succ x≡y)
    ... | i₂ x≢y = i₂ (contrapositive succ-inj x≢y)

sm+n≡m+sn : ∀ m n → succ m + n ≡ m + succ n
sm+n≡m+sn zero     n = refl
sm+n≡m+sn (succ m) n = ap succ (sm+n≡m+sn m n)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero     zero     = refl
+-comm zero     (succ n) = ap succ (+-comm zero n)
+-comm (succ m) zero     = ap succ (+-comm m zero)
+-comm (succ m) (succ n) = begin
  succ m + succ n     ≡⟨⟩
  succ (m + succ n)   ≡⟨ +-comm m (succ n) |in-ctx succ ⟩
  succ (succ n + m)   ≡⟨⟩
  succ (succ (n + m)) ≡⟨ +-comm n m |in-ctx (succ ∘ succ) ⟩
  succ (succ (m + n)) ≡⟨⟩
  succ (succ m + n)   ≡⟨ +-comm (succ m) n |in-ctx succ ⟩
  succ (n + succ m)   ≡⟨⟩
  succ n + succ m     ∎

data _≤_ (m : ℕ) : ℕ → Type₀ where
  refl : m ≤ m
  succ : {n : ℕ} → m ≤ n → m ≤ succ n

_≰_ : ℕ → ℕ → Type₀
m ≰ n = ¬ m ≤ n

_<_ : ℕ → ℕ → Type₀
m < n = succ m ≤ n

_≮_ : ℕ → ℕ → Type₀
m ≮ n = ¬ m < n

0≤n : ∀ n → zero ≤ n
0≤n zero     = refl
0≤n (succ n) = succ (0≤n n)

n≮0 : ∀ n → n ≮ zero
n≮0 n = λ ()

m≤n⇒sm≤sn : ∀ {m n} → m ≤ n → succ m ≤ succ n
m≤n⇒sm≤sn refl       = refl
m≤n⇒sm≤sn (succ m≤n) = succ (m≤n⇒sm≤sn m≤n)

sm≤sn⇒m≤n : ∀ {m n} → succ m ≤ succ n → m ≤ n
sm≤sn⇒m≤n {m}          refl         = refl
sm≤sn⇒m≤n {m} {zero}   (succ sm≤sn) = sm≤sn ↯ n≮0 m
sm≤sn⇒m≤n {m} {succ n} (succ sm≤sn) = succ (sm≤sn⇒m≤n sm≤sn)

m≰n⇒sm≰sn : ∀ {m n} → m ≰ n → succ m ≰ succ n
m≰n⇒sm≰sn m≰n = λ sm≤sn → sm≤sn⇒m≤n sm≤sn ↯ m≰n

<-irrefl : ∀ n → n ≮ n
<-irrefl zero     = λ()
<-irrefl (succ n) = λ sn<sn → sn<sn ↯ m≰n⇒sm≰sn (<-irrefl n)

m<n⇒m≤n : ∀ {m n} → m < n → m ≤ n
m<n⇒m≤n refl       = succ refl
m<n⇒m≤n (succ m<n) = succ (m<n⇒m≤n m<n)

m≰sn⇒m≰n : ∀ {m n} → m ≰ succ n → m ≰ n
m≰sn⇒m≰n m≰sn m≤n = succ m≤n ↯ m≰sn

m≰n⇒sm≰n : ∀ {m n} → m ≰ n → succ m ≰ n
m≰n⇒sm≰n m≰n sm≤n = m<n⇒m≤n sm≤n ↯ m≰n

m≤n⇒n≮m : ∀ {m n} → m ≤ n → n ≮ m
m≤n⇒n≮m refl       = <-irrefl _
m≤n⇒n≮m (succ m≤n) = m≰n⇒sm≰n (m≤n⇒n≮m m≤n)

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym refl       _   = refl
≤-antisym (succ m≤n) n<m = n<m ↯ m≤n⇒n≮m m≤n

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans refl       m≤p        = m≤p
≤-trans m≤n        refl       = m≤n
≤-trans (succ m≤n) (succ n<p) = ≤-trans m≤n (succ (m<n⇒m≤n n<p))

m≤n⇒m≢n⇒m<n : ∀ {m n} → m ≤ n → m ≢ n → m < n
m≤n⇒m≢n⇒m<n refl       m≢m = refl ↯ m≢m
m≤n⇒m≢n⇒m<n (succ m≤n) _   = m≤n⇒sm≤sn m≤n

wf-< : WellFounded _<_
wf-< = λ x → accessible (acc x) where
  acc : ∀ x y → y < x → Accessible _<_ y
  acc zero y y<0            = y<0 ↯ n≮0 y
  acc (succ x) _ refl       = accessible (λ y y<x → acc x y y<x)
  acc (succ x) y (succ y<x) = acc x y y<x
