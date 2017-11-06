{-# OPTIONS --without-K --rewriting #-}

module Base.Natural where

open import Base
open import Base.Equality
open import Base.WellFounded

infix 4 _≤_ _≰_ _≥_ _≱_ _<_ _≮_ _>_ _≯_

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
    _==_ : (x y : ℕ) → Dec (x ≡ y)
    zero   == zero   = yes refl
    zero   == succ y = no  (zero≢succ y)
    succ x == zero   = no  (succ≢zero x)
    succ x == succ y with x == y
    ... | yes x≡y = yes (ap succ x≡y)
    ... | no  x≢y = no  (contrapositive succ-inj x≢y)

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

_≥_ : ℕ → ℕ → Type₀
m ≥ n = n ≤ m

_≱_ : ℕ → ℕ → Type₀
m ≱ n = n ≰ m

_<_ : ℕ → ℕ → Type₀
m < n = succ m ≤ n

_>_ : ℕ → ℕ → Type₀
m > n = n < m

_≮_ : ℕ → ℕ → Type₀
m ≮ n = ¬ m < n

_≯_ : ℕ → ℕ → Type₀
m ≯ n = n ≮ m

-- TODO: this needs some MASSIVE cleaning up.

≡⇒≤ : ∀ {m n} → m ≡ n → m ≤ n
≡⇒≤ refl = refl

0≤n : ∀ n → zero ≤ n
0≤n zero     = refl
0≤n (succ n) = succ (0≤n n)

0<sn : ∀ n → zero < succ n
0<sn zero     = refl
0<sn (succ n) = succ (0<sn n)

n≮0 : ∀ n → n ≮ zero
n≮0 n = λ ()

n≤0⇒n≡0 : ∀ {n} → n ≤ zero → n ≡ zero
n≤0⇒n≡0 refl = refl

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
<-irrefl zero     = λ ()
<-irrefl (succ n) = λ sn<sn → sn<sn ↯ m≰n⇒sm≰sn (<-irrefl n)

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ refl       = succ refl
<⇒≤ (succ m<n) = succ (<⇒≤ m<n)

m≰sn⇒m≰n : ∀ {m n} → m ≰ succ n → m ≰ n
m≰sn⇒m≰n m≰sn m≤n = succ m≤n ↯ m≰sn

≰⇒≮ : ∀ {m n} → m ≰ n → m ≮ n
≰⇒≮ m≰n m<n = <⇒≤ m<n ↯ m≰n

≤⇒≯ : ∀ {m n} → m ≤ n → m ≯ n
≤⇒≯ refl       = <-irrefl _
≤⇒≯ (succ m≤n) = ≰⇒≮ (≤⇒≯ m≤n)

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym refl       _   = refl
≤-antisym (succ m≤n) n<m = n<m ↯ ≤⇒≯ m≤n

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans refl       m≤p        = m≤p
≤-trans m≤n        refl       = m≤n
≤-trans (succ m≤n) (succ n<p) = m≤n ⟨ ≤-trans ⟩ (succ (<⇒≤ n<p))

m≤n⇒m≢n⇒m<n : ∀ {m n} → m ≤ n → m ≢ n → m < n
m≤n⇒m≢n⇒m<n refl       m≢m = refl ↯ m≢m
m≤n⇒m≢n⇒m<n (succ m≤n) _   = m≤n⇒sm≤sn m≤n

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m zero     = refl
m≤n+m m (succ n) = succ (m≤n+m m n)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n m n = ≡-rec (_≤_ m) (m≤n+m m n) (+-comm n m)

m+n≤p⇒m≤p : ∀ {m n p} → m + n ≤ p → m ≤ p
m+n≤p⇒m≤p {m} {n} refl         = m≤m+n m n
m+n≤p⇒m≤p         (succ m+n≤p) = succ (m+n≤p⇒m≤p m+n≤p)

m+n≤p⇒n≤p : ∀ {m n p} → m + n ≤ p → n ≤ p
m+n≤p⇒n≤p {m} {n} {p} m+n≤p = m+n≤p⇒m≤p (≡-rec (flip _≤_ p) m+n≤p (+-comm m n))

wf-< : WellFounded _<_
wf-< = λ x → accessible (acc x) where
  acc : ∀ x y → y < x → Accessible _<_ y
  acc zero y y<0            = y<0 ↯ n≮0 y
  acc (succ x) _ refl       = accessible (λ y y<x → acc x y y<x)
  acc (succ x) y (succ y<x) = acc x y y<x

n-n≡0 : ∀ n → n - n ≡ zero
n-n≡0 zero     = refl
n-n≡0 (succ n) = n-n≡0 n

m≤n⇒sn-m≡s[n-m] : ∀ {m n} → m ≤ n → succ n - m ≡ succ (n - m)
m≤n⇒sn-m≡s[n-m] {zero}   m≤n        = refl
m≤n⇒sn-m≡s[n-m] {succ m} refl       = m≤n⇒sn-m≡s[n-m] {m} refl
m≤n⇒sn-m≡s[n-m] {succ m} (succ m≤n) = m≤n⇒sn-m≡s[n-m] (<⇒≤ m≤n)

m+n-n≡m : ∀ m n → m + n - n ≡ m
m+n-n≡m zero     n = n-n≡0 n
m+n-n≡m (succ m) n = m≤n⇒sn-m≡s[n-m] (m≤n+m n m) ∙ ap succ (m+n-n≡m m n)

m≤n⇒[n-m]+m≡n : ∀ {m n} → m ≤ n → (n - m) + m ≡ n
m≤n⇒[n-m]+m≡n {m} refl       = ap (flip _+_ m) (n-n≡0 m)
m≤n⇒[n-m]+m≡n {m} (succ m≤n) =
  ap (flip _+_ m) (m≤n⇒sn-m≡s[n-m] m≤n) ∙ ap succ (m≤n⇒[n-m]+m≡n m≤n)

mutual

  m-sn≤m-n : ∀ m n → m - succ n ≤ m - n
  m-sn≤m-n zero n = 0≤n (zero - n)
  m-sn≤m-n (succ m) n = m-n≤sm-n m n

  m-n≤sm-n : ∀ m n → m - n ≤ succ m - n
  m-n≤sm-n m zero     = succ refl
  m-n≤sm-n m (succ n) = m-sn≤m-n m n

m+n≤p⇒m≤p-n : ∀ {m n p} → m + n ≤ p → m ≤ p - n
m+n≤p⇒m≤p-n {m} {n}          refl         = ≡-rec (_≤_ m) refl (m+n-n≡m m n ⁻¹)
m+n≤p⇒m≤p-n {m} {n} {succ p} (succ m+n≤p) =
  m+n≤p⇒m≤p-n m+n≤p ⟨ ≤-trans ⟩ m-n≤sm-n p n

_≤?_ : ∀ m n → m ≤ n ⊎ m ≰ n
zero   ≤? n    = i₁ (0≤n n)
succ m ≤? zero = i₂ (λ ())
succ m ≤? succ n with m ≤? n
... | i₁ m≤n = i₁ (m≤n⇒sm≤sn m≤n)
... | i₂ m≰n = i₂ (m≰n⇒sm≰sn m≰n)

sm≰sn⇒m≰n : ∀ {m n} → succ m ≰ succ n → m ≰ n
sm≰sn⇒m≰n {m} {n} sm≰sn = λ m≤n → m≤n⇒sm≤sn m≤n ↯ sm≰sn

mutual

  ≮⇒≥ : ∀ {m n} → m ≮ n → m ≥ n
  ≮⇒≥ {m} {zero}   m≮n   = 0≤n m
  ≮⇒≥ {m} {succ n} sm≰sn = ≰⇒> (sm≰sn⇒m≰n sm≰sn)

  ≰⇒> : ∀ {m n} → m ≰ n → m > n
  ≰⇒> {zero}   {n} 0≰n = 0≤n n ↯ 0≰n
  ≰⇒> {succ m} {n} m≮n = m≤n⇒sm≤sn (≮⇒≥ m≮n)

≰⇒≥ : ∀ {m n} → m ≰ n → m ≥ n
≰⇒≥ = <⇒≤ ∘ ≰⇒>

n≢sn : {n : ℕ} → n ≢ succ n
n≢sn {zero}   = λ ()
n≢sn {succ n} = λ sn≡ssn → n≢sn (succ-inj sn≡ssn)

<⇒≢ : ∀ {m n} → m < n → m ≢ n
<⇒≢ m<m refl = m<m ↯ <-irrefl _

>⇒≢ : ∀ {m n} → m > n → m ≢ n
>⇒≢ m>n = λ m≡n → (m≡n ⁻¹) ↯ <⇒≢ m>n
