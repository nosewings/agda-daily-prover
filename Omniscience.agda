{-# OPTIONS --without-K --rewriting #-}

module Omniscience where

open import Base
open import Base.WellFounded
open import Base.Equality
open import Base.Natural

open import Decreasing

LPO : Type₀
LPO = (f : ℕ → 𝟚) → (Σ[ n ∶ ℕ ] f n ≡ 1₂) ⊎ (Π[ n ∶ ℕ ] f n ≡ 0₂)

InfiniteValley : (ℕ → ℕ) → ℕ → Type₀
InfiniteValley f x = ∀ y → x ≤ y → f y ≡ f x

module LPO⇒InfiniteValleys where

  module _ (f : ℕ → ℕ) where

    g : (ℕ → 𝟚)
    g x with f x ≟ f zero
    ... | i₁ _ = 0₂
    ... | i₂ _ = 1₂

    g≡0₂-inv : ∀ {x} → g x ≡ 0₂ → f x ≡ f zero
    g≡0₂-inv {x} _ with f x ≟ f zero
    g≡0₂-inv     _    | i₁ f[x]≡f[0] = f[x]≡f[0]
    g≡0₂-inv     ()   | i₂ _

    g≡1₂-Decreasing-inv : Decreasing f → ∀ {x} → g x ≡ 1₂ → f x < f zero
    g≡1₂-Decreasing-inv dec {x} _ with f x ≟ f zero
    g≡1₂-Decreasing-inv dec     ()   | i₁ _
    g≡1₂-Decreasing-inv dec     _    | i₂ f[x]≢f[0] = m≤n⇒m≢n⇒m<n (Decreasing-≤ dec (0≤n _)) f[x]≢f[0]

  shift : ∀ {ℓ} {A : Type ℓ} → ℕ → (ℕ → A) → (ℕ → A)
  shift n f = λ x → f (x + n)

  shift-Decreasing : ∀ {f} → Decreasing f → ∀ n → Decreasing (shift n f)
  shift-Decreasing dec n = λ x → dec (x + n)

  -- Let f : ℕ → ℕ be decreasing. Use the limited principle of omniscience to
  -- determine whether gᶠ is 1₂ somewhere or 0₂ everywhere.
  -- 
  -- If gᶠ is 0₂ everywhere, then f(x) = f(0) for all x by the inversion
  -- princple for g(x) = 0. This means that f has an infinite valley at 0.
  --
  -- If gᶠ is 1₂ at x, recurse on shift x f. (We have shown above that this
  -- function is decreasing). The recursion will eventually terminate because
  -- f(x) < f(0) by the inversion principle for gᶠ(x) = 1₂, and the less-than
  -- relationship is well-founded.
  --
  -- The recursive call yields y : ℕ and v : InfiniteValley (shift x f) y. The
  -- expanded type of v is ∀ z → y ≤ z → f (z + x) ≡ f (y + x), so we take y + x
  -- as the starting point for the infinite valley in f.
  --
  -- Now we need to show that, for all z : ℕ, if y + x ≤ z, then
  -- f(z) = f(y + x).
  --
  -- If y + x ≤ z, then z ≥ x. It follows that (z - x) + x = z, so
  -- f(z) = f((z - x) + x).
  --
  -- Again using the fact that y + x ≤ z, we conclude that y ≤ z - x. This means
  -- that z - x is in the valley v, so f((z - x) + x) = f(y + x). This concludes
  -- the proof.
  
  LPO⇒InfiniteValleys : LPO → (f : ℕ → ℕ) → Decreasing f → Σ ℕ (InfiniteValley f)
  LPO⇒InfiniteValleys lpo = λ f dec → WellFounded-induction (on-wf wf-< (π₁ ⨾ _&_ 0)) _ go (f , dec) where

    _≺_ : Σ (ℕ → ℕ) Decreasing → Σ (ℕ → ℕ) Decreasing → Type₀
    (f , _) ≺ (g , _) = f zero < g zero

    go : ∀ u → (∀ w → w ≺ u → Σ ℕ (InfiniteValley (π₁ w))) → Σ ℕ (InfiniteValley (π₁ u))
    go (f , dec) rec with lpo (g f)
    ... | i₂ g≡0₂ = zero , (λ x _ → g≡0₂-inv f (g≡0₂ x))
    ... | i₁ (x , p) with rec (shift x f , shift-Decreasing dec x) (g≡1₂-Decreasing-inv f dec p)
    ... | y , v = y + x , help where
      help : ∀ z → y + x ≤ z → f z ≡ f (y + x)
      help z y+x≤z = begin
        f z             ≡⟨ m≤n⇒[n-m]+m≡n {x} (m+n≤p⇒n≤p {y} y+x≤z) |in-ctx f ⟩⁻¹
        f ((z - x) + x) ≡⟨ v (z - x) (m+n≤p⇒m≤p-n y+x≤z) ⟩
        f (y + x)       ∎

module InfiniteValleys⇒LPO where

  -- An injection from 𝟚 to ℕ.

  i : 𝟚 → ℕ
  i 0₂ = 1
  i 1₂ = 0

  -- Some basic facts about i.

  i≡0⊎i≡1 : ∀ x → i x ≡ 0 ⊎ i x ≡ 1
  i≡0⊎i≡1 0₂ = i₂ refl
  i≡0⊎i≡1 1₂ = i₁ refl

  i≤1 : ∀ x → i x ≤ 1
  i≤1 x with i x | i≡0⊎i≡1 x
  ... | _ | i₁ refl = succ refl
  ... | _ | i₂ refl = refl

  i≡0-inv : ∀ {x} → i x ≡ 0 → x ≡ 1₂
  i≡0-inv {0₂} ()
  i≡0-inv {1₂} _ = refl

  module _ (f : ℕ → 𝟚) where

    -- Intuitively, g(x) = 1 if f(y) = 0₂ for all y ≤ x; otherwise, g(x) = 0.

    g : ℕ → ℕ
    g zero = i (f zero)
    g (succ x) with g x
    ... | zero   = 0
    ... | succ _ = i (f (succ x))

    -- Either g(x) = 0 or g(x) = 1 for all x.

    g≡0⊎g≡1 : ∀ x → g x ≡ 0 ⊎ g x ≡ 1
    g≡0⊎g≡1 zero = i≡0⊎i≡1 (f zero)
    g≡0⊎g≡1 (succ x) with g x | g≡0⊎g≡1 x
    ... | _ | i₁ refl = i₁ refl
    ... | _ | i₂ refl = i≡0⊎i≡1 (f (succ x))

    -- Clearly, g is decreasing: g(x) ≤ 1 for all x; and if g(x) = 0, then
    -- g(y) = 0 for all y ≥ x.

    dec : Decreasing g
    dec zero with f 0
    ... | 1₂ = refl
    ... | 0₂ = i≤1 (f 1)
    dec (succ x) with g x | g≡0⊎g≡1 x
    ... | _ | i₁ refl = refl
    ... | _ | i₂ refl with f (succ x)
    ... | 0₂ = i≤1 (f (succ (succ x)))
    ... | 1₂ = refl

    -- If g(x) = 0, then there exists some y ≤ x such that f(y) = 1₂.

    g≡0-inv : ∀ x → g x ≡ 0 → Σ[ y ∶ ℕ ] f y ≡ 1₂
    g≡0-inv zero     i[f[0]]≡0 = zero , i≡0-inv i[f[0]]≡0
    g≡0-inv (succ x) i[f[sx]]≡0 with g x | inspect g x | g≡0⊎g≡1 x
    ... | _ | [ g[x]≡0 ] | i₁ refl = g≡0-inv x g[x]≡0
    ... | _ | _          | i₂ refl = succ x , i≡0-inv i[f[sx]]≡0

    -- If g(x) = 1, then f(x) = 0₂.

    g≡1-inv : ∀ {x} → g x ≡ 1 → f x ≡ 0₂
    g≡1-inv {zero}   _ with f zero
    g≡1-inv {zero}   _    | 0₂ = refl
    g≡1-inv {zero}   ()   | 1₂
    g≡1-inv {succ x} _ with g x | g≡0⊎g≡1 x
    g≡1-inv {succ x} ()   | _   | i₁ refl
    g≡1-inv {succ x} _    | _   | i₂ refl with f (succ x)
    g≡1-inv {succ x} _    | _   | i₂ refl    | 0₂ = refl
    g≡1-inv {succ x} ()   | _   | i₂ refl    | 1₂

    -- If g(x) = 1, then f(y) = 0₂ for all y ≤ x.

    g≡1-inv-≤ : ∀ {x} → g x ≡ 1 → ∀ {y} → y ≤ x → f y ≡ 0₂
    g≡1-inv-≤          g[x]≡1 refl = g≡1-inv g[x]≡1
    g≡1-inv-≤ {succ x} _      (succ y≤x) with g x | inspect g x | g≡0⊎g≡1 x
    g≡1-inv-≤ {succ x} ()     (succ y≤x)    | _   | _           | i₁ refl
    g≡1-inv-≤ {succ x} _      (succ y≤x)    | _   | [ g[x]≡1 ]  | i₂ refl = g≡1-inv-≤ g[x]≡1 y≤x

  -- Take f : 𝟚 → ℕ and find a point x after which gᶠ remains constant.
  --
  -- If gᶠ(x) = 0, then there exists some y ≤ x such that f(y) = 1₂, as shown
  -- above. (In this case it does not even matter that gᶠ remains constant.)
  --
  -- If gᶠ(x) = 1, then f is 0₂ everywhere by the following argument:
  --
  -- Take y : ℕ. Determine whether y ≤ x (this can be done constructively).
  --
  -- If y ≤ x, then f(y) = 0₂ by the generalized inversion principle for
  -- g(x) = 1.
  --
  -- If y ≰ x, then y ≥ x. Since gᶠ is constant after x, gᶠ(y) = 1, so
  -- f(y) = 0₂.

  InfiniteValleys⇒LPO : (∀ f → Decreasing f → Σ ℕ (InfiniteValley f)) → LPO
  InfiniteValleys⇒LPO vs f with vs (g f) (dec f)
  ... | x , v with g f x | inspect (g f) x | g≡0⊎g≡1 f x
  ... | _ | [ g[x]≡0 ] | i₁ refl = i₁ (g≡0-inv f x g[x]≡0)
  ... | _ | [ g[x]≡1 ] | i₂ refl = i₂ (λ y → case y ≤? x of λ{ (i₁ y≤x) → g≡1-inv-≤ f g[x]≡1 y≤x
                                                             ; (i₂ y≰x) → g≡1-inv f (v y (≰⇒≥ y≰x))
                                                             })
