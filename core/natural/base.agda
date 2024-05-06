{-# OPTIONS --without-K #-}

module core.natural.base where

open import core.base

data ℕ : Type lzero where
    Z   : ℕ
    suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- data _≤_ : ℕ → ℕ → Type where
--     z≤n : ∀ {n} → 0 ≤ n
--     n≤n : ∀ {n m} → n ≤ m → suc n ≤ suc m

pred : ℕ → ℕ
pred Z = Z
pred (suc n) = n

_+_ : ℕ → ℕ → ℕ
Z + m     = m 
suc n + m = suc (n + m)
infixr 20 _+_

_-_ : ℕ → ℕ → ℕ
n - Z     = n 
n - suc m = (pred n) - m

_**_ : ℕ → ℕ → ℕ
Z ** m     = Z 
suc n ** m = m + (n ** m)

_^_ : ℕ → ℕ → ℕ
x ^ Z     = 1 
x ^ suc n = x ** (x ^ n)

module _ where
    open import core.identity

    _≤_ : ℕ → ℕ → Type
    n ≤ m = Σ ℕ (λ x → x + n ≡ m)

    _<_ : ℕ → ℕ → Type
    x < y = (suc x) ≤ y

module _ where
    open import core.boolean.base

    leq : ℕ → ℕ → 𝔹
    leq Z y = true
    leq (suc x) Z = false
    leq (suc x) (suc y) = leq x y

    less : ℕ → ℕ → 𝔹
    less x y = leq (suc x) y

    _%_ : ℕ → ℕ → ℕ
    {-# TERMINATING #-}
    n % m with less n m
    ... | false = (n - m) % m
    ... | true  = n 
    infixr 20 _%_