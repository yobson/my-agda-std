{-# OPTIONS --without-K #-}

module core.natural.properties where

open import core.base
open import core.identity
open import core.natural.base

+-id : ∀ {a b c d : ℕ} → (a ≡ b) → (c ≡ d) → a + c ≡ b + d
+-id ≡-refl ≡-refl = ≡-refl

+-idₗ : ∀ {a b c : ℕ} → (a ≡ b) → a + c ≡ b + c
+-idₗ a=b = +-id a=b ≡-refl

+-idᵣ : ∀ {a b c} → (b ≡ c) → a + b ≡ a + c
+-idᵣ = +-id ≡-refl

+-unitₗ : ∀ {n} → (0 + n) ≡ n
+-unitₗ {Z}     = ≡-refl 
+-unitₗ {suc n} = ≡-refl 

+-unitᵣ : ∀ {n} → (n + 0) ≡ n
+-unitᵣ {Z}     = ≡-refl 
+-unitᵣ {suc n} = ≡-ap suc +-unitᵣ

+-1 : ∀ {n} → n + 1 ≡ suc n
+-1 {Z} = ≡-refl
+-1 {suc n} = ≡-ap suc +-1

+-assoc : ∀ {x y z} → x + (y + z) ≡ (x + y) + z
+-assoc {Z} = ≡-refl
+-assoc {suc x} = ≡-ap suc (+-assoc {x})

+-suc : ∀ {a} {b} → suc (a + b) ≡ a + suc b
+-suc {Z} = ≡-ap suc ≡-refl
+-suc {suc a} = ≡-ap suc +-suc

+-comm : ∀ {a b} → a + b ≡ b + a
+-comm {Z} = ≡-sym +-unitᵣ        
+-comm {suc a} {b} = ≡-trans (≡-ap suc (+-comm {a})) +-suc

**-unitₗ : ∀ {n : ℕ} → (n ** 1) ≡ n
**-unitₗ {Z} = ≡-refl 
**-unitₗ {suc n} = ≡-ap suc (**-unitₗ {n})

**-unitᵣ : ∀ {n : ℕ} → (1 ** n) ≡ n
**-unitᵣ {Z} = ≡-refl 
**-unitᵣ {suc n} = ≡-ap suc (**-unitᵣ {n})
