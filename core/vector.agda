module core.vector where

open import core.base
open import core.natural.base
open import core.natural.properties


data Vector (A : Type) : ℕ → Type where
    ⟨⟩ : Vector A 0
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

_++_ : ∀ {A n m} → Vector A n → Vector A m → Vector A (n + m)
⟨⟩ ++ ys = ys 
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)