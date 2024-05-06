{-# OPTIONS --without-K #-}

module core.boolean.properties where

open import core.base
open import core.identity
open import core.boolean.base

∨-comm : ∀ {p q : 𝔹} → p ∨ q ≡ q ∨ p
∨-comm {false} {false} = ≡-refl
∨-comm {false} {true} = ≡-refl  
∨-comm {true} {false} = ≡-refl 
∨-comm {true} {true} = ≡-refl

∨-assoc : ∀ {p q r : 𝔹} → p ∨ q ∨ r ≡ (p ∨ q) ∨ r
∨-assoc {false} {false} {false} = ≡-refl
∨-assoc {false} {false} {true} = ≡-refl
∨-assoc {false} {true} {false} = ≡-refl
∨-assoc {false} {true} {true} = ≡-refl  
∨-assoc {true} {false} {false} = ≡-refl
∨-assoc {true} {false} {true} = ≡-refl  
∨-assoc {true} {true} {r} = ≡-refl

data _≤_ : 𝔹 → 𝔹 → Type where
    f≤n : ∀ {b} → false ≤ b
    t≤t : true ≤ true
