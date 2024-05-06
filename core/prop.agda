{-# OPTIONS --without-K --prop #-}

module core.prop where

open import core.base

module _
    {l : Level}
    where

    True : Prop (lsuc l)
    True = ∀ (P : Prop l) → P → P

    False : Prop (lsuc l)
    False = ∀ (P : Prop l) → P → ⊥

    data Squash (A : Type l) : Prop l where
        squash : A → Squash A
