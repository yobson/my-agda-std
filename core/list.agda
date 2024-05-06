module core.list where

open import core.base

data List (A : Type) : Type where
    [] : List A
    _::_ : A → List A → List A

data Index {A : Type} : List A → Type where