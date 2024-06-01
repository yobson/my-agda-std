{-# OPTIONS --without-K --level-universe #-}

module core.base where

open import Agda.Primitive
    using (Level ; lzero ; lsuc ; _⊔_ ; Prop)
    renaming (Set to Type)
    public


data ⊥ : Type where

record ⊤ : Type where
    constructor
        *
open ⊤ public
{-# BUILTIN UNIT ⊤ #-}

record Σ {a b} (A : Type a) (B : A → Type b) : Type (a ⊔ b) where
  constructor _,_
  field
    wit : A
    prf : B wit
open Σ public

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}

record _×_ {l j} (A : Type l) (B : Type j) : Type (l ⊔ j) where
    constructor _,_
    field
        fst : A
        snd : B
open _×_ public

data _⨄_ {l1 l2} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
    left  : A → A ⨄ B
    right : B → A ⨄ B
