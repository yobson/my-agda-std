{-# OPTIONS --without-K #-}
module core.boolean.base where

open import core.base

data 𝔹 : Type lzero where
  false true : 𝔹
{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

if_then_else_ : ∀ {l} {A : Type l} → 𝔹 → A → A → A
if false then t else f = f
if true then t else f = t

_∧_ : 𝔹 → 𝔹 → 𝔹
false ∧ q = false 
true  ∧ q = q
infixr 20 _∧_

_∨_ : 𝔹 → 𝔹 → 𝔹
false ∨ q = q 
true  ∨ q = true
infixr 20 _∨_

_⟶_ : 𝔹 → 𝔹 → 𝔹
p ⟶ q = if p then q else true

_iff_ : 𝔹 → 𝔹 → 𝔹
false iff false = true
false iff true  = false  
true iff false  = false 
true iff true   = true

¬_ : 𝔹 → 𝔹
¬ false = true 
¬ true = false
infix 30 ¬_