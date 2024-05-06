{-# OPTIONS --without-K #-}

module core.equiv where

open import core.base
open import core.identity

module _
    {𝓵1 𝓵2 : Level} {A : Type 𝓵1} {B : Type 𝓵2} (f : A → B)
    where

    is-section : (B → A) → Type 𝓵2
    is-section g = f ∘ g ~ id

module _
    {𝓵1 𝓵2 : Level} {A : Type 𝓵1} {B : Type 𝓵2} (f : A → B)
    where

    section : Type (𝓵1 ⊔ 𝓵2)
    section = Σ (B → A) (is-section f)

module _
    {𝓵1 𝓵2 : Level} {A : Type 𝓵1} {B : Type 𝓵2}
    where

    is-retraction : (f : A → B) (g : B → A) → Type 𝓵1
    is-retraction f g = g ∘ f ~ id

    retraction : (f : A → B) → Type (𝓵1 ⊔ 𝓵2)
    retraction f = Σ (B → A) (is-retraction f)

module _
  {𝓵1 𝓵2 : Level} {A : Type 𝓵1} {B : Type 𝓵2}
  where

  is-equiv : (A → B) → Type (𝓵1 ⊔ 𝓵2)
  is-equiv f = section f × retraction f

module _
  {𝓵1 𝓵2 : Level} (A : Type 𝓵1) (B : Type 𝓵2)
  where

  equiv : Type (𝓵1 ⊔ 𝓵2)
  equiv = Σ (A → B) is-equiv

infix 6 _≃_

_≃_ : {𝓵1 𝓵2 : Level} (A : Type 𝓵1) (B : Type 𝓵2) → Type (𝓵1 ⊔ 𝓵2)
A ≃ B = equiv A B

postulate
    univalance : ∀ {𝓵 : Level} {A : Type 𝓵} {B : Type 𝓵} → (A ≃ B) ≃ (A ≡ B)