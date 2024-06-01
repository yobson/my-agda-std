{-# OPTIONS --without-K #-}

module core.equiv where

open import core.base
open import core.identity

record Iso {𝓵₁ 𝓵₂} {A : Type 𝓵₁} {B : Type 𝓵₂} (to : A → B) : Type (𝓵₁ ⊔ 𝓵₂) where
  field
    from : B → A
    to∘from : ∀ {x} → to(from(x)) ≡ x
    from∘to : ∀ {x} → from(to(x)) ≡ x
open Iso public


_≃_ : ∀ {𝓵₁ 𝓵₂} (A : Type 𝓵₁) (B : Type 𝓵₂) → Type (𝓵₁ ⊔ 𝓵₂)
_≃_ A B = Σ (A → B) Iso

postulate
  univalence : ∀ {𝓵} {A B : Type 𝓵} → (A ≃ B) ≃ (A ≡ B)

≃-sym : ∀ {𝓵₁ 𝓵₂} {A : Type 𝓵₁} {B : Type 𝓵₂} → A ≃ B → B ≃ A
wit (≃-sym (A→B , iso)) = from iso
prf (≃-sym (A→B , iso)) = record 
  { from = A→B
  ; to∘from = from∘to iso 
  ; from∘to = to∘from iso 
  }

module _
  {𝓵₁ 𝓵₂ : Level}
  {A : Type 𝓵₁}
  {B : Type 𝓵₂}
  where

  ≃-map : A ≃ B → A → B
  ≃-map (A→B , _) x = A→B x

  ≃-contrmap : B ≃ A → A → B
  ≃-contrmap equiv = ≃-map (≃-sym equiv)

liftEquiv : ∀ {𝓵} {A B : Type 𝓵} → (A ≡ B) → (A ≃ B)
liftEquiv ≡-refl = (λ x → x) , record 
  { from = λ z → z 
  ; to∘from = ≡-refl 
  ; from∘to = ≡-refl 
  }

liftId : ∀ {𝓵} {A B : Type 𝓵} → (A ≃ B) → (A ≡ B)
liftId = wit univalence