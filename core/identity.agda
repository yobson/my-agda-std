{-# OPTIONS --without-K #-}

module core.identity where

open import core.base

data Id {l : Level} (A : Type l) (x : A) : A → Type l where
    ≡-refl : Id A x x

{-# BUILTIN EQUALITY Id #-}

module _ 
    {l : Level}
    where

    _≡_ : ∀ {A : Type l} → A → A → Type l
    _≡_ {A = A} x y = Id A x y
    infix 0 _≡_

    ≡-sym : ∀ {A : Type l} {a b : A} → a ≡ b → b ≡ a
    ≡-sym ≡-refl = ≡-refl

    ≡-trans : ∀ {A : Type l} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    ≡-trans ≡-refl ≡-refl = ≡-refl

module _ where
    id : ∀ {l : Level} {X : Type l} → X → X
    id x = x

module _ 
    {l₁ l₂ : Level}
    {A : Type l₁} {B : Type l₂} 
    where

    ≡-ap : ∀ {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
    ≡-ap f ≡-refl = ≡-refl

module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  infix 6 _~_
  _~_ : (f g : (x : A) → B x) → Type (l1 ⊔ l2)
  f ~ g = (x : A) → f x ≡ g x

module _ 
    {l₁ l₂ l₃ : Level}
    where

    ≡-ap₂ : ∀ {A : Type l₁} {B : Type l₂} {C : Type l₃} {a b : A} {c d : B} (f : A → B → C) → a ≡ b → c ≡ d → f a c ≡ f b d
    ≡-ap₂ f ≡-refl ≡-refl = ≡-refl

module _ 
    where

    infixr 15 _∘_

    _∘_ : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : (a : A) → B a → Type l3} →
          ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
    (g ∘ f) a = g (f a)

module ≡-Reasoning {l : Level} {A : Type l} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ step-≡
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ x y≡z x≡y  =  ≡-trans x≡y y≡z

  syntax step-≡ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  ≡-refl

open ≡-Reasoning
