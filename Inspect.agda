{-# OPTIONS --without-K #-}

module Inspect where

open import prelude

record Reveal_·_is_ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (ℓ₁ ⊔ ℓ₂) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]
