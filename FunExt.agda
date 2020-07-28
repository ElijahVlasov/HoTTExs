{-# OPTIONS --without-K #-}

module FunExt where

open import prelude

happly : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {f g : ∀ a → P a}
  → f ≡ g → f == g
happly refl = ==-refl

funext-axiom : ∀ {ℓ₁ ℓ₂}
  → Set ((lsuc ℓ₁) ⊔ (lsuc ℓ₂))
funext-axiom {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} = ∀ (A : Set ℓ₁) (P : A → Set ℓ₂) (f g : ∀ a → P a) → isequiv (happly {f = f} {g = g})
