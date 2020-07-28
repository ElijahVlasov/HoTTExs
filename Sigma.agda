{-# OPTIONS --without-K #-}

module Sigma where

open import prelude

Σ-paths : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {x y : Σ A P}
  → x ≡ y ≅ Σ (proj₁ x ≡ proj₁ y) (λ p → transp {P = P} p (proj₂ x) ≡ proj₂ y)
Σ-paths {A = A} {P} {a , b} {a' , b'} = (λ { refl → refl , refl }) ,
                                        (quasi-isequiv _ (record { g = λ { (refl , refl) → refl } ;
                                                                   g∘f = λ { refl → refl } ;
                                                                   f∘g = λ { (refl , refl) → refl } }))

Σ-paths' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {x y : Σ A P}
  → x ≡ y ≅ Σ (proj₁ x ≡ proj₁ y) (λ p → transp {P = P} (~ p) (proj₂ y) ≡ proj₂ x)
Σ-paths' {A = A} {P} {a , b} {a' , b'} = (λ { refl → refl , refl }) ,
                                        (quasi-isequiv _ (record { g = λ { (refl , refl) → refl } ;
                                                                   g∘f = λ { refl → refl } ;
                                                                   f∘g = λ { (refl , refl) → refl } }))


{-Σ-equiv : ∀ {ℓ₁} {A : Set ℓ₁} {P Q : A → Set ℓ₂}
  → -}
