{-# OPTIONS --without-K #-}

module Coproducts where

open import prelude

module LeftCode {ℓ} {A B : Set ℓ} (a₀ : A) where

  codeˡ : A ⊎ B → Set ℓ
  codeˡ  (inl a) = a₀ ≡ a
  codeˡ  (inr b) = Lift ℓ 𝕆

  ⊎-pathsˡ : ∀ (x : A ⊎ B) → (inl a₀) ≡ x ≅ codeˡ x
  ⊎-pathsˡ x = encode x , quasi-isequiv (record { g = decode x ; g∘f = decode∘encode x ; f∘g = encode∘decode x })
    where
      encode : ∀ (x : A ⊎ B) (p : (inl a₀) ≡ x) → codeˡ x
      encode x p = transp {P = codeˡ} p refl

      decode : ∀ (x : A ⊎ B) (c : codeˡ x) → (inl a₀) ≡ x
      decode (inl x) c = ap inl c

      decode∘encode : ∀ (x : A ⊎ B) (p : inl a₀ ≡ x) → decode x (encode x p) ≡ p
      decode∘encode .(inl a₀) refl = refl

      encode∘decode : ∀ (x : A ⊎ B) (c : codeˡ x) → encode x (decode x c) ≡ c
      encode∘decode (inl x) refl = refl


open LeftCode public

module RightCode {ℓ} {A B : Set ℓ} (b₀ : B) where

  codeʳ : A ⊎ B → Set ℓ
  codeʳ (inl a) = Lift ℓ 𝕆
  codeʳ (inr b) = b₀ ≡ b

  ⊎-pathsʳ : ∀ (x : A ⊎ B) → (inr b₀) ≡ x ≅ codeʳ x
  ⊎-pathsʳ x = encode x , quasi-isequiv (record { g = decode x ; g∘f = decode∘encode x ; f∘g = encode∘decode x })
    where
      encode : ∀ (x : A ⊎ B) (p : (inr b₀) ≡ x) → codeʳ x
      encode x p = transp {P = codeʳ} p refl

      decode : ∀ (x : A ⊎ B) (c : codeʳ x) → (inr b₀) ≡ x
      decode (inr x) c = ap inr c

      decode∘encode : ∀ (x : A ⊎ B) (p : inr b₀ ≡ x) → decode x (encode x p) ≡ p
      decode∘encode .(inr b₀) refl = refl

      encode∘decode : ∀ (x : A ⊎ B) (c : codeʳ x) → encode x (decode x c) ≡ c
      encode∘decode (inr x) refl = refl

open RightCode public
