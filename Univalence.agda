{-# OPTIONS --without-K #-}
module Univalence where

open import prelude

idtoeqv' : ∀ {ℓ} (A B : Set ℓ) → A ≡ B → (A ≅ B)
idtoeqv' A B p = transp {P = id} p , transp-equiv

idtoeqv : ∀ {ℓ} (A B : Set ℓ) → A ≡ B → (Lift (lsuc ℓ) (A ≅ B))
idtoeqv A B p = lift (idtoeqv' A B p)

--transp {P = id} p , transp-equiv

isUnivalent : (ℓ : Level) → Set (lsuc ℓ)
isUnivalent ℓ = ∀ (A B : Set ℓ) → isequiv (idtoeqv A B)

coe-≅ : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {P : Set ℓ₁ → Set ℓ₂ }
  → isUnivalent ℓ₁ → A ≅ B → P A → P B
coe-≅ {A = A} {B = B} {P = P} p A≅B u
  = transp {P = P} (isequiv.left (p A B) (lift A≅B)) u

{-coe2-≅ ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {P : Set ℓ₁ → Set ℓ₂ }
  → isUnivalent ℓ₁ → A ≅ B → P A → P B-}

idtoeqv-refl : ∀ {ℓ} {A : Set ℓ} → idtoeqv A A refl ≡ lift ≅-refl
idtoeqv-refl = refl

{-univⁱ-refl : ∀ {ℓ} → (e : isUnivalent ℓ) → ∀ (A : Set ℓ) → (isequiv.right (e A A) (lift ≅-refl) ) ≡ refl
univⁱ-refl e A = ap (isequiv.right (e A A)) (~ idtoeqv-refl)  ∙ isequiv.right∘f (e A A) refl 
-}
