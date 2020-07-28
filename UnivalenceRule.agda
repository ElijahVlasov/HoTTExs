{-# OPTIONS --without-K --rewriting #-}

module UnivalenceRule where

open import prelude
open import Univalence

infix 30 _↦_
postulate  
 _↦_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ

{-# BUILTIN REWRITE _↦_ #-}

module UnivalenceFromUnivalenceRule where
  -- Univalence rule
  postulate
    𝕁ᵘ : ∀ {ℓ}
      (C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ))
      (t : (A : Set ℓ) → C A A ≅-refl) →
      ---------------------------------------
      (A B : Set ℓ) (e : A ≅ B) → C A B e

    𝕁ᵘ-β : ∀ {ℓ}
        {C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ)}
        {t : (A : Set ℓ) → C A A ≅-refl} →
        {A : Set ℓ} →
        ------------------------------
        𝕁ᵘ C t A A ≅-refl ↦ t A

  {-# REWRITE 𝕁ᵘ-β #-}

  univ-axiom : ∀ ℓ → isUnivalent ℓ
  univ-axiom ℓ A B = quasi-isequiv _ (record { g = λ { (lift e) → 𝕁ᵘ (λ A B _ → A ≡ B) (λ A → refl) A B e } ;
                                               g∘f = λ { refl → refl } ;
                                               f∘g = λ { (lift e) → 𝕁ᵘ (λ A' B' e' → idtoeqv A' B' (𝕁ᵘ (λ A B _ → A ≡ B)
                                                                                         (λ A → refl) A' B' e') ≡ lift e')
                                                                       (λ A → refl)
                                                                       A
                                                                       B
                                                                       e} } )

module UnivalenceRuleFromUnivalence (ua : ∀ {ℓ} → isUnivalent ℓ) where 

  private
    univ-quasi : ∀ {ℓ} → (A B : Set ℓ) → quasiinv (idtoeqv A B)
    univ-quasi A B = isequiv-quiv _ (ua A B)

  univⁱ-refl : ∀ {ℓ} → (e : isUnivalent ℓ) → ∀ (A : Set ℓ) → (quasiinv.g (univ-quasi A A) (lift ≅-refl) ) ≡ refl
  univⁱ-refl e A = ap (quasiinv.g (univ-quasi A A)) (~ idtoeqv-refl)  ∙ (quasiinv.g∘f (univ-quasi A A) refl) 

  𝕁ᵘ : ∀ {ℓ} →
      (C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ))
      (t : (A : Set ℓ) → C A A ≅-refl) →
      ---------------------------------------
      (A B : Set ℓ) (e : A ≅ B) → C A B e
  𝕁ᵘ {ℓ = ℓ} C t A B e = transp {P = λ e' → C A B e'} (ap unlift (quasiinv.f∘g (univ-quasi A B) (lift e)))
                                                       (𝕁 (λ (A' B' : Set ℓ) (p : A' ≡ B') → C A' B' (idtoeqv' A' B' p))
                                                          (λ A' → t A')
                                                          A
                                                          B
                                                          (quasiinv.g (univ-quasi A B) (lift e)))

    
  𝕁ᵘ-β : ∀ {ℓ}
      {C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ)}
      {t : (A : Set ℓ) → C A A ≅-refl} →
      {A : Set ℓ} →
      ------------------------------
      𝕁ᵘ C t A A ≅-refl ≡ t A
  𝕁ᵘ-β {ℓ = ℓ} {C = C} {t = t}  {A = A} = {!transp !} ∙ {!!}

--transp (quasiinv.g∘f (univ-quasi A A) refl ) {!!}
{-transp {P = λ { p → transp {P = λ e' → C A A e'} (ap unlift (quasiinv.f∘g (univ-quasi A A) (lift ≅-refl)))
                                                       (𝕁 (λ (A' B' : Set ℓ) (p : A' ≡ B') → C A' B' (idtoeqv' A' B' p))
                                                          (λ A' → t A')
                                                          A
                                                          A
                                                          p) ≡ t A }} {!(~ univⁱ-refl ua A)!} {!!}-}
  --transp {P = {!!}} {!!} {!!}
  --transp {!!} {!!} --(~ univⁱ-refl ua A) {!!}
