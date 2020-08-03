{-# OPTIONS --without-K #-}

module UnivalenceRule where

open import prelude
open import Sigma
open import Univalence
open import Equivalences

module UnivalenceFromPropUnivRule where

  postulate
    𝕁ᵘ : ∀ {ℓ}
        (C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ))
        (t : (A : Set ℓ) → C A A ≅-refl) →
        ---------------------------------------
        (A B : Set ℓ) (e : A ≅ B) → C A B e

  postulate
    𝕁ᵘ-β : ∀ {ℓ}
          {C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ)}
          {t : (A : Set ℓ) → C A A ≅-refl} →
          {A : Set ℓ} →
          ------------------------------
          𝕁ᵘ C t A A ≅-refl ≡ t A

  univ-axiom : ∀ ℓ → isUnivalent ℓ
  univ-axiom ℓ A B = quasi-isequiv  (record { g = λ { (lift e) → 𝕁ᵘ (λ A B _ → A ≡ B) (λ A → refl) A B e } ;
                                              g∘f = λ { refl → 𝕁ᵘ-β } ;
                                              f∘g = λ { (lift e) → 𝕁ᵘ (λ A' B' e' → idtoeqv A' B' (𝕁ᵘ (λ A B _ → A ≡ B)
                                                                                         (λ A → refl) A' B' e') ≡ lift e')
                                                                       (λ A → ap (idtoeqv A A) 𝕁ᵘ-β)
                                                                       A
                                                                       B
                                                                       e } })

module UnivalenceRuleFromUnivalence (ua : ∀ {ℓ} → isUnivalent ℓ) where 

  private
    univ-quasi : ∀ {ℓ} → (A B : Set ℓ) → quasiinv (idtoeqv A B)
    univ-quasi A B = isequiv-quiv _ (ua A B)

    univ-hae : ∀ {ℓ} → (A B : Set ℓ) → ishae (idtoeqv A B)
    univ-hae A B = qinv-ishae (idtoeqv A B) (univ-quasi A B)

  univⁱ-refl : ∀ {ℓ} → (e : isUnivalent ℓ) → ∀ (A : Set ℓ) → (ishae.g (univ-hae A A) (lift ≅-refl) ) ≡ refl
  univⁱ-refl e A = ap (ishae.g (univ-hae A A)) (~ idtoeqv-refl)  ∙ (ishae.η (univ-hae A A) refl) 

  𝕁ᵘ : ∀ {ℓ} →
      (C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ))
      (t : (A : Set ℓ) → C A A ≅-refl) →
      ---------------------------------------
      (A B : Set ℓ) (e : A ≅ B) → C A B e
  𝕁ᵘ {ℓ = ℓ} C t A B e = transp {P = λ e' → C A B e'} (ap unlift (ishae.ε (univ-hae A B) (lift e)))
                                                       (𝕁 (λ (A' B' : Set ℓ) (p : A' ≡ B') → C A' B' (idtoeqv' A' B' p))
                                                          t 
                                                          A
                                                          B
                                                          (quasiinv.g (univ-quasi A B) (lift e)))

  univalence-≅-refl : ∀ {ℓ} {A : Set ℓ} → refl ≡ (ishae.g (univ-hae A A) (lift ≅-refl))
  univalence-≅-refl {A = A} = ~ ishae.η (univ-hae A A) refl
    
  𝕁ᵘ-β : ∀ {ℓ}
      {C : (A B : Set ℓ) → (e : A ≅ B) → Set (lsuc ℓ)}
      {t : (A : Set ℓ) → C A A ≅-refl} →
      {A : Set ℓ} →
      ------------------------------
      𝕁ᵘ C t A A ≅-refl ≡ t A
  𝕁ᵘ-β {ℓ = ℓ} {C = C} {t = t} {A = A} = ap (transp { P = λ e' → C A A e' }
                                            (ap unlift
                                             (ishae.ε (univ-hae A A) (lift ((λ a → a) , id-isequiv)))))
                                                        (~ apd (λ x →
                                                          𝕁 (λ A' B' p → C A' B' (idtoeqv' A' B' p)) t A A
                                                          x) univalence-≅-refl)
                                         ∙ ((~ transp-ap  {p = (ishae.ε (univ-hae A A) (lift ((λ a → a) , id-isequiv)))} {f = unlift})
                                         ∙ (transp-equal-paths (~ (ishae.τ (univ-hae A A) refl )) 
                                         ∙ ((~ transp-ap {p = ishae.η (univ-hae A A) refl} {f = idtoeqv A A}) 
                                         ∙ (transp-p-~p ((ishae.η (univ-hae A A) refl))))))
