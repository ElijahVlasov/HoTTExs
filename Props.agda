{-# OPTIONS --without-K #-}

module Props where

open import prelude
open import Sigma
open import Univalence

hProp : (ℓ : Level) → Set (lsuc ℓ)
hProp ℓ = Σ (Set ℓ) isProp

LiftP : ∀ {ℓ} → (Lift (lsuc (lsuc ℓ)) (hProp ℓ)) → hProp (lsuc ℓ)
LiftP {ℓ} (lift (A , isPropA)) = (Lift (lsuc ℓ) A) , (λ { (lift x) (lift y) → ap (lift {ℓ₂ = lsuc ℓ}) (isPropA x y)} )

PropositionalResizing : (ℓ : Level) → Set (lsuc (lsuc ℓ))
PropositionalResizing ℓ = isequiv (LiftP {ℓ = ℓ})

{-module FromHigherToLower (prop-resizing : ∀ {ℓ} → PropositionalResizing ℓ) where
  from-higher-to-lower : ∀ {ℓ} {B : Set (lsuc ℓ)} → (isPropB : isProp B)
    → B → proj₁ (unlift (isequiv.left (prop-resizing ) (B , isPropB)))
  from-higher-to-lower {B = B} isPropB b = {!!}-}

isProp-contractible-path-spaces : ∀ {ℓ} {A : Set ℓ} → isProp A
  → ∀ (x y : A) → isContr (x ≡ y)
isProp-contractible-path-spaces {A = A} isPropA x y = record { center = isPropA x y ;
                                                       contr = λ p → (~ idʳ) ∙ (cancelˡ {q = ~ isPropA x y} (
                                                                      assoc ∙ (ap (_∙ refl) invˡ ∙
                                                                                 loops-are-refls y ((~ isPropA x y) ∙ p)))) }
   where
     loops-are-refls : ∀ (x : A) (p : x ≡ x) → refl ≡ p
     loops-are-refls x p = (((~ invˡ {p = isPropA x x}) ∙ (ap (_∙_ (~ isPropA x x)) (~ idˡ) ∙
                                                         ap (_∙_ _) (ap (_∙ _) (ap-const p))))
                                      ∙ (~ homotopy-naturality'' (isPropA x) p)) ∙ ap-id

module doubleisProp {ℓ} (funext : ∀ {A : Set ℓ} {P : A → Set ℓ} {f g : ∀ a → P a}
                                                       → (∀ (x : A) → f x ≡ g x) → f ≡ g) where

  isProp-isProp : ∀ {A : Set ℓ} → isProp (isProp A)
  isProp-isProp isPropA isPropA' = funext λ x → funext λ y → isContr-isProp (isProp-contractible-path-spaces isPropA x y)
                                                                              (isPropA x y) (isPropA' x y)

open doubleisProp public

  {-isProp-isContr : ∀ {ℓ} {A : Set ℓ} → isProp (isContr A)
  isProp-isContr record { center = a ;
                          contr = contr }
                 record { center = a' ;
                          contr = contr' } = {!!}
-}
isProp-inhabited-isContr : ∀ {ℓ} {A : Set ℓ} → isProp A → A → isContr A
isProp-inhabited-isContr isPropA a = record { center = a ; contr = λ x → isPropA a x }

isProp-𝕆 : ∀ {ℓ} → isProp (Lift ℓ 𝕆)
isProp-𝕆 () y

𝕆ₚ : ∀ {ℓ} → hProp ℓ
𝕆ₚ {ℓ = ℓ} = Lift ℓ 𝕆 , isProp-𝕆

isProp-𝟙 : ∀ {ℓ} → isProp (Lift ℓ 𝟙)
isProp-𝟙 (lift tt) (lift tt) = refl

𝟙ₚ : ∀ {ℓ} → hProp ℓ
𝟙ₚ {ℓ = ℓ} = (Lift ℓ 𝟙) , isProp-𝟙

inhab-prop≅𝟙 : ∀ {ℓ} {A : Set ℓ} → isProp A → A → A ≅ (Lift ℓ 𝟙)
inhab-prop≅𝟙 isPropA a = (λ x → lift tt) , (quasi-isequiv (record { g = λ { (lift tt) → a} ;
                                                                       g∘f = λ x → isPropA _ _ ;
                                                                       f∘g = λ { (lift tt) → isProp-𝟙 _ _ } }) )
inhab-prop≡𝟙 : ∀ {ℓ} {A : Set ℓ} → isUnivalent ℓ → isProp A → A → A ≡ (Lift ℓ 𝟙)
inhab-prop≡𝟙 {ℓ = ℓ} {A = A} univalence isPropA a = isequiv.left (univalence A (Lift ℓ 𝟙)) (lift (inhab-prop≅𝟙 isPropA a))

inhab-¬-prop≅𝕆 : ∀ {ℓ} {A : Set ℓ} → isProp A → (¬ A) → A ≅ (Lift ℓ 𝕆)
inhab-¬-prop≅𝕆 isPropA a = a , (quasi-isequiv (record { g = λ { () } ; g∘f = λ x → isPropA _ _ ; f∘g = λ { () } }))

inhab-¬-prop≡𝕆 : ∀ {ℓ} {A : Set ℓ} → isUnivalent ℓ → isProp A → (¬ A) → A ≡ (Lift ℓ 𝕆)
inhab-¬-prop≡𝕆 {ℓ = ℓ} {A = A} univalence isPropA a = isequiv.left (univalence A (Lift ℓ 𝕆)) (lift (inhab-¬-prop≅𝕆 isPropA a))

module ∀-prop-proof (funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {f g : ∀ a → P a}
                                                       → (∀ (x : A) → f x ≡ g x) → f ≡ g) where
  ∀-prop : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
    → isProp A → (∀ (a : A) → isProp (P a)) → isProp (∀ a → P a)
  ∀-prop isPropA isPropPa f g = funext λ a → isPropPa a _ _

open ∀-prop-proof public

module PropTrunc where
  private
    data ∥_∥' {ℓ} (A : Set ℓ) : Set ℓ where
      ⟦_⟧' : A → ∥ A ∥'


  ∥_∥ : ∀ {ℓ} (A : Set ℓ) → Set ℓ
  ∥ A ∥ = ∥ A ∥'

  ⟦_⟧ : ∀ {ℓ} {A : Set ℓ} → A → ∥ A ∥
  ⟦_⟧ = ⟦_⟧'

  ∥∥-rec : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B)
    → isProp B → ∥ A ∥ → B
  ∥∥-rec f isPropB ⟦ a ⟧' = f a

  ∥∥-ind : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : ∥ A ∥ → Set ℓ₂}
    → (∀ (a : A) → P ⟦ a ⟧) → (∀ (x : ∥ A ∥) → isProp (P x)) → ∀ (x : ∥ A ∥) → P x
  ∥∥-ind ind isPropPx ⟦ a ⟧' = ind a

  postulate 
    ∥∥-prop : ∀ {ℓ} {A : Set ℓ} → isProp A 

open PropTrunc public

∥∥-ind' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : ∥ A ∥ → Set ℓ₂}
    → (∀ (a : A) → P ⟦ a ⟧) → (∀ (x : ∥ A ∥) → isProp (P x)) → ∀ (x : ∥ A ∥) → P x
∥∥-ind' {A = A} {P = P} Pa isPropPx x = ∥∥-rec (λ a → transp {P = P} (∥∥-prop ⟦ a ⟧ x) (Pa a)) (isPropPx x) x

_∨_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ∨ B = ∥ A ⊎ B ∥

LEM : (ℓ : Level) → Set (lsuc ℓ)
LEM ℓ = ∀ (A : Set ℓ) → isProp A → A ⊎ (¬ A)

isProp-≅ : ∀ {ℓ} {A B : Set ℓ} → A ≅ B → isProp A → isProp B
isProp-≅ (f , e) isPropA b b' with (isequiv-quiv f e)
isProp-≅ (f , e) isPropA b b' | record { g = g ;
                                         g∘f = g∘f ;    -- b ≡ f ∘ g b
                                         f∘g = f∘g } = 
                                                 (~ f∘g b) ∙
                                                ((ap f (isPropA (g b)
                                                                (g b')) ∙
                                                       f∘g b'))

isContr-≅ :  ∀ {ℓ} {A B : Set ℓ} → A ≅ B → isContr A → isContr B
isContr-≅ (f , e) isContrA = isProp-inhabited-isContr (isProp-≅ (f , e) (isContr-isProp isContrA)) (f (isContr.center isContrA))

isProp-× : ∀ {ℓ} {A B : Set ℓ} → isProp A → isProp B → isProp (A × B)
isProp-× isPropA isPropB = λ x y → isequiv.left (proj₂ Σ-paths) ((isPropA _ _) , (isPropB _ _))

isContr-× : ∀ {ℓ} {A B : Set ℓ} → isContr A → isContr B → isContr (A × B)
isContr-× isContrA isContrB = isProp-inhabited-isContr (isProp-× (isContr-isProp isContrA) (isContr-isProp isContrB))
                                                       ((isContr.center isContrA) , (isContr.center isContrB))
isContr-any-center : ∀ {ℓ} {A : Set ℓ} → isContr A → (a : A) → ∀ (x : A) → a ≡ x
isContr-any-center isContrA a x = (~ isContr.contr isContrA a) ∙ isContr.contr isContrA x

