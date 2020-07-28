{-# OPTIONS --without-K #-}

module Chapter3 where

open import prelude
open import ApEquiv
open import Coproducts
open import Equivalences
open import FunExt
open import Sigma
open import Univalence
open import Props

-- Ex 3.1


isProp-≅' : ∀ {ℓ} {A B : Set ℓ} → isUnivalent ℓ → A ≅ B
  → isProp A → isProp B
isProp-≅' = coe-≅ 

isSet-≅ : ∀ {ℓ} {A B : Set ℓ} → A ≅ B → isSet A → isSet B
isSet-≅ e isSetA b b' with (≅-sym e)
isSet-≅ e isSetA b b' | f , e' = isProp-≅ (≅-sym (=-≅ f e' b b')) (isSetA (f b) (f b')) -- isProp-≅ (≅-sym (=-≅ f e' b b')) (isSetA (f b) (f b')) 

isSet-≅' : ∀ {ℓ} {A B : Set ℓ} → isUnivalent ℓ → A ≅ B → isSet A → isSet B
isSet-≅' = coe-≅

-- 3.2

⊎-isSet : ∀ {ℓ} {A B : Set ℓ} → isSet A → isSet B → isSet (A ⊎ B)
⊎-isSet {A = A} {B = B} isSetA isSetB (inl a) y = isProp-≅ (≅-sym (⊎-pathsˡ a y)) (isProp-codeˡ a y)
  where
    isProp-codeˡ : ∀ (a : A) (y : A ⊎ B) → isProp (codeˡ a y)
    isProp-codeˡ a (inl a') = isSetA a a'
    isProp-codeˡ a (inr b) = isProp-𝕆
⊎-isSet {A = A} {B = B} isSetA isSetB (inr b) y = isProp-≅ (≅-sym (⊎-pathsʳ b y)) (isProp-codeʳ b y)
  where
    isProp-codeʳ : ∀ (b : B) (y : A ⊎ B) → isProp (codeʳ b y)
    isProp-codeʳ b (inl a) = isProp-𝕆
    isProp-codeʳ b (inr b') = isSetB b b'

-- 3.3

Σ-isSet : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} →
  isSet A → (∀ (a : A) → isSet (P a)) → isSet (Σ A P)
Σ-isSet isSetA isSetPa x y p q = isequiv.left (ap-equiv (proj₁ Σ-paths) (isequiv-quiv _ (proj₂ Σ-paths)) p q)
                                              (isequiv.left (proj₂ Σ-paths) ((isSetA _ _ _ _) , isSetPa _ _ _ _ _))

module Ex34 (funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {f g : ∀ a → P a}
                                                       → (∀ (x : A) → f x ≡ g x) → f ≡ g) where 

  -- 3.4
  isProp→isContr→ : ∀ {ℓ} {A : Set ℓ} → isProp A → isContr (A → A)
  isProp→isContr→ isPropA = record {
                               center = id ; -- id ;
                               contr = λ f → funext λ a → isPropA a (f a) } -- λ f → funext λ a → isPropA a (f a) }

  isContr→→isProp : ∀ {ℓ} {A : Set ℓ} → isContr (A → A) → isProp A
  isContr→→isProp {A = A} isContrA→A x y = ap (λ f → f y) f≡g  --  ap (λ f → f x) f≡g
    where
      f : A → A
      f a = x

      g : A → A
      g a = y

      f≡g : f ≡ g
      f≡g = isContr-isProp isContrA→A f g --isContr-isProp isContrA→A f g

  isProp-isContr' : ∀ {ℓ} {A : Set ℓ} → isProp (isContr' A)
  isProp-isContr' {A = A} (a , contr) (a' , contr') = isequiv.left (proj₂ Σ-paths) ((contr a') , funext λ x →
                                                                                  isContr-isProp
                                                                                  (isProp-contractible-path-spaces (isContr-isProp (isequiv.left (proj₂ isContr≅isContr') ((a , contr)))) a' x) _ _) 
  isProp-isContr : ∀ {ℓ} {A : Set ℓ} → isProp (isContr A)
  isProp-isContr {A = A} = isProp-≅ (≅-sym isContr≅isContr') isProp-isContr'

  -- 3.5
  isPropA≅A→isContrA : ∀ {ℓ} {A : Set ℓ} → isProp A ≅ (A → isContr A)
  isPropA≅A→isContrA = (λ isPropA → λ a → record { center = a ;
                                                     contr = λ x → isPropA a x }) ,
                        quasi-isequiv _ (record { g = λ q → λ x y → (~ (isContr.contr (q x) x)) ∙ isContr.contr (q x) y ;
                                                  g∘f = λ isPropA → isProp-isProp funext _ _ ;
                                                  f∘g = λ f →  funext λ x →  isProp-isContr _ _ })

-- Ex 3.6

  isProp¬A : ∀ {ℓ} {A : Set ℓ} → isProp (¬ A)
  isProp¬A f _ = funext λ a → rec-𝕆 (f a)

  LEM-isProp : ∀ {ℓ} {A : Set ℓ} → isProp A → isProp (A ⊎ (¬ A))
  LEM-isProp isPropA (inl a) (inl a') = ap inl (isPropA a a')
  LEM-isProp isPropA (inl a) (inr ¬a') = rec-𝕆 (¬a' a)
  LEM-isProp isPropA (inr ¬a) (inl a') = rec-𝕆 (¬a a')
  LEM-isProp isPropA (inr ¬a) (inr ¬a') = ap inr (isProp¬A ¬a ¬a')

-- Ex 3.7
  ex37 : ∀ {ℓ} {A B : Set ℓ} → isProp A → isProp B → ¬ (A × B)
    → isProp (A ⊎ B)
  ex37 isPropA isPropB ¬A×B (inl a) (inl a') = ap inl (isPropA a a')
  ex37 isPropA isPropB ¬A×B (inl a) (inr b)  = rec-𝕆 (¬A×B (a , b))
  ex37 isPropA isPropB ¬A×B (inr b) (inl a)  = rec-𝕆 (¬A×B (a , b))
  ex37 isPropA isPropB ¬A×B (inr b) (inr b') = ap inr (isPropB b b')

-- Ex 3.8

module Ex38  (e : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Set ℓ)
            (iseq : isequiv-conditions e) where
  ∥quiv∥-to-e : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → ∥ quasiinv f ∥ → e f
  ∥quiv∥-to-e f quivf = ∥∥-rec (isequiv-conditions.from-quiv iseq f) (isequiv-conditions.e-isProp iseq f) quivf

  e-to-∥quiv∥ : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → e f → ∥ quasiinv f ∥
  e-to-∥quiv∥ f ef = ⟦ isequiv-conditions.to-quiv iseq f ef ⟧

  ∥quiv∥-to-e∘e-to-∥quiv∥ : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → (∥quiv∥-to-e f) ∘ (e-to-∥quiv∥ f) == id
  ∥quiv∥-to-e∘e-to-∥quiv∥ f x = isequiv-conditions.e-isProp iseq f _ _

  e-to-∥quiv∥∘∥quiv∥-to-e : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → (e-to-∥quiv∥ f) ∘ (∥quiv∥-to-e f) == id
  e-to-∥quiv∥∘∥quiv∥-to-e f x = ∥∥-prop _ _

  quasiinv≅iseq : ∀ {ℓ} {A B : Set ℓ} {f : A → B} → ∥ quasiinv f ∥ ≅ e f
  quasiinv≅iseq {f = f} = ∥quiv∥-to-e f , quasi-isequiv _ (record { g = e-to-∥quiv∥ f ;
                                                                   g∘f = e-to-∥quiv∥∘∥quiv∥-to-e f ;
                                                                   f∘g = ∥quiv∥-to-e∘e-to-∥quiv∥ f })

-- Ex 3.9

module Ex39 {ℓ} (univalence : isUnivalent ℓ)
                (funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {f g : ∀ a → P a}
                                                       → (∀ (x : A) → f x ≡ g x) → f ≡ g) where

  LEM-Prop : LEM ℓ → hProp ℓ ≅ (Lift (lsuc ℓ) 𝟚)
  LEM-Prop LEM = f , (quasi-isequiv _ (record { g = g ; g∘f = g∘f ; f∘g = f∘g }))
    where
      true-or-false : (A : Set ℓ) → isProp A → 𝟚
      true-or-false A isPropA with (LEM A isPropA) 
      true-or-false A isPropA | inl a  = inr tt
      true-or-false A isPropA | inr ¬a = inl tt

      f : hProp ℓ → (Lift (lsuc ℓ) 𝟚)
      f (A , isPropA) = lift (true-or-false A isPropA)

      g : (Lift (lsuc ℓ) 𝟚) → hProp ℓ
      g (lift (inl tt)) = 𝕆ₚ
      g (lift (inr tt)) = 𝟙ₚ

      g∘f : g ∘ f == id
      g∘f (A , isPropA) with (LEM A isPropA)
      g∘f (A , isPropA) | inl a  = isequiv.left (proj₂ Σ-paths) ((~ inhab-prop≡𝟙 univalence isPropA a) , isProp-isProp funext _ _)
      g∘f (A , isPropA) | inr ¬a = isequiv.left (proj₂ Σ-paths) ((~ inhab-¬-prop≡𝕆 univalence isPropA ¬a) , (isProp-isProp funext _ _))

      f∘g : f ∘ g == id
      f∘g (lift (inl tt)) with (LEM (Lift ℓ 𝕆) isProp-𝕆)
      f∘g (lift (inl tt)) | inr x = refl
      f∘g (lift (inr tt)) with (LEM (Lift ℓ 𝟙) isProp-𝟙)
      f∘g (lift (inr tt)) | inl (lift tt) = refl
      f∘g (lift (inr tt)) | inr x = rec-𝕆 (lift ( unlift (x (lift tt)))) 
      
-- Ex 3.15

module Ex315 {ℓ} (prop-resize : PropositionalResizing ℓ) where
  private
    prop-resize-quiv : quasiinv (LiftP {ℓ = ℓ})
    prop-resize-quiv = isequiv-quiv _ prop-resize

  PropTr : Set (lsuc ℓ) → Set (lsuc ℓ)
  PropTr A = ∀ (P : hProp ℓ) → (A → (proj₁ P)) → (proj₁ P)

  squash : ∀ {A : Set (lsuc ℓ)} → A → PropTr A
  squash a = λ { (P , isPropP) f → f a }
 
  PropTr-univ-lift : ∀ {A B : Set (lsuc ℓ)} (f : A → B)
    → isProp B → PropTr A → B
  PropTr-univ-lift {B = B} f isPropB x with (quasiinv.g prop-resize-quiv (B , isPropB))
  PropTr-univ-lift {B = B} f isPropB x | lift (B' , isPropB') = transp {P = id} (ap proj₁ (quasiinv.f∘g prop-resize-quiv (B , isPropB)))
                                                                                {!!}
    {-where
      proj-eq : ∀ (B : Set (lsuc ℓ)) (isPropB : isProp B) →
        proj₁ ((LiftP ∘ quasiinv.g prop-resize-quiv) (B , isPropB)) ≡ Lift (lsuc ℓ)
                                                                           (proj₁ {!quasiinv.g prop-resize-quiv (B , isPropB)!} ) --(quasiinv.g prop-resize-quiv (B , isPropB)) )
      proj-eq = {!refl!}-}
  

-- Ex 3.21

module Ex321 {ℓ} (extensionality : funext-axiom {ℓ₁ = ℓ} {ℓ₂ = ℓ}) where
  private
    funext-quasi : ∀ {A : Set ℓ} {P : A → Set ℓ} {f g : ∀ a → P a} → quasiinv (happly {f = f} {g = g}) 
    funext-quasi {A} {P} {f} {g} = isequiv-quiv _ (extensionality A P f g)

    funext : ∀ {A : Set ℓ} {P : A → Set ℓ} {f g : ∀ a → P a} → f == g → f ≡ g
    funext {A = A} {P = P} {f = f} {g = g} = quasiinv.g funext-quasi
  

  isPropP→P≅∥P∥ : ∀ {P : Set ℓ} → isProp P → (P ≅ ∥ P ∥)
  isPropP→P≅∥P∥ isPropP = ⟦_⟧ , (quasi-isequiv _ (record { g = λ x → ∥∥-rec id isPropP x ;
                                                          g∘f = λ x → refl ;
                                                          f∘g = λ x → ∥∥-ind {P = λ p → ⟦ ∥∥-rec id isPropP p ⟧ ≡ p}
                                                                              (λ a → refl)
                                                                              (λ p → ∥∥-prop)
                                                                              x }))

  P≅∥P∥→isPropP : ∀ {P : Set ℓ} → (P ≅ ∥ P ∥) → isProp P
  P≅∥P∥→isPropP (f , e) x y = (~ isequiv.right∘f e x) ∙ (ap (isequiv.right e) (∥∥-prop _ _) ∙ isequiv.right∘f e y)

  isPropP≅P≅∥P∥ : ∀ {P : Set ℓ} → isProp P ≅ (P ≅ ∥ P ∥)
  isPropP≅P≅∥P∥ {P = P} = isPropP→P≅∥P∥ ,
                 quasi-isequiv _ (record { g = P≅∥P∥→isPropP ;
                                           g∘f = λ x → isProp-isProp {ℓ = ℓ} funext _ _ ;
                                           f∘g = λ { (f , e) → isequiv.left (proj₂ Σ-paths) ((funext (λ x → ∥∥-prop _ _)) ,
                                                                                              isequiv-prop extensionality
                                                                                                           f
                                                                                                           _
                                                                                                           _) } })
   
                     
