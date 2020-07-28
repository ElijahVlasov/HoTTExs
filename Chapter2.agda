module Chapter2 where
 
open import prelude
open import Sigma
open import FunExt
open import Equivalences

module Exercise1and2 {ℓ : Level} {A : Set ℓ} where

  _∙ˡ_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  p ∙ˡ refl = p

  infix 30 _∙ˡ_

  _∙ʳ_ : {x y z : A} →  x ≡ y → y ≡ z → x ≡ z
  refl ∙ʳ q = q

  infix 30 _∙ʳ_

  _∙₁_ : ∀ {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → p ∙ q ≡ p ∙ˡ q
  refl ∙₁ refl = refl

  _∙₂_ : ∀ {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → p ∙ˡ q ≡ p ∙ʳ q
  refl ∙₂ refl = refl

  _∙₃_ : ∀ {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → p ∙ q ≡ p ∙ʳ q
  refl ∙₃ refl = refl

  ∙-△ : ∀ {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → (p ∙₁ q) ∙ (p ∙₂ q) ≡ (p ∙₃ q)
  ∙-△ refl refl = refl

module Excercise3 where

  _∙'_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  p ∙' q = transp q p
 
  _∙₄_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → (p ∙ q) ≡ (p ∙' q)
  refl ∙₄ refl = refl

module Excercise4 where
  --higher-path {ℓ} {A : Set ℓ} (n : ℕ) : Set ℓ
  --higher-path n
    

module Excercise5 {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} (p : x ≡ y) (f : A → B)  where

  f236 : (f x ≡ f y) → ((transp p (f x)) ≡ f y)
  f236 q = transportconst p (f x) ∙ q

  f237 : ((transp p (f x)) ≡ f y) → (f x ≡ f y)
  f237 q = (~ transportconst p (f x)) ∙ q

  f236-f237-quasiinv : quasiinv f236
  f236-f237-quasiinv = record {
    g = f237 ;
    g∘f = λ ι → assoc ∙ ((ap (λ θ → θ ∙ ι) invˡ) ∙ idˡ) ;
    f∘g = λ ι → assoc ∙ ((ap (λ θ → θ ∙ ι) invʳ) ∙ idˡ) }

-- ((~ transportconst p (f x)) ∙ transportconst p (f x))

module Excercise6 {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) where
  precomp-quasiinv : ∀ z → quasiinv (λ (q : y ≡ z)  → p ∙ q)
  precomp-quasiinv z = record {
    g = λ q → (~ p) ∙ q ;
    g∘f = λ u → assoc ∙ ((ap (λ ι → ι ∙ u) invˡ) ∙ idˡ) ;
    f∘g = λ u → assoc ∙ ((ap (λ ι → ι ∙ u) invʳ) ∙ idˡ) }

module Excercise9 {ℓ} (A B : Set ℓ) (funext : ∀ {C D : Set ℓ } {f g : C → D} → (∀ x → f x ≡ g x) → f ≡ g) where

  canon-morph : ∀ (X : Set ℓ) → (A ⊎ B → X) → ((A → X) × (B → X))
  canon-morph X f = (f ∘ inl) , (f ∘ inr)

  ⊎-univprop : ∀ {X : Set ℓ} → quasiinv (canon-morph X)
  ⊎-univprop = record {
    g = λ { (a , b) (inl x) → a x ;
            (a , b) (inr x) → b x} ;
    g∘f = λ { x → funext λ { (inl x) → refl ;
                              (inr x) → refl } }  ;
    f∘g = λ { (x , y) → refl } }

module Excercise10 {ℓ} {A : Set ℓ} (B : A → Set ℓ) (C : Σ A (λ x → B x) → Set ℓ) where

  to : Σ A (λ x → Σ (B x) (λ y → C (x , y))) →
      Σ (Σ A (λ x → B x)) (λ p → C p)
  to (x , (y , z)) = (x , y) , z

  from : Σ (Σ A (λ x → B x)) (λ p → C p) →
     Σ A (λ x → Σ (B x) (λ y → C (x , y)))
  from ((x , y) , z) = x , (y , z)

  to∘from==id : to ∘ from == id
  to∘from==id ((x , y) , z) = refl

  from∘to==id : from ∘ to == id
  from∘to==id (x , (y , z)) = refl

  Σ-assoc : Σ A (λ x → Σ (B x) (λ y → C (x , y))) ≅ Σ (Σ A (λ x → B x)) (λ p → C p)
  Σ-assoc = to , quasi-isequiv _ (record { g = from ; g∘f = from∘to==id ; f∘g = to∘from==id })

module Excercise13 (extensionality : funext-axiom {ℓ₁ = lzero} {ℓ₂ = lzero} ) where
  private
    funext-quasi : ∀ {A : Set lzero} {P : A → Set lzero} {f g : ∀ a → P a} → quasiinv (happly {f = f} {g = g}) 
    funext-quasi {A} {P} {f} {g} = isequiv-quiv _ (extensionality A P f g)

    funext : ∀ {A : Set lzero} {P : A → Set lzero} {f g : ∀ a → P a} → f == g → f ≡ g
    funext {A = A} {P = P} {f = f} {g = g} = quasiinv.g funext-quasi
  neg : 𝟚 → 𝟚
  neg (inl x) = inr x
  neg (inr x) = inl x

  neg∘neg==id : neg ∘ neg == id
  neg∘neg==id (inl x) = refl
  neg∘neg==id (inr x) = refl

  enum : 𝟚 → 𝟚 ≅ 𝟚
  enum (inl tt) = id , quasi-isequiv _ (record { g = id ; g∘f = λ x → refl ; f∘g = λ x → refl })
  enum (inr tt) = neg , quasi-isequiv _ (record { g = neg ; g∘f = neg∘neg==id ; f∘g = neg∘neg==id })

  ev0 : 𝟚 ≅ 𝟚 → 𝟚
  ev0 (x , y) = x (inl tt)

  record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
    constructor [_]
    field eq : f x ≡ y

  inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
  inspect f x = [ refl ]

  enum∘ev0==id : enum ∘ ev0 == id
  enum∘ev0==id (f , e) with (f (inl tt)) | inspect f (inl tt)
  enum∘ev0==id (f , e) | inl tt | [ eq ] = isequiv.left (proj₂ Σ-paths) ((funext (λ { (inl tt) → ~ eq ;
                                                                                      (inr tt) → inrtt≡finrtt (~ eq)  })) ,
                                                                         isequiv-prop extensionality f _ _ )
    where
      inrtt≡finrtt : inl tt ≡ f (inl tt) → inr tt ≡ f (inr tt)
      inrtt≡finrtt eq with (𝟚-decidable (f (inr tt)))
      inrtt≡finrtt eq | inl x = rec-𝕆 (inltt≠inrtt ((~ isequiv.right∘f e (inl tt)) ∙ (ap (isequiv.right e) ((~ eq) ∙ (~ x))
                                                                        ∙ isequiv.right∘f e (inr tt))))
      inrtt≡finrtt eq | inr x = ~ x
  enum∘ev0==id (f , e) | inr tt | [ eq ] = isequiv.left (proj₂ Σ-paths) ((funext (λ { (inl tt) → ~ eq ;
                                                                                      (inr tt) → inltt≡finrtt (~ eq) })) ,
                                                                          isequiv-prop extensionality f _ _)
    where
      inltt≡finrtt : inr tt ≡ f (inl tt) → inl tt ≡ f (inr tt)
      inltt≡finrtt eq with (𝟚-decidable (f (inr tt)))
      inltt≡finrtt eq | inl x = ~ x
      inltt≡finrtt eq | inr x = rec-𝕆 (inltt≠inrtt ((~ isequiv.right∘f e (inl tt)) ∙ (ap (isequiv.right e) ((~ eq) ∙ (~ x))
                                                                                        ∙ isequiv.right∘f e (inr tt))))

  𝟚≅𝟚≅𝟚 : 𝟚 ≅ (𝟚 ≅ 𝟚)
  𝟚≅𝟚≅𝟚 = enum , quasi-isequiv _ (record { g = ev0 ;
                                            g∘f = λ { (inl tt) → refl ;
                                                      (inr tt) → refl } ;
                                            f∘g = enum∘ev0==id })

{-(λ { (inl x) → id , quasi-isequiv id (record { g = id ; g∘f = λ x → refl ; f∘g = λ x → refl }) ;
                (inr x) → neg , (quasi-isequiv neg (record { g = neg ; g∘f = neg∘neg≡id ; f∘g = neg∘neg≡id })) }) ,
           quasi-isequiv _ (record
                             { g = λ { (x , y) → x (inl tt) } ;
                               g∘f = λ { (inl tt) → refl ;
                                         (inr tt) → refl } ;
                               f∘g = λ { (x , y) → {!!} }
                                     } )-}
--𝟚≅𝟚≅𝟚 = (λ { (inl x) → id , quasi-isequiv id (record { g = id ; g∘f = λ x → refl ; f∘g = λ x → refl }) ;
--                (inr x) → neg , quasi-isequiv neg (record { g = neg ; g∘f = λ x → neg∘neg≡id x ; f∘g = λ x → neg∘neg≡id x }) }) ,
--                                             record { left = {!!} ; f∘left = {!!} ; right = {!!} ; right∘f = {!!} }
  
