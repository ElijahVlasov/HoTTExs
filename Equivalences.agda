{-# OPTIONS --without-K #-}

module Equivalences where

open import prelude
open import Sigma
open import FunExt
open import Props

record ishae {ℓ} {A B : Set ℓ} (f : A → B) : Set ℓ where
  field
    g : B → A
    η : g ∘ f == id
    ε : f ∘ g == id
    τ : ∀ (x : A) → ap f (η x) ≡ ε (f x)

isContrFibers : ∀ {ℓ₁} {A B : Set ℓ₁} → (A → B) → Set ℓ₁
isContrFibers {A = A} {B = B} f = ∀ (b : B) → isContr (fib f b)

linv' : ∀ {ℓ} {A B : Set ℓ} (f : A → B)
    → Set ℓ
linv' {A = A} {B = B} f = Σ (B → A) (λ r → r ∘ f == id)

rinv' : ∀ {ℓ} {A B : Set ℓ} (f : A → B)
    → Set ℓ
rinv' {A = A} {B = B} f = Σ (B → A) (λ s → f ∘ s == id)


linv'≅linv : ∀ {ℓ} {A B : Set ℓ} {f : A → B}
  → linv' f ≅ linv f
linv'≅linv {f = f} = (λ { (r , p) → record { r = r ; r∘f = p } }) ,
                     quasi-isequiv (record { g = λ { record { r = r ; r∘f = r∘f } → r , r∘f } ;
                                               g∘f = λ { (r , p) → refl } ;
                                               f∘g = λ { record { r = r ; r∘f = r∘f } → refl } })

rinv'≅rinv : ∀ {ℓ} {A B : Set ℓ} {f : A → B}
  → rinv' f ≅ rinv f
rinv'≅rinv {f = f} = (λ { (s , p) → record { s = s ; f∘s = p } }) ,
                     quasi-isequiv (record { g = λ { record { s = s ; f∘s = f∘s } → s , f∘s } ;
                                               g∘f = λ { (s , p) → refl } ;
                                               f∘g = λ { record { s = s ; f∘s = f∘s } → refl} })

qinv-ishae : ∀ {ℓ} {A B : Set ℓ} (f : A → B)
  → quasiinv f → ishae f
qinv-ishae {A = A} f record { g = g ;
                      g∘f = g∘f ;
                      f∘g = f∘g } = record { g = g ;
                                             η = g∘f ;
                                             ε = ((f∘g ✴ (f ∘ g))ˢ)  * ((f ☆ (g∘f ✴ g)) * f∘g) ;
                                             τ = λ (x : A) → ((~ idˡ) ∙ ap (_∙ ap f (g∘f x)) (~ invˡ {p = f∘g (f ((g ∘ f) x))}))
                                                                                ∙ ((~ assoc) ∙ ap (_∙_ (~ f∘g (f (g (f x)))))
                                                                                                     ((( (~ homotopy-naturality (f∘g ✴ f)
                                                                                                                                (g∘f x)) ∙
                                                                                                        ap (_∙ _) (~ ap-func f (f ∘ g) _)) ∙
                                                                                                       (~ ap (_∙ _) ap-func-calc))
                                                                                                     ∙ (~ ap (_∙ _) (ap (ap f)
                                                                                                          (homotopy-naturality-f==id
                                                                                                                                 g∘f
                                                                                                                                 x)))) ) }
  where
    ap-func-calc : ∀ {x : A} → (ap f (ap (λ z → (g ∘ f) z) (g∘f x)))
                          ≡ ap (f ∘ g) (ap f (g∘f x))
    ap-func-calc {x = x} = ap (ap f) (~ ap-func f g _) ∙ ap-func g f _


fib-paths : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (y : B) (u v : fib f y)
  → u ≡ v ≅ (Σ (proj₁ u ≡ proj₁ v) (λ γ → ap f γ ∙ (proj₂ v) ≡ proj₂ u))
fib-paths {A = A} {B = B} f y (x , p) (x' , p') = ≅-trans Σ-paths ((λ { (q , w) → q , ((~ fib-transp q p' ) ∙ transp-back q
                                                                                                                   p
                                                                                                                   p'
                                                                                                                   w) }) ,
                                                           quasi-isequiv (record { g = λ { (q , w) → q ,
                                                                                                       (transp-forth q
                                                                                                                     p
                                                                                                                     p'
                                                                                                                 (fib-transp q p'
                                                                                                                  ∙ w)) } ;
                                                                                     g∘f = λ { (refl , refl) →
                                                                                               isequiv.left (proj₂ (Σ-paths))
                                                                                                            (refl ,
                                                                                                            (~-∙ ∙
                                                                                                             (ap (_∙_ (~ ((~ (~ idˡ)) ∙
                                                                                                                        refl))) ~~-id
                                                                                                             ∙ (ap (_∙ idˡ) ~-∙ ∙
                                                                                                                ((~ assoc) ∙
                                                                                                                (idˡ ∙
                                                                                                                (ap (_∙ idˡ) ~~-id ∙
                                                                                                                invˡ))))))) } ;
                                                                                     f∘g = λ { (refl , refl) →
                                                                                               isequiv.left (proj₂ (Σ-paths))
                                                                                                            (refl ,
                                                                                                            (ap
                                                                                                              (_∙ (~ (~ ((~ idˡ) ∙ refl))))
                                                                                                              ~~-id
                                                                                                             ∙ (ap (_∙_ idˡ) ~~-id ∙
                                                                                                                (assoc ∙ (ap (_∙ refl) invʳ
                                                                                                                        ∙ refl))))) } }))
 where
   fib-transp : ∀ {x x' : A} (p : x ≡ x') (q : f x' ≡ y) → transp {P = λ x → f x ≡ y} (~ p) q ≡ (ap f p ∙ q)
   fib-transp refl q = ~ idˡ

hae-fib-contr : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (e : ishae f) (y : B)
  → isContr (fib f y)
hae-fib-contr f record { g = g ;
                         η = η ;
                         ε = ε ;
                         τ = τ } y = record { center = (g y) , (ε y) ;
                                              contr = λ { (x , p) → isequiv.left (proj₂ (fib-paths f y _ _) )
                                                                                  (((~ ap g p) ∙ η x) ,
                                                                                    (ap (_∙ _) ap-∙ ∙
                                                                                    (ap (_∙ p) (ap (_∙_ _) (τ x)) ∙
                                                                                    (ap (_∙ _) (ap (_∙ _) (ap (ap f) ap-~) ∙
                                                                                    (ap (_∙ _) (ap-func g f _) ∙ homotopy-naturality ε (~ p))) ∙
                                                                                    (ap (_∙ _) (ap (_∙_ _) ap-id) ∙
                                                                                    ((~ assoc) ∙ (ap (_∙_ (ε y)) invˡ ∙ idʳ))))))) } }

quiv-contractible-fibers : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (e : quasiinv f) (y : B)
  → isContr (fib f y)
quiv-contractible-fibers f e y = hae-fib-contr f (qinv-ishae f e) y

module isequivprop {ℓ} (extensionality : funext-axiom {ℓ₁ = ℓ} {ℓ₂ = ℓ}) where
  private
    funext-quasi : ∀ {A : Set ℓ} {P : A → Set ℓ} {f g : ∀ a → P a} → quasiinv (happly {f = f} {g = g}) 
    funext-quasi {A} {P} {f} {g} = isequiv-quiv _ (extensionality A P f g)

    funext : ∀ {A : Set ℓ} {P : A → Set ℓ} {f g : ∀ a → P a} → f == g → f ≡ g
    funext {A = A} {P = P} {f = f} {g = g} = quasiinv.g funext-quasi
    
  postcomp-quasi : ∀ {A B : Set ℓ} (f : A → B) (e : quasiinv f)
    → ∀ (C : Set ℓ) → quasiinv (λ (h : C → A) → f ∘ h)
  postcomp-quasi {A = A} {B = B} f record { g = g ;
                                           g∘f = g∘f ;
                                           f∘g = f∘g } C = record { g = λ (h : C → B) → g ∘ h ;
                                                                    g∘f = λ h → funext λ c → g∘f (h c) ;
                                                                    f∘g = λ h → funext λ c → f∘g (h c) }

  precomp-quasi : ∀ {A B : Set ℓ} (f : A → B) (e : quasiinv f)
    → ∀ (C : Set ℓ) → quasiinv (λ (h : B → C) → h ∘ f)
  precomp-quasi {A = A} {B = B} f record { g = g ;
                                            g∘f = g∘f ;
                                            f∘g = f∘g } C = record { g = λ h → h ∘ g ;
                                                                     g∘f = λ h → funext λ c → ap h (f∘g c) ;
                                                                     f∘g = λ h → funext λ c → ap h (g∘f c) }

  quasi-linv'-contr : ∀ {A B : Set ℓ} (f : A → B) (e : quasiinv f)
    → isContr (linv' f)
  quasi-linv'-contr {A = A} {B = B} f e = isContr-≅ (≅-sym linv'≅fib) (quiv-contractible-fibers (λ h → h ∘ f) (precomp-quasi f e A) id) 
    where
      linv'≅fib : linv' f ≅ fib (λ (g : B → A) → g ∘ f) id
      linv'≅fib = (λ { (r , p) → r , funext p }) , quasi-isequiv (record { g = λ { (r , p) → r , happly p } ;
                                                                            g∘f = λ { (r , p) → isequiv.left (proj₂ Σ-paths)
                                                                                                                (refl ,
                                                                                                                 quasiinv.f∘g
                                                                                                                   funext-quasi p
                                                                                                                   ) } ;
                                                                            f∘g = λ { (r , p) → isequiv.left (proj₂ Σ-paths)
                                                                                                                (refl ,
                                                                                                                (quasiinv.g∘f
                                                                                                                  funext-quasi p)) } })

  quasi-linv-contr : ∀ {A B : Set ℓ} (f : A → B) (e : quasiinv f)
    → isContr (linv f)
  quasi-linv-contr f e = isContr-≅ linv'≅linv (quasi-linv'-contr f e)

  quasi-rinv'-contr : ∀ {A B : Set ℓ} (f : A → B) (e : quasiinv f)
    → isContr (rinv' f)
  quasi-rinv'-contr {A = A} {B = B} f e = isContr-≅ (≅-sym rinv'≅fib) (quiv-contractible-fibers (λ h → f ∘ h) (postcomp-quasi f e B) id) 
    where
      rinv'≅fib : rinv' f ≅ fib (λ (g : B → A) → f ∘ g) id
      rinv'≅fib = (λ { (s , p) → s , (funext p) }) ,
                  quasi-isequiv (record { g = λ { (r , p) → r , (happly p) } ;
                                          g∘f = λ { (s , p) → isequiv.left (proj₂ Σ-paths) (refl , (quasiinv.f∘g
                                                                                                      funext-quasi p))} ;
                                          f∘g = λ { (s , p) → isequiv.left (proj₂ Σ-paths) (refl , (quasiinv.g∘f
                                                                                                                  funext-quasi p))} })

  quasi-rinv-contr : ∀ {A B : Set ℓ} (f : A → B) (e : quasiinv f)
    → isContr (rinv f)
  quasi-rinv-contr f e = isContr-≅ rinv'≅rinv (quasi-rinv'-contr f e)

   
  isequiv-prop : ∀ {A B : Set ℓ} → (f : A → B)
    → isProp (isequiv f)
  isequiv-prop f e = isContr-any-center (isContr-≅ (≅-sym (isequiv-linv-rinv f)) (isContr-× (quasi-linv-contr f (isequiv-quiv f e))
                                                                       (quasi-rinv-contr f (isequiv-quiv f e)))) e

open isequivprop public

   {-test : ∀ (q : f x ≡ y) → (~ (~ idˡ)) ∙
               transp-back refl (proj₂ (x , (ap f refl ∙ q))) q
               (transp-forth refl (proj₂ (x , (ap f refl ∙ q))) (proj₂ (x , q))z
               (fib-transp refl q ∙ refl)) ≡ refl
   test q = {!!}-}
   --test : ∀ () isequiv.left (proj₂ Σ-paths) (refl , ((~ idˡ) ∙ idˡ)) ≡ refl {a = (x , p)}

