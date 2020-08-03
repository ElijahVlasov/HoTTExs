{-# OPTIONS --without-K #-}

module ApEquiv where

open import prelude

path-lemma : ∀ {ℓ} {A : Set ℓ} {x y z t : A} (p₁ : x ≡ y) (p₂ p₂′ : y ≡ z) (p₃ : z ≡ t)
  → p₂ ≡ p₂′ → ( p₁ ∙ (p₂ ∙ p₃)) ≡ ( p₁ ∙ (p₂′ ∙ p₃))
path-lemma p₁ p₂ .p₂ p₃ refl = refl

intricate-association : ∀ {ℓ} {A : Set ℓ} {x y z t u v : A} (p : x ≡ y) (q : y ≡ z) (s : z ≡ t)
  (h : t ≡ u) (k : u ≡ v)
  → (p ∙ (q ∙ (s ∙ (h ∙ k)))) ≡ p ∙ ((q ∙ (s ∙ h)) ∙ k)
intricate-association refl refl refl refl refl = refl

less-intricate-path-calculation : ∀ {ℓ} {A : Set ℓ} {x y z t : A} (s : x ≡ y) (p : x ≡ z) (q : z ≡ t)
  → p ≡ (s ∙ ((~ s) ∙ (p ∙ (q ∙ (~ q))))) 
less-intricate-path-calculation refl refl refl = refl

side-cancellation : ∀ {ℓ} {A : Set ℓ} → {x y z t : A} (s : x ≡ y) (p : y ≡ z) (q : t ≡ z)
  → ((~ s) ∙ ((s ∙ (p ∙ (~ q))) ∙ q)) ≡ p
side-cancellation refl refl refl = refl       

module ApAux {ℓ} {A B : Set ℓ} {f : A → B} (e : quasiinv f) {x y : A} (p : f x ≡ f y)  where
  equality₁ : p ≡ ((~ quasiinv.f∘g e (f x)) ∙ ((ap f (ap (quasiinv.g e) p)) ∙ quasiinv.f∘g e (f y)))
  equality₁ = (~ ap-id) ∙ (
              homotopy-naturality'' (quasiinv.f∘g e) p ∙
               (~ path-lemma (~ quasiinv.f∘g e (f x)) _ (ap (f ∘ quasiinv.g e) p) (quasiinv.f∘g e (f y)) (ap-func _ _ _)))

  equality₂ : ap (quasiinv.g e) p ≡ (quasiinv.g∘f e x ∙ ((~ quasiinv.g∘f e x) ∙
                                         (ap (quasiinv.g e) p ∙ (quasiinv.g∘f e y ∙ (~ quasiinv.g∘f e y)))))
  equality₂ = less-intricate-path-calculation (quasiinv.g∘f e x) (ap (quasiinv.g e) p) (quasiinv.g∘f e y)

  equality₃ : (quasiinv.g∘f e x ∙ ((~ quasiinv.g∘f e x) ∙
                                       (ap (quasiinv.g e) p ∙ (quasiinv.g∘f e y ∙ (~ quasiinv.g∘f e y)))))
                                         ≡ ap (quasiinv.g e) (ap f
                                                     ((~ quasiinv.g∘f e x) ∙ (ap (quasiinv.g e) p ∙ quasiinv.g∘f e y)))
  equality₃ = intricate-association (quasiinv.g∘f e x)
                                    ((~ quasiinv.g∘f e x))
                                    (ap (quasiinv.g e) p)
                                    (quasiinv.g∘f e y)
                                    (~ quasiinv.g∘f e y) ∙
              (path-lemma (quasiinv.g∘f e x)
                          ((~ quasiinv.g∘f e x) ∙ (ap (quasiinv.g e) p ∙ quasiinv.g∘f e y))
                          (ap id ((~ quasiinv.g∘f e x) ∙ (ap (quasiinv.g e) p ∙ quasiinv.g∘f e y)))
                          (~ quasiinv.g∘f e y)
                          (~ ap-id) ∙
              (~ (ap-func _ _ _ ∙ homotopy-naturality' (quasiinv.g∘f e) _)))

  equality₄ : ap f (ap (quasiinv.g e) (ap f ((~ quasiinv.g∘f e x) ∙ (ap (quasiinv.g e) p ∙ quasiinv.g∘f e y))))
                ≡ (quasiinv.f∘g e (f x) ∙ (ap f ((~ quasiinv.g∘f e x) ∙
                                                 (ap (quasiinv.g e) p ∙ quasiinv.g∘f e y)) ∙
                                                 (~ quasiinv.f∘g e (f y))))

  equality₄ = ap-func _ _ _ ∙ (
              homotopy-naturality' (quasiinv.f∘g e) _ ∙
              ap (_∙_ (quasiinv.f∘g e (f x))) (ap (_∙ _) ap-id ))

ap-equiv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (e : quasiinv f)
  → ∀ (x y : A) → isequiv (ap {x = x} {y = y} f)
ap-equiv {A = A} {B = B} f e x y = quasi-isequiv (record {
                                    g = λ q → (~ (quasiinv.g∘f e) x) ∙ (ap (quasiinv.g e) q ∙ (quasiinv.g∘f e) y) ; -- (~ (quasiinv.g∘f e) x) ∙ (ap (quasiinv.g e) q ∙ (quasiinv.g∘f e) y) ;
                                    g∘f = λ { refl → ap (_∙_ (~ quasiinv.g∘f e x)) idˡ ∙ invˡ } ;
                                    f∘g = λ p → ~ (ApAux.equality₁ e p ∙
                                                   (ap (λ z → (~ quasiinv.f∘g e (f x)) ∙ (z ∙  quasiinv.f∘g e (f y)))
                                                               (ap (ap f) (ApAux.equality₂ e p ∙
                                                                 ApAux.equality₃ e p) ∙
                                                                   ApAux.equality₄ e p ) ∙
                                                   side-cancellation _ _ _)) })
  
=-≅ : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (e : isequiv f)
  → ∀ (x y : A) → (x ≡ y ≅ f x ≡ f y)
=-≅ f e x y = (ap f) , (ap-equiv f (isequiv-quiv f e) x y)
