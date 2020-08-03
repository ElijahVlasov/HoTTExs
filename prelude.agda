{-# OPTIONS --without-K #-}

module prelude where

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_; Setω) 

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

infix 40 _∘_

id : ∀ {ℓ} {A : Set ℓ} → A → A
id a = a 

record Lift {ℓ₁} ℓ₂ (A : Set ℓ₁) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor lift
  field
    unlift : A

open Lift public

data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : ∀ {a} → a ≡ a

𝕁 : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} →
      (C : (x y : A) → x ≡ y → Set ℓ₂)
      (t : (a : A) → C a a refl) →
      ---------------------------------
      (x y : A) → (p : x ≡ y) → C x y p
𝕁 C t a a refl = t a

_∙_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

infix 30 _∙_

~_ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
~ refl = refl

~~-id : ∀ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y} → (~ (~ p)) ≡ p
~~-id {p = refl} = refl

~-∙ : ∀ {ℓ} {A : Set ℓ} {x y z : A} {p : x ≡ y} {q : y ≡ z}
  → (~ (p ∙ q)) ≡ (~ q) ∙ (~ p)
~-∙ {p = refl} {refl} = refl

assoc : ∀ {ℓ} {A : Set ℓ} {x y z u : A} {p : x ≡ y} {q : y ≡ z} {s : z ≡ u}
  → p ∙ (q ∙ s) ≡ (p ∙ q) ∙ s
assoc {p = refl}  {q = refl}  {s = refl} = refl

idˡ : ∀ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y}
  → refl ∙ p ≡ p
idˡ {p = refl} = refl

idʳ : ∀ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y}
  → p ∙ refl ≡ p
idʳ {p = refl} = refl

invˡ : ∀ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y}
  → (~ p) ∙ p ≡ refl
invˡ {p = refl} = refl

invʳ : ∀ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y}
  → p ∙ (~ p) ≡ refl
invʳ {p = refl} = refl

ap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} (f : A → B) (p : x ≡ y) → f x ≡ f y
ap f refl = refl

cancelʳ : ∀ {ℓ} {A : Set ℓ} {x y z : A} {p₁ p₂ : x ≡ y} {q : y ≡ z}
  → p₁ ∙ q ≡ p₂ ∙ q → p₁ ≡ p₂
cancelʳ {p₁ = p₁} {p₂ = p₂} {q = q} α = (~ idʳ) ∙ (ap (_∙_ p₁) (~ invʳ {p = q}) ∙ (
                                                   assoc ∙ (ap (_∙ (~ q)) α ∙ ((~ assoc) ∙ (ap (_∙_ p₂) invʳ ∙ idʳ)))))

cancelˡ : ∀ {ℓ} {A : Set ℓ} {x y z : A} {p₁ p₂ : x ≡ y} {q : z ≡ x}
  → q ∙ p₁ ≡ q ∙ p₂ → p₁ ≡ p₂
cancelˡ {p₁ = p₁} {p₂ = p₂} {q = q} α = (~ idˡ) ∙ (ap (_∙ p₁) (~ invˡ {p = q}) ∙ ((~ assoc) ∙ (ap (_∙_ (~ q)) α
                                                                                 ∙ (assoc ∙ (ap (_∙ p₂) invˡ ∙ idˡ)))))



ap-id : ∀ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y} → ap id p ≡ p
ap-id {p = refl} = refl

ap-∙ : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {x y z : A} {p : x ≡ y} {q : y ≡ z}
  → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ {p = refl} {refl} = refl

ap-~ : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {x y : A} {p : x ≡ y}
  → (~ ap f p) ≡ ap f (~ p)
ap-~ {p = refl} = refl

ap-func : ∀ {ℓ} {A B C : Set ℓ} {x y : A}  (f : A → B) (g : B → C) (p : x ≡ y)
  → ap g (ap f p) ≡ ap (g ∘ f) p
ap-func f g refl = refl

ap-const : ∀ {ℓ} {A : Set ℓ} {x y : A} {c : A} (p : x ≡ y)
  →  refl ≡ ap (λ _ → c) p
ap-const refl = refl

transp : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → {x y : A} → x ≡ y → P x → P y
transp refl u = u

transportconst : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A}
  (p : x ≡ y) (b : B) → transp p b ≡ b
transportconst refl b = refl

transp-p-~p : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → {x y : A} → (p : x ≡ y) {u : P y}
    → transp {P = P} p (transp {P = P} (~ p) u) ≡ u
transp-p-~p refl = refl

transp-back : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → {x y : A} → (p : x ≡ y) (u : P x) (v : P y)
    → transp p u ≡ v → transp (~ p) v ≡ u
transp-back refl u v = ~_

transp-forth : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → {x y : A} → (p : x ≡ y) (u : P x) (v : P y)
    → transp (~ p) v ≡ u → transp p u ≡ v
transp-forth refl u v = ~_

transp-back∘transp-forth : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → {x y : A} → {p : x ≡ y} {u : P x} {v : P y}
    → ∀ (γ : transp (~ p) v ≡ u) → transp-back p u v (transp-forth p u v γ) ≡ γ
transp-back∘transp-forth {p = refl} γ = ~~-id

transp-ap : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {P : B → Set ℓ₃} {x y : A}
  {p : x ≡ y} {f : A → B} {u : P (f x)} → (transp {P = λ x → P (f x)} p u) ≡ transp {P = P} (ap f p) u
transp-ap {p = refl} = refl

transp-∙ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {x y z : A}
  {p : x ≡ y} {q : y ≡ z} {u : P x} → (transp q (transp {P = P} p u)) ≡ (transp {P = P} (p ∙ q) u)
transp-∙ {p = refl} {refl} = refl

transp-equal-paths : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → {x y : A} → {p q : x ≡ y} → (α : p ≡ q) {u : P x}
    → transp {P = P} p u ≡ transp {P = P} q u
transp-equal-paths refl = refl

apd : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {x y : A} (f : ∀ x → P x)
  → (p : x ≡ y) → transp p (f x) ≡ f y
apd f refl = refl

data Σ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  _,_ : (x : A) (y : B x) → Σ A B

proj₁ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → Σ A B → A
proj₁ (x , y) = x

proj₂ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → (p : Σ A B) → B (proj₁ p)
proj₂ (x , y) = y

_×_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (λ _ → B)

data 𝕆 : Set where

rec-𝕆 : ∀ {ℓ} {A : Set ℓ} → Lift ℓ 𝕆 → A
rec-𝕆 ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ = ℓ} A = A → Lift ℓ 𝕆

data 𝟙 : Set where
  tt : 𝟙

data ℕ : Set where
  O : ℕ
  succ : ℕ → ℕ

data _⊎_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

rec-⊎ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (A → C) → (B → C) → (A ⊎ B → C)
rec-⊎ f g (inl x) = f x
rec-⊎ f g (inr x) = g x

𝟚 = 𝟙 ⊎ 𝟙

rec-𝟚 : ∀ {ℓ} {C : Set ℓ} → (c₀ c₁ : C) → 𝟚 → C
rec-𝟚 c₀ c₁ (inl x) = c₀
rec-𝟚 c₀ c₁ (inr x) = c₁

ind-𝟚 : ∀ {ℓ} {P : 𝟚 → Set ℓ}
  → P (inl tt) → P (inr tt) → ∀ (x : 𝟚) → P x
ind-𝟚 Pl Pr (inl tt) = Pl
ind-𝟚 Pl Pr (inr tt) = Pr

𝟚-decidable : ∀ (x : 𝟚) → (x ≡ inl tt) ⊎ (x ≡ inr tt)
𝟚-decidable (inl tt) = inl refl
𝟚-decidable (inr tt) = inr refl

inltt≠inrtt : ¬ (inl tt ≡ inr tt)
inltt≠inrtt eq = lift (transp {P = λ { (inl tt) → 𝟙 ;
                                       (inr tt) → 𝕆 }} eq tt)

_==_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → {P : A → Set ℓ₂} → (f g : ∀ x → P x) → Set (ℓ₁ ⊔ ℓ₂)
_==_ f g = ∀ x → f x ≡ g x

==-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → {P : A → Set ℓ₂} → {f : ∀ x → P x}
  → f == f
==-refl = λ x → refl

_ˢ : ∀ {ℓ} {A : Set ℓ} → {P : A → Set ℓ} → {f g : ∀ x → P x}
  → f == g → g == f
_ˢ h x = ~ h x

_*_ : ∀ {ℓ} {A : Set ℓ} → {P : A → Set ℓ} → {f g h : ∀ x → P x}
  → f == g → g == h → f == h
α * β = λ x → α x ∙ β x

ap-==ᵈ : ∀ {ℓ} {A : Set ℓ} → {P Q : A → Set ℓ} → {f g : ∀ x → P x}
  → (h : f == g) → (F : ∀ (x : A) → P x → Q x) → ((λ x → (F x) (f x)) == (λ x → (F x) (g x)))
ap-==ᵈ h F x = ap (F x) (h x)

_☆_ : ∀ {ℓ} {A B C : Set ℓ} → {f g : A → B}
  → (q : B → C) → (f == g) → (q ∘ f == q ∘ g)
_☆_ q h x = ap q (h x)

==-postᵈ : ∀ {ℓ} {A B : Set ℓ} → {P : A → Set ℓ} → {f g : ∀ x → P x}
  → (h : f == g) → (q : B → A) → ((λ x → f (q x)) == (λ x → g (q x)))
==-postᵈ h q b = h (q b)

_✴_ : ∀ {ℓ} {A B C : Set ℓ} → {f g : A → B}
  → (h : f == g) → (q : C → A) → f ∘ q == g ∘ q
_✴_ h q c = h (q c)


homotopy-naturality : ∀ {ℓ} {A B : Set ℓ} → {f g : A → B} → (h : f == g) → {x y : A} → (p : x ≡ y)
  → ap f p ∙ (h y) ≡ (h x) ∙ (ap g p)  
homotopy-naturality h refl = idˡ ∙ (~ idʳ)

{-homotopy-naturalityⁱ : ∀ {ℓ} {A B : Set ℓ} → {f g : A → B} → (h : f == g) → {x y : A} → (p : x ≡ y)
  → (h y) ∙ (~ ap f p) ≡ (~ ap g p) ∙ (h x)
homotopy-naturalityⁱ h p = ?-}

homotopy-naturality' : ∀ {ℓ} {A B : Set ℓ} → {f g : A → B} → (h : f == g) → {x y : A} → (p : x ≡ y)
  → ap f p ≡ (h x) ∙ ((ap g p) ∙ (~ (h y)))
homotopy-naturality' h {x = x} {y = y} refl = (~ invʳ) ∙ ap (_∙_ (h x)) (~ idˡ)

homotopy-naturality'' : ∀ {ℓ} {A B : Set ℓ} → {f g : A → B} → (h : f == g) → {x y : A} → (p : x ≡ y)
  → ap g p ≡ (~ (h x)) ∙ ((ap f p) ∙ (h y))
homotopy-naturality'' h {x = x} {y = y} refl = (~ invˡ) ∙ ap (_∙_ (~ h x)) (~ idˡ) 

homotopy-naturality-f==id : ∀ {ℓ} {A : Set ℓ} {f : A → A} (h : f == id)
  → ∀ (x : A) →  h (f x) ≡ ap f (h x)
homotopy-naturality-f==id {f = f} h x = (~ idʳ) ∙ (ap (_∙_ (h (f x))) (~ invʳ {p = h x}) ∙ (ap (_∙_ (h (f x))) (ap (_∙ (~ h x)) (~ ap-id))
                                                 ∙ (~ homotopy-naturality' h (h x))))

record quasiinv {ℓ} {A B : Set ℓ} (f : A → B) : Set ℓ where
  field
    g : B → A
    g∘f : g ∘ f == id
    f∘g : f ∘ g == id

record isequiv {ℓ} {A B : Set ℓ} (f : A → B) : Set ℓ where
  field
    left : B → A
    f∘left : f ∘ left == id
    right : B → A
    right∘f : right ∘ f == id

quasi-isequiv : ∀ {ℓ} {A B : Set ℓ} {f : A → B} → quasiinv f → isequiv f
quasi-isequiv record { g = g ; g∘f = g∘f ; f∘g = f∘g } = record { left = g ; f∘left = f∘g ; right = g ; right∘f = g∘f }

isequiv-quiv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → isequiv f → quasiinv f
isequiv-quiv f record { left = left ;
                        f∘left = f∘left ;
                        right = right ;
                        right∘f = right∘f } = record { g = left ;
                                                       g∘f = λ x
                                                         → γ (f x) ∙ right∘f x ;
                                                       f∘g = f∘left }
  where
    γ : left == right
    γ x = (~ right∘f (left x)) ∙ ap right (f∘left x)


_≅_ : ∀ {ℓ} (A B : Set ℓ) → Set ℓ
A ≅ B = Σ (A → B) (λ f → isequiv f)

id-isequiv : ∀ {ℓ} {A : Set ℓ} → isequiv (id {A = A})
id-isequiv = record { left = id ;
                      f∘left = λ x → refl ;
                      right = id ;
                      right∘f = λ x → refl }

≅-refl : ∀ {ℓ} {A : Set ℓ} → A ≅ A
≅-refl = id , id-isequiv

≅-sym : ∀ {ℓ} {A B : Set ℓ} → A ≅ B → B ≅ A
≅-sym (f , e)   with (isequiv-quiv f e)
≅-sym (f , e)   | record { g = g ;
                           g∘f = g∘f ;
                           f∘g = f∘g } = g , (quasi-isequiv (record { g = f ;
                                                                        g∘f = f∘g ;
                                                                        f∘g = g∘f }))

≅-trans : ∀ {ℓ} {A B C : Set ℓ} → A ≅ B → B ≅ C → A ≅ C
≅-trans (f₁ , e₁) (f₂ , e₂)   with (isequiv-quiv f₁ e₁) | (isequiv-quiv f₂ e₂)
≅-trans (f₁ , e₁) (f₂ , e₂) | record { g = g₁ ;
                                      g∘f = g₁∘f₁ ;
                                      f∘g = f₁∘g₁ } | record { g = g₂ ;
                                                              g∘f = g₂∘f₂ ;
                                                              f∘g = f₂∘g₂ } = f₂ ∘ f₁ , quasi-isequiv
                                                                                                      (record { g = g₁ ∘ g₂ ;
                                                                                                                g∘f = λ x →
                                                                                                                  ap g₁ (g₂∘f₂ (f₁ x)) ∙
                                                                                                                        g₁∘f₁ x ;
                                                                                                                f∘g = λ x →
                                                                                                                  ap f₂ (f₁∘g₁ (g₂ x)) ∙
                                                                                                                         f₂∘g₂ x })              

infix 10 _≅_

transp-equiv : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {x y : A}
  {p : x ≡ y} → isequiv (transp {P = P} p)
transp-equiv {p = refl} = id-isequiv

record linv  {ℓ} {A B : Set ℓ} (f : A → B) : Set ℓ where
  field
    r : B → A
    r∘f : r ∘ f == id
 
record rinv  {ℓ} {A B : Set ℓ} (f : A → B) : Set ℓ where
  field
    s : B → A
    f∘s : f ∘ s == id


isequiv-linv-rinv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) →
  isequiv f ≅ (linv f × rinv f)
isequiv-linv-rinv f = (λ e → (record { r = isequiv.right e ;
                                        r∘f = isequiv.right∘f e}) ,
                               record { s = isequiv.left e ;
                                        f∘s = isequiv.f∘left e }) ,
                      quasi-isequiv (record { g = λ { (linvf , rinvf) → record { left = rinv.s rinvf ;
                                                                                    f∘left = rinv.f∘s rinvf ;
                                                                                    right = linv.r linvf ;
                                                                                    right∘f = linv.r∘f linvf } } ;
                                                g∘f = λ x → refl ;
                                                f∘g = λ { (linvf , rinvf) → refl } })


record isContr {ℓ} (A : Set ℓ) : Set ℓ where
  field
    center : A
    contr : ∀ (x : A) → center ≡ x

isProp : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isProp A = ∀ (x y : A) → x ≡ y

isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ (x y : A) → isProp (x ≡ y)

isContr-isProp : ∀ {ℓ} {A : Set ℓ} → isContr A → isProp A
isContr-isProp record { center = center ;
                        contr = contr } x y = (~ contr x) ∙ contr y

isContr' : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isContr' A = Σ A (λ x → ∀ (y : A) → x ≡ y)

isContr≅isContr' : ∀ {ℓ} {A : Set ℓ} → isContr A ≅ isContr' A
isContr≅isContr' = (λ { record { center = center ;
                                 contr = contr } → center , contr }) ,
                   quasi-isequiv (record { g = λ { (x , y) → record { center = x ; contr = y } };
                                             g∘f = λ { record { center = center ; contr = contr } → refl } ;
                                             f∘g = λ { (x , y) → refl} })


record isequiv-conditions (e : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Set ℓ) : Setω where
  field
    to-quiv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → e f → quasiinv f
    from-quiv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → quasiinv f → e f
    e-isProp : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → isProp (e f) 

fib : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (b : B) → Set ℓ
fib {A = A} {B = B} f b = Σ A (λ a → f a ≡ b)
