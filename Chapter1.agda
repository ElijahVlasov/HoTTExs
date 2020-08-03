{-# OPTIONS --without-K #-}

module Chapter1 where

open import prelude

iter : {C : Set} → C → (C → C) → ℕ → C
iter c₀ cₛ O = c₀
iter c₀ cₛ (succ n) = cₛ (iter c₀ cₛ n)

aux-suc : {C : Set} → (ℕ → C → C) → ℕ × C → ℕ × C
aux-suc cₛ p = succ (proj₁ p) , cₛ (proj₁ p) (proj₂ p)

rec : {C : Set} → C → (ℕ → C → C) → ℕ → C
rec {C} c₀ cₛ n = proj₂ (iter (O , c₀) (aux-suc cₛ) n)


rec-zero : ∀ {C : Set} {c₀ : C} {cₛ : ℕ → C → C}
  → rec c₀ cₛ O ≡ c₀
rec-zero = refl

rec-succ : ∀ {C : Set} (c₀ : C) (cₛ : ℕ → C → C) (n : ℕ)
  → rec c₀ cₛ (succ n) ≡ cₛ n (rec c₀ cₛ n)
rec-succ c₀ cₛ O = refl
rec-succ c₀ cₛ (succ n) = {!!} ∙ {!!} 


data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

recb : ∀ {ℓ} {C : Set ℓ} → C → C → 𝔹 → C
recb c₀ c₁ tt = c₁
recb c₀ c₁ ff = c₀


¬¬¬-¬ : ∀ {A : Set} →
  ¬ (¬ (¬ A)) → (¬ A)
¬¬¬-¬ x a = x λ f → f a -- x λ f → f a

k : ∀ {A B : Set} → A → B → A
k a b = a

A-¬¬A : ∀ {A : Set} → A → (¬ (¬ A))
A-¬¬A a f = f a


demorg : ∀ {A B : Set} → ((¬ A) ⊎ (¬ B)) → (¬ (A × B)) 
demorg p (x , y) = rec-⊎ (A-¬¬A x) (A-¬¬A y) p

¬¬LEM : ∀ {A : Set} → (¬ (¬ (A ⊎ (¬ A))))
¬¬LEM p = p (inr λ a → p (inl a))  -- p (inr λ a → p (inl a))

_+_ : ℕ → ℕ → ℕ
O + m = m
succ n + m = succ (n + m)

infix 30 _+_

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm O n = ~ n+O=n n
  where 
  n+O=n : ∀ n → n + O ≡ n
  n+O=n O = refl
  n+O=n (succ n) = ap succ (n+O=n n)
+-comm (succ m) n = ap succ (+-comm m n) ∙ (~ +succ=succ+ n m)
  where
  +succ=succ+ : ∀ n m → n + succ m ≡ succ (n + m)
  +succ=succ+ O m = refl
  +succ=succ+ (succ n) m = ap succ (+succ=succ+ n m)

