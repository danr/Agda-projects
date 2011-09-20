--------------------------------------------------------------------------------
-- Some work based on a lecture notes in the course Advanced Functional
-- Programming by Nils Anders Danielsson:
-- http://www.cse.chalmers.se/edu/course/afp/lectures/lecture11/html/Proof-by-reflection.html
--
-- Todo:
--   ∙ Remove unnecessary parentheses
--------------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module AbelianGroupSolver {c ℓ} (Gr : AbelianGroup c ℓ) where
       
open AbelianGroup Gr renaming (Carrier to G)
import Algebra.Props.Group        as GP; open GP (group)
import Algebra.Props.AbelianGroup as AP; open AP (Gr)

open import Data.Vec     hiding (_⊛_ ; _++_ ; [_])
open import Data.Nat     renaming (_+_ to _ℕ+_)
open import Data.Integer renaming (suc to ℤsuc)
open import Data.Fin     hiding (_+_)
open import Data.Product using (proj₁ ; proj₂)

open import Function

open import Relation.Binary

private

  Group-Setoid : Setoid c ℓ
  Group-Setoid = record { Carrier = G ; _≈_ = _≈_
                        ; isEquivalence = isEquivalence }

  import Relation.Binary.EqReasoning as EqR; open EqR Group-Setoid

  ------------------------------------------------------------------------------
  -- Two lemmas used in this file

  lemma₁ : ∀ a b c d → ((a ∙ b) ∙ (c ∙ d)) ≈ ((a ∙ c) ∙ (b ∙ d))
  lemma₁ a b c d =   begin
      (a ∙ b) ∙ (c ∙ d)      ≈⟨ sym (assoc (a ∙ b) c d) ⟩
      ((a ∙ b) ∙ c) ∙ d      ≈⟨ assoc a b c ⟨ ∙-cong ⟩ refl ⟩
      (a ∙ (b ∙ c)) ∙ d      ≈⟨ (refl ⟨ ∙-cong ⟩ comm b c) ⟨ ∙-cong ⟩ refl ⟩
      (a ∙ (c ∙ b)) ∙ d      ≈⟨ sym (assoc a c b) ⟨ ∙-cong ⟩ refl {d} ⟩
      ((a ∙ c) ∙ b) ∙ d      ≈⟨ assoc (a ∙ c) b d ⟩
      (a ∙ c) ∙ (b ∙ d)
    ∎
  
  lemma₂ : ε ≈ (ε ⁻¹)
  lemma₂ = begin
      ε                ≈⟨ sym (proj₂ inverse ε) ⟩
      ε ∙ (ε ⁻¹)       ≈⟨ proj₁ identity (ε ⁻¹) ⟩
      ε ⁻¹
    ∎ 
  
  ------------------------------------------------------------------------------
  -- Exponentiation of elements in the group
  
  _^′_ : G → ℕ → G
  g ^′ zero  = ε
  g ^′ suc n = g ∙ (g ^′ n)
  
  _^_ : G → ℤ → G
  g ^ (+ n)    = g ^′ n
  g ^ -[1+ n ] = (g ^′ suc n) ⁻¹

  ------------------------------------------------------------------------------
  -- Properties of exponentiation
  
  ^′-add-law : (x y : ℕ) (g : G) → (g ^′ (x ℕ+ y)) ≈ ((g ^′ x) ∙ (g ^′ y))
  ^′-add-law zero    y g = sym (proj₁ identity (g ^′ y))
  ^′-add-law (suc x) y g = begin
      g ∙ (g ^′ (x ℕ+ y))             ≈⟨ refl {g} ⟨ ∙-cong ⟩ ^′-add-law x y g ⟩
      g ∙ ((g ^′ x) ∙ (g ^′ y))       ≈⟨ sym (assoc _ _ _) ⟩
      (g ∙ (g ^′ x)) ∙ (g ^′ y)
    ∎
  
  ^-sub-law : (x y : ℕ) (g : G) → (g ^ (x ⊖ y)) ≈ ((g ^′ x) ∙ ((g ^′ y) ⁻¹))
  ^-sub-law zero zero g = lemma₂ ⟨ trans ⟩ sym (proj₁ identity (ε ⁻¹))
  ^-sub-law zero (suc y) g = sym (proj₁ identity _)
  ^-sub-law (suc x) zero g = begin
       g ∙ (g ^′ x)           ≈⟨ sym (proj₂ identity _) ⟩
      (g ∙ (g ^′ x)) ∙ ε      ≈⟨ refl ⟨ ∙-cong ⟩ lemma₂ ⟩
      (g ∙ (g ^′ x)) ∙ (ε ⁻¹)
    ∎ 
  ^-sub-law (suc x) (suc y) g = begin
                         g ^ (x ⊖ y)              ≈⟨ sym (proj₁ identity _) ⟩
                   ε ∙  (g ^ (x ⊖ y))             ≈⟨ sym (proj₂ inverse g) ⟨ ∙-cong ⟩ ^-sub-law x y g  ⟩
      (g ∙ (g ⁻¹)  ) ∙ ((g ^′ x) ∙ ((g ^′ y) ⁻¹)) ≈⟨ lemma₁ _ _ _ _ ⟩
      (g ∙ (g ^′ x)) ∙ ((g ⁻¹) ∙ ((g ^′ y) ⁻¹))   ≈⟨ refl ⟨ ∙-cong ⟩ -‿∙-comm _ _ ⟩
      (g ∙ (g ^′ x)) ∙ ((g ∙ (g ^′ y)) ⁻¹)
    ∎
    
  ^-add-law : (x y : ℤ) (g : G) → (g ^ (x + y)) ≈ ((g ^ x) ∙ (g ^ y))
  ^-add-law -[1+ x ] -[1+ y ] g = begin
      (g      ∙ (g      ∙ (g ^′ (x ℕ+ y)))) ⁻¹            ≈⟨ sym (-‿∙-comm _ _) ⟩ 
      (g ⁻¹)  ∙ ((g     ∙ (g ^′ (x ℕ+ y))) ⁻¹)            ≈⟨ refl ⟨ ∙-cong ⟩ sym (-‿∙-comm _ _) ⟩
      (g ⁻¹)  ∙ ((g ⁻¹) ∙ ((g ^′ (x ℕ+ y)) ⁻¹))           ≈⟨ sym (assoc _ _ _) ⟩
      ((g ⁻¹) ∙ (g ⁻¹)) ∙ ((g ^′ (x ℕ+ y)) ⁻¹)            ≈⟨ refl ⟨ ∙-cong ⟩ ⁻¹-cong (^′-add-law x y g) ⟩
      ((g ⁻¹) ∙ (g ⁻¹)) ∙ (((g ^′ x)     ∙ (g ^′ y)) ⁻¹)  ≈⟨ refl ⟨ ∙-cong ⟩ sym (-‿∙-comm _ _) ⟩
      ((g ⁻¹) ∙ (g ⁻¹)) ∙ (((g ^′ x) ⁻¹) ∙ ((g ^′ y) ⁻¹)) ≈⟨ lemma₁ _ _ _ _ ⟩
      ((g ⁻¹) ∙ ((g ^′ x) ⁻¹)) ∙ ((g ⁻¹) ∙ ((g ^′ y) ⁻¹)) ≈⟨ (-‿∙-comm _ _) ⟨ ∙-cong ⟩ (-‿∙-comm _ _) ⟩
      ((g     ∙ (g ^′ x)) ⁻¹)  ∙ ((g     ∙ (g ^′ y)) ⁻¹)
    ∎
  ^-add-law -[1+ x ]   (+ y)  g = ^-sub-law y (suc x) g ⟨ trans ⟩ comm _ _
  ^-add-law   (+ x)  -[1+ y ] g = ^-sub-law x (suc y) g
  ^-add-law   (+ x)    (+ y)  g = ^′-add-law x y g
  
  ^-negate-law : (x : ℤ) (g : G) → (g ^ (- x)) ≈ ((g ^ x) ⁻¹)
  ^-negate-law -[1+ x ]  g = sym (⁻¹-involutive _)
  ^-negate-law (+ zero)  g = lemma₂
  ^-negate-law (+ suc x) g = refl

--------------------------------------------------------------------------------
-- Modelling an expression of groups

data Expr (n : ℕ) : Set where
  var   : (x : Fin n) → Expr n
  unit  : Expr n
  inv   : (e : Expr n) → Expr n
  _⊛_   : (e₁ e₂ : Expr n) → Expr n

private
  
  ------------------------------------------------------------------------------
  -- Evaluating an expression under a context
  
  Env : ℕ → Set c
  Env n = Vec G n
  
  ⟦_⟧ : ∀ {n} → Expr n → Env n → G
  ⟦ var x   ⟧ Γ = lookup x Γ
  ⟦ unit    ⟧ Γ = ε
  ⟦ inv e   ⟧ Γ = ⟦ e ⟧ Γ ⁻¹
  ⟦ e₁ ⊛ e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ∙ ⟦ e₂ ⟧ Γ
  
  ------------------------------------------------------------------------------
  -- A normal form, a linearisation so to say, of an expression
  
  NF : ℕ → Set
  NF n = Vec ℤ n
  
  ⟦_⟧′ : ∀ {n} → NF n → Env n → G
  ⟦ []       ⟧′ []      = ε
  ⟦ (x ∷ xs) ⟧′ (g ∷ Γ) = (g ^ x) ∙ ⟦ xs ⟧′ Γ
  
  ----------------------------------------------------------------------------
  -- Compute the normal form of an expression
  
  vecWith : {A : Set} {n : ℕ} → A → A → Fin n → Vec A n
  vecWith x y zero    = x ∷ replicate y
  vecWith x y (suc n) = y ∷ vecWith x y n
  
  normalise : ∀ {n} → Expr n → NF n
  normalise (var x)   = vecWith (+ 1) (+ 0) x
  normalise unit      = replicate (+ 0)
  normalise (inv e)   = map -_ (normalise e)
  normalise (e₁ ⊛ e₂) = zipWith _+_ (normalise e₁) (normalise e₂)
  
  ------------------------------------------------------------------------------
  -- zipWith _+_ of normal forms and _∙_ in the group is a homomorphism
  
  ∙-homomorphic : ∀ {n} (nf₁ nf₂ : NF n) (Γ : Env n)
                → ⟦ zipWith _+_ nf₁ nf₂ ⟧′ Γ ≈ (⟦ nf₁ ⟧′ Γ ∙ ⟦ nf₂ ⟧′ Γ)
  ∙-homomorphic []       []       []      = sym (proj₁ identity ε)
  ∙-homomorphic (x ∷ xs) (y ∷ ys) (g ∷ Γ) = begin
      (g ^ (x + y)) ∙ (⟦ zipWith _+_ xs ys ⟧′ Γ)       ≈⟨ ^-add-law x y g ⟨ ∙-cong ⟩ ∙-homomorphic xs ys Γ ⟩
      ((g ^ x) ∙ (g ^ y)) ∙ (⟦ xs ⟧′ Γ ∙ ⟦ ys ⟧′ Γ)    ≈⟨ lemma₁ _ _ _ _ ⟩
      (((g ^ x) ∙ ⟦ xs ⟧′ Γ) ∙ ((g ^ y) ∙ ⟦ ys ⟧′ Γ))
    ∎
                                                    
  ------------------------------------------------------------------------------
  -- Inverting the normal form and then evaluating, is the same as inverting after
  
  invertible : ∀ {n} (nf : NF n) (Γ : Env n) 
             → ⟦ map -_ nf ⟧′ Γ ≈ ⟦ nf ⟧′ Γ ⁻¹
  invertible []       []      = lemma₂ 
  invertible (x ∷ xs) (g ∷ Γ) = begin
      (g ^ (- x)) ∙ ⟦ map -_ xs ⟧′ Γ       ≈⟨ ^-negate-law x g ⟨ ∙-cong ⟩ invertible xs Γ ⟩
      ((g ^ x) ⁻¹) ∙ (⟦ xs ⟧′ Γ ⁻¹)        ≈⟨ -‿∙-comm _ _ ⟩
      ((g ^ x) ∙ ⟦ xs ⟧′ Γ) ⁻¹
    ∎
  
  ------------------------------------------------------------------------------
  -- The unit and the variables are also correct
    
  unit-correct : ∀ {n} (Γ : Env n) → ⟦ normalise unit ⟧′ Γ ≈ ε
  unit-correct []      = refl
  unit-correct (g ∷ Γ) = proj₁ identity _ ⟨ trans ⟩ (unit-correct Γ)
    
  var-correct : ∀ {n} (x : Fin n) (Γ : Env n) 
              → ⟦ normalise (var x) ⟧′ Γ ≈ ⟦ var x ⟧ Γ
  var-correct zero    (g ∷ Γ) = (proj₂ identity g ⟨ ∙-cong ⟩ unit-correct Γ) ⟨ trans ⟩ (proj₂ identity g)
  var-correct (suc x) (g ∷ Γ) = proj₁ identity _ ⟨ trans ⟩ var-correct x Γ
  
  ------------------------------------------------------------------------------
  -- Normalisation of an expression respects evaluation of the expression
  
  normalise-correct : ∀ {n} (e : Expr n) (Γ : Env n) 
                    → ⟦ normalise e ⟧′ Γ ≈ ⟦ e ⟧ Γ
  normalise-correct (var x)   Γ = var-correct x Γ 
  normalise-correct unit      Γ = unit-correct Γ 
  normalise-correct (inv e)   Γ = begin
      ⟦ normalise (inv e) ⟧′ Γ    ≈⟨ invertible (normalise e) Γ ⟩
      ⟦ normalise e       ⟧′ Γ ⁻¹ ≈⟨ ⁻¹-cong (normalise-correct e Γ) ⟩
      ⟦ e ⟧ Γ ⁻¹
    ∎ 
  normalise-correct (e₁ ⊛ e₂) Γ = begin
      ⟦ normalise (e₁ ⊛ e₂) ⟧′ Γ                ≈⟨ ∙-homomorphic (normalise e₁) (normalise e₂) Γ ⟩
      ⟦ normalise e₁ ⟧′ Γ ∙ ⟦ normalise e₂ ⟧′ Γ ≈⟨ normalise-correct e₁ Γ ⟨ ∙-cong ⟩ normalise-correct e₂ Γ ⟩
      ⟦ e₁ ⟧ Γ ∙ ⟦ e₂ ⟧ Γ
    ∎ 
                                  
--------------------------------------------------------------------------------
-- Using the fancy Reflection library

import Relation.Binary.Reflection as Reflection

open Reflection Group-Setoid var ⟦_⟧ (⟦_⟧′ ∘ normalise) normalise-correct
  public renaming (_⊜_ to _:=_)

--------------------------------------------------------------------------------
-- Some examples

private
  module Examples (x y z : G) where
    
    ex₁ : (x ∙ (y ∙ (z ∙ z))) ≈ (((x ∙ y) ∙ ε) ∙ (z ∙ z))
    ex₁ = solve₁ 3 (λ x y z → x ⊛ (y ⊛ (z ⊛ z))
                          := ((x ⊛ y) ⊛ unit) ⊛ (z ⊛ z)) x y z refl
  
    ex₂ : (x ∙ y) ⁻¹ ≈ (y ⁻¹ ∙ x ⁻¹)
    ex₂ = solve₁ 2 (λ x y → inv (x ⊛ y) := inv y ⊛ inv x) x y refl
  
    ex₃  : ε ⁻¹ ≈ ε
    ex₃ = solve₁ 0 (inv unit := unit) refl
  
    lemma₁-revisited : ∀ a b c d → ((a ∙ b) ∙ (c ∙ d)) ≈ ((a ∙ c) ∙ (b ∙ d))
    lemma₁-revisited = solve 4 (λ a b c d → ((a ⊛ b) ⊛ (c ⊛ d))
                                         := ((a ⊛ c) ⊛ (b ⊛ d))) refl