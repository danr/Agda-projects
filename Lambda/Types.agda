module Lambda.Types where

open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality

data Ty : Set where
  _⟶_ : (α β : Ty) → Ty
  BoolTy NatTy : Ty

infixr 30 _⟶_

data Ctxt (A : Set) : Set where
  ε   : Ctxt A
  _◃_ : (x : A) (xs : Ctxt A) → Ctxt A

_◃◃_ : {A : Set} → Ctxt A → Ctxt A → Ctxt A
ε ◃◃ Γ = Γ
(x ◃ xs) ◃◃ Γ = x ◃ (xs ◃◃ Γ)

◃◃-assoc : {A : Set} (Γ₁ Γ₂ Γ₃ : Ctxt A)
         → ((Γ₁ ◃◃ Γ₂) ◃◃ Γ₃) ≡ (Γ₁ ◃◃ (Γ₂ ◃◃ Γ₃))
◃◃-assoc ε        Γ₂ Γ₃ = refl
◃◃-assoc (γ ◃ Γ₁) Γ₂ Γ₃ rewrite ◃◃-assoc Γ₁ Γ₂ Γ₃ = refl

-- ◃◃-ε : {A : Set} (Γ : Ctxt A) → Γ ◃◃ ε

infixr 20 _◃_ _◃◃_
infix 10 _∈_

data _∈_ {A : Set} (x : A) : Ctxt A → Set where
  z : ∀ {xs} → x ∈ x ◃ xs
  s : ∀ {y ys} (n : x ∈ ys) → x ∈ y ◃ ys

data Lam (Γ : Ctxt Ty) : Ty → Set where
  var : ∀ {α}   (n : α ∈ Γ) → Lam Γ α
  _∙_ : ∀ {α β} (e₁ : Lam Γ (α ⟶ β)) (e₂ : Lam Γ α) → Lam Γ β
  ƛ : ∀ {α β} (e : Lam (α ◃ Γ) β) → Lam Γ (α ⟶ β)
  natrec : ∀ {C} (p : Lam Γ C)
                 (h : Lam Γ (NatTy ⟶ C ⟶ C))
                 (n : Lam Γ NatTy)
               → Lam Γ C
  if : ∀ {C} (b : Lam Γ BoolTy) (t f : Lam Γ C) → Lam Γ C
  bool : (b : Bool) → Lam Γ BoolTy
  nat : (n : ℕ) → Lam Γ NatTy

--  natrec p h zero = p
--  natrec p h (succ n) = h n (natrec p h n)
