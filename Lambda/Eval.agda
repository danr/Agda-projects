module Lambda.Eval where

open import Lambda.Types
open import Data.Bool
open import Data.Nat

⟦_⟧ : Ty → Set
⟦ α ⟶ β ⟧ = ⟦ α ⟧ → ⟦ β ⟧
⟦ BoolTy ⟧ = Bool
⟦ NatTy ⟧ = ℕ

data Values : Ctxt Ty → Set where
  ε   : Values ε
  _◃_ : {Γ : Ctxt Ty} {α : Ty}
        (v : ⟦ α ⟧) (vs : Values Γ) → Values (α ◃ Γ)

natrec′ : {C : Set} → C → (ℕ → C → C) → ℕ → C
natrec′ p h zero = p
natrec′ p h (suc n) = h n (natrec′ p h n)

eval : {α : Ty} {Γ : Ctxt Ty} → Values Γ → Lam Γ α → ⟦ α ⟧
eval ε (var ())
eval (v ◃ vs) (var z) = v
eval (v ◃ vs) (var (s n)) = eval vs (var n)
eval V (e₁ ∙ e₂) = (eval V e₁) (eval V e₂)
eval V (ƛ e) = λ x → eval (x ◃ V) e
eval V (natrec p h n) = natrec′ (eval V p) (eval V h) (eval V n)
eval V (if b t f) = if (eval V b) then (eval V t) else (eval V f)
eval V (bool b) = b
eval V (nat n) = n