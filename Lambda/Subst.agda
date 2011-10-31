module Lambda.Subst where

open import Lambda.Types
-- open import Relation.Binary.PropositionalEquality
{-

weaken-∈ : ∀ {α : Ty} Γ₁ Γ₂ → α ∈ Γ₁ → α ∈ (Γ₁ ◃◃ Γ₂)
weaken-∈ {α} .(α ◃ xs) Γ₂ (z {xs}) = z
weaken-∈ .(y ◃ ys) Γ₂ (s {y} {ys} n) = s (weaken-∈ ys Γ₂ n)

weaken : ∀ {α} → ∀ Γ₁ Γ₂ → Lam Γ₁ α → Lam (Γ₁ ◃◃ Γ₂) α
weaken Γ₁ Γ₂ (var n) = var (weaken-∈ Γ₁ Γ₂ n)
weaken Γ₁ Γ₂ (e₁ ∙ e₂) = weaken Γ₁ Γ₂  e₁ ∙ weaken Γ₁ Γ₂  e₂
weaken Γ₁ Γ₂ (ƛ e) = ƛ (weaken _ Γ₂ e )
weaken Γ₁ Γ₂ (natrec p h n) = natrec (weaken Γ₁ Γ₂  p) (weaken Γ₁ Γ₂  h) (weaken Γ₁ Γ₂  n)
weaken Γ₁ Γ₂ (if b t f) = if (weaken Γ₁ Γ₂  b) (weaken Γ₁ Γ₂  t) (weaken Γ₁ Γ₂  f)
weaken Γ₁ Γ₂ (bool b) = bool b
weaken Γ₁ Γ₂ (nat n) = nat n


weaken⁺-∈ : ∀ {α : Ty} Γ₁ Γ₂ → α ∈ Γ₂ → α ∈ (Γ₁ ◃◃ Γ₂)
weaken⁺-∈ ε Γ₂ n = n
weaken⁺-∈ (x ◃ xs) Γ₂ n = s (weaken⁺-∈ xs Γ₂ n)

weaken⁺ : ∀ {α} → ∀ Γ₁ Γ₂ → Lam Γ₂ α → Lam (Γ₁ ◃◃ Γ₂) α
weaken⁺ Γ₁ Γ₂ (var n) = var (weaken⁺-∈ Γ₁ Γ₂ n)
weaken⁺ Γ₁ Γ₂ (e₁ ∙ e₂) = weaken⁺ Γ₁ Γ₂  e₁ ∙ weaken⁺ Γ₁ Γ₂  e₂
weaken⁺ .{α ⟶ β} Γ₁ Γ₂ (ƛ {α} {β} e) = ƛ {!  !}
weaken⁺ Γ₁ Γ₂ (natrec p h n) = natrec (weaken⁺ Γ₁ Γ₂  p) (weaken⁺ Γ₁ Γ₂  h) (weaken⁺ Γ₁ Γ₂  n)
weaken⁺ Γ₁ Γ₂ (if b t f) = if (weaken⁺ Γ₁ Γ₂  b) (weaken⁺ Γ₁ Γ₂  t) (weaken⁺ Γ₁ Γ₂  f)
weaken⁺ Γ₁ Γ₂ (bool b) = bool b
weaken⁺ Γ₁ Γ₂ (nat n) = nat n

-}

weak-∈ : ∀ {Γ Δ} {δ γ : Ty} → γ ∈ Γ ◃◃ Δ → γ ∈ Γ ◃◃ δ ◃ Δ
weak-∈ {ε} {ε} ()
weak-∈ {x ◃ xs} {ε} z = z
weak-∈ {x ◃ xs} {ε} (s n) = s (weak-∈ {xs} {ε} n)
weak-∈ {ε} {x ◃ xs} z = s z
weak-∈ {ε} {x ◃ xs} (s n) = s (weak-∈ {ε} {xs} n)
weak-∈ {x ◃ xs} {x' ◃ xs'} z = z
weak-∈ {x ◃ xs} {x' ◃ xs'} (s n) = s (weak-∈ {xs} {x' ◃ xs'} n)

weak : ∀ Δ Γ {δ γ} → Lam (Γ ◃◃ Δ) γ → Lam (Γ ◃◃ δ ◃ Δ) γ
weak Δ Γ (var n) = var (weak-∈ {Γ} {Δ} n)
weak Δ Γ (e₁ ∙ e₂) = weak Δ Γ e₁ ∙ weak Δ Γ e₂
weak Δ Γ {δ} {α ⟶ β} (ƛ e) = ƛ (weak Δ (α ◃ Γ) {δ} {β} e)
weak Δ Γ (natrec p h n) = natrec (weak Δ Γ p) (weak Δ Γ h) (weak Δ Γ n)
weak Δ Γ (if b t f) = if (weak Δ Γ b) (weak Δ Γ t) (weak Δ Γ f)
weak Δ Γ (bool b) = bool b
weak Δ Γ (nat n) = nat n

data _⇐_ (Δ : Ctxt Ty) : Ctxt Ty → Set where
  ε   : Δ ⇐ ε
  _◂_ : ∀ {γ Γ} → Lam Δ γ → Δ ⇐ Γ → Δ ⇐ (γ ◃ Γ)

wk : ∀ {Δ Γ δ} → Δ ⇐ Γ → (δ ◃ Δ) ⇐ Γ
wk     ε        = ε
wk {Δ} (y ◂ ys) = weak Δ ε y ◂ (wk ys)

id : ∀ {Γ} → Γ ⇐ Γ
id {ε} = ε
id {γ ◃ Γ} = (var z) ◂ wk id

subst : ∀ {α Γ Δ} → Lam Γ α → Δ ⇐ Γ → Lam Δ α
subst (var ()) ε
subst (var z) (y ◂ ys) = y
subst (var (s n)) (y ◂ ys) = subst (var n) ys
subst (e₁ ∙ e₂) k = (subst e₁ k) ∙ (subst e₂ k)
subst (ƛ e) k = ƛ (subst e (var z ◂ wk k))
subst (natrec p h n) k = natrec (subst p k) (subst h k) (subst n k)
subst (if b t f) k = if (subst b k) (subst t k) (subst f k)
subst (bool b) k = bool b
subst (nat n) k = nat n

app-sub : ∀ {α β Γ} → Lam (α ◃ Γ) β → Lam Γ α → Lam Γ β
app-sub t e = subst t (e ◂ id)
