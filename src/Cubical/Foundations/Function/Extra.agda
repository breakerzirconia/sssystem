module Cubical.Foundations.Function.Extra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

infix 5 _∘ⁿ_
_∘ⁿ_ : {A : Type ℓ} → (A → A) → ℕ → A → A
(f ∘ⁿ zero) x = x
(f ∘ⁿ suc n) x = f ((f ∘ⁿ n) x)
