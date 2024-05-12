module Cubical.Algebra.AbGroup.Properties.Extra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group

private
  variable
    ℓ : Level

module AbGroupTheory (A : AbGroup ℓ) where
  open GroupTheory (AbGroup→Group A)
  open AbGroupStr (str A)

  -Id : - 0g ≡ 0g
  -Id =
      - 0g
    ≡⟨ sym (+IdL (- 0g)) ⟩
      0g + (- 0g)
    ≡⟨ +InvR 0g ⟩
      0g
    ∎

  +-IdR : (x : ⟨ A ⟩) → x - 0g ≡ x
  +-IdR x =
      x - 0g
    ≡⟨⟩
      x + (- 0g)
    ≡⟨ cong (λ $ → x + $) -Id ⟩
      x + 0g
    ≡⟨ +IdR x ⟩
      x
    ∎

  +-Self : (x : ⟨ A ⟩) → x - x ≡ 0g
  +-Self x =
      x - x
    ≡⟨⟩
      x + (- x)
    ≡⟨ +InvR x ⟩
      0g
    ∎

  -Hom : (x y : ⟨ A ⟩) → (- x) + (- y) ≡ - (x + y)
  -Hom x y =
      (- x) + (- y)
    ≡⟨ sym (+IdL _) ⟩
      0g + (- x) + (- y)
    ≡⟨ cong (λ $ → $ + ((- x) + (- y))) (sym (+InvL _)) ⟩
      ((- (y + x)) + (y + x)) + (- x) + (- y)
    ≡⟨ sym (+Assoc _ _ _) ⟩
      (- (y + x)) + (y + x) + (- x) + (- y)
    ≡⟨ cong (λ $ → (- (y + x)) + $) (sym (+Assoc _ _ _)) ⟩
      (- (y + x)) + y + x + (- x) + (- y)
    ≡⟨ cong (λ $ → (- (y + x)) + (y + $)) (+Assoc _ _ _) ⟩
      (- (y + x)) + y + (x + (- x)) + (- y)
    ≡⟨ cong (λ $ → - (y + x) + (y + ($ + (- y)))) (+InvR _) ⟩
      (- (y + x)) + y + 0g + (- y)
    ≡⟨ cong (λ $ → (- (y + x)) + (y + $)) (+IdL _) ⟩
      (- (y + x)) + y + (- y)
    ≡⟨ cong (λ $ → (- (y + x)) + $) (+InvR _) ⟩
      (- (y + x)) + 0g
    ≡⟨ +IdR _ ⟩
      - (y + x)
    ≡⟨ cong (-_) (+Comm _ _) ⟩
      - (x + y)
    ∎

  +-NAssoc : (x y z : ⟨ A ⟩) → x - y - z ≡ x - (y + z)
  +-NAssoc x y z =
      x - y - z
    ≡⟨⟩
      (x + (- y)) + (- z)
    ≡⟨ sym (+Assoc _ _ _) ⟩
      x + (- y) + (- z)
    ≡⟨ cong (x +_) (-Hom _ _) ⟩
      x + (- (y + z))
    ≡⟨⟩
      x - (y + z)
    ∎

  +-Swap : (x y z : ⟨ A ⟩) → x - y - z ≡ x - z - y
  +-Swap x y z =
      x - y - z
    ≡⟨ +-NAssoc _ _ _ ⟩
      x - (y + z)
    ≡⟨ cong (λ $ → x - $) (+Comm _ _) ⟩
      x - (z + y)
    ≡⟨ sym (+-NAssoc _ _ _) ⟩
      x - z - y
    ∎
