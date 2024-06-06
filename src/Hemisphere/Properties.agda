module Hemisphere.Properties where

open import Cubical.Data.Nat
  using (ℕ; zero; suc; ·-suc)
  renaming (_·_ to _*_; _+_ to _⊹_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.AbGroup.Base

open import Cubical.Algebra.AbGroup.Properties.Extra
open import Cubical.Foundations.Function.Extra
open import Hemisphere.Base

private
  variable
    ℓ : Level

-----------------------------------------------------------------------
-- Properties of hemispheres

module HemisphereTheory (H : Hemisphere ℓ) where
  open AbGroupTheory (Hemisphere→AbGroup H)
  open HemisphereStr (str H)

  ◠Id : ◠ 0h ≡ 0h
  ◠Id =
      ◠ 0h
    ≡⟨ sym (+IdL _) ⟩
      0h + ◠ 0h
    ≡⟨ cong (_+ ◠ 0h) (sym (+InvL _)) ⟩
      (- (◠ 0h) + ◠ 0h) + ◠ 0h
    ≡⟨ sym (+Assoc _ _ _) ⟩
      - (◠ 0h) + ◠ 0h + ◠ 0h
    ≡⟨ cong (- (◠ 0h) +_) (sym (◠+Hom _ _)) ⟩
      - (◠ 0h) + ◠ (0h + 0h)
    ≡⟨ cong (λ $ → - (◠ 0h) + ◠ $) (+IdL _) ⟩
      - (◠ 0h) + ◠ 0h
    ≡⟨ +InvL _ ⟩
      0h
    ∎

  ◠Inv : (x : ⟨ H ⟩) → ◠ (- x) ≡ - (◠ x)
  ◠Inv x =
      ◠ (- x)
    ≡⟨ sym (+IdL _) ⟩
      0h + ◠ (- x)
    ≡⟨ cong (_+ ◠ (- x)) (sym (+InvL _)) ⟩
      (- (◠ x) + ◠ x) + ◠ (- x)
    ≡⟨ sym (+Assoc _ _ _) ⟩
      - (◠ x) + ◠ x + ◠ (- x)
    ≡⟨ cong (- (◠ x) +_) (sym (◠+Hom _ _)) ⟩
      - (◠ x) + ◠ (x + (- x))
    ≡⟨ cong (λ $ → - (◠ x) + ◠ $) (+InvR _) ⟩
      - (◠ x) + ◠ 0h
    ≡⟨ cong (- (◠ x) +_) ◠Id ⟩
      - (◠ x) + 0h
    ≡⟨ +IdR _ ⟩
      - (◠ x)
    ∎

  ◠TwoTimes : (x : ⟨ H ⟩) → ◠ (x + x) ≡ x
  ◠TwoTimes x =
      ◠ (x + x)
    ≡⟨ ◠+Hom _ _ ⟩
      ◠ x + ◠ x
    ≡⟨ ◠Twice _ ⟩
      x
    ∎

  ◠ⁿ⁺¹TwoTimes : (n : ℕ) → (x : ⟨ H ⟩) → (◠_ ∘ⁿ suc n) (x + x) ≡ (◠_ ∘ⁿ n) x
  ◠ⁿ⁺¹TwoTimes zero x = ◠TwoTimes x
  ◠ⁿ⁺¹TwoTimes (suc n) x = cong ◠_ (◠ⁿ⁺¹TwoTimes n x)

  □◠ⁿSwap : (n : ℕ) → (x : ⟨ H ⟩) → □ (◠_ ∘ⁿ n) x ≡ (◠_ ∘ⁿ 2 * n) (□ x)
  □◠ⁿSwap zero x = refl
  □◠ⁿSwap (suc n) x =
      □ (◠_ ∘ⁿ suc n) x
    ≡⟨⟩
      □ (◠ (◠_ ∘ⁿ n) x)
    ≡⟨ □◠Swap _ ⟩
      ◠ (◠ (□ (◠_ ∘ⁿ n) x))
    ≡⟨ cong (λ $ → ◠ (◠ $)) (□◠ⁿSwap n x) ⟩
      ◠ (◠ (◠_ ∘ⁿ 2 * n) (□ x))
    ≡⟨⟩
      (◠_ ∘ⁿ 2 ⊹ 2 * n) (□ x)
    ≡⟨ cong (λ $ → (◠_ ∘ⁿ $) (□ x)) (sym (·-suc 2 n)) ⟩
      (◠_ ∘ⁿ 2 * suc n) (□ x)
    ∎

  ·Comm : (x y : ⟨ H ⟩) → x · y ≡ y · x
  ·Comm x y =
      x · y
    ≡⟨⟩
      ◠ (□ (x + y) - □ x - □ y)
    ≡⟨ cong (λ $ → ◠ (□ $ - □ x - □ y)) (+Comm x y) ⟩
      ◠ (□ (y + x) - □ x - □ y)
    ≡⟨ cong ◠_ (+-Swap _ _ _) ⟩
      ◠ (□ (y + x) - □ y - □ x)
    ≡⟨⟩
      y · x
    ∎

  ·IdL : (x : ⟨ H ⟩) → 0h · x ≡ 0h
  ·IdL x =
      0h · x
    ≡⟨⟩
      ◠ (□ (0h + x) - □ 0h - □ x)
    ≡⟨ cong (λ $ → ◠ (□ $ - □ 0h - □ x)) (+IdL x) ⟩
      ◠ (□ x - □ 0h - □ x)
    ≡⟨ cong (λ $ → ◠ (□ x - $ - □ x)) □Id ⟩
      ◠ (□ x - 0h - □ x)
    ≡⟨ cong (λ $ → ◠ ($ - □ x)) (+-IdR (□ x)) ⟩
      ◠ (□ x - □ x)
    ≡⟨ cong (◠_) (+-Self (□ x)) ⟩
      ◠ 0h
    ≡⟨ ◠Id ⟩
      0h
    ∎

  ·IdR : (x : ⟨ H ⟩) → x · 0h ≡ 0h
  ·IdR x =
      x · 0h
    ≡⟨ ·Comm _ _ ⟩
      0h · x
    ≡⟨ ·IdL _ ⟩
      0h
    ∎
