module Hemisphere.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.AbGroup.Base

open import Hemisphere.Base
open import Cubical.Algebra.AbGroup.Properties.Extra

private
  variable
    ℓ : Level

-----------------------------------------------------------------------
-- Properties of Sssystem

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
    ≡⟨ cong (◠_) (+-InvR (□ x)) ⟩
      ◠ 0h
    ≡⟨ ◠Id ⟩
      0h
    ∎

  ·IdR : (x : ⟨ H ⟩) → x · 0h ≡ 0h
  ·IdR x =
      x · 0h
    ≡⟨⟩
      ◠ (□ (x + 0h) - □ x - □ 0h)
    ≡⟨ cong (λ $ → ◠ (□ $ - □ x - □ 0h)) (+Comm _ _) ⟩
      ◠ (□ (0h + x) - □ x - □ 0h)
    ≡⟨ cong (◠_) (+-Swap _ _ _) ⟩
      ◠ (□ (0h + x) - □ 0h - □ x)
    ≡⟨⟩
      0h · x
    ≡⟨ ·IdL _ ⟩
      0h
    ∎

-- ·OneR : {{_ : Hemisphere H}} → (x : H) → x · 1h ≡ x
-- ·OneR x =
--     x · 1h
--   ≡⟨⟩
--     ◠ (□ (x + 1h) - □ x - □ 1h)
--   ≡⟨ {!!} ⟩
--     x
--   ∎
