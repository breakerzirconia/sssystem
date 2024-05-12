module Hemisphere.Unital.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Hemisphere.Base
open import Hemisphere.Properties
open import Hemisphere.Unital.Base
open import Cubical.Algebra.AbGroup.Properties.Extra

private
  variable
    ℓ : Level

-----------------------------------------------------------------------
-- Properties of unital hemispheres

module UnitalHemisphereTheory (U : UnitalHemisphere ℓ) where
  open AbGroupTheory (Hemisphere→AbGroup (UnitalHemisphere→Hemisphere U))
  open HemisphereTheory (UnitalHemisphere→Hemisphere U)
  open UnitalHemisphereStr (str U)

  ·UnityR : (x : ⟨ U ⟩) → x · 1h ≡ x
  ·UnityR x =
      x · 1h
    ≡⟨⟩
      ◠ (□ (x + 1h) - □ x - □ 1h)
    ≡⟨ cong (λ $ → ◠ (□ (x + 1h) - □ x - $)) □Unity ⟩
      ◠ (□ (x + 1h) - □ x - 1h)
    ≡⟨ cong (λ $ → ◠ ($ - □ x - 1h)) (□+Unity _) ⟩
      ◠ ((□ x + x + x + 1h) - □ x - 1h)
    ≡⟨ cong (λ $ → ◠ ($ - □ x - 1h)) (+Comm _ _) ⟩
      ◠ (((x + x + 1h) + □ x) - □ x - 1h)
    ≡⟨ cong (λ $ → ◠ ($ - 1h)) (sym (+Assoc _ _ _)) ⟩
      ◠ ((x + x + 1h) + (□ x - □ x) - 1h)
    ≡⟨ cong (λ $ → ◠ ((x + x + 1h) + $ - 1h)) (+-Self _) ⟩
      ◠ ((x + x + 1h) + 0h - 1h)
    ≡⟨ cong (λ $ → ◠ ($ - 1h)) (+IdR _) ⟩
      ◠ ((x + x + 1h) - 1h)
    ≡⟨ cong (λ $ → ◠ ($ - 1h)) (+Assoc _ _ _) ⟩
      ◠ (((x + x) + 1h) - 1h)
    ≡⟨ cong ◠_ (sym (+Assoc _ _ _)) ⟩
      ◠ ((x + x) + (1h - 1h))
    ≡⟨ cong (λ $ → ◠ ((x + x) + $)) (+-Self _) ⟩
      ◠ ((x + x) + 0h)
    ≡⟨ cong ◠_ (+IdR _) ⟩
      ◠ (x + x)
    ≡⟨ ◠Two _ ⟩
      x
    ∎

  ·UnityL : (x : ⟨ U ⟩) → 1h · x ≡ x
  ·UnityL x =
      1h · x
    ≡⟨⟩
      ◠ (□ (1h + x) - □ 1h - □ x)
    ≡⟨ cong (λ $ → ◠ (□ $ - □ 1h - □ x)) (+Comm _ _) ⟩
      ◠ (□ (x + 1h) - □ 1h - □ x)
    ≡⟨ cong (◠_) (+-Swap _ _ _) ⟩
      ◠ (□ (x + 1h) - □ x - □ 1h)
    ≡⟨⟩
      x · 1h
    ≡⟨ ·UnityR _ ⟩
      x
    ∎

  ·Half : (x : ⟨ U ⟩) → x · ◠ 1h ≡ ◠ x
  ·Half x = {!!}
