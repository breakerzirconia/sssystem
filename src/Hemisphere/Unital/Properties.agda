module Hemisphere.Unital.Properties where

open import Cubical.Data.Nat
  using (ℕ; zero; suc)
  renaming (_·_ to _*_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.AbGroup.Properties.Extra
open import Cubical.Foundations.Function.Extra
open import Hemisphere.Base
open import Hemisphere.Properties
open import Hemisphere.Unital.Base

private
  variable
    ℓ : Level

-----------------------------------------------------------------------
-- Properties of unital hemispheres

module UnitalHemisphereTheory (U : UnitalHemisphere ℓ) where
  open AbGroupTheory (Hemisphere→AbGroup (UnitalHemisphere→Hemisphere U))
  open HemisphereTheory (UnitalHemisphere→Hemisphere U)
  open UnitalHemisphereStr (str U)

  □+Unity : (x : ⟨ U ⟩) → □ (x + 1h) ≡ □ x + (x + x) + 1h
  □+Unity x = □+◠ⁿUnity 0 x

  □+◠ⁿ⁺¹Unity : (n : ℕ) → (x : ⟨ U ⟩) → □ (x + (◠_ ∘ⁿ suc n) 1h) ≡ □ x + (◠_ ∘ⁿ n) x + (◠_ ∘ⁿ 2 * suc n) 1h
  □+◠ⁿ⁺¹Unity n x =
      □ (x + (◠_ ∘ⁿ suc n) 1h)
    ≡⟨ □+◠ⁿUnity (suc n) x ⟩
      □ x + (◠_ ∘ⁿ suc n) (x + x) + (◠_ ∘ⁿ 2 * suc n) 1h
    ≡⟨ cong (λ $ → □ x + $ + (◠_ ∘ⁿ 2 * suc n) 1h) (◠ⁿ⁺¹TwoTimes n x) ⟩
      □ x + (◠_ ∘ⁿ n) x + (◠_ ∘ⁿ 2 * suc n) 1h
    ∎

  □+OneHalf : (x : ⟨ U ⟩) → □ (x + ◠ 1h) ≡ □ x + x + ◠ (◠ 1h)
  □+OneHalf x = □+◠ⁿ⁺¹Unity 0 x

  ·◠ⁿUnityR : (n : ℕ) → (x : ⟨ U ⟩) → x · (◠_ ∘ⁿ n) 1h ≡ (◠_ ∘ⁿ n) x
  ·◠ⁿUnityR n x =
      x · (◠_ ∘ⁿ n) 1h
    ≡⟨⟩
      ◠ (□ (x + (◠_ ∘ⁿ n) 1h) - □ x - □ ((◠_ ∘ⁿ n) 1h))
    ≡⟨ cong (λ $ → ◠ ($ - □ x - □ ((◠_ ∘ⁿ n) 1h))) (□+◠ⁿUnity n x) ⟩
      ◠ (□ x + (◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h - □ x - □ ((◠_ ∘ⁿ n) 1h))
    ≡⟨ cong (λ $ → ◠ (□ x + (◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h - □ x - $)) (□◠ⁿSwap n 1h)  ⟩
      ◠ (□ x + (◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h - □ x - (◠_ ∘ⁿ 2 * n) (□ 1h))
    ≡⟨ cong (λ $ → ◠ ($ - □ x - (◠_ ∘ⁿ 2 * n) (□ 1h))) (+Comm _ _) ⟩
      ◠ (((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h) + □ x - □ x - (◠_ ∘ⁿ 2 * n) (□ 1h))
    ≡⟨ cong (λ $ → ◠ ($ - (◠_ ∘ⁿ 2 * n) (□ 1h))) (sym (+Assoc _ _ _)) ⟩
      ◠ (((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h) + (□ x - □ x) - (◠_ ∘ⁿ 2 * n) (□ 1h))
    ≡⟨ cong (λ $ → ◠ (((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h) + $ - (◠_ ∘ⁿ 2 * n) (□ 1h))) (+-Self _) ⟩
      ◠ (((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h) + 0h - (◠_ ∘ⁿ 2 * n) (□ 1h))
    ≡⟨ cong (λ $ → ◠ ($ - (◠_ ∘ⁿ 2 * n) (□ 1h))) (+IdR _) ⟩
      ◠ ((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h - (◠_ ∘ⁿ 2 * n) (□ 1h))
    ≡⟨ cong (λ $ → ◠ ((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h - (◠_ ∘ⁿ 2 * n) $)) □Unity ⟩
      ◠ ((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ 2 * n) 1h - (◠_ ∘ⁿ 2 * n) 1h)
    ≡⟨ cong ◠_ (sym (+Assoc _ _ _)) ⟩
      ◠ ((◠_ ∘ⁿ n) (x + x) + ((◠_ ∘ⁿ 2 * n) 1h - (◠_ ∘ⁿ 2 * n) 1h))
    ≡⟨ cong (λ $ → ◠ ((◠_ ∘ⁿ n) (x + x) + $)) (+-Self _) ⟩
      ◠ ((◠_ ∘ⁿ n) (x + x) + 0h)
    ≡⟨ cong ◠_ (+IdR _) ⟩
      ◠ (◠_ ∘ⁿ n) (x + x)
    ≡⟨⟩
      (◠_ ∘ⁿ suc n) (x + x)
    ≡⟨ ◠ⁿ⁺¹TwoTimes n x ⟩
      (◠_ ∘ⁿ n) x
    ∎

  ·◠ⁿUnityL : (n : ℕ) → (x : ⟨ U ⟩) → (◠_ ∘ⁿ n) 1h · x ≡ (◠_ ∘ⁿ n) x
  ·◠ⁿUnityL n x =
      (◠_ ∘ⁿ n) 1h · x
    ≡⟨ ·Comm _ _ ⟩
      x · (◠_ ∘ⁿ n) 1h
    ≡⟨ ·◠ⁿUnityR n x ⟩
      (◠_ ∘ⁿ n) x
    ∎

  ·UnityR : (x : ⟨ U ⟩) → x · 1h ≡ x
  ·UnityR x = ·◠ⁿUnityR 0 x

  ·UnityL : (x : ⟨ U ⟩) → 1h · x ≡ x
  ·UnityL x = ·◠ⁿUnityL 0 x
