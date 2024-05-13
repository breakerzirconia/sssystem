module Hemisphere.Unital.Base where

open import Cubical.Data.Nat
  using (ℕ)
  renaming (_·_ to _*_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Foundations.Function.Extra
open import Hemisphere.Base

private
  variable
    ℓ : Level

record IsUnitalHemisphere {U : Type ℓ}
                          (0h 1h : U) (_+_ : U → U → U) (-_ □_ ◠_ : U → U) : Type ℓ where

  constructor isunitalhemisphere

  field
    isHemisphere : IsHemisphere 0h _+_ -_ □_ ◠_

    □Unity : □ 1h ≡ 1h
    □+◠ⁿUnity : (n : ℕ) → (x : U) → □ (x + (◠_ ∘ⁿ n) 1h) ≡ (□ x) + ((◠_ ∘ⁿ n) (x + x) + (◠_ ∘ⁿ (2 * n)) 1h)

  open IsHemisphere isHemisphere public

record UnitalHemisphereStr (U : Type ℓ) : Type ℓ where

  constructor unitalhemispherestr

  field
    0h : U
    1h : U
    _+_ : U → U → U
    -_ : U → U
    □_ : U → U
    ◠_ : U → U

    isUnitalHemisphere : IsUnitalHemisphere 0h 1h _+_ -_ □_ ◠_

  infixr 7 _+_
  infix  8 -_
  infix  8 □_
  infix  8 ◠_

  open IsUnitalHemisphere isUnitalHemisphere public

UnitalHemisphere : ∀ ℓ → Type (ℓ-suc ℓ)
UnitalHemisphere ℓ = TypeWithStr ℓ UnitalHemisphereStr

open HemisphereStr
open UnitalHemisphereStr
open IsUnitalHemisphere

UnitalHemisphereStr→HemisphereStr : {U : Type ℓ} → UnitalHemisphereStr U → HemisphereStr U
UnitalHemisphereStr→HemisphereStr U .0h = U .0h
UnitalHemisphereStr→HemisphereStr U ._+_ = U ._+_
UnitalHemisphereStr→HemisphereStr U .-_ = U .-_
UnitalHemisphereStr→HemisphereStr U .□_ = U .□_
UnitalHemisphereStr→HemisphereStr U .◠_ = U .◠_
UnitalHemisphereStr→HemisphereStr U .isHemisphere = U .isUnitalHemisphere .isHemisphere

UnitalHemisphere→Hemisphere : UnitalHemisphere ℓ → Hemisphere ℓ
fst (UnitalHemisphere→Hemisphere U) = fst U
snd (UnitalHemisphere→Hemisphere U) = UnitalHemisphereStr→HemisphereStr (snd U)
