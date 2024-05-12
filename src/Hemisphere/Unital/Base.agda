module Hemisphere.Unital.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Hemisphere.Base

private
  variable
    ℓ : Level

record IsUnitalHemisphere {H : Type ℓ}
                          (0h 1h : H) (_+_ : H → H → H) (-_ □_ ◠_ : H → H) : Type ℓ where

  constructor isunitalhemisphere

  field
    isHemisphere : IsHemisphere 0h _+_ -_ □_ ◠_

    □Unity : □ 1h ≡ 1h
    □+Unity : (x : H) → □ (x + 1h) ≡ (□ x) + (x + (x + 1h))

  open IsHemisphere isHemisphere public

record UnitalHemisphereStr (H : Type ℓ) : Type ℓ where

  constructor unitalhemispherestr

  field
    0h : H
    1h : H
    _+_ : H → H → H
    -_ : H → H
    □_ : H → H
    ◠_ : H → H

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

UnitalHemisphereStr→HemisphereStr : {H : Type ℓ} → UnitalHemisphereStr H → HemisphereStr H
UnitalHemisphereStr→HemisphereStr Hs .0h = Hs .0h
UnitalHemisphereStr→HemisphereStr Hs ._+_ = Hs ._+_
UnitalHemisphereStr→HemisphereStr Hs .-_ = Hs .-_
UnitalHemisphereStr→HemisphereStr Hs .□_ = Hs .□_
UnitalHemisphereStr→HemisphereStr Hs .◠_ = Hs .◠_
UnitalHemisphereStr→HemisphereStr Hs .isHemisphere = Hs .isUnitalHemisphere .isHemisphere

UnitalHemisphere→Hemisphere : UnitalHemisphere ℓ → Hemisphere ℓ
fst (UnitalHemisphere→Hemisphere U) = fst U
snd (UnitalHemisphere→Hemisphere U) = UnitalHemisphereStr→HemisphereStr (snd U)
