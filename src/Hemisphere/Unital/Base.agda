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

    □One : □ 1h ≡ 1h
    □+One : (x : H) → □ (x + 1h) ≡ (((□ x) + x) + x) + 1h

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

  infixl 6 _+_
  infix  8 -_
  infix  8 □_
  infix  8 ◠_

  open IsUnitalHemisphere isUnitalHemisphere public

UnitalHemisphere : ∀ ℓ → Type (ℓ-suc ℓ)
UnitalHemisphere ℓ = TypeWithStr ℓ UnitalHemisphereStr
