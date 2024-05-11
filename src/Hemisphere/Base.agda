module Hemisphere.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ : Level

record IsHemisphere {H : Type ℓ}
                    (0h : H) (_+_ : H → H → H) (-_ □_ ◠_ : H → H) : Type ℓ where

  constructor ishemisphere

  field
    isAbGroup : IsAbGroup 0h _+_ -_

    □Id : □ 0h ≡ 0h
    □◠Swap : (x : H) → □ (◠ x) ≡ ◠ (◠ (□ x))

    ◠Twice : (x : H) → (◠ x) + (◠ x) ≡ x
    ◠+Hom : (x y : H) → ◠ (x + y) ≡ (◠ x) + (◠ y)

  private
    module Ab = IsAbGroup isAbGroup

  infixl 7 _·_

  -- Multiplication
  _·_ : H → H → H
  x · y = ◠ (□ (x + y) Ab.- □ x Ab.- □ y)

  open IsAbGroup isAbGroup public

record HemisphereStr (H : Type ℓ) : Type ℓ where

  constructor hemispherestr

  field
    0h : H
    _+_ : H → H → H
    -_ : H → H
    □_ : H → H
    ◠_ : H → H

    isHemisphere : IsHemisphere 0h _+_ -_ □_ ◠_

  infixr 6 _+_
  infix  8 -_
  infix  8 □_
  infix  8 ◠_

  open IsHemisphere isHemisphere public

Hemisphere : ∀ ℓ → Type (ℓ-suc ℓ)
Hemisphere ℓ = TypeWithStr ℓ HemisphereStr

open AbGroupStr
open HemisphereStr
open IsHemisphere

HemisphereStr→AbGroupStr : {H : Type ℓ} → HemisphereStr H → AbGroupStr H
HemisphereStr→AbGroupStr Hs .0g = Hs .0h
HemisphereStr→AbGroupStr Hs ._+_ = Hs ._+_
HemisphereStr→AbGroupStr Hs .-_ = Hs .-_
HemisphereStr→AbGroupStr Hs .isAbGroup = Hs .isHemisphere .isAbGroup

Hemisphere→AbGroup : Hemisphere ℓ → AbGroup ℓ
fst (Hemisphere→AbGroup A) = fst A
snd (Hemisphere→AbGroup A) = HemisphereStr→AbGroupStr (snd A)
