module Hemisphere.Base where

open import Agda.Primitive
open import Data.Nat hiding (_+_)

open import Hemisphere.Core public

private
  variable
    ℓ : Level
    H : Set ℓ

infixl 8 _∙_
_∙_ : {{_ : Hemisphere H}} → ℕ → H → H
zero ∙ x = 0h
suc zero ∙ x = x
2+ n ∙ x = suc n ∙ x + x

infixl 6 _-_
_-_ : {{_ : Hemisphere H}} → H → H → H
x - y = x + (- y)

infixl 7 _·_
_·_ : {{_ : Hemisphere H}} → H → H → H
x · y = ◠ (□ (x + y) - □ x - □ y)

