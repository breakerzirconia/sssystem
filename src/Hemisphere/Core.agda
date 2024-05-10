module Hemisphere.Core where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ : Level

-- record IsHemisphere {H : Set ℓ}
--                     (_+_ : H → H → H) (0h : H) (-_ : H → H)
--                     (1h : H) (□_ : H → H) (◠_ : H → H) : Set ℓ where

--   constructor ishemisphere

--   field
--     +Assoc : (x y z : H) → (x + y) + z ≡ x + (y + z)

--     +IdL : (x : H) → 0h + x ≡ x
--     +IdR : (x : H) → x + 0h ≡ x

--     +InvL : (x : H) → (- x) + x ≡ 0h
--     +InvR : (x : H) → x + (- x) ≡ 0h

--     +Comm : (x y : H) → x + y ≡ y + x

--     □Id : □ 0h ≡ 0h
--     □One : □ 1h ≡ 1h
--     □+One : (x : H) → □ (x + 1h) ≡ (((□ x) + x) + x) + 1h
--     □◠Swap : (x : H) → □ (◠ x) ≡ ◠ (◠ (□ x))

--     ◠Id : ◠ 0h ≡ 0h
--     ◠Twice : (x : H) → (◠ x) + (◠ x) ≡ x
--     ◠+Hom : (x y : H) → ◠ (x + y) ≡ (◠ x) + (◠ y)

-- open IsHemisphere {{...}} public

record Hemisphere (H : Set ℓ) : Set ℓ where

  constructor hemisphere

  field
    _+_ : H → H → H
    0h : H
    -_ : H → H

    1h : H
    □_ : H → H
    ◠_ : H → H

    +Assoc : (x y z : H) → (x + y) + z ≡ x + (y + z)
    +IdL : (x : H) → 0h + x ≡ x
    +IdR : (x : H) → x + 0h ≡ x
    +InvL : (x : H) → (- x) + x ≡ 0h
    +InvR : (x : H) → x + (- x) ≡ 0h
    +Comm : (x y : H) → x + y ≡ y + x

    □Id : □ 0h ≡ 0h
    □One : □ 1h ≡ 1h
    □+One : (x : H) → □ (x + 1h) ≡ (((□ x) + x) + x) + 1h
    □◠Swap : (x : H) → □ (◠ x) ≡ ◠ (◠ (□ x))

    ◠Id : ◠ 0h ≡ 0h
    ◠Twice : (x : H) → (◠ x) + (◠ x) ≡ x
    ◠+Hom : (x y : H) → ◠ (x + y) ≡ (◠ x) + (◠ y)

  infixl 6 _+_

open Hemisphere {{...}} public
