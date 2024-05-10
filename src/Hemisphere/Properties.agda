module Hemisphere.Properties where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Syntax

open import Hemisphere.Base

private
  variable
    ℓ : Level
    H : Set ℓ

open Relation.Binary.PropositionalEquality.≡-Reasoning

-----------------------------------------------------------------------
-- Regular properties of abelian groups

-Id : {{_ : Hemisphere H}} → - 0h ≡ 0h
-Id =
    - 0h
  ≡⟨ sym (+IdL (- 0h)) ⟩
    0h + (- 0h)
  ≡⟨ +InvR 0h ⟩
    0h
  ∎

+-IdR : {{_ : Hemisphere H}} → (x : H) → x - 0h ≡ x
+-IdR x =
    x - 0h
  ≡⟨⟩
    x + (- 0h)
  ≡⟨ cong (λ $ → x + $) -Id ⟩
    x + 0h
  ≡⟨ +IdR x ⟩
    x
  ∎

+-InvR : {{_ : Hemisphere H}} → (x : H) → x - x ≡ 0h
+-InvR x =
    x - x
  ≡⟨⟩
    x + (- x)
  ≡⟨ +InvR x ⟩
    0h
  ∎

-Hom : {{_ : Hemisphere H}} → (x y : H) → (- x) + (- y) ≡ - (x + y)
-Hom x y =
    (- x) + (- y)
  ≡⟨ sym (+IdL _) ⟩
    0h + ((- x) + (- y))
  ≡⟨ cong (λ $ → $ + ((- x) + (- y))) (sym (+InvL _)) ⟩
    (- (y + x)) + (y + x) + ((- x) + (- y))
  ≡⟨ +Assoc _ _ _ ⟩
    (- (y + x)) + ((y + x) + ((- x) + (- y)))
  ≡⟨ cong (λ $ → (- (y + x)) + $) (+Assoc _ _ _) ⟩
    (- (y + x)) + (y + (x + ((- x) + (- y))))
  ≡⟨ cong (λ $ → (- (y + x)) + (y + $)) (sym (+Assoc _ _ _)) ⟩
    (- (y + x)) + (y + ((x + (- x)) + (- y)))
  ≡⟨ cong (λ $ → - (y + x) + (y + ($ + (- y)))) (+InvR _) ⟩
    (- (y + x)) + (y + (0h + (- y)))
  ≡⟨ cong (λ $ → (- (y + x)) + (y + $)) (+IdL _) ⟩
    (- (y + x)) + (y + (- y))
  ≡⟨ cong (λ $ → (- (y + x)) + $) (+InvR _) ⟩
    (- (y + x)) + 0h
  ≡⟨ +IdR _ ⟩
    - (y + x)
  ≡⟨ cong (-_) (+Comm _ _) ⟩
    - (x + y)
  ∎

+-NAssoc : {{_ : Hemisphere H}} → (x y z : H) → x - y - z ≡ x - (y + z)
+-NAssoc x y z =
    x - y - z
  ≡⟨⟩
    x + (- y) + (- z)
  ≡⟨ +Assoc _ _ _ ⟩
    x + ((- y) + (- z))
  ≡⟨ cong (x +_) (-Hom _ _) ⟩
    x + (- (y + z))
  ≡⟨⟩
    x - (y + z)
  ∎

+-Swap : {{_ : Hemisphere H}} → (x y z : H) → x - y - z ≡ x - z - y
+-Swap x y z =
    x - y - z
  ≡⟨ +-NAssoc _ _ _ ⟩
    x - (y + z)
  ≡⟨ cong (λ $ → x - $) (+Comm _ _) ⟩
    x - (z + y)
  ≡⟨ sym (+-NAssoc _ _ _) ⟩
    x - z - y
  ∎

-----------------------------------------------------------------------
-- Properties of the Sssystem

·IdL : {{_ : Hemisphere H}} → (x : H) → 0h · x ≡ 0h
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

·IdR : {{_ : Hemisphere H}} → (x : H) → x · 0h ≡ 0h
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

·OneR : {{_ : Hemisphere H}} → (x : H) → x · 1h ≡ x
·OneR x =
    x · 1h
  ≡⟨⟩
    ◠ (□ (x + 1h) - □ x - □ 1h)
  ≡⟨ {!!} ⟩
    x
  ∎
