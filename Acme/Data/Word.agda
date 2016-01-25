module Acme.Data.Word where

open import Acme.Data.Type
open import Acme.Data.Bit
open import Acme.Data.Nat

NonEmptyWord : Type → Type
NonEmptyWord ih []       = false
NonEmptyWord ih (c ∷ cs) = Bit (c ∷ []) ∧ ih cs

Word : ⟨ Nat ⟩ → Type
Word = NatInduction isEmpty $ λ _ → NonEmptyWord

private

  0asWord4 : ⟨ Word ! "SSSSZ" ! ⟩
  0asWord4 = ! "0000" !
