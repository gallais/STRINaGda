module Acme.Data.Nat where

open import Data.List
open import Data.Char as Char
open import Data.Bool
open import Data.Product
open import Acme.Data.Type

open import Function
open import lib.Nullary

Nat : Type
Nat []       = false
Nat (c ∷ cs) =
    toBool (c Char.≟ 'Z')
  ∨ toBool (c Char.≟ 'S') ∧ Nat cs

`zero : valOfType Nat
`zero = ('Z' ∷ [] , _)

`succ : Nat ⟶ Nat
`succ (n , prn) = ('S' ∷ n , prn)

NatRec :
  {P : Type} (pz : valOfType P) (ps : P ⟶ P)
  (cs : valOfType Nat) → valOfType P
NatRec {P} pz ps = uncurry go
  where
    go : (cs : String) (prcs : cs ofType Nat) → valOfType P
    go []       ()
    go (c ∷ cs) prcs =
      (dec′ (λ d → (T $ toBool d ∨ toBool (c Char.≟ 'S') ∧ Nat cs) → valOfType P)
            (c Char.≟ 'Z') (λ d pr → pz) $ const $
       dec′ (λ d → (T $ toBool d ∧ Nat cs) → valOfType P)
            (c Char.≟ 'S') (const $ ps ∘ go cs) (const $ λ ())
      ) prcs

add : valOfType Nat → Nat ⟶ Nat
add m = λ n → NatRec n `succ m

import Data.String as Str

`3+2 : valOfType Nat
`3+2 = add ! "SSSZ" ! ! "SSZ" !