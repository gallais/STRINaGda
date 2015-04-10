module Acme.Data.Nat where

open import Data.List
open import Data.Char as Char
open import Data.Bool
open import Data.Product
open import Acme.Data.Type

open import Data.Nat as ℕ hiding (eq?)
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import lib.Nullary

eq? : {A : Set} (d : (a b : A) → Dec (a ≡ b)) → (a b : A) → Bool
eq? d a b = dec (d a b) (const true) (const false)

Nat : Type
Nat []       = false
Nat (c ∷ cs) =
  dec (c Char.≟ 'Z') (const true) $ const $
  dec (c Char.≟ 'S') (const $ Nat cs) (const false)

`zero : valOfType Nat
`zero = ('Z' ∷ [] , _)

`succ : Nat ⟶ Nat
`succ (n , prn) = ('S' ∷ n , prn)

NatRec :  {P : Type} (pz : valOfType P) (ps : P ⟶ P)
  (cs : valOfType Nat) → valOfType P
NatRec {P} pz ps = uncurry go
  where
    go : (cs : String) (prcs : cs ofType Nat) → valOfType P
    go []       ()
    go (c ∷ cs) prcs =
      (dec′ (λ d → (pr : T $ dec d (const true) $ const $ dec(c Char.≟ 'S') (const $ Nat cs) (const false)) → valOfType P)
            (c Char.≟ 'Z') (λ d pr → pz) $ const $
            dec′ (λ d → T (dec d (const $ Nat cs) (const false)) → valOfType P)
            (c Char.≟ 'S') (const $ ps ∘ go cs) (const $ λ ())
      ) prcs

add : valOfType Nat → Nat ⟶ Nat
add m = λ n → NatRec n `succ m

import Data.String as Str

`3+2 : valOfType Nat
`3+2 = add (Str.toList "SSSZ" , _) (Str.toList "SSZ" , _)

