module Acme.Data.Nat where

open import Data.List
open import Data.Char as Char
open import Data.Bool
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

`zero : List Char
`zero = 'Z' ∷ []

`succ : List Char → List Char
`succ n = 'S' ∷ n

Nat-ind :
  {P : Set} (pz : P) (ps : P → P)
  (cs : List Char) (prcs : cs ofType Nat) → P
Nat-ind {P} pz ps = go
  where
    go : (cs : List Char) (prcs : cs ofType Nat) → P
    go []       ()
    go (c ∷ cs) prcs =
      (dec′ (λ d → (pr : T $ dec d (const true) $ const $ dec(c Char.≟ 'S') (const $ Nat cs) (const false)) → P)
            (c Char.≟ 'Z') (λ d pr → pz) $ const $
            dec′ (λ d → T (dec d (const $ Nat cs) (const false)) → P)
            (c Char.≟ 'S') (const $ ps ∘ go cs) (const $ λ ())
      ) prcs

add : (m : List Char) (prm : m ofType Nat)
      (n : List Char) (prn : n ofType Nat) → List Char
add m prm n prn = Nat-ind n `succ m prm

`3+2 : List Char
`3+2 = add (`succ $ `succ $ `succ `zero) _ (`succ $ `succ `zero) _

