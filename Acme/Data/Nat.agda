module Acme.Data.Nat where

open import Data.List
open import Data.Char as Char
open import Data.Bool
open import Data.Product
open import Acme.Data.Type

open import Function
open import Relation.Nullary
open import lib.Nullary
open import Relation.Binary.PropositionalEquality

isNil? : ∀ {ℓᵃ} {A : Set ℓᵃ} (xs : List A) → Dec (xs ≡ [])
isNil? []      = yes refl
isNil? (_ ∷ _) = no (λ ())

Nat : Type
Nat []       = false
Nat (c ∷ cs) =
    toBool (c Char.≟ 'Z') ∧ toBool (isNil? cs)
  ∨ toBool (c Char.≟ 'S') ∧ Nat cs

`zero : valOfType Nat
`zero = ('Z' ∷ [] , _)

`succ : Nat ⟶ Nat
`succ (n , prn) = ('S' ∷ n , prn)

NatInduction : {P : valOfType Nat → Type}
  (pz : valOfType $ P `zero) (ps : ∀ n → P n ⟶ P (`succ n))
  (cs : valOfType Nat) → valOfType $ P cs
NatInduction {P} pz ps = uncurry go
  where
    go : (cs : String) (prcs : cs ofType Nat) → valOfType $ P $ cs , prcs
    go []       ()
    go (c ∷ cs) prcs =
      (dec′ (λ d → (T $ toBool d ∧ toBool (isNil? cs) ∨ toBool (c Char.≟ 'S') ∧ Nat cs) →
                    valOfType $ P $ c ∷ cs , prcs)
            (c Char.≟ 'Z') PZ $ const $
       dec′ (λ d → (T $ toBool d ∧ Nat cs) → valOfType $ P $ c ∷ cs , prcs)
            (c Char.≟ 'S') (λ p pcs → PS p $ go cs pcs) (const $ λ ())
      ) prcs
      where
        PS : {c : Char} {cs : List Char} {prccs : c ∷ cs ofType Nat} {prcs : cs ofType Nat}
             (eq : c ≡ 'S') (pr : valOfType $ P $ cs , prcs) → valOfType $ P $ c ∷ cs , prccs
        PS {cs = cs} {prccs} {prcs} refl val rewrite T-unique prccs prcs = ps (cs , prcs) val

        PZ : {c : Char} {cs : List Char} {prcs : c ∷ cs ofType Nat}
             (eq : c ≡ 'Z') (pr : T $ toBool (isNil? cs) ∨ toBool (c Char.≟ 'S') ∧ Nat cs) →
             valOfType $ P $ c ∷ cs , prcs
        PZ {cs = cs} refl pr =
          dec′ (λ d → (T $ toBool d ∨ false) → valOfType $ P $ 'Z' ∷ cs , _) (isNil? cs)
          (λ eq _ → PZ′ eq) (const $ λ ()) pr
          where
            PZ′ : {cs : List Char} {prcs : T (toBool (isNil? cs) ∨ false)}
                  (eq : cs ≡ []) → valOfType $ P $ 'Z' ∷ cs , prcs
            PZ′ refl = pz

add : valOfType Nat → Nat ⟶ Nat
add m = λ n → NatInduction n (const `succ) m

import Data.String as Str

`3+2 : valOfType Nat
`3+2 = add ! "SSSZ" ! ! "SSZ" !

