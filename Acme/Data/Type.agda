module Acme.Data.Type where

open import Data.List
open import Data.Char
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

String : Set
String = List Char

Type : Set
Type = String → Bool

infix 1 _ofType_
_ofType_ : String → Type → Set
a ofType A = T (A a)

T-unique : {a : Bool} (pr₁ pr₂ : T a) → pr₁ ≡ pr₂
T-unique {true}  pr₁ pr₂ = refl
T-unique {false} ()  pr₂

valOfType : Type → Set
valOfType A = Σ[ str ∈ String ] (str ofType A)

_⟶_ : Type → Type → Set
A ⟶ B = valOfType A → valOfType B

import Data.String as Str

infix 0 !_!
!_! : {A : Type} (a : Str.String) {pr : Str.toList a ofType A} →
      valOfType A
! a ! {pr} = Str.toList a , pr