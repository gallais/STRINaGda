module Acme.Data.Type where

open import Data.List
open import Data.Char
open import Data.Bool
open import Data.Product

String : Set
String = List Char

Type : Set
Type = String → Bool

infix 1 _ofType_
_ofType_ : String → Type → Set
a ofType A = T (A a)

valOfType : Type → Set
valOfType A = Σ[ str ∈ String ] (str ofType A)

_⟶_ : Type → Type → Set
A ⟶ B = valOfType A → valOfType B