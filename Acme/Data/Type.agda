module Acme.Data.Type where

open import Data.List
open import Data.Char
open import Data.Bool

Type : Set
Type = List Char → Bool

infix 1 _ofType_
_ofType_ : List Char → Type → Set
a ofType A = T (A a)