module Acme.Data.String where

open import Acme.Data.Type

RawString : Type
RawString = λ _ → true

AlphaString : Type
AlphaString = RawString
