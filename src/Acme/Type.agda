module Acme.Type where

open import Agda.Builtin.Bool using (Bool; true; false) public
open import Agda.Builtin.Char using (Char)
  renaming (primCharEquality to _==_) public
open import Agda.Builtin.Equality using (_≡_; refl) public
open import Agda.Builtin.List using (List; []; _∷_) public
open import Agda.Builtin.String using (String)
  renaming (primStringToList to unpack) public
open import Agda.Builtin.Unit using (⊤; tt) public
open import Agda.Builtin.TrustMe using ()
  renaming (primTrustMe to trustMe) public


Type : Set
Type = List Char → Bool

data ⊥ : Set where

T : Bool → Set
T true = ⊤
T false = ⊥

_∈_ : List Char → Type → Set
x ∈ A = T (A x)

record Elt (A : Type) : Set where
  constructor [_]
  field value     : List Char
        @0 {{check}} : value ∈ A
open Elt public

infix 100 _∋_
_∋_ : (A : Type) (str : String) → {{unpack str ∈ A}} → Elt A
A ∋ str = record { value = unpack str }

infixr 3 _&&_
_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

infixr 2 _||_
_||_ : Bool → Bool → Bool
true || b = true
false || b = b

isNil : List Char → Bool
isNil [] = true
isNil _ = false

data Reflects (a : Char) : Char → Bool → Set where
  true  : Reflects a a true
  false : ∀ {b} → Reflects a b false

mkTrue : ∀ {a b} → a ≡ b → Reflects a b true
mkTrue refl = true

_≟_ : (a b : Char) → Reflects a b (a == b)
a ≟ b with a == b
... | false = false
... | true  = mkTrue trustMe

private

  variable
    A B : Set
    x y z : A

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq
