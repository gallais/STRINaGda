module Acme.Type where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
  renaming (primCharEquality to _==_)
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.String
  renaming (primStringToList to unpack)

Type : Set
Type = List Char → Bool

record ⊤ : Set where
  instance constructor tt
data ⊥ : Set where

T : Bool → Set
T true = ⊤
T false = ⊥

_∈_ : List Char → Type → Set
x ∈ A = T (A x)

record Elt (A : Type) : Set where
  constructor [_]
  field value     : List Char
        {{check}} : value ∈ A
open Elt

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

ℕ : Type
ℕ (c ∷ cs) = c == 'Z' && isNil cs
          || c == 'S' && ℕ cs
ℕ _ = false

zero = ℕ ∋ "Z"

suc : Elt ℕ → Elt ℕ
suc [ n ] = [ 'S' ∷ n ]

data Reflects (a : Char) : Char → Bool → Set where
  true  : Reflects a a true
  false : ∀ {b} → Reflects a b false

open import Agda.Builtin.Equality.Erase
  renaming (primEraseEquality to erase)

_≟_ : (a b : Char) → Reflects a b (a == b)
a ≟ b with a == b
... | false = false
... | true  = mkTrue trustMe where

  trustMe : a ≡ b
  trustMe = erase eq where postulate eq : a ≡ b

  mkTrue : ∀ {a b} → a ≡ b → Reflects a b true
  mkTrue refl = true

module _ (P : Elt ℕ → Set)
         (P0 : P zero)
         (PS : ∀ n → P n → P (suc n))
         where

  induction : ∀ n → P n
  induction [ ccs@(c ∷ cs) ] = checkZ (c ≟ 'Z') cs refl where

    checkS : ∀ {b} → Reflects c 'S' b → ∀ cs →
             {{T (b && ℕ cs)}} →
             ∀ {ccs} → c ∷ cs ≡ ccs .value → P ccs
    checkS true cs refl = PS [ cs ] (induction [ cs ])

    checkZ : ∀ {b} → Reflects c 'Z' b → ∀ cs →
             {{T (b && isNil cs || c == 'S' && ℕ cs)}} →
             ∀ {ccs} → c ∷ cs ≡ ccs .value → P ccs
    checkZ true  [] refl = P0
    checkZ false cs eq   = checkS (c ≟ 'S') cs eq

module _ (P : Elt ℕ → Set)
         (P0 : P zero)
         (PS : ∀ n → P n → P (suc n))
         where

  _ : induction P P0 PS zero ≡ P0
  _ = refl

  _ : ∀ n → induction P P0 PS (suc n) ≡ PS n (induction P P0 PS n)
  _ = λ n → refl

_+_ : Elt ℕ → Elt ℕ → Elt ℕ
m + n = induction (λ _ → Elt ℕ) n (λ _ → suc) m

_ : ℕ ∋ "SSSZ" + ℕ ∋ "SZ" ≡ ℕ ∋ "SSSSZ"
_ = refl
