module Acme.Type where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char)
  renaming (primCharEquality to _==_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
  renaming (primStringToList to unpack)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.TrustMe using ()
  renaming (primTrustMe to trustMe)


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

one    = ℕ ∋ "SZ"
two    = suc (suc zero)
three  = ℕ ∋ "SSSZ"
four   = suc three

data Reflects (a : Char) : Char → Bool → Set where
  true  : Reflects a a true
  false : ∀ {b} → Reflects a b false

mkTrue : ∀ {a b} → a ≡ b → Reflects a b true
mkTrue refl = true

_≟_ : (a b : Char) → Reflects a b (a == b)
a ≟ b with a == b
... | false = false
... | true  = mkTrue trustMe

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

_ : ∀ {P P0 PS} → induction P P0 PS zero ≡ P0
_ = refl

_ : ∀ {P P0 PS n} →
    induction P P0 PS (suc n) ≡ PS n (induction P P0 PS n)
_ = refl

_+_ : Elt ℕ → Elt ℕ → Elt ℕ
m + n = induction (λ _ → Elt ℕ) n (λ _ → suc) m

_ : three + one ≡ four
_ = refl

_*_ : Elt ℕ → Elt ℕ → Elt ℕ
m * n = induction (λ _ → Elt ℕ) zero (λ _ → n +_) m

_ : two * three ≡ four + two
_ = refl

variable
  A B : Set
  x y z : A

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

zero-+ : ∀ m → zero + m ≡ m
zero-+ m = refl

+-zero : ∀ m → m + zero ≡ m
+-zero =
  induction
    (λ m → m + zero ≡ m)
    refl
    (λ n → cong suc)

suc-+ : ∀ m n → suc m + n ≡ suc (m + n)
suc-+ m n = refl

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc m n =
  induction
    (λ m → (m + suc n) ≡ suc (m + n))
    refl
    (λ n → cong suc)
    m

+-sym : ∀ m n → m + n ≡ n + m
+-sym m n =
  induction
    (λ m → m + n ≡ n + m)
    (sym (+-zero n))
    (λ m ih → trans (cong suc ih) (sym (+-suc n m)))
    m

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc m n p =
  induction
    (λ m → ((m + n) + p) ≡ (m + (n + p)))
    refl
    (λ m → cong suc)
    m

Fin : Elt ℕ → Type
Fin = induction (λ _ → Type) (λ _ → false) (λ _ → step)

  where

  step : Type → Type
  step ih [] = false
  step ih (c ∷ cs) = c == 'Z' && isNil cs
                  || c == 'S' && ih cs

fzero : ∀ {n} → Elt (Fin (suc n))
fzero {n} = Fin (suc n) ∋ "Z"

fsuc : ∀ {n} → Elt (Fin n) → Elt (Fin (suc n))
fsuc [ k ] = [ 'S' ∷ k ]
