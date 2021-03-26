module Acme.Data.Nat where

open import Acme.Type

ℕ   : Type
isZ : Type
isS : Type

ℕ cs = isZ cs || isS cs

isZ [] = false
isZ (c ∷ cs) = c == 'Z' && isNil cs

isS [] = false
isS (c ∷ cs) = c == 'S' && ℕ cs

zero = ℕ ∋ "Z"

suc : Elt ℕ → Elt ℕ
suc [ n ] = [ 'S' ∷ n ]

one    = ℕ ∋ "SZ"
two    = suc (suc zero)
three  = ℕ ∋ "SSSZ"
four   = suc three

module _ (P : Elt ℕ → Set)
         (P0 : P zero)
         (PS : ∀ n → P n → P (suc n))
         where

  induction : ∀ n → P n
  induction [ ccs@(c ∷ cs) ] = checkZ (c ≟ 'Z') cs refl where

    checkS : ∀ {b} → Reflects c 'S' b → ∀ cs →
             {{@0 _ : IsTrue (b && ℕ cs)}} →
             ∀ {ccs} → c ∷ cs ≡ ccs .value → P ccs
    checkS true cs refl = PS [ cs ] (induction [ cs ])

    checkZ : ∀ {b} → Reflects c 'Z' b → ∀ cs →
             {{@0 _ : IsTrue (b && isNil cs || isS (c ∷ cs))}} →
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

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n =
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
