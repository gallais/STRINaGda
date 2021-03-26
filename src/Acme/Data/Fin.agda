module Acme.Data.Fin where

open import Acme.Type
open import Acme.Data.Nat as ℕ using (ℕ)

Fin : Elt ℕ → Type
Fin = ℕ.induction (λ _ → Type) base (λ _ → step)

  where

  base : Type
  base _ = false

  step : Type → Type
  step ih [] = false
  step ih (c ∷ cs) = c == 'Z' && isNil cs
                  || c == 'S' && ih cs

zero : ∀ {n} → Elt (Fin (ℕ.suc n))
zero {n} = Fin (ℕ.suc n) ∋ "Z"

suc : ∀ {n} → Elt (Fin n) → Elt (Fin (ℕ.suc n))
suc [ k ] = [ 'S' ∷ k ]

sub : ∀ n str → str ∈ Fin n → str ∈ ℕ
sub = ℕ.induction
        (λ n → ∀ str → str ∈ Fin n → str ∈ ℕ)
        (λ _ ())
         step

  where

  step : ∀ n → (∀ str → str ∈ Fin n → str ∈ ℕ) →
               (∀ str → str ∈ Fin (ℕ.suc n) → str ∈ ℕ)
  step n ih (c ∷ cs) isFin = checkZ (c ≟ 'Z') cs {{isFin}} where

    checkS : ∀ {b} → Reflects c 'S' b → ∀ cs →
             {{IsTrue (b && Fin n cs)}} →
             (c ∷ cs) ∈ ℕ
    checkS true cs {{isFin}} = ih cs isFin

    checkZ : ∀ {b} → Reflects c 'Z' b → ∀ cs →
             {{IsTrue (b && isNil cs || c == 'S' && Fin n cs)}} →
             (c ∷ cs) ∈ ℕ
    checkZ true  [] = _
    checkZ false cs = checkS (c ≟ 'S') cs

cast : ∀ {n} → Elt (Fin n) → Elt ℕ
cast {n} p .value = p .value
cast {n} p .check = sub n (p .value) (p .check)
