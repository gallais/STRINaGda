module Acme.Data.Nat where

open import Level
open import Acme.Data.Type
open import Acme.Data.Bit

Nat : Type
Nat []       = false
Nat (c ∷ cs) = c == 'Z' ∧ isEmpty cs
             ∨ c == 'S' ∧ Nat cs

`zero : ⟨ Nat ⟩
`zero = ! "Z" !

`succ : Nat ⟶′ Nat
`succ (n , prn) = 'S' ∷ n , prn

NatInduction : {ℓ : Level} {P : Nat ⟶ Set ℓ}
  (pz : P `zero) (ps : ∀ n → P n → P (`succ n))
  (cs : ⟨ Nat ⟩) → P cs
NatInduction {ℓ} {P} Pz Ps (bs , pr) = go bs pr where
  
  go : (cs : String) .(pr : cs ∈ Nat) → P (cs , pr)
  go []       ()
  go (c ∷ cs) pr = (
    dec PZ (c ≟ 'Z') (pz c cs pr) $ λ ¬c≡Z →
    dec PS (c ≟ 'S') (ps c cs pr) $ λ ¬c≡S →
    ZeroElim
    ) pr where
     
    PZ : Dec (c ≡ 'Z') → Set ℓ
    PZ d = .([ isYes d ∧ isEmpty cs ∨ c == 'S' ∧ Nat cs ]) → P (c ∷ cs , pr)
     
    pz : ∀ c cs .pr → c ≡ 'Z' → .([ isEmpty cs ∨ c == 'S' ∧ Nat cs ]) → P (c ∷ cs , pr)
    pz .'Z' []      pr refl hf = Pz
    pz .'Z' (_ ∷ _) pr refl hf = ZeroElim hf
       
    PS : Dec (c ≡ 'S') → Set ℓ
    PS d = .([ isYes d ∧ Nat cs ]) → P (c ∷ cs , pr)
     
    ps : ∀ c cs .pr → c ≡ 'S' → .([ Nat cs ]) → P (c ∷ cs , pr)
    ps .'S' cs pr refl hf = Ps (cs , pr) (go cs pr)

NatCase : {P : Nat ⟶ Set}
  (pz : P `zero) (ps : ∀ n → P (`succ n)) →
  (b : ⟨ Nat ⟩) → P b
NatCase pz ps = NatInduction pz (λ n _ → ps n)

infixr 6 _*_
infixr 5 _+_
infixr 7 _^_

_+_ : Nat ⟶ Nat ⟶′ Nat
m + n = NatInduction n (λ _ → `succ) m

_*_ : Nat ⟶ Nat ⟶′ Nat
m * n = NatInduction `zero (λ _ → n +_) m

_^_ : Nat ⟶ Nat ⟶′ Nat
m ^ n = NatInduction ! "SZ" ! (λ _ → m *_) n

private

  `2 : ⟨ Nat ⟩
  `2 = ! "SSZ" !

  `3 : ⟨ Nat ⟩
  `3 = ! "SSSZ" !

  `5 : ⟨ Nat ⟩
  `5 = ! "SSSSSZ" !

  `3+2≡5 : `3 + `2 ≡ `5
  `3+2≡5 = refl

  `3*5≡2^2+5+2*3 : `3 * `5 ≡ `2 ^ `2 + `5 + `2 * `3
  `3*5≡2^2+5+2*3 = refl

_≤_ : Nat ⟶ Nat ⟶′ Bit
_≤_ = NatInduction (λ _ → ! "1" !) (λ _ ih n → NatCase ! "0" ! ih n)

private

  `3≤5 : Bit[ `3 ≤ `5 ]
  `3≤5 = one

  `5≤3 : Bit[ `5 ≤ `3 ] → Zero
  `5≤3 = λ x → x
