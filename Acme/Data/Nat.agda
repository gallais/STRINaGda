module Acme.Data.Nat where

open import Acme.Data.Type

Nat : Type
Nat []       = false
Nat (c ∷ cs) = c == 'Z' ∧ isEmpty cs
             ∨ c == 'S' ∧ Nat cs

`zero : ⟨ Nat ⟩
`zero = ! "Z" !

`succ : Nat ⟶′ Nat
`succ (n , prn) = 'S' ∷ n , prn

NatInduction : {P : Nat ⟶ Set}
  (pz : P `zero) (ps : ∀ n → P n → P (`succ n))
  (cs : ⟨ Nat ⟩) → P cs
NatInduction {P} Pz Ps (bs , pr) = go bs pr
  where
    go : (cs : String) .(pr : cs ∈ Nat) → P (cs , pr)
    go []       ()
    go (c ∷ cs) pr = (
      dec PZ (c ≟ 'Z') (pz c cs pr) $ λ ¬c≡Z →
      dec PS (c ≟ 'S') (ps c cs pr) $ λ ¬c≡S →
      ZeroElim
      ) pr

     where
     
       PZ : Dec (c ≡ 'Z') → Set
       PZ d = .([ isYes d ∧ isEmpty cs ∨ c == 'S' ∧ Nat cs ]) → P (c ∷ cs , pr)
     
       pz : ∀ c cs .pr → c ≡ 'Z' → .([ isEmpty cs ∨ c == 'S' ∧ Nat cs ]) → P (c ∷ cs , pr)
       pz .'Z' []      pr refl hf = Pz
       pz .'Z' (_ ∷ _) pr refl hf = ZeroElim hf
       
       PS : Dec (c ≡ 'S') → Set
       PS d = .([ isYes d ∧ Nat cs ]) → P (c ∷ cs , pr)
     
       ps : ∀ c cs .pr → c ≡ 'S' → .([ Nat cs ]) → P (c ∷ cs , pr)
       ps .'S' cs pr refl hf = Ps (cs , pr) (go cs pr)

add : Nat ⟶ Nat ⟶′ Nat
add m = λ n → NatInduction n (λ _ → `succ) m

`3+2≡5 : add ! "SSSZ" ! ! "SSZ" ! ≡ ! "SSSSSZ" !
`3+2≡5 = refl
