module Acme.Data.Bit where

open import Level
open import Acme.Data.Type

Bit : Type
Bit []       = false
Bit (a ∷ as) = (a == '0' ∨ a == '1') ∧ isEmpty as

BitInduction :
  {ℓ : Level} {P : Bit ⟶ Set ℓ} → P ! "0" ! → P ! "1" ! →
  (b : ⟨ Bit ⟩) → P b
BitInduction {ℓ} {P} bit0 bit1 (b , pr) = go b pr where

  go : ∀ b .(pr : b ∈ Bit) → P (b , pr)
  go []       ()
  go (a ∷ as) pr = (
    dec P0 (a ≟C '0') (p0 a as pr) $ λ ¬a≡0 →
    dec P1 (a ≟C '1') (p1 a as pr) $ λ ¬a≡1 →
    ZeroElim
    ) pr

    where

     P0 : Dec (a ≡ '0') → Set ℓ
     P0 d = .([ (isYes d ∨ a == '1') ∧ isEmpty as ]) → P (a ∷ as , pr)
   
     p0 : ∀ a as .pr → a ≡ '0' → .([ isEmpty as ]) → P (a ∷ as , pr)
     p0 .'0' []      pr refl _ = bit0
     p0 .'0' (_ ∷ _) pr refl ()

     P1 : Dec (a ≡ '1') → Set ℓ
     P1 d = .([ isYes d ∧ isEmpty as ]) → P (a ∷ as , pr)
     
     p1 : ∀ a as .pr → (eq : a ≡ '1') → .([ isEmpty as ]) → P (a ∷ as , pr)
     p1 .'1' []      pr refl _ = bit1
     p1 .'1' (_ ∷ _) pr refl ()

Bit[_] : Bit ⟶ Set
Bit[_] = BitInduction Zero One
