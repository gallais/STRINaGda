module Acme.Data.Word where

open import Level
open import Acme.Data.Type
open import Acme.Data.Bit
open import Acme.Data.Nat

NonEmptyWord : Type → Type
NonEmptyWord ih []       = false
NonEmptyWord ih (c ∷ cs) = Bit (c ∷ []) ∧ ih cs

Word : Nat ⟶  Type
Word = NatInduction isEmpty $ λ _ → NonEmptyWord

`ε : ⟨ Word ! "Z" ! ⟩
`ε = ! "" !

_`<_]_ : Bit ⟶ ∀ (n : ⟨ Nat ⟩) → Word n ⟶′ Word (`succ n)
b `< n ] w = val b ++ val w , BitInduction {_} {P} (pr w) (pr w) b where
  P : Bit ⟶ Set
  P b = (val b ++ val w) ∈ Word (`succ n)

private

  0asWord4 : ⟨ Word ! "SSSSZ" ! ⟩
  0asWord4 = ! "0000" !

WordInduction : {ℓ : Level} {P : (n : ⟨ Nat ⟩) → Word n ⟶ Set ℓ} →
  P ! "Z" ! `ε →
  (ih : ∀ n b w → P n w → P (`succ n) (b `< n ] w)) →
  ∀ n w → P n w
WordInduction {ℓ} {P} Pε P<] n (w , pr) = NatInduction {ℓ} {Q} pε p<] n w pr where

  Q : Nat ⟶ Set ℓ
  Q n = ∀ w .(pr : w ∈ Word n) → P n (w , pr)

  pε : ∀ w → .(pr : [ isEmpty w ]) → P ! "Z" ! (w , pr)
  pε []      pr = Pε
  pε (_ ∷ _) pr = ZeroElim pr

  p<] : ∀ n → Q n → Q (`succ n)
  p<] n ih []      pr = ZeroElim pr
  p<] n ih (b ∷ w) pr = (
    bool PB (Bit (b ∷ [])) (
    bool PW (Word n w) (pb b w pr) (λ _ _ → ZeroElim)
    ) (λ _ → ZeroElim)
    ) pr where

    PB : Bool → Set ℓ
    PB d = .([ d ∧ Word n w ]) → P (`succ n) (b ∷ w , pr)

    PW : Bool → Set ℓ
    PW d = [ Bit (b ∷ []) ] → .([ d ]) → P (`succ n) (b ∷ w , pr)

    pb : ∀ b w .pr → [ Word n w ] → [ Bit (b ∷ []) ] → .One → P (`succ n) (b ∷ w , pr)
    pb b w pr hw hb _ = P<] n (b ∷ [] , hb) (w , hw) (ih w hw)


BitToNat : Bit ⟶′ Nat
BitToNat = BitInduction ! "Z" ! ! "SZ" !

WordToNat : {n : ⟨ Nat ⟩} → Word n ⟶′ Nat
WordToNat {n} w = WordInduction `zero (λ n b _ ih → BitToNat b * ! "SSZ" ! ^ n + ih) n w

private

  `5≡5 : WordToNat { ! "SSSSZ" ! } ! "0101" ! ≡ ! "SSSSSZ" !
  `5≡5 = refl
