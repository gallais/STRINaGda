module Acme.Data.Type.Grammar where

open import Acme.Data.Type

record Rest (xs : String) : Set where
  constructor mkRest
  field
    rest : String
    .prf : rest < xs
open Rest public

Parser : Set
Parser = (xs : String) → Maybe (Rest xs)

parsed : Parser → Type
parsed A str = isSome (A str)
             ∧′ (isEmpty ∘ rest ∘ fromSome (A str))

record Parsed (A : Parser) (xs : String) : Set where
  field
    grabed : ⟨ parsed A ⟩
    left   : String
    .eq    : xs ≡ val grabed ++ left

Rest∷ : {c : Char} {str : String} → Rest str → Rest (c ∷ str)
Rest∷ (mkRest r pr) = mkRest r (trans pr (step _ _))

charString : Char → String → Parser
charString c []         (c′ ∷ rest) = guard (c == c′) >> some (mkRest rest (step c′ rest)) 
charString c (c′ ∷ str) (s′ ∷ str′) = guard (c == s′) >> fmap Rest∷ (charString c′ str str′)
charString c _ _ = none

string : (str : String) {pr : < not (isEmpty str) >} → Parser
string [] {}
string (c ∷ str) = charString c str

UnitParser : Parser
UnitParser = string ⟦ "[]" ⟧

failParser : Parser
failParser = λ _ → none

infixr 2 _<|>_
_<|>_ : Parser → Parser → Parser
p <|> q = λ str → maybe (q str) some (p str)

enum : (str : List (String)) {pr : list (λ a _ → < not (isEmpty a) > ×_) One str} → Parser
enum []                = failParser
enum (str ∷ strs) {pr} = string str {fst pr} <|> enum strs {snd pr}

infixr 3 _<*>_
bind : (xs : String) → (p : Maybe (Rest xs)) → ((r : Rest xs) → Maybe (Rest (rest r))) → Maybe (Rest xs)
bind xs p q = maybe none (λ r → fmap (λ s → mkRest (rest s) (trans (prf s) (prf r))) (q r)) p

app : (xs : String) → (p : Parser) → ((r : Rest xs) → Maybe (Rest (rest r))) → Maybe (Rest xs)
app xs p q = bind xs (p xs) q

_<*>_ : Parser → Parser → Parser
p <*> q = λ xs → app xs p (λ r → q (rest r))

BoolParser : Parser
BoolParser = enum (⟦ "[`True]" ⟧ ∷ ⟦ "[`False]" ⟧ ∷ [])

PairParser : Parser → Parser → Parser
PairParser a b = string ⟦ "`Pair " ⟧ <*> a <*> string ⟦ " " ⟧ <*> b

private

  Unit : ⟨ parsed UnitParser ⟩
  Unit = ! "[]" !

  True : ⟨ parsed BoolParser ⟩
  True = ! "[`True]" !

  FalseUnit : ⟨ parsed (PairParser BoolParser UnitParser) ⟩
  FalseUnit = ! "`Pair [`False] []" !

data Desc : Set where
  `∃ : (A : Parser) (d : parsed A ⟶ Desc) → Desc
  `T : Desc
  `X : Desc

desc : Desc → (x : Char) (xs : String) → (∀ ys → .(ys < x ∷ xs) → Maybe (Rest ys)) → Maybe (Rest xs)
desc (`∃ A d) x xs X = {!!}
desc `T       x xs X = string ⟦ " []" ⟧ xs
desc `X       x xs X = X xs (step _ xs)

tr : ∀ {ℓ} {A : Set ℓ} {xs : List A} {ys} z {zs} → xs < ys → ys < z ∷ zs → xs < zs
tr z [] (∷ []) = []
tr z [] (∷ (∷ q)) = []
tr z (∷ ()) (∷ [])
tr z (∷ p) (∷ (∷ q)) = ∷ tr z p (∷ q)

constr : (c : Text) (d : Desc) (xs : String) → (∀ ys → .(ys < xs) → Maybe (Rest ys)) → Maybe (Rest xs)
constr c d xs X =
  app xs (string (⟦ "[`" ⟧ ++ ⟦ c ⟧)) $ λ r →
  bind (rest r) (desc d ' ' (rest r) (λ ys lt → app ys (string ⟦ " " ⟧) (λ zs → X (rest zs) (tr ' '(prf zs) (trans lt (∷ (prf r))))))) (λ s → string ⟦ "]" ⟧ (rest s))

record Data : Set where
  constructor mkData
  field constrs : List (Text × Desc)
open Data public

mu : (cs : Data) → Parser
mu cs = induction (λ xs → Maybe (Rest xs)) (go (constrs cs)) where

  go : (cs : List (Text × Desc)) (xs : String) (X : ∀ ys → .(ys < xs) → Maybe (Rest ys)) → Maybe (Rest xs)
  go []       xs X = failParser xs
  go (c ∷ cs) xs X = maybe (go cs xs X) some (constr (fst c) (snd c) xs X) -- <|> unfolded

nat : Data
nat = mkData $ ("Zero" & `T)
             ∷ ("Succ" & `X)
             ∷ []

ℕ : Type
ℕ = parsed (mu nat)

private

  zero : ⟨ ℕ ⟩
  zero = ! "[`Zero []]" !

  three : ⟨ ℕ ⟩
  three = ! "[`Succ [`Succ [`Succ [`Zero []]]]]" !
