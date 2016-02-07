module Acme.DB.SQL where

open import Level

open import Acme.Data.Type
open import Acme.Data.Nat
open import Acme.Data.String

record Row : Set where
  constructor _←_
  field
    name : Text
    type : Type
open Row public

Table : Set
Table = List Row

foldr : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} (c : A → B → B) (n : B) → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

map : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} (f : A → B) → List A → List B
map f = foldr (λ x → f x ∷_) []


all : {A : Set} → (A → Bool) → List A → Bool
all P = foldr (λ a → P a ∧_) true

one : {A : Set} → (A → Bool) → List A → Bool
one P = foldr (λ a → P a ∨_) false

infix 5 _∋_ε_
data _∋_ε_ (r : Row) : Text → Table → Set where
  z : {t : Table} → r ∋ name r ε r ∷ t
  s : {t : Table} {n : Text} {s : Row} → r ∋ n ε t → r ∋ n ε s ∷ t

infix 5 _ε?_
_ε?_ : (n : Text) (t : Table) → Dec (∃ λ r → r ∋ n ε t)
n ε? []    = no (λ { (_ & ()) })
n ε? r ∷ t with n ≟T name r | n ε? t
... | yes eq | _ rewrite eq = yes (r & z)
... | _ | yes (r′ & p)      = yes (r′ & s p)
... | no ¬eq | no ¬p        = no {!!}

data VSQL : List Row → Set where
  []  : VSQL []
  _∷_ : {r : Row} {rs : List Row} → ⟨ type r ⟩ → VSQL rs → VSQL (r ∷ rs)

VSQL′ : (rs : List Row) → Set
VSQL′ []       = One
VSQL′ (r ∷ []) = ⟨ type r ⟩ 
VSQL′ (r ∷ rs) = ⟨ type r ⟩ × VSQL′ rs

vsql : {rs : List Row} (vs : VSQL rs) → VSQL′ rs
vsql []             = mkOne
vsql (v ∷ [])       = v
vsql (v ∷ (w ∷ vs)) = v & vsql (w ∷ vs)

VSQLS : List Row → Set
VSQLS rs = List (VSQL rs)

VSQLS′ : List Row → Set
VSQLS′ rs = List (VSQL′ rs)

vsqls : {rs : List Row} (vs : VSQLS rs) → VSQLS′ rs
vsqls = map vsql


data SQL (A : Set) : Set where
  RETURN     : A → SQL A
  SELECTFROM : (t : Table) (rs : List (Pair Row $ λ r → r ∋ name r ε t))
               (k : VSQLS (map fst rs) → SQL A) → SQL A
  INSERTINTO : (t : Table) (vs : VSQL′ t) (k : One → SQL A) → SQL A

infix 4 insertinto
insertinto : (t : Table) (vs : VSQL′ t) → SQL One
insertinto t vs = INSERTINTO t vs RETURN
syntax insertinto t vs = INSERT vs INTO t

data AllIn (t : Table) : (rs : List Row) (ns : List Text) → Set where
  []     : AllIn t [] []
  _:&_∷_ : (r : Row) {n : Text} {rs : List Row} {ns : List Text} →
           r ∋ n ε t → AllIn t rs ns → AllIn t (r ∷ rs) (n ∷ ns)

AllIn? : (ns : List Text) (t : Table) → Dec (∃ λ rs → AllIn t rs ns)
AllIn? []       t = yes ([] & [])
AllIn? (n ∷ ns) t with n ε? t | AllIn? ns t
... | yes (r & p) | yes (rs & ps) = yes (r ∷ rs & r :& p ∷ ps)
... | _ | _ = no {!!}

fromYes : {P : Set} (d : Dec P) {_ : < isYes d >} → P
fromYes (yes p) = p
fromYes (no ¬p) {()}

collapseε : {r : Row} {n : Text} {t : Table} → r ∋ n ε t → n ≡ name r
collapseε z     = refl
collapseε (s x) = collapseε x

collapse : {t : Table} {rs : List Row} {ns : List Text} →
           AllIn t rs ns → List (Pair Row $ λ r → r ∋ name r ε t)
collapse []            = []
collapse (r :& x ∷ xs) rewrite collapseε x = (r & x) ∷ collapse xs

infix 3 [_
data SELECTED (t : Table) : Set where
  *   : SELECTED t
  [_  : (xs : List Text) {pr : < isYes (AllIn? xs t) >} → SELECTED t

diag : (t : Table) → List (Pair Row $ λ r → r ∋ name r ε t)
diag []      = []
diag (r ∷ t) = (r & z) ∷ map (bimap id s) (diag t)

toList : (t : Table) → SELECTED t → List (Pair Row $ λ r → r ∋ name r ε t)
toList t *             = diag t
toList t ([_ xs {pr}) = collapse (snd (fromYes (AllIn? xs t) {pr}))

infix 2 selectfrom
selectfrom : (t : Table) (sel : SELECTED t) → SQL (VSQLS (map fst (toList t sel)))
selectfrom t *               = SELECTFROM t (diag t) RETURN
selectfrom t ([_ xs {pr}) = SELECTFROM t (collapse (snd (fromYes (AllIn? xs t) {pr}))) RETURN

syntax selectfrom t rs = SELECT rs FROM t


return : {A : Set} → A → SQL A
return = RETURN

_>>=_ : {A B : Set} (mA : SQL A) (f : A → SQL B) → SQL B
RETURN a          >>= f = f a
SELECTFROM t rs k >>= f = SELECTFROM t rs (λ a → k a >>= f)
INSERTINTO t vs k >>= f = INSERTINTO t vs (λ a → k a >>= f)

fmap : {A B : Set} (f : A → B) → SQL A → SQL B
fmap f ma = ma >>= (return ∘ f)

postulate

  runSQL : {A : Set} → SQL A → A

infixr 4 cons
infix  5 singleton
singleton : {ℓ : Level} {A : Set ℓ} → A → List A
singleton a = a ∷ []
cons : {ℓ : Level} {A : Set ℓ} → A → List A → List A
cons = _∷_
syntax singleton a = a ]
syntax cons x xs = x , xs

private

  CustomerID      = "CustomerID"      ← Nat
  CustomerSurname = "CustomerSurname" ← AlphaString
  CustomerPoints  = "CustomerPoints"  ← Nat

  Customer : Table
  Customer = CustomerID ∷ CustomerSurname ∷ CustomerPoints ∷ []

  SelectIDSurname : SQL (VSQLS (CustomerID ∷ CustomerSurname ∷ []))
  SelectIDSurname = SELECT [ "CustomerID" , "CustomerSurname" ] FROM Customer

  Select* : SQL $ List $ ⟨ Nat ⟩ × ⟨ AlphaString ⟩ × ⟨ Nat ⟩
  Select* = fmap vsqls $ SELECT * FROM Customer

  mkNewCustomer : ⟨ Nat ⟩ → ⟨ AlphaString ⟩ → SQL One
  mkNewCustomer id sn = INSERT id & sn & ! "Z" ! INTO Customer -- a new customer start with 0 points

  IDSurname : List (⟨ Nat ⟩ × ⟨ AlphaString ⟩)
  IDSurname = vsqls $ runSQL SelectIDSurname
