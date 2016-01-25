module Acme.Data.Type where

open import Level

record One : Set where
  constructor *

data Zero : Set where

ZeroElim : {ℓ : Level} {A : Set ℓ} → .Zero → A
ZeroElim ()

data Bool : Set where true false : Bool

[_] : Bool → Set
[ true  ] = One
[ false ] = Zero

infixr 6 _∧_
infixr 5 _∨_
_∧_ : Bool → Bool → Bool
true  ∧ c = c
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
false ∨ c     = c

postulate
  Char : Set
{-# BUILTIN CHAR  Char  #-}
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

primitive
  primCharEquality : Char → Char → Bool

¬_ : Set → Set
¬ P = P → Zero

data Dec (A : Set) : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A

dec : {P : Set} (C : Dec P → Set) (d : Dec P) (yes : (p : P) → C (yes p)) (no : (¬p : ¬ P) → C (no ¬p)) → C d
dec C (yes p) y n  = y p
dec C (no ¬p) y n = n ¬p

data _≡_ {ℓ : Level} {A : Set ℓ} (a : A) : (b : A) → Set ℓ where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

private
 primitive
   primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
trustMe = primTrustMe

infix 5 _≟_
_≟_ : (a b : Char) → Dec (a ≡ b)
a ≟ b with primCharEquality a b
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

isYes : {A : Set} → Dec A → Bool
isYes d = dec _ d (λ _ → true) (λ _ → false)

_==_ : Char → Char → Bool
a == b = isYes (a ≟ b)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

String = List Char

isEmpty : String → Bool
isEmpty [] = true
isEmpty _  = false


Type : Set
Type = String → Bool

infix 4 _∈_
_∈_ : String → Type → Set
a ∈ A = [ A a ]

infixr 3 _,_
record ⟨_⟩ (A : Type) : Set where
  constructor _,_
  field
    val : String
    .pr : val ∈ A

infixr 3 _⟶_ _⟶′_
_⟶_ : {ℓ : Level} → Type → Set ℓ → Set ℓ
A ⟶ B = ⟨ A ⟩ → B
_⟶′_ : Type → Type → Set
A ⟶′ B = A ⟶ ⟨ B ⟩

postulate
  Text : Set
{-# BUILTIN STRING Text #-}

primitive
  primStringToList : Text → String

⟦_⟧ = primStringToList

infixr 0 _$_
_$_ : {A B : Set} (f : A → B) (x : A) → B
f $ x = f x

infix 0 !_!
!_! : {A : Type} (a : Text) {pr : ⟦ a ⟧ ∈ A} →
      ⟨ A ⟩
! a ! {pr} = ⟦ a ⟧ , pr
