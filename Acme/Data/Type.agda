module Acme.Data.Type where

open import Level

record One : Set where
  constructor mkOne

data Zero : Set where

ZeroElim : {ℓ : Level} {A : Set ℓ} → .Zero → A
ZeroElim ()

infixr 5 _&_
record Pair (A : Set) (B : A → Set) : Set where
  constructor _&_
  field
    fst : A
    snd : B fst
open Pair public

∃ : {A : Set} (B : A → Set) → Set
∃ B = Pair _ B

infixr 2 _×_
_×_ : (A B : Set) → Set
A × B = Pair A (λ _ → B)

bimap : {A C : Set} {B : A → Set} {D : C → Set} (f : A → C) (g : {a : A} → B a → D (f a)) → Pair A B → Pair C D
bimap f g (fst & snd) = f fst & g snd

data Bool : Set where true false : Bool

<_> : Bool → Set
< true  > = One
< false > = Zero

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ P = P → Zero

bool : {ℓ : Level} (C : Bool → Set ℓ) →
       (b : Bool) (t : < b > → C true) (f : ¬ < b > → C false) → C b
bool C true  t f = t mkOne
bool C false t f = f (λ x → x)

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

data Dec {ℓ : Level} (A : Set ℓ) : Set ℓ where
  yes : A   → Dec A
  no  : ¬ A → Dec A

dec : {ℓ ℓ′ : Level} {P : Set ℓ} (C : Dec P → Set ℓ′)
      (d : Dec P) (yes : (p : P) → C (yes p)) (no : (¬p : ¬ P) → C (no ¬p)) → C d
dec C (yes p) y n  = y p
dec C (no ¬p) y n = n ¬p

infix 1 _≡_
data _≡_ {ℓ : Level} {A : Set ℓ} (a : A) : (b : A) → Set ℓ where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

private
 primitive
   primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
trustMe = primTrustMe

infix 5 _≟C_
_≟C_ : (a b : Char) → Dec (a ≡ b)
a ≟C b with primCharEquality a b
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

isYes : {A : Set} → Dec A → Bool
isYes d = dec _ d (λ _ → true) (λ _ → false)

_==_ : Char → Char → Bool
a == b = isYes (a ≟C b)

infixr 10 _∷_
data List {ℓ : Level} (A : Set ℓ) : Set ℓ where
  []  : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

String = List Char

isEmpty : String → Bool
isEmpty [] = true
isEmpty _  = false


Type : Set
Type = String → Bool

infix 7 _∈_
_∈_ : String → Type → Set
a ∈ A = < A a >

infix 7 _∈?_
_∈?_ : (a : String) (A : Type) → Dec (a ∈ A)
a ∈? A with A a
... | true  = yes mkOne
... | false = no (λ x → x)

infixr 3 _,,_
record ⟨_⟩ (A : Type) : Set where
  constructor _,,_
  field
    val : String
    .pr : val ∈ A
open ⟨_⟩ public

infixr 3 _⟶_ _⟶′_
_⟶_ : {ℓ : Level} → Type → Set ℓ → Set ℓ
A ⟶ B = ⟨ A ⟩ → B
_⟶′_ : Type → Type → Set
A ⟶′ B = A ⟶ ⟨ B ⟩

postulate
  Text : Set
{-# BUILTIN STRING Text #-}

primitive
  primStringEquality : Text → Text → Bool
  primStringToList   : Text   → String
  primStringFromList : String → Text

⟦_⟧ = primStringToList

infix 5 _≟T_
_≟T_ : (a b : Text) → Dec (a ≡ b)
a ≟T b with primStringEquality a b
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

_==T_ : (s t : Text) → Bool
s ==T t = isYes (s ≟T t)

show : {A : Type} → A ⟶ Text
show a = primStringFromList (val a)

id : {A : Set} → A → A
id = λ x → x

infixl 1 _∘_
_∘_ : {ℓ : Level} {A B C : Set ℓ} (g : B → C) (f : A → B) → A → C
g ∘ f = λ a → g (f a)

infixr 0 _$_
_$_ : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} (f : A → B) (x : A) → B
f $ x = f x

infix 0 !_!
!_! : {A : Type} (a : Text) {pr : ⟦ a ⟧ ∈ A} → ⟨ A ⟩
! a ! {pr} = ⟦ a ⟧ ,, pr

!_∋_! : (A : Type) (a : Text) {pr : ⟦ a ⟧ ∈ A} → ⟨ A ⟩
! A ∋ a ! {pr} = ! a ! {pr}
