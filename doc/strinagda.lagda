\documentclass[11pt, twocolumn]{article}

\usepackage{fullpage}
\usepackage{agda}
\setlength{\mathindent}{0pt}

\title{Dependent Stringly-Typed Programming}
\author{gallais}

\begin{document}
\maketitle

\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}

module strinagda where

postulate IMPOSSIBLE : ∀ {ℓ} {A : Set ℓ} → A
\end{code}

\begin{code}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Char
  using (Char)
  renaming (primCharEquality to _==_)

infixr 3 _∧_
_∧_ : Bool → Bool → Bool
true  ∧ b = b
_     ∧ b = false

infixr 2 _∨_
_∨_ : Bool → Bool → Bool
true  ∨ b = true
_     ∨ b = b

infixr 5 _∷_
data String : Set where
  []   : String
  _∷_  : Char → String → String

Type : Set
Type = String → Bool

infix 3 _∶_
_∶_ : String → Type → Set
a ∶ A = A a ≡ true

infix 1 [_]
infix 3 the_
record [_] (A : Type) : Set where
  constructor the_
  field  value       : String
         .{{valid}}  : value ∶ A
open [_] public

absurd : ∀ {a} {A : Set a} →
         .{{pr : false ≡ true}} → A
absurd {{}}

⊥ : Type
⊥ _ = false

⊥-elim : {A : Set} → [ ⊥ ] → A
⊥-elim v = absurd

⊤ : Type
⊤ [] = true
⊤ _  = false

tt : [ ⊤ ]
tt = the []

⊤-eta : (t u : [ ⊤ ]) → t ≡ u
⊤-eta (the []) (the []) = refl
⊤-eta (the t ∷ ts) _ = absurd
⊤-eta _ (the u ∷ us) = absurd

headed : Char → Type → Type
headed hd A []        = false
headed hd A (c ∷ cs)  = c == hd ∧ A cs

_⊎_ : Type → Type → Type
(A ⊎ B) str = headed 'L' A str
            ∨ headed 'R' B str

Nat : Type
Nat []       = false
Nat (c ∷ n)  = c == 'Z' ∧ ⊤ n
             ∨ c == 'S' ∧ Nat n

zero : [ Nat ]
zero = the 'Z' ∷ []

suc : [ Nat ] → [ Nat ]
suc (the n) = the 'S' ∷ n

module Nat where

 module _
   (P   : [ Nat ] → Set)
   (pZ  : P zero)
   (pS  : ∀ n → P n → P (suc n))
   where

  induction : ∀ n → P n
  induction (the 'S' ∷ n)   = pS (the n) (induction (the n))
  induction (the 'Z' ∷ [])  = pZ
  induction _               = IMPOSSIBLE

 iter : {A : Set} → A → (A → A) → [ Nat ] → A
 iter z s = induction _ z (λ _ → s)

 _+_ : [ Nat ] → [ Nat ] → [ Nat ]
 m + n = iter n suc m

 _*_ : [ Nat ] → [ Nat ] → [ Nat ]
 m * n = iter zero (n +_) m

 _^_ : [ Nat ] → [ Nat ] → [ Nat ]
 m ^ n = iter (suc zero) (m *_) n

Fin : [ Nat ] → Type
Fin = Nat.induction
  (λ _ → Type)
  ⊥
  (λ _ _ _ → true)

fzero : ∀ {n} → [ Fin (suc n) ]
fzero = {!!}

fsuc : ∀ {n} → [ Fin n ] → [ Fin (suc n) ]
fsuc = {!!}
\end{code}

\end{document}
