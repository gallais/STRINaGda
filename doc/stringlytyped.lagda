\documentclass[twocolumn]{article}

\usepackage{fullpage}
\usepackage{nopageno}
\usepackage{hyperref}
\usepackage{agda}
\setlength{\mathindent}{5pt}

\usepackage{todonotes}

\usepackage[T1]{fontenc}
\input{unicode}
\input{commands}

\bibliographystyle{abbrvnat}

\title{Dependent Stringly-Typed Programming}
\author{gallais}

\begin{document}
\maketitle

\section{Introduction}

Static type systems started as a lightweight compile time check enforcing
basic hygiene by preventing users from e.g. adding an integer to a boolean.
Seduced by the promise of ever more guarantees computer scientists have
invented ever more powerful type systems to the point where they could
formalise all of mathematics as types and programs.

In this paper we reclaim this power to the advantage of the honest working
programmer by demonstrating how one can use the ivory tower concepts to
revitalise the age old practice of stringly typed programming. We will use
Agda as our language of choice because it provides us with powerful enough
``unsafe'' primitives to conduct our experiment. This paper is a self-contained
literate Agda file so the interested reader should be able to independently
reproduce our results. You can also find the content at
\url{https://github.com/gallais/STRINaGda}.

\section{What even is a type?}

% https://medium.com/@samth/on-typed-untyped-and-uni-typed-languages-8a3b4bedf68c
% https://semantic-domain.blogspot.com/2019/08/on-relationship-between-static-analysis.html
% https://hal.inria.fr/hal-01399694

For our purposes, we will simply say that a type is a function that, given a
linked list of characters, tells us whether we should accept it or not as a
value of that type.
%
Luckily Agda provides us with builtin notions of \AD{List}, \AD{Char},
and \AD{Bool} so this is easily defined.

\begin{code}
open import Agda.Builtin.List  using (List)
open import Agda.Builtin.Char  using (Char)
open import Agda.Builtin.Bool  using (Bool)

Type = List Char → Bool
\end{code}

Next we can define what it means to belong to a type. By definition, a
list of characters belongs to a type if the function returns the boolean
true when run on that list. To make this formal we need to define an Agda
function internalising the predicate ``this boolean is true''.

Agda ships with a notion of trivial truthfulness (the unit type) but
unfortunately it does not provide us with a notion of trivial falsity.
So we have to define the empty ourselves as a sum type with zero
constructor.

\begin{code}
open import Agda.Builtin.Unit using (⊤)

data ⊥ : Set where
\end{code}

Equipped with trivial truthfulness and trivial falsity, we can internalise
what it means for a boolean to be true by pattern matching on it and
returning the unit type if it is \AIC{true}, or the empty one if it is
\AIC{false}.

\begin{code}
open Agda.Builtin.Bool using (true; false)

IsTrue : Bool → Set
IsTrue true   = ⊤
IsTrue false  = ⊥
\end{code}

This is precisely what we need to express what it means for a list of
characters to belong to a given type: run the type on the
list of characters and check it returned \AIC{true}.

\begin{code}
_∈_ : List Char → Type → Set
cs ∈ A = IsTrue (A cs)
\end{code}

We can define a convenient wrapper for elements of a given type by packing
a list of characters together with the proof that it is accepted at that
type. We use a dependent \AK{record} and make the \ARF{check} field an
instance argument, that is to say that we never want to have to write these
proofs explicitly and expect Agda to just automatically pass them around
without needing our help.

\begin{code}
record Elt (A : Type) : Set where
  constructor [_]
  field value     : List Char
        {{check}} : value ∈ A
open Elt
\end{code}

Agda's string literals are tied to its builtin notion of \AF{String} which
is distinct from \AF{List Char}. We can luckily convert from one to the
other by unpacking the string. We define a convenient helper function to,
given a string and a type, return an element of that type by checking that
the unpacked string is accepted at that type. This will help us write
concrete examples and unit tests.

\begin{code}
open import Agda.Builtin.String using (String)
  renaming (primStringToList to unpack)

infix 100 _∋_
_∋_ : (A : Type) (str : String) →
      {{unpack str ∈ A}} → Elt A
A ∋ str = record { value = unpack str }
\end{code}


\section{Our First Type: ℕ}

As is customary in any document talking about dependent types, we will start
by defining the natural numbers. The customary presentation is that a natural
number is either zero or the successor of a natural natural number. In terms
of strings, we will characterise this as being either the ``Z'' string or a
string starting with `S' and whose tail is itself a natural number.

Agda, being a very inpractical programming language, does not ship with
\AF{\_\&\&\_} and \AF{\_||\_} defined on booleans.
The standard library does provide these definitions but has to be installed
separately and wwe want this document to be self-contained so we will have
to start by defining them ourselves.

\begin{code}
infixr 3 _&&_
_&&_ : Bool → Bool → Bool
true   && b = b
false  && b = false

infixr 2 _||_
_||_ : Bool → Bool → Bool
true   || b = true
false  || b = b
\end{code}

Next we need a way to test that a list of characters is empty.
The builtin type \AD{List} has two constructors: \AIC{[]} for the
empty list, and \AIC{\_∷\_} for putting together a character as the
head of the linked list a tail of additional characters. A list is
empty precisely when it is \AIC{[]}.

\begin{code}
open Agda.Builtin.List using ([]; _∷_)

isNil : List Char → Bool
isNil []       = true
isNil (_ ∷ _)  = false
\end{code}

The last piece of the puzzle is the ability to test two characters
for equality. This is once again provided as a primitive by Agda and
we import it and simply rename it to make the code more readable.

\begin{code}
open Agda.Builtin.Char
  renaming (primCharEquality to _==_)
\end{code}

We are now ready to define the type of natural numbers. If the input
list of characters is non-empty then it may be a natural number. We
check that it is
either `Z'-headed and with an empty tail (i.e. zero)
or `S'-headed and with a tail that is itself a natural number (i.e. successor).

\begin{code}
ℕ : Type
ℕ (c ∷ cs)  =   c == 'Z' && isNil cs
            ||  c == 'S' && ℕ cs
ℕ _ = false
\end{code}

Unsurprisingly we can define the \AF{zero} and \AF{suc} constructors
for \AD{ℕ}. Note that we do not need to write any proofs that the
strings are valid: Agda takes care of the proofs for us by a mix of
computation and implicit proof construction.

\begin{code}
zero : Elt ℕ
zero = ℕ ∋ "Z"

suc : Elt ℕ → Elt ℕ
suc [ n ] = [ 'S' ∷ n ]
\end{code}

We can define constant numbers either by using our \AF{\_∋\_} gadget or by
using \AF{suc} and \AF{zero}, whatever feels most convenient.

\begin{code}
one    = ℕ ∋ "SZ"
two    = suc (suc zero)
three  = ℕ ∋ "SSSZ"
four   = suc three
\end{code}

\section{Stringly Typed Programming}

Being able to construct values of a given type is all well and good but
we, as programmers, want to be able to take them apart too.

Induction is the dependently typed equivalent of primitive recursion:
for a predicate \AB{P} on values of type \AF{ℕ},
if we can prove that {\AB{P} \AF{zero}} holds
and that for any natural number \AB{n}, if {\AB{P} \AB{n}} holds
then so does {\AB{P} (\AF{suc} \AB{n})}
then we ought to be able to have a function computing from a natural
number \AB{n} a proof of type {\AB{P} \AB{n}}.

\subsection{Small Scale Reflection}

The tricky part in defining induction for the natural numbers is in connecting
the observations made by the boolean-valued equality test \AF{\_==\_} with
propositional equality.
%
To do that we introduce a \AD{Reflects} indexed family inspired by the
architecture of Coq's small scale reflection
library~\cite{assia_mahboubi_2021_4457887}.
A proof {\AD{Reflects} \AB{c} \AB{d} \AB{b}} is,
if the boolean \AB{b} is \AIC{true} equivalent to a proof that \AB{c} is
equal to \AB{d},
and otherwise a useless token.
We name the \AD{Reflects} constructors the same as their index boolean so
that matching on such a proof looks like matching on the original boolean.

\begin{code}
data Reflects (c : Char) : Char → Bool → Set where
  true  : Reflects c c true
  false : ∀ {d} → Reflects c d false
\end{code}

We can readily prove that if \AB{a} and \AB{b} are known to be the same
according to Agda's builtin notion of propositional equality then we have
that {\AD{Reflects} \AB{a} \AB{b} \AIC{true}}.

\begin{code}
open import Agda.Builtin.Equality using (_≡_; refl)

mkTrue : ∀ {a b} → a ≡ b → Reflects a b true
mkTrue refl = true
\end{code}

The only thing missing for us is a proof that whenever the test
{\AB{a} \AF{==} \AB{b}} returns \AIC{true} then {\AB{a} \AD{≡} \AB{b}}.
Unfortunately Agda does not provide us a primitive proof of this fact.
We will have to use an unsafe primitive called \AF{trustMe} to build
such a proof.

\begin{code}
open import Agda.Builtin.TrustMe
  renaming (primTrustMe to trustMe)
\end{code}

By combining \AF{mkTrue} and \AF{trustMe} we can write a function demonstrating
that the {(\AB{a} \AF{==} \AB{b})} test produces a boolean that reflects a test
on propositional equality.

\begin{code}
_≟_ : (a b : Char) → Reflects a b (a == b)
a ≟ b with a == b
... | false = false
... | true = mkTrue trustMe
\end{code}

\subsection{Induction principle for ℕ}

And with that in our backpocket we are well equipped to prove induction.
First we use an anonymous module to parametrise all of the following definitions
over the same predicate \AB{P}, proof of the base case \AB{P0} and proof of the
step case \AB{PS}.

\begin{code}
module _ (P : Elt ℕ → Set)
         (P0 : P zero)
         (PS : ∀ n → P n → P (suc n))
         where
\end{code}

And we then prove the \AF{induction} principle stating that \AB{P} holds for
all of the natural numbers.

\begin{code}
  induction : ∀ n → P n
\end{code}

The details of the proof are not very illuminating but we include them for
completeness' sake. We start by checking
whether the natural number is zero, in which case we can use the base case,
or whether it is a successor in which case we use the step case together
with a recursive call to \AF{induction}.

The stage has been set just right so that things compute where they should,
impossible branches are self-evidently impossible and therefore the proof
goes through. The thing to notice if we want to understand the proof is that
the expression in the \AF{IsTrue} instance argument gets smaller as we make
more and more observations that constrain what the input natural number may
be like.

\begin{code}
  induction [ ccs@(c ∷ cs) ] = checkZ (c ≟ 'Z') cs refl

   where

    checkS : ∀ {b} → Reflects c 'S' b → ∀ cs →
      {{IsTrue (b && ℕ cs)}} →
      ∀ {ccs} → c ∷ cs ≡ ccs .value → P ccs
    checkS true cs refl = PS [ cs ] (induction [ cs ])

    checkZ : ∀ {b} → Reflects c 'Z' b → ∀ cs →
      {{IsTrue (b && isNil cs || c == 'S' && ℕ cs)}} →
      ∀ {ccs} → c ∷ cs ≡ ccs .value → P ccs
    checkZ true  [] refl = P0
    checkZ false cs eq   = checkS (c ≟ 'S') cs eq
\end{code}

A primitive recursion operator is of course not just one that has
the right type but one that has the right computational behaviour too.
We can readily check that our \AF{induction} function behaves exactly
like the primitive recursor on natural numbers ought to by writing two
unit tests.

First, when applied to \AF{zero}, the recursor returns its base case.

\begin{code}
_ : ∀ {P P0 PS} → induction P P0 PS zero ≡ P0
_ = refl
\end{code}

Second, when applied to the successor of a natural number \AB{n}, the
recursor returns its step case applied to \AB{n} and the result of the
recursive call.

\begin{code}
_ : ∀ {P P0 PS n} →
      induction P P0 PS (suc n)
    ≡ PS n (induction P P0 PS n)
_ = refl
\end{code}

The fact that both of these unit tests are provable by \AIC{refl} means
that Agda can tell by computation alone that the expressions are equal.

\subsection{Example: Addition, Multiplication}

As is well known, primitive recursion is enough to implement addition and
multiplication on the natural numbers.

\begin{code}
_+_ : Elt ℕ → Elt ℕ → Elt ℕ
m + n = induction (λ _ → Elt ℕ) n (λ _ → suc) m

_ : three + one ≡ four
_ = refl
\end{code}

\begin{code}
_*_ : Elt ℕ → Elt ℕ → Elt ℕ
m * n = induction (λ _ → Elt ℕ) zero (λ _ → n +_) m

_ : two * three ≡ four + two
_ = refl
\end{code}


\todo{Fin + Fin ⊆ Nat?}

\section{Conclusion}

\bibliography{main}

\end{document}
