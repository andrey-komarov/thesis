This is LITERATE AGDA!!!!

\begin{code}
module Ololo where

  data B : Set where
    T F : B

\end{code}

\AgdaHide{
\begin{code}
  data C : Set where
\end{code}
}

\begin{code}

  data Nat : Set where
    zero : Nat
    suc : Nat → Nat

  record Stream (A : Set) : Set where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream

  repeat : {A : Set} (a : A) -> Stream A
  head (repeat a) = a
  tail (repeat a) = repeat a

  nats : Nat -> Stream Nat
  head (nats zero) = zero
  tail (nats zero) = nats zero
  head (nats (suc x)) = x
  tail (nats (suc x)) = nats x
\end{code}

\begin{code}
id : (let * = Set) (A : *) → A → A
id A x = x
\end{code}
