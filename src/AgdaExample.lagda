\AgdaHide{
\begin{code}
module AgdaExample where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{code}
}

В языке Agda возможно определение рекурсивных типов без явного
использования $\mu$- или $W$-типов:

\begin{code}
data ℕList : Set where
  [] : ℕList
  _∷_ : (head : ℕ) → (tail : ℕList) → ℕList
\end{code}

Здесь написано, что список натуральных чисел~--- это или пустой
список~(\AgdaInductiveConstructor{[]}),
либо~(\AgdaInductiveConstructor{\_∷\_}) пара из головы
списка~(натурального числа) и хвоста-списка.

Это определение можно обобщить до списка над произвольными типами:

\begin{code}
data List (A : Set) : Set where
  [] : List A
  _∷_ : (head : ℕ) → (tail : List A) → List A
\end{code}
