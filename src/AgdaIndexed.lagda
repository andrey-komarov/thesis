\AgdaHide{
\begin{code}
module AgdaIndexed where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
  
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a
\end{code}
}

Помимо всего прочего, Agda предоставляет возможность заводить
\emph{индексированные} типы. Пример такого типа приведён ниже.

\begin{code}
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)
\end{code}

Здесь тип \AgdaDatatype{Vec} \emph{индексирован} натуральным
числом~(своей длиной). Перепишем эту же стуктуру, используя
вместо индексирования параметризацию:

\begin{code}
data Vec-ni (A : Set) (n : ℕ) : Set where
  []  : (n ≡ zero) → Vec-ni A n
  _∷_ : ∀ {k} → (n ≡ succ k) → A → Vec-ni A k → Vec-ni A n
\end{code}

Как видно, забота о корректности индексов была переложена с
компилятора на программиста: нужно самому следить, что то, что было
индексами, имеет нужную форму. Agda решает эти проблемы с помощью механизма \emph{унификации}.

