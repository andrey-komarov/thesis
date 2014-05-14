
\AgdaHide{
\begin{code}
module VCSreport where

open import OXIj.BrutalDepTypes

module With-⋀-and-⋙ (A : Set) where

  open Data-Vec
  open ≡-Prop

\end{code}
}

\section{Вектора}

\subsection{Форма}

Построим систему контроля версий, в которой под контролем версий будут
находиться вектора длины \AgdaBound{n} элементов типа \AgdaBound{A}.
Патчи, соответственно, будут каким-то образом изменять эти вектора.
Определим для каждого патча его \emph{форму}: нечто, сообщающее,
\emph{что именно} будет менять патч в репозитории. В данном случае,
форма будет вектором булевых переменных такой же длины. Каждая
переменная отвечает за то, будет ли меняться соответствующий этой
позиции элемент:

\begin{code}
  Form : ℕ → Set
  Form = Vec Bool 
\end{code}

\subsection{Патч}

Теперь определим \emph{патч}, индексированный только что опеределённой
формой так, чтобы он менял только элементы, стоящие на местах, на
которых в которых в форме стоит \AgdaInductiveConstructor{true}:
  
\begin{code}
  data Patch : ∀ {n} → Form n → Set where
\end{code}

Патч, ничего не делающий с векторами нулевой длины.

\begin{code}
    O : Patch []
\end{code}

Имея патч, оперирующий векторами длины \AgdaBound{n}, можно получить
патч, оперирующий векторами длины \AgdaBound{n} $+ 1$, не меняющий
элемент на первой позиции и соответственно имеющемуся патчу меняющий
остальные.

\begin{code}
    ⊥∷ : ∀ {n}{f : Form n} → Patch f → Patch (false ∷ f)
\end{code}

Или же, можно сделать патч, ожидающий увидеть на первой позиции
\AgdaBound{from}, заменяющий \AgdaBound{from} на \AgdaBound{to} и
применяющий к хвосту вектора имеющийся патч.

\begin{code}
    ⟨_⇒_⟩∷_ : ∀ {n}{f : Form n}
      → (from to : A)
      → Patch f → Patch (true ∷ f)
\end{code}

\subsection{Совместные формы}

Определим для двух форм отношение \emph{совместности}. Две формы
называются \emph{совместными}, если два патча, обладающие этими
формами, никогда не будут \emph{конфликтовать}. Формально понятие
\emph{конфликтования} патчей будет введено позднее. На данный момент,
можно довериться интуитивному пониманию этого понятия.

\begin{code}
  data _∥_ : ∀ {n} → Form n → Form n → Set where
    []∥[] : [] ∥ []
    ⊥∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (false ∷ f₂)
    ⊤∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (true ∷ f₁) ∥ (false ∷ f₂)
    ⊥∥⊤ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (true ∷ f₂)
\end{code}

Здесь дано индуктивное опеределение совместности форм, которое гласит,
что пустые формы совместны, а непустые совместны, если первыми
элементами в них идут не два \AgdaInductiveConstructor{true}.
    
\subsection{TODO ??? Вложенность патчей}

\begin{code}
  data _⊂_ : ∀ {n} → Form n → Form n → Set where
    []⊂[] : [] ⊂ []
    ⊂⊤ : ∀ {n}{f₁ f₂ : Form n} → (b : Bool) → (b ∷ f₁) ⊂ (true ∷ f₂)
    ⊥⊂⊥ : ∀ {n}{f₁ f₂ : Form n} → (false ∷ f₁) ⊂ (false ∷ f₂)
\end{code}

\subsection{Возможность композиции конфликтующих патчей}

Введём для двух, возможно, конфликтующих, патчей отношение
\emph{возможности быть применёнными последовательно}. Разрешим второму
патчу менять только то, что уже поменял первый. 
    
\begin{code}
  data _⋙?_ : ∀ {n}{f₁ f₂ : Form n} → Patch f₁ → Patch f₂ → Set where  
\end{code}

Пустые патчи можно применять последовательно. 

\begin{code}
    O⋙?O : O ⋙? O
\end{code}

Оба патча не меняют первый элемент. 

\begin{code}
    ⊥⋙?⊥ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (p₁ ⋙? p₂) → (⊥∷ p₁) ⋙? (⊥∷ p₂)
\end{code}

Только первый патч меняет первый элемент.

\begin{code}
    ⊤⋙?⊥ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (from to : A) → (p₁ ⋙? p₂)
      → (⟨ from ⇒ to ⟩∷ p₁) ⋙? (⊥∷ p₂)
\end{code}

Оба патча меняют первый элемент.

\begin{code}
    ⊤⋙?⊤ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (from to to₂ : A) → (p₁ ⋙? p₂)
      → (⟨ from ⇒ to ⟩∷ p₁) ⋙? (⟨ to ⇒ to₂ ⟩∷ p₂)
\end{code}

\subsection{Возможность применения патча к вектору}
    
Определим для патча и вектора отношение <<\emph{можно применить к}>>.
Будем говорить, что патч \AgdaBound{p} можно применить к вектору
\AgdaBound{v}, если на тех местах вектора, где в форме у \AgdaBound{p}
указано \AgdaInductiveConstructor{true}, стоит то, что ожидает увидеть
патч.

\begin{code}
  data _⊏_ : ∀ {n}{f : Form n} → Patch f → Vec A n → Set where
\end{code}

Пустой патч можно применить к пустому вектору.

\begin{code}
    []⊏[] : O ⊏ []
\end{code}

Патч, не меняющий первый элемент, применить можно.

\begin{code}
    ⊥⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a : A) → p ⊏ v → (⊥∷ p) ⊏ (a ∷ v)
\end{code}

Патч, меняющий первый элемент можно применить только если первым
элементом вектора стоит ожидаемый патчем элемент.

\begin{code}
    ⊤⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a b : A)
      → p ⊏ v → (⟨ a ⇒ b ⟩∷ p) ⊏ (a ∷ v)
\end{code}
