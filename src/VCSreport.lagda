\section{Вектора}

\AgdaHide{
\begin{code}
module VCSreport where

open import OXIj.BrutalDepTypes

module With-⋀-and-⋙ (A : Set) (eqA : (a b : A) → Dec (a ≡ b)) where

  open Data-Vec
  open ≡-Prop

\end{code}
}

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

Например, формы 
\begin{tikzpicture}\matrix 
{\vecfe & \vecff & \vecfe & \vecfe & \vecff \\};
\end{tikzpicture} 
и 
\begin{tikzpicture}\matrix 
{\vecfe & \vecfe & \vecff & \vecff & \vecfe \\};
\end{tikzpicture} 
совместны, а 
\begin{tikzpicture}\matrix 
{\vecfe & \vecff & \vecfe & \vecfe & \vecff \\};
\end{tikzpicture} и 
\begin{tikzpicture}\matrix 
{\vecfe & \vecfe & \vecff & \vecff & \vecff \\};
\end{tikzpicture}~--- нет.
    
\subsection{Патч}

Теперь определим \emph{патч}, индексированный только что опеределённой
формой так, чтобы он менял только элементы, стоящие на местах, на
которых в которых в форме стоит \AgdaInductiveConstructor{true}:

\begin{figure}
  \centering
  \begin{subfigure}{0.45\textwidth}
    \centering
    \begin{tikzpicture}[anchor=center]
      \matrix [draw=red]
      {\vecf & \vect{a}{b} & \vecf & \vecf       & \vect{z}{y} \\};
    \end{tikzpicture}
    \caption{Патч}
    \label{fig:vec-patch-example-patch}
  \end{subfigure}
  \begin{subfigure}{0.45\textwidth}
    \centering
    \begin{tikzpicture}
      \matrix
      {\vecfe & \vecff & \vecfe & \vecfe & \vecff \\};
    \end{tikzpicture}
    \caption{Его форма}
    \label{fig:vec-patch-example-form}
  \end{subfigure}
  \caption{Патч для вектора}
  \label{fig:vec-patch-example}
\end{figure}
  
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

На рисунке~\ref{fig:vec-patch-example-patch} изображён патч для
векторов длины пять, заменяющий $a$ на второй позиции на $b$, $z$ на
пятой~--- на $y$. На рисунке~\ref{fig:vec-patch-example-form}
изображена его форма: вторая и пятая позиции меняются.

\AgdaHide{
\subsection{TODO ??? Вложенность патчей}

\begin{code}
  data _⊂_ : ∀ {n} → Form n → Form n → Set where
    []⊂[] : [] ⊂ []
    ⊂⊤ : ∀ {n}{f₁ f₂ : Form n} → (b : Bool) → (b ∷ f₁) ⊂ (true ∷ f₂)
    ⊥⊂⊥ : ∀ {n}{f₁ f₂ : Form n} → (false ∷ f₁) ⊂ (false ∷ f₂)
\end{code}
}

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

Напишем функцию применения патча \AgdaBound{p} к вектору
\AgdaBound{x}. Функция принимает на вход патч \AgdaBound{p}, вектор
\AgdaBound{x} и доказательство того, что \AgdaBound{p} можно применить
к \AgdaBound{x}.

\begin{code}
  patch : ∀ {n}{f : Form n} → (p : Patch f) → (x : Vec A n) → p ⊏ x → Vec A n
\end{code}

Применение пустого патча к пустому вектору даёт пустой вектор.

\begin{code}
  patch O [] []⊏[] = []
\end{code}

Применение патча, не меняющего первый элемент.

\begin{code}
  patch (⊥∷ p) (x ∷ xs) (⊥⊏ .x p-xs) = x ∷ patch p xs p-xs
\end{code}

Применение патча, меняющего первый элемент.

\begin{code}
  patch (⟨ .f ⇒ t ⟩∷ p) (f ∷ xs) (⊤⊏ .f .t p-xs) = 
    t ∷ patch p xs p-xs
\end{code}

\subsection{Эквивалентность патчей}

Введём над патчами отношение \emph{эквивалентности}. Назовём патчи
эквивалентными, если:

\begin{itemize}
\item их можно применять к одним и тем же векторам;
\item при применении к одному и тому же вектору получается одно и то же.
\end{itemize}

\begin{code}
  _⟶_ : ∀ {n}{f₁ f₂ : Form n}
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  _⟶_ {n} p₁ p₂ = ∀ (x : Vec A n) 
    → (p₁-x : p₁ ⊏ x) → Σ (p₂ ⊏ x) (λ p₂-x → 
      (patch p₁ x p₁-x ≡ patch p₂ x p₂-x))
\end{code}
      
\begin{code}
  _⟷_ : ∀ {n}{f₁ f₂ : Form n}
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  p₁ ⟷ p₂ = (p₁ ⟶ p₂) ∧ (p₂ ⟶ p₁)
\end{code}

Для того, чтобы отношение $\approx$ было отношением эквивалентности,
нужно, чтобы оно было:

\begin{itemize}
\item рефлексивным: $a \approx a$;
\item симметричным: $a \approx b \to b \approx a$;
\item транзитивным: $(a \approx b) \wedge (b \approx c) \to (a \approx c)$.
\end{itemize}

Все эти три свойства можно доказать.

\AgdaHide{
\begin{code}
  module ⟷-equiv where
    ⟷-refl : ∀ {n}{f : Form n} → (p : Patch f)
      → p ⟷ p
    ⟷-refl p = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)

    ⟶-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
      → {p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
      → (p₁ ⟶ p₂) → (p₂ ⟶ p₃) → (p₁ ⟶ p₃)
    ⟶-trans {p₁ = p₁}{p₂}{p₃} p₁⟶p₂ p₂⟶p₃ x p₁⊏x 
      with patch p₁ x p₁⊏x | p₁⟶p₂ x p₁⊏x
    ... | .(patch p₂ x p₂⊏x) | p₂⊏x , refl = p₂⟶p₃ x p₂⊏x
  
    ⟷-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
      → {p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
      → (p₁ ⟷ p₂) → (p₂ ⟷ p₃) → (p₁ ⟷ p₃)
    ⟷-trans (p₁⟶p₂ , p₂⟶p₁) (p₂⟶p₃ , p₃⟶p₂) = 
      (⟶-trans p₁⟶p₂ p₂⟶p₃) , (⟶-trans p₃⟶p₂ p₂⟶p₁)
      
    ⟷-symm : ∀ {n}{f₁ f₂ : Form n}
      → {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (p₁ ⟷ p₂) → (p₂ ⟷ p₁)
    ⟷-symm p₁⟷p₂ = snd p₁⟷p₂ , fst p₁⟷p₂

  open ⟷-equiv
\end{code}
}

TODO неправильное определение ⟷.

\subsection{Объединение неконфликтующих патчей}

Введём функцию, строяющую по двум совместным формам их объединение.
Эта функция просто будет считать поэлементное <<или>> двух форм.
Например, 
\begin{tikzpicture}\matrix 
{\vecfe & \vecff & \vecfe & \vecfe & \vecff \\};
\end{tikzpicture} \AgdaFunction{∧ₛ}
\begin{tikzpicture}\matrix 
{\vecfe & \vecfe & \vecff & \vecff & \vecfe \\};
\end{tikzpicture} \AgdaFunction{≡}
\begin{tikzpicture}\matrix 
{\vecfe & \vecff & \vecff & \vecff & \vecff \\};
\end{tikzpicture}

\begin{code}
  _∧ₛ_ : ∀ {n} (f₁ f₂ : Form n) → f₁ ∥ f₂ → Form n
  _∧ₛ_ [] [] []∥[] = []
  _∧ₛ_ (.false ∷ xs) (.false ∷ ys) (⊥∥⊥ p) = false ∷ (xs ∧ₛ ys) p
  _∧ₛ_ (.true ∷ xs) (.false ∷ ys) (⊤∥⊥ p) = true ∷ (xs ∧ₛ ys) p
  _∧ₛ_ (.false ∷ xs) (.true ∷ ys) (⊥∥⊤ p) = true ∷ (xs ∧ₛ ys) p

  unite : ∀ {n} {f₁ f₂ : Form n} → f₁ ∥ f₂ → Form n
  unite {n} {f₁} {f₂} p = (f₁ ∧ₛ f₂) p
\end{code}

На основе этой функции определим функцию, которая по двум патчам с
совместными формами построит их объединение. Патч-объединение будет
изменять значение на позиции, если хотя бы в одном из объединяемых
патчей изменение на этой позиции было. Пример использования
\AgdaFunction{\_∧ₚ\_} изображён на
рисунке~\ref{fig:vec-merge-nonconflict}.

\begin{code}
  _∧ₚ_ : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → (f₁∥f₂ : f₁ ∥ f₂) → Patch (unite f₁∥f₂)    
  _∧ₚ_ O O []∥[] = O
  _∧ₚ_ (⊥∷ p₁) (⊥∷ p₂) (⊥∥⊥ f₁∥f₂) = ⊥∷ ((p₁ ∧ₚ p₂) f₁∥f₂)
  _∧ₚ_ (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) (⊥∥⊤ f₁∥f₂) = 
    ⟨ from ⇒ to ⟩∷ (p₁ ∧ₚ p₂) f₁∥f₂
  _∧ₚ_ (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊤∥⊥ f₁∥f₂) = 
    ⟨ from ⇒ to ⟩∷ (p₁ ∧ₚ p₂) f₁∥f₂
\end{code}

\begin{figure}
  \centering
  \begin{tikzpicture}
    \matrix [draw=red] (lhs)
    {\vecf & \vect{a}{b} & \vecf & \vecf       & \vect{z}{b} \\};
  
    \node [vecpatch-op, right=0 of lhs] {$\wedge$};

    \matrix [draw=red, below=3mm of lhs] (rhs)
    {\vecf & \vecf       & \vecf & \vect{x}{x} & \vecf \\};

    \node [vecpatch-op, left=0 of rhs] {$\wedge$};
    \node [vecpatch-op, right=0 of rhs] {$=$};
  
    \matrix [draw=red, below=3mm of rhs] (res)
    {\vecf & \vect{a}{b} & \vecf & \vect{x}{x} & \vect{z}{b} \\};
  
    \node [vecpatch-op, left=0 of res] {$=$};
  \end{tikzpicture}

  \caption{Неконфликтующее объединение векторов}
  \label{fig:vec-merge-nonconflict}
\end{figure}

\AgdaHide{
\begin{code}
  ⟶-prepend-⊥⊥ : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → (p₁ ⟶ p₂) → (⊥∷ p₁ ⟶ ⊥∷ p₂)
  ⟶-prepend-⊥⊥ {p₁ = p₁}{p₂} p₁⟶p₂ (x ∷ xs) (⊥⊏ .x p₁⊏xs) 
    with patch p₁ xs p₁⊏xs | p₁⟶p₂ xs p₁⊏xs
  ... | .(patch p₂ xs p₂⊏xs) | p₂⊏xs , refl = (⊥⊏ x p₂⊏xs) , refl
  
  ⟶-prepend-⊤⊤ : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → (from to : A)
    → (p₁ ⟶ p₂) → (⟨ from ⇒ to ⟩∷ p₁ ⟶ ⟨ from ⇒ to ⟩∷ p₂)
  ⟶-prepend-⊤⊤ {p₁ = p₁}{p₂} .x to p₁⟷p₂ (x ∷ xs) (⊤⊏ .x .to p₁⊏xs) 
    with patch p₁ xs p₁⊏xs | p₁⟷p₂ xs p₁⊏xs 
  ... | .(patch p₂ xs p₂⊏xs) | p₂⊏xs , refl = ⊤⊏ x to p₂⊏xs , refl
\end{code}
}

\AgdaHide{
\begin{code}
  module ⟷-∧-lemmas where
\end{code}
}

Коммутативность отношения совместности форм. Доказательство по
индукции по структуре доказательства \AgdaBound{f₁} \AgdaFunction{∥}
\AgdaBound{f₂}.

\begin{code} 
    ∥-comm : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → f₂ ∥ f₁
\end{code}

\AgdaHide{
\begin{code}
    ∥-comm []∥[] = []∥[]
    ∥-comm (⊥∥⊥ f₁∥f₂) = ⊥∥⊥ (∥-comm f₁∥f₂)
    ∥-comm (⊤∥⊥ f₁∥f₂) = ⊥∥⊤ (∥-comm f₁∥f₂)
    ∥-comm (⊥∥⊤ f₁∥f₂) = ⊤∥⊥ (∥-comm f₁∥f₂)
\end{code}
}

Если есть три попарно совместных формы, то объединение первых двух
совместно с третьей. Доказательство по индукции по доказательствам
попарной совместности.

\begin{code}
    lemma-∥-unite : ∀ {n}{f₁ f₂ f₃ : Form n} 
      → (f₁∥f₂ : f₁ ∥ f₂) → f₂ ∥ f₃ → f₁ ∥ f₃
      → unite f₁∥f₂ ∥ f₃
\end{code}

\AgdaHide{
\begin{code}
    lemma-∥-unite []∥[] []∥[] []∥[] = []∥[]
    lemma-∥-unite (⊥∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) = 
      ⊥∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊥∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) (⊥∥⊤ f₁∥f₃) = 
      ⊥∥⊤ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊤∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊤∥⊥ f₁∥f₃) = 
      ⊤∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊥∥⊤ f₁∥f₂) (⊤∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) = 
      ⊤∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
\end{code}
}

Коммутативность операции объединения неконфликтующих патчей. 
Получающиеся при обмене аргументов местами патчи эквивалентны.

\begin{code}    
    ∧-comm : ∀ {n}{f₁ f₂ : Form n}
      → (f₁∥f₂ : f₁ ∥ f₂)
      → (p₁ : Patch f₁) → (p₂ : Patch f₂)
      → ((p₁ ∧ₚ p₂) f₁∥f₂) ⟷ ((p₂ ∧ₚ p₁) (∥-comm f₁∥f₂))
\end{code}

\AgdaHide{
\begin{code}
    ∧-comm []∥[] O O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-comm (⊥∥⊥ f₁∥f₂) (⊥∷ p₁) (⊥∷ p₂) =
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-comm f₁∥f₂ p₁ p₂
    ∧-comm (⊤∥⊥ f₁∥f₂) (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) =
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-comm f₁∥f₂ p₁ p₂
    ∧-comm (⊥∥⊤ f₁∥f₂) (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-comm f₁∥f₂ p₁ p₂
\end{code}
}

Транзитивность. Если три патча попарно не конфликтуют, то неважно, в 
каком порядке их применять. 

\begin{code}
    ∧-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
      → (f₁∥f₂ : f₁ ∥ f₂) → (f₂∥f₃ : f₂ ∥ f₃) → (f₁∥f₃ : f₁ ∥ f₃)
      → (p₁ : Patch f₁) → (p₂ : Patch f₂) → (p₃ : Patch f₃)
      → ((p₁ ∧ₚ p₂) f₁∥f₂ ∧ₚ p₃) (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
        ⟷ 
        (p₁ ∧ₚ (p₂ ∧ₚ p₃) f₂∥f₃) 
          (∥-comm (lemma-∥-unite f₂∥f₃ (∥-comm f₁∥f₃) (∥-comm f₁∥f₂)))
\end{code}

\AgdaHide{
\begin{code}          
    ∧-trans []∥[] []∥[] []∥[] O O O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-trans (⊥∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊥∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) (⊥∥⊤ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) (⟨ from ⇒ to ⟩∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊤∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊤∥⊥ f₁∥f₃) (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where 
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊤∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) () p₁ p₂ p₃
    ∧-trans (⊥∥⊤ f₁∥f₂) (⊤∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where 
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
\end{code}
}


\subsection{Объединение конфликтующих патчей}

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


Как уже оговаривалось выше, при конфликтующем объединении патчей
считается, что второй патч меняет только то, что уже изменил первый.
Напишем функцию, которая последовательно применяет два патча,
обладающие таким свойством. Пример использования изображён на 
рисунке~\ref{fig:vec-merge-conflict}.

\begin{code}
  _⋙ₚ_ : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → (p₁ ⋙? p₂) → Patch f₁
  _⋙ₚ_ O O O⋙?O = O
  _⋙ₚ_ (⊥∷ p₁) (⊥∷ p₂) (⊥⋙?⊥ p₁-p₂) = ⊥∷ ((p₁ ⋙ₚ p₂) p₁-p₂)
  _⋙ₚ_ (⟨ a ⇒ b ⟩∷ p₁) (⊥∷ p₂) (⊤⋙?⊥ .a .b p₁-p₂) = 
    ⟨ a ⇒ b ⟩∷ ((p₁ ⋙ₚ p₂) p₁-p₂)
  _⋙ₚ_ (⟨ a ⇒ .b ⟩∷ p₁) (⟨ b ⇒ c ⟩∷ p₂) (⊤⋙?⊤ .a .b .c p₁-p₂) = 
    ⟨ a ⇒ c ⟩∷ ((p₁ ⋙ₚ p₂) p₁-p₂)
\end{code}

\begin{figure}
  \centering
  \begin{tikzpicture}
    \matrix [draw=red] (lhs)
    {\vecf & \vect{a}{b} & \vect{x}{y} & \vecf & \vect{z}{y} \\};

    \node [vecpatch-op, right=0 of lhs] {$\ggg$};

    \matrix [draw=red, below=3mm of lhs] (rhs)
    {\vecf & \vect{b}{c} & \vecf       & \vecf & \vect{y}{x} \\};

    \node [vecpatch-op, left=0 of rhs] {$\ggg$};
    \node [vecpatch-op, right=0 of rhs] {$=$};
          
    \matrix [draw=red, below=3mm of rhs] (res)
    {\vecf & \vect{a}{c} & \vect{x}{y} & \vecf & \vect{z}{x} \\};
          
    \node [vecpatch-op, left=0 of res] {$=$};
  \end{tikzpicture}
  \caption{Конфликтующее объединение векторов}
  \label{fig:vec-merge-conflict}
\end{figure}

\AgdaHide{
\begin{code}
  module ⟷-⋙-lemmas where
\end{code}
}
    
ТУТ МОДНАЯ КАРТИНКА, ОПИСЫВАЮЩАЯ ЭТО СВОЙСТВО

\begin{code}
    ∧-⋙-lem : ∀ {n} {fᵃ fᵇ fᶜ' fᶜ'' : Form n}
      (c' : Patch fᶜ')(c'' : Patch fᶜ'')
      (a : Patch fᵃ)(b : Patch fᵇ)
      (c'∥c'' : fᶜ' ∥ fᶜ'') 
      (a∥b : fᵃ ∥ fᵇ)
      (a∧b>>>?c : (a ∧ₚ b) a∥b ⋙? ((c' ∧ₚ c'') c'∥c''))
      (a>>>?c' : a ⋙? c')
      (b>>>?c'' : b ⋙? c'')
      → (((a ∧ₚ b) a∥b) ⋙ₚ ((c' ∧ₚ c'') c'∥c'')) a∧b>>>?c 
        ⟷ ((a ⋙ₚ c') a>>>?c' ∧ₚ (b ⋙ₚ c'') b>>>?c'') a∥b
\end{code}

\AgdaHide{
\begin{code}
    ∧-⋙-lem O O O O []∥[] []∥[] O⋙?O O⋙?O O⋙?O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊥ a∥b) (⊥⋙?⊥ a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊥⋙?⊥ b⋙c'') = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⟨ from ⇒ to ⟩∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊤ a∥b) (⊤⋙?⊥ .from .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊥ .from .to b⋙c'') = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⟨ from ⇒ to ⟩∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊤∥⊥ a∥b) (⊤⋙?⊥ .from .to a∧b⋙?c) (⊤⋙?⊥ .from .to a⋙?c') (⊥⋙?⊥ b⋙c'') =
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⟨ from ⇒ to ⟩∷ c'') (⊥∷ a) (⟨ from₁ ⇒ .from ⟩∷ b) (⊥∥⊤ c'∥c'') (⊥∥⊤ a∥b) (⊤⋙?⊤ .from₁ .from .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊤ .from₁ .from .to b⋙c'') = 
      (⟶-prepend-⊤⊤ from₁ to (fst p)) , ⟶-prepend-⊤⊤ from₁ to (snd p) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⊥∷ c'') (⟨ from₁ ⇒ .from ⟩∷ a) (⊥∷ b) (⊤∥⊥ c'∥c'') (⊤∥⊥ a∥b) (⊤⋙?⊤ .from₁ .from .to a∧b⋙?c) (⊤⋙?⊤ .from₁ .from .to a⋙?c') (⊥⋙?⊥ b⋙c'') =
      (⟶-prepend-⊤⊤ from₁ to (fst p)) , ⟶-prepend-⊤⊤ from₁ to (snd p) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
\end{code}
}

Ассоциативность \AgdaFunction{\_⋙\_}.

\begin{code}
    ⋙-assoc : ∀ {n}{f₁ f₂ f₃ : Form n}{p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
      → (p₁>>?p₂ : p₁ ⋙? p₂)
      → ([p₁>>ₚp₂]>>?p₃ : (p₁ ⋙ₚ p₂) p₁>>?p₂ ⋙? p₃)
      → (p₂>>?p₃ : p₂ ⋙? p₃)
      → (p₁>>?[p₂>>ₚp₃] : p₁ ⋙? (p₂ ⋙ₚ p₃) p₂>>?p₃)
      → (((p₁ ⋙ₚ p₂) p₁>>?p₂) ⋙ₚ p₃) [p₁>>ₚp₂]>>?p₃
        ⟷
        (p₁ ⋙ₚ (p₂ ⋙ₚ p₃) p₂>>?p₃) p₁>>?[p₂>>ₚp₃]
\end{code}

\AgdaHide{
\begin{code}        
    ⋙-assoc O⋙?O O⋙?O O⋙?O O⋙?O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ⋙-assoc (⊥⋙?⊥ p₁⋙?p₂) (⊥⋙?⊥ [p₁⋙p₂]⋙?p₃) (⊥⋙?⊥ p₂⋙?p₃) (⊥⋙?⊥ p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]
    ⋙-assoc (⊤⋙?⊥ from to p₁⋙?p₂) (⊤⋙?⊥ .from .to [p₁⋙p₂]⋙?p₃) (⊥⋙?⊥ p₂⋙?p₃) (⊤⋙?⊥ .from .to p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , ⟶-prepend-⊤⊤ from to (snd p) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]
    ⋙-assoc (⊤⋙?⊤ from to to₂ p₁⋙?p₂) (⊤⋙?⊥ .from .to₂ [p₁⋙p₂]⋙?p₃) (⊤⋙?⊥ .to .to₂ p₂⋙?p₃) (⊤⋙?⊤ .from .to .to₂ p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊤⊤ from to₂ (fst p)) , ⟶-prepend-⊤⊤ from to₂ (snd p) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]
    ⋙-assoc (⊤⋙?⊤ from to to₂ p₁⋙?p₂) (⊤⋙?⊤ .from .to₂ to₃ [p₁⋙p₂]⋙?p₃) (⊤⋙?⊤ .to .to₂ .to₃ p₂⋙?p₃) (⊤⋙?⊤ .from .to .to₃ p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊤⊤ from to₃ (fst p)) , ⟶-prepend-⊤⊤ from to₃ (snd p) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]
\end{code}
}

\AgdaHide{
\begin{code}
  drop : ∀ {n} (b₁ b₂ : Bool) (f₁ f₂ : Form n)
    → (b₁ ∷ f₁) ∥ (b₂ ∷ f₂) → f₁ ∥ f₂
  drop .false .false f₃ f₄ (⊥∥⊥ p) = p
  drop .true .false f₃ f₄ (⊤∥⊥ p) = p
  drop .false .true f₃ f₄ (⊥∥⊤ p) = p

  ∥-dec : ∀ {n} (f₁ f₂ : Form n) → Dec (f₁ ∥ f₂)
  ∥-dec [] [] = yes []∥[]
  ∥-dec (true ∷ f₁) (true ∷ f₂) = no (no-tt f₁ f₂) where
    no-tt : ∀ {n} (f₁ f₂ : Form n) → ¬ ((true ∷ f₁) ∥ (true ∷ f₂))
    no-tt _ _ ()
  ∥-dec (true ∷ f₁) (false ∷ f₂) with ∥-dec f₁ f₂
  ... | yes a = yes (⊤∥⊥ a)
  ... | no ¬a = no (¬a ∘ drop true false f₁ f₂) where
  ∥-dec (false ∷ f₁) (true ∷ f₂) with ∥-dec f₁ f₂
  ... | yes a = yes (⊥∥⊤ a)
  ... | no ¬a = no (¬a ∘ drop false true f₁ f₂)
  ∥-dec (false ∷ f₁) (false ∷ f₂) with ∥-dec f₁ f₂
  ... | yes a = yes (⊥∥⊥ a)
  ... | no ¬a = no (¬a ∘ drop false false f₁ f₂)
  
  ⋙?-dec : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → Dec (p₁ ⋙? p₂)
  ⋙?-dec O O = yes O⋙?O
  ⋙?-dec (⊥∷ p₁) (⊥∷ p₂) with ⋙?-dec p₁ p₂ 
  ... | yes a = yes (⊥⋙?⊥ a)
  ... | no ¬a = no (¬a ∘ ⊥⊥-drop) where
    ⊥⊥-drop : ⊥∷ p₁ ⋙? ⊥∷ p₂ → p₁ ⋙? p₂
    ⊥⊥-drop (⊥⋙?⊥ p) = p
  ⋙?-dec (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) = no fail where
    fail : ⊥∷ p₁ ⋙? (⟨ from ⇒ to ⟩∷ p₂) → ⊥
    fail ()
  ⋙?-dec (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) with ⋙?-dec p₁ p₂
  ... | yes a = yes (⊤⋙?⊥ from to a)
  ... | no ¬a = no (¬a ∘ ⊤⊥-drop) where
    ⊤⊥-drop : ∀ {a b : A} → (⟨ a ⇒ b ⟩∷ p₁) ⋙? ⊥∷ p₂ → p₁ ⋙? p₂
    ⊤⊥-drop (⊤⋙?⊥ _ _ p) = p
  ⋙?-dec (⟨ from₁ ⇒ to₁ ⟩∷ p₁) (⟨ from₂ ⇒ to₂ ⟩∷ p₂) with ⋙?-dec p₁ p₂
  ... | yes a = cmp (eqA to₁ from₂) where
    cmp : Dec (to₁ ≡ from₂) 
      → Dec ((⟨ from₁ ⇒ to₁ ⟩∷ p₁) ⋙? (⟨ from₂ ⇒ to₂ ⟩∷ p₂))
    cmp (yes aa) rewrite aa = yes (⊤⋙?⊤ from₁ from₂ to₂ a)
    cmp (no ¬a) = no (¬a ∘ ends-eq) where
      ends-eq : ∀ {a b c d : A} → (⟨ a ⇒ b ⟩∷ p₁) ⋙? (⟨ c ⇒ d ⟩∷ p₂) → b ≡ c
      ends-eq (⊤⋙?⊤ a c d p) = refl
  ... | no ¬a = no (¬a ∘ ⊤⊤-drop) where
    ⊤⊤-drop : ∀ {a b c d} → (⟨ a ⇒ b ⟩∷ p₁) ⋙? (⟨ c ⇒ d ⟩∷ p₂) → p₁ ⋙? p₂
    ⊤⊤-drop (⊤⋙?⊤ _ _ _ p) = p
\end{code}
}
