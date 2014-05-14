
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

\subsection{Применение патча}

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

\subsection{Объединение неконфликтующих патчей}

Введём функцию, строяющую по двум совместным формам их объединение.
Эта функция просто будет считать поэлементное <<или>> двух форм.

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
патчей изменение на этой позиции было.

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

\subsection{Объединение конфликтующих патчей}

Как уже оговаривалось выше, при конфликтующем объединении патчей
считается, что второй патч меняет только то, что уже изменил первый.
Напишем функцию, которая последовательно применяет два патча,
обладающие таким свойством.

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

    
  module ⟷₂-∧-lemmas where
    ∥-comm : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → f₂ ∥ f₁
    ∥-comm []∥[] = []∥[]
    ∥-comm (⊥∥⊥ f₁∥f₂) = ⊥∥⊥ (∥-comm f₁∥f₂)
    ∥-comm (⊤∥⊥ f₁∥f₂) = ⊥∥⊤ (∥-comm f₁∥f₂)
    ∥-comm (⊥∥⊤ f₁∥f₂) = ⊤∥⊥ (∥-comm f₁∥f₂)

    lemma-∥-unite : ∀ {n}{f₁ f₂ f₃ : Form n} 
      → (f₁∥f₂ : f₁ ∥ f₂) → f₂ ∥ f₃ → f₁ ∥ f₃
      → unite f₁∥f₂ ∥ f₃
    lemma-∥-unite []∥[] []∥[] []∥[] = []∥[]
    lemma-∥-unite (⊥∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) = 
      ⊥∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊥∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) (⊥∥⊤ f₁∥f₃) = 
      ⊥∥⊤ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊤∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊤∥⊥ f₁∥f₃) = 
      ⊤∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊥∥⊤ f₁∥f₂) (⊤∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) = 
      ⊤∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    
    ∧-comm : ∀ {n}{f₁ f₂ : Form n}
      → (f₁∥f₂ : f₁ ∥ f₂)
      → (p₁ : Patch f₁) → (p₂ : Patch f₂)
      → ((p₁ ∧ₚ p₂) f₁∥f₂) ⟷ ((p₂ ∧ₚ p₁) (∥-comm f₁∥f₂))
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
    
    ∧-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
      → (f₁∥f₂ : f₁ ∥ f₂) → (f₂∥f₃ : f₂ ∥ f₃) → (f₁∥f₃ : f₁ ∥ f₃)
      → (p₁ : Patch f₁) → (p₂ : Patch f₂) → (p₃ : Patch f₃)
      → ((p₁ ∧ₚ p₂) f₁∥f₂ ∧ₚ p₃) (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
        ⟷ 
        (p₁ ∧ₚ (p₂ ∧ₚ p₃) f₂∥f₃) 
          (∥-comm (lemma-∥-unite f₂∥f₃ (∥-comm f₁∥f₃) (∥-comm f₁∥f₂)))
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
