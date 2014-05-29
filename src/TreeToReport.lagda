\section{Деревья}

\AgdaHide{
\begin{code}
module TreeToReport where

open import OXIj.BrutalDepTypes

open ≡-Prop

postulate A : Set

\end{code}
}

В этой части будет рассмотрен второй вид ревизии~--- двоичные
деревья~(рисунок~\ref{fig:repotypes-tree}).

Дадим классическое определение двоичного дерева: дерево это либо лист,
который хранит какое-то значение, либо левое и правое поддеревья.

\begin{code}
data Tree : Set where
  Leaf : (val : A) → Tree
  Branch : (left right : Tree) → Tree
\end{code}
  
\subsection{Форма}

Возьмём в качестве \emph{формы} патчей двоичное дерево, в листьях
которого стоит либо метка \AgdaInductiveConstructor{Take}, означающая,
что эта вершина вместе со всем её поддеревом будет заменена патчем,
либо метка \AgdaInductiveConstructor{Skip}, означающая, что патч будет
игнорировать эту вершину и никак на неё не повлияет.

\begin{code}
data Form : Set where
  Take : Form
  Skip : Form
  Branch : (left right : Form) → Form
\end{code}

Естесственным образом вводится опеределение совместности таких форм.
Формы совместны, если:

\begin{code}
data _∥_ : Form → Form → Set where
\end{code}

В корне первой стоит метка \AgdaInductiveConstructor{Skip}

\begin{code}
  ∅∥✴ : (s : Form) → Skip ∥ s
\end{code}

Либо, в корне второй стоит метка \AgdaInductiveConstructor{Skip}

\begin{code}
  ✴∥∅ : (s : Form) → s ∥ Skip
\end{code}

Либо, рассматриваемые формы не являются листьями и их соответствующие
поддеревья совместны

\begin{code}
  Branch-∥ : ∀ {L1 R1 L2 R2 : Form} → L1 ∥ L2 → R1 ∥ R2 
    → Branch L1 R1 ∥ Branch L2 R2
\end{code}
    
\subsection{Патч}

Определим патч аналогично тому, как это делалось в случае с векторами.
Патч может:

\begin{code}
data Patch : Form → Set where
\end{code}

Ничего не менять

\begin{code}
  I : Patch Skip
\end{code}

Либо, заменить какое-то поддерево на другое поддерево

\begin{code}
  ⟨_⇒_⟩ : (from to : Tree) → Patch Take
\end{code}

Либо, что-то сделать в поддеревьях

\begin{code}
  ⟨_∧_⟩ : ∀ {sl sr : Form} → (left : Patch sl) (right : Patch sr)
    → Patch (Branch sl sr)
\end{code}

\begin{figure}
  \centering
  \begin{subfigure}[b]{0.65\textwidth}
    \centering
    \begin{tikzpicture}
      \node[treev,font=\small] (from) {a}
      child {node[treev,font=\small,yshift=7mm] {b}
      }
      child[missing] {}
      ;
      \node[fit=(from)(from-1),inner sep=0,outer sep=0] (whole from) {};

      \node[treev,font=\small, right=4mm of from] (to) {c}
      child[missing] {}
      child {node[treev,font=\small,yshift=7mm] {d}     
      }
      ;
      \node[fit=(to)(to-2),inner sep=0,outer sep=0] (whole to){};
      \path[treearr] (whole from) -- (whole to); 

      \node[outer sep=0,fit=(whole from)(whole to),draw=black] (patch){};
      \begin{pgfonlayer}{background}
        \node [fill=yellow,fit=(whole from)(whole to)] {};
      \end{pgfonlayer}
      
      \node[treev,font=\small,above right=of patch] (tt) {};
      \path[treearr] (tt) -- (patch);
      
      \node[treev,font=\small,below right=of tt] (tr) {};
      \path[treearr] (tt) -- (tr);
      
      \node[treev,font=\small,below left=of tr] (from2) {e};
      \node[right=4mm of from2] (to2) {$\varepsilon$};
      \path[treearr] (from2) -- (to2);

      \node[outer sep=0,fit=(from2)(to2),draw=black] (patch2){};
      \begin{pgfonlayer}{background}
        \node [fill=yellow,fit=(from2)(to2)] {};
      \end{pgfonlayer}
      
      \path[treearr] (tr) -- (patch2);
      
      \node[below right=of tr,xshift=-7mm,yshift=2.5mm] (trr) {};
      \path[treearr] (tr) -- (trr);
    \end{tikzpicture}
    \caption{Патч для дерева}
  \end{subfigure}
  \begin{subfigure}[b]{0.3\textwidth}
    \centering
    \begin{tikzpicture}
      \node[treev] {}
      child[treearr] {node[treev,fill=patchform] {}
      }
      child[treearr] {node[treev] {}
        child[treearr] {node[treev,fill=patchform] {}
        }
        child[treearr] {node[treev,fill=green] {}
        }
      }
      ;
    \end{tikzpicture}
    \caption{Его форма}
  \end{subfigure}
  \caption{Пример патча для дерева}
  \label{fig:tree-patch-example}
\end{figure}

Пример патча и его формы можно видеть на
рисунке~\ref{fig:tree-patch-example}.
    
Основное отличие от патча над векторами заключается в том, что здесь
может меняться размер структуры: в векторе один символ всегда
заменялся на один символ. Здесь же поддерево произвольного размера
заменяется также на поддерево произвольного размера.

Когда заданный патч может быть применён к заданному дереву?

\begin{code}
data _⊏_ : ∀ {s : Form} → Patch s → Tree → Set where
\end{code}

Пустой патч можно применить всегда.

\begin{code}
  ⊏-I : (t : Tree) → I ⊏ t
\end{code}

Патч, меняющий дерево на другое, можно применить только к заменяемому
дереву.

\begin{code}
  ⊏-⇒ : (from to : Tree) → ⟨ from ⇒ to ⟩ ⊏ from
\end{code}

Если патчи применимы к поддеревьям, то из них можно собрать патч,
применимый к целому дереву.

\begin{code}
  ⊏-∧ : {sl sr : Form} {pl : Patch sl} {pr : Patch sr} {tl tr : Tree}
    → pl ⊏ tl → pr ⊏ tr → ⟨ pl ∧ pr ⟩ ⊏ Branch tl tr
\end{code}

Напишем функцию применения патча. Она принимает патч, дерево и 
доказательство того, что этот патч можно применить.

\begin{code}
patch : {s : Form} → (p : Patch s) → (t : Tree) → p ⊏ t → Tree
\end{code}

Применение пустого патча ничего не делает.

\begin{code}
patch I t (⊏-I .t) = t
\end{code}

Замена дерева заменяет дерево. % (!)

\begin{code}
patch ⟨ .t ⇒ to ⟩ t (⊏-⇒ .t .to) = to
\end{code}

Применить под-патчи к поддеревьям.

\begin{code}
patch ⟨ pl ∧ pr ⟩ (Branch tl tr) (⊏-∧ l-a r-a) = 
  Branch (patch pl tl l-a) (patch pr tr r-a)
\end{code}

\subsection{Эквивалентность патчей}

Будем называть два патча эквивалентными, если области определения у
них совпадают и на этой общей области определения их применение даёт
один и тот же результат. Прежде чем вводить, Непосредственно,
Эквивалентность, введём отношение, которое можно назвать \emph{не
хуже, чем}:

\begin{code}
_⟶_ : ∀ {s₁ s₂ : Form}
  → (p₁ : Patch s₁) → (p₂ : Patch s₂) → Set
_⟶_ {n} p₁ p₂ = ∀ {x : Tree}
  → (p₁-x : p₁ ⊏ x) → Σ (p₂ ⊏ x) (λ p₂-x → 
    (patch p₁ x p₁-x ≡ patch p₂ x p₂-x))
\end{code}

\AgdaBound{p₁} \AgdaFunction{⋀} \AgdaBound{p₂}: область определения
\AgdaBound{p₂} является надмножеством области определения
\AgdaBound{p₂} и на общей области определения результаты применения
патча совпадают.

Определим эквивалентность как взаимовложенность областей определения
и равенство на общей области опеределения.

\begin{code}
_⟷_ : ∀ {f₁ f₂ : Form}
  → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
p₁ ⟷ p₂ = (p₁ ⟶ p₂) ∧ (p₂ ⟶ p₁)
\end{code}

Стоит обратить внимание, что следующее определение, несмотря на то,
что кажется корректным, таковым не является: отсутствует гарантия, что
области определения патчей совпадают.

\begin{code}
_⟷-bad_ : ∀ {s₁ s₂ : Form} 
  → (p₁ : Patch s₁) → (p₂ : Patch s₂) → Set
p₁ ⟷-bad p₂ = ∀ (x : Tree) → (p₁⊏x : p₁ ⊏ x) → (p₂⊏x : p₂ ⊏ x) 
  → patch p₁ x p₁⊏x ≡ patch p₂ x p₂⊏x
\end{code}

Например, согласно этому неправильному определению будут эквивалентны:

\begin{code}
⟷-bad-test : ∀ {a b c d} → a ≠ c → ⟨ a ⇒ b ⟩ ⟷-bad ⟨ c ⇒ d ⟩
⟷-bad-test a≠c a (⊏-⇒ .a _) (⊏-⇒ .a _) = ⊥-elim (a≠c refl)
\end{code}

\begin{code}
⟷-refl : ∀ {s : Form} (p : Patch s) → p ⟷ p
⟷-refl p = (λ x → x , refl) , (λ x → x , refl)

⟷-comm : ∀ {s₁ s₂} {p₁ : Patch s₁} {p₂ : Patch s₂}
  → (p₁ ⟷ p₂) → (p₂ ⟷ p₁)
⟷-comm (1⟶2 , 2⟶1) = (2⟶1 , 1⟶2)

⟶-trans : {s₁ s₂ s₃ : Form} {p₁ : Patch s₁}{p₂ : Patch s₂}{p₃ : Patch s₃}
  → (p₁ ⟶ p₂) → (p₂ ⟶ p₃) → (p₁ ⟶ p₃)
⟶-trans {p₁ = p₁}{p₂}{p₃} 1⟶2 2⟶3 {x} p⊏x 
  with patch p₁ x p⊏x | 1⟶2 p⊏x 
... | ._ | p₂⊏x , refl = 2⟶3 p₂⊏x

⟷-trans : {s₁ s₂ s₃ : Form} {p₁ : Patch s₁}{p₂ : Patch s₂}{p₃ : Patch s₃}
  → (p₁ ⟷ p₂) → (p₂ ⟷ p₃) → (p₁ ⟷ p₃)
⟷-trans (1⟶2 , 2⟶1) (2⟶3 , 3⟶2) = 
  (⟶-trans 1⟶2 2⟶3) , (⟶-trans 3⟶2 2⟶1)

⟶-branch : ∀ {L1 L2 R1 R2 : Form}
  → {l₁ : Patch L1} {l₂ : Patch L2} {r₁ : Patch R1} {r₂ : Patch R2}
  → (l₁ ⟶ l₂) → (r₁ ⟶ r₂) → ⟨ l₁ ∧ r₁ ⟩ ⟶ ⟨ l₂ ∧ r₂ ⟩
⟶-branch {l₁ = l₁}{l₂}{r₁}{r₂} l₁⟶l₂ r₁⟶r₂ (⊏-∧ {tl = tl}{tr} l⊏L r⊏R) 
  with patch l₁ tl l⊏L | l₁⟶l₂ l⊏L 
    | patch r₁ tr r⊏R | r₁⟶r₂ r⊏R
... | ._ | l₂⊏L , refl | ._ | r₂⊏R , refl = 
  ⊏-∧ l₂⊏L r₂⊏R , refl

⟷-branch : ∀ {L1 L2 R1 R2 : Form}
  → {l₁ : Patch L1} {l₂ : Patch L2} {r₁ : Patch R1} {r₂ : Patch R2}
  → (l₁ ⟷ l₂) → (r₁ ⟷ r₂) → ⟨ l₁ ∧ r₁ ⟩ ⟷ ⟨ l₂ ∧ r₂ ⟩
⟷-branch (l₁⟶l₂ , l₂⟶l₁) (r₁⟶r₂ , r₂⟶r₁) = 
  (⟶-branch l₁⟶l₂ r₁⟶r₂) , (⟶-branch l₂⟶l₁ r₂⟶r₁)
\end{code}



\subsection{Объединение неконфликтующих патчей}

\begin{figure}
  \centering
    \begin{tikzpicture}
      [level distance=1cm]
      \node[treev] (lhsr) {}
      child[treearr] {node[treev] {}
        child[treearr] {node[rectangle, minimum height=1cm] {}
        }
        child[treearr] {node[fill=yellow,rectangle,draw=black] {$A \to B$}
        }
      }
      child[treearr] {node[rectangle, minimum height=1cm] {}
      };
      \node[fit=(lhsr)(lhsr-1)(lhsr-1-1)(lhsr-1-2)(lhsr-2)] (lhs) {};

      \node[right=0 of lhs,font=\Huge] (and) {$\wedge$};

      \node[treev, right=2cm of lhsr] (rhsr) {}
      child[treearr] {node[rectangle, minimum height=1cm] {}
      }
      child[treearr] {node[fill=yellow,rectangle,draw=black] {$C \to D$}
      };
      \node[fit=(rhsr)(rhsr-1)(lhsr-2)] (rhs) {};

      \node[right=3.3cm of lhs,font=\Huge] (eq) {$=$};

      \node[treev, right=3.4cm of rhsr] (lhsr) {}
      child[treearr] {node[treev] {}
        child[treearr] {node[rectangle, minimum height=1cm] {}
        }
        child[treearr] {node[fill=yellow,rectangle,draw=black] {$A \to B$}
        }
      }
      child[treearr] {node[fill=yellow,rectangle,draw=black] {$C \to D$}
      };
    \end{tikzpicture}
  \caption{Неконфликтующее объединение патчей}
  \label{fig:tree-merge-nonconflict}
\end{figure}

Перед реализацией объединения понадобится несколько вспомогательных
функций. Объединение двух совместных форм:

\begin{code}
_^_ : (sl sr : Form) → sl ∥ sr → Form
_^_ .Skip sr (∅∥✴ .sr) = sr
_^_ sl .Skip (✴∥∅ .sl) = sl
_^_ (Branch L1 R1) (Branch L2 R2) (Branch-∥ pl pr) = 
  Branch ((L1 ^ L2) pl) ((R1 ^ R2) pr)
\end{code}

И её более удобная для использования копия:

\begin{code}
unite : {f₁ f₂ : Form} → f₁ ∥ f₂ → Form
unite {f₁} {f₂} p = (f₁ ^ f₂) p
\end{code}

Непосредственно, объеденение~(рисунок~\ref{fig:tree-merge-nonconflict}):

\begin{code}
_⋀_ : {s₁ s₂ : Form} (p₁ : Patch s₁) (p₂ : Patch s₂)
  → (s₁∥s₂ : s₁ ∥ s₂) → Patch (unite s₁∥s₂)
_⋀_ I I (∅∥✴ .Skip) = I
_⋀_ I I (✴∥∅ .Skip) = I
_⋀_ I ⟨ from ⇒ to ⟩ (∅∥✴ .Take) = ⟨ from ⇒ to ⟩
_⋀_ I (⟨_∧_⟩ {sl} {sr} pl pr) (∅∥✴ .(Branch sl sr)) = ⟨ pl ∧ pr ⟩
_⋀_ ⟨ from ⇒ to ⟩ I (✴∥∅ .Take) = ⟨ from ⇒ to ⟩
_⋀_ (⟨_∧_⟩ {sl} {sr} pl pr) I (✴∥∅ .(Branch sl sr)) = ⟨ pl ∧ pr ⟩
_⋀_ ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ (Branch-∥ s₁∥s₂ s₃∥s₄) = 
  ⟨ (p₁ ⋀ p₃) s₁∥s₂ ∧ (p₂ ⋀ p₄) s₃∥s₄ ⟩
\end{code}

Во всех случаях, кроме последнего, один из операндов равен
\AgdaInductiveConstructor{I}, поэтому в качестве ответа берётся другой
операнд. В последнем же случае делаются два рекурсивных запуска от 
пар левых и правых поддеревьев и результаты берутся как левое и правое
поддерево результата, соответственно.
  

\begin{code}
module ⋙-try2 where
  data _⋙?_ : {s₁ s₂ : Form} (p₁ : Patch s₁) (p₂ : Patch s₂) → Set where
    ✴⋙?I : ∀ {s : Form} (p : Patch s) → p ⋙? I
    Here-⋙? : ∀ (t₁ t₂ t₃ : Tree) → ⟨ t₁ ⇒ t₂ ⟩ ⋙? ⟨ t₂ ⇒ t₃ ⟩
    Branch-⋙? : ∀ {s₁ s₂ s₃ s₄} 
      → {p₁ : Patch s₁} {p₂ : Patch s₂} {p₃ : Patch s₃} {p₄ : Patch s₄}
      → (L : p₁ ⋙? p₂) → (R : p₃ ⋙? p₄) → ⟨ p₁ ∧ p₃ ⟩ ⋙? ⟨ p₂ ∧ p₄ ⟩
      
  ⋙?-uniq : ∀ {s₁ s₂ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂}
    → (?₁ ?₂ : p₁ ⋙? p₂) → ?₁ ≡ ?₂
  ⋙?-uniq (✴⋙?I p₁) (✴⋙?I .p₁) = refl
  ⋙?-uniq (Here-⋙? t₁ t₂ t₃) (Here-⋙? .t₁ .t₂ .t₃) = refl
  ⋙?-uniq (Branch-⋙? ?₁ ?₂) (Branch-⋙? ?₃ ?₄) 
    rewrite ⋙?-uniq ?₁ ?₃ | ⋙?-uniq ?₂ ?₄ = refl
  
  ⋙ : {s₁ s₂ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂}
    → p₁ ⋙? p₂ → Patch s₁
  ⋙ (✴⋙?I p₁) = p₁
  ⋙ (Here-⋙? t₁ t₂ t₃) = ⟨ t₁ ⇒ t₃ ⟩
  ⋙ (Branch-⋙? p₁⋙?p₂ p₃⋙?p₄) = ⟨ ⋙ p₁⋙?p₂ ∧ ⋙ p₃⋙?p₄ ⟩
  
  ⋙-preserves : ∀ {s₁ s₂ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂}
    → (?₁ ?₂ : p₁ ⋙? p₂) → ⋙ ?₁ ⟷ ⋙ ?₂
  ⋙-preserves (✴⋙?I p₁) (✴⋙?I .p₁) = ⟷-refl p₁
  ⋙-preserves (Here-⋙? t₁ t₂ t₃) (Here-⋙? .t₁ .t₂ .t₃) = 
    ⟷-refl ⟨ t₁ ⇒ t₃ ⟩
  ⋙-preserves (Branch-⋙? ?₁ ?₂) (Branch-⋙? ?₃ ?₄) = 
    ⟷-branch (⋙-preserves ?₁ ?₃) (⋙-preserves ?₂ ?₄)

  ⋙-assoc : ∀ {s₁ s₂ s₃ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂} {p₃ : Patch s₃}
    → (1⋙?2 : p₁ ⋙? p₂)
    → ([1⋙2]⋙?3 : (⋙ 1⋙?2) ⋙? p₃)
    → (2⋙?3 : p₂ ⋙? p₃)
    → (1⋙?[2⋙3] : p₁ ⋙? (⋙ 2⋙?3))
    → (⋙ [1⋙2]⋙?3) ⟷ (⋙ 1⋙?[2⋙3])
  ⋙-assoc (✴⋙?I p₁) (✴⋙?I .p₁) (✴⋙?I .I) (✴⋙?I .p₁) = ⟷-refl p₁
  ⋙-assoc (Here-⋙? t₁ t₂ t₃) (✴⋙?I .(⟨ t₁ ⇒ t₃ ⟩)) (✴⋙?I .(⟨ t₂ ⇒ t₃ ⟩)) (Here-⋙? .t₁ .t₂ .t₃) = ⟷-refl ⟨ t₁ ⇒ t₃ ⟩
  ⋙-assoc (Here-⋙? t₁ t₂ t₃) (Here-⋙? .t₁ .t₃ t₄) (Here-⋙? .t₂ .t₃ .t₄) (Here-⋙? .t₁ .t₂ .t₄) = ⟷-refl ⟨ t₁ ⇒ t₄ ⟩
  ⋙-assoc 
    (Branch-⋙? 1⋙?2 3⋙?4) 
    (✴⋙?I .(⟨ ⋙ 1⋙?2 ∧ ⋙ 3⋙?4 ⟩)) 
    (✴⋙?I ._) 
    (Branch-⋙? 1⋙?[2⋙0] 3⋙?[4⋙0]) 
    = ⟷-branch (⋙-preserves 1⋙?2 1⋙?[2⋙0]) 
      (⋙-preserves 3⋙?4 3⋙?[4⋙0])
  ⋙-assoc 
    (Branch-⋙? 1⋙?2 3⋙?4) 
    (Branch-⋙? [1⋙2]⋙?5 [3⋙4]⋙?6) 
    (Branch-⋙? 2⋙?5 4⋙?6) 
    (Branch-⋙? 1⋙?[2⋙5] 3⋙?[4⋙6]) 
    = ⟷-branch 
      (⋙-assoc 1⋙?2 [1⋙2]⋙?5 2⋙?5 1⋙?[2⋙5]) 
      (⋙-assoc 3⋙?4 [3⋙4]⋙?6 4⋙?6 3⋙?[4⋙6])

open ⋙-try2
\end{code}

\begin{code}
patch-lem : ∀ {s₁ s₂ : Form} 
  → (x : Tree) → (p : s₁ ∥ s₂)
  → (p₁ : Patch s₁) → (p₂ : Patch s₂)
  → p₁ ⊏ x → p₂ ⊏ x
  → ((p₁ ⋀ p₂) p ⊏ x)
patch-lem x (∅∥✴ .Skip) I I (⊏-I .x) (⊏-I .x) = ⊏-I x
patch-lem x (✴∥∅ .Skip) I I (⊏-I .x) (⊏-I .x) = ⊏-I x
patch-lem x (∅∥✴ .Take) I ⟨ .x ⇒ to ⟩ (⊏-I .x) (⊏-⇒ .x .to) = 
  ⊏-⇒ x to
patch-lem x (∅∥✴ .(Branch sl sr)) I (⟨_∧_⟩ {sl} {sr} p₂ p₃) p₁⊏x p₂⊏x = p₂⊏x
patch-lem x (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I p₁⊏x p₂⊏x = p₁⊏x
patch-lem x (✴∥∅ .(Branch sl sr)) (⟨_∧_⟩ {sl} {sr} p₁ p₂) I p₁⊏x p₂⊏x = p₁⊏x
patch-lem (Leaf val) (Branch-∥ pl pr) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ () p₂⊏x
patch-lem (Branch tl tr) (Branch-∥ pl pr) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ (⊏-∧ p₁⊏tl p₂⊏tr) (⊏-∧ p₃⊏tl p₄⊏tr) = 
  ⊏-∧ (patch-lem tl pl p₁ p₃ p₁⊏tl p₃⊏tl) 
      (patch-lem tr pr p₂ p₄ p₂⊏tr p₄⊏tr)

∥-comm : ∀ {s₁ s₂ : Form} → s₁ ∥ s₂ → s₂ ∥ s₁
∥-comm {.Skip} {s₂} (∅∥✴ .s₂) = ✴∥∅ s₂
∥-comm {s₁} (✴∥∅ .s₁) = ∅∥✴ s₁
∥-comm (Branch-∥ s₁∥s₂ s₁∥s₃) = 
  Branch-∥ (∥-comm s₁∥s₂) (∥-comm s₁∥s₃)

lemma-∥-unite : {s₁ s₂ s₃ : Form} 
  → (s₁∥s₂ : s₁ ∥ s₂) → s₂ ∥ s₃ → s₁ ∥ s₃
  → unite s₁∥s₂ ∥ s₃
lemma-∥-unite {.Skip} {s₂} (∅∥✴ .s₂) s₂∥s₃ s₁∥s₃ = s₂∥s₃
lemma-∥-unite {s₁} (✴∥∅ .s₁) s₂∥s₃ s₁∥s₃ = s₁∥s₃
lemma-∥-unite (Branch-∥ {L1} {R1} {L2} {R2} L1∥L2 R1∥R2) (✴∥∅ .(Branch L2 R2)) s₁∥s₃ = ✴∥∅ (Branch ((L1 ^ L2) L1∥L2) ((R1 ^ R2) R1∥R2))
lemma-∥-unite (Branch-∥ L1∥L2 R1∥R2) (Branch-∥ s₂∥s₃ s₂∥s₄) (Branch-∥ s₁∥s₃ s₁∥s₄) 
  = Branch-∥ (lemma-∥-unite L1∥L2 s₂∥s₃ s₁∥s₃)
    (lemma-∥-unite R1∥R2 s₂∥s₄ s₁∥s₄)
                                                              
\end{code}

  
\begin{code}
patch-⊏-indep : {s : Form} (p : Patch s) (t : Tree)
  → (⊏₁ ⊏₂ : p ⊏ t)
  → patch p t ⊏₁ ≡ patch p t ⊏₂
patch-⊏-indep I t (⊏-I .t) (⊏-I .t) = refl
patch-⊏-indep ⟨ .t ⇒ to ⟩ t (⊏-⇒ .t .to) (⊏-⇒ .t .to) = refl
patch-⊏-indep (⟨_∧_⟩ {sl}{sr} pl pr) .(Branch tl tr) (⊏-∧ {.sl} {.sr} {.pl} {.pr} {tl} {tr} ⊏₁ ⊏₂) (⊏-∧ ⊏₃ ⊏₄) 
  rewrite patch-⊏-indep pl tl ⊏₁ ⊏₃ | patch-⊏-indep pr tr ⊏₂ ⊏₄ = refl
\end{code}
  
\begin{code}
∥-comm²≡id : {s₁ s₂ : Form} → (s₁∥s₂ : s₁ ∥ s₂)
  → s₁∥s₂ ≡ ∥-comm (∥-comm s₁∥s₂)
∥-comm²≡id {.Skip} {s₂} (∅∥✴ .s₂) = refl
∥-comm²≡id {s₁} (✴∥∅ .s₁) = refl
∥-comm²≡id (Branch-∥ L1∥L2 R1∥R2) 
  -- почему-то не захотел работать rewrite. Пришлось сделать with
  with ∥-comm (∥-comm L1∥L2) | ∥-comm²≡id L1∥L2
     | ∥-comm (∥-comm R1∥R2) | ∥-comm²≡id R1∥R2
∥-comm²≡id (Branch-∥ .i1 .i2) | i1 | refl | i2 | refl = refl
\end{code}
  
\begin{code}
-- Неправда
--unite-lem : {s₁ s₂ : Form} → (∥₁ ∥₂ : s₁ ∥ s₂) → ∥₁ ≡ ∥₂
--unite-lem {.Skip} {s₂} (∅∥✴ .s₂) (∅∥✴ .s₂) = refl
--unite-lem (∅∥✴ .Skip) (✴∥∅ .Skip) = {!!}
--unite-lem (✴∥∅ .Skip) (∅∥✴ .Skip) = {!!}
--unite-lem {s₁} (✴∥∅ .s₁) (✴∥∅ .s₁) = {!!}
--unite-lem (Branch-∥ ∥₁ ∥₂) (Branch-∥ ∥₃ ∥₄) = {!!}

-- Не тайпчекается
--⋀-∥-indep : {s₁ s₂ : Form} (p₁ : Patch s₁) (p₂ : Patch s₂)
--  → (∥₁ ∥₂ : s₁ ∥ s₂) → 
--  (p₁ ⋀ p₂) ∥₁ ≡ (p₁ ⋀ p₂) ∥₂
--⋀-∥-indep p₁ p₂ ∥₁ ∥₂ = ?
\end{code}

\begin{code}
⋀-comm : ∀ {s₁ s₂ : Form}
  → (s₁∥s₂ : s₁ ∥ s₂)
  → (p₁ : Patch s₁) → (p₂ : Patch s₂)
  → ((p₁ ⋀ p₂) s₁∥s₂) ⟷ ((p₂ ⋀ p₁) (∥-comm s₁∥s₂))
⋀-comm (∅∥✴ .Skip) I I = ⟷-refl I
⋀-comm (∅∥✴ .Take) I ⟨ from ⇒ to ⟩ = ⟷-refl ⟨ from ⇒ to ⟩
⋀-comm (∅∥✴ ._) I ⟨ p₂ ∧ p₃ ⟩ = ⟷-refl ⟨ p₂ ∧ p₃ ⟩
⋀-comm (✴∥∅ .Skip) I I = ⟷-refl I
⋀-comm (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I = ⟷-refl ⟨ from ⇒ to ⟩
⋀-comm (✴∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ I = ⟷-refl ⟨ p₁ ∧ p₂ ⟩
⋀-comm (Branch-∥ L1∥L2 R1∥R2) ⟨ l₁ ∧ r₁ ⟩ ⟨ l₂ ∧ r₂ ⟩ 
  = ⟷-branch L R
  where
    L = ⋀-comm L1∥L2 l₁ l₂
    R = ⋀-comm R1∥R2 r₁ r₂

 
-- Не надо смотреть на размер доказательства. На самом деле, подавляющее большинство
--   случаев доказались сами после вбивания в дырку `patch-⊏-indep` и C-c C-a.
--   Не доказались сами только два случая в середине, для них пришлось делать
--   `∥-comm²≡id` и один в конце, в котором, как и ожидалось, был рекурсивный вызов.
--   Вообще, от того, что у утверждения (s₁ ∥ s₂) может быть два структурно неэквивалентных
--   доказательства вылазит куча проблем.
⋀-assoc : ∀ {s₁ s₂ s₃ : Form} 
  → (s₁∥s₂ : s₁ ∥ s₂) → (s₂∥s₃ : s₂ ∥ s₃) → (s₁∥s₃ : s₁ ∥ s₃)
  → (p₁ : Patch s₁) → (p₂ : Patch s₂) → (p₃ : Patch s₃)
  → (((p₁ ⋀ p₂) s₁∥s₂) ⋀ p₃) (lemma-∥-unite s₁∥s₂ s₂∥s₃ s₁∥s₃) ⟷ 
    (p₁ ⋀ ((p₂ ⋀ p₃) s₂∥s₃)) 
      (∥-comm (lemma-∥-unite s₂∥s₃ (∥-comm s₁∥s₃) (∥-comm s₁∥s₂)))
⋀-assoc (∅∥✴ .Skip) (∅∥✴ .Skip) (∅∥✴ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✴ .Skip) (∅∥✴ .Take) (∅∥✴ .Take) I I ⟨ from ⇒ to ⟩ = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (∅∥✴ .Skip) (∅∥✴ ._) (∅∥✴ ._) I I ⟨ p₃ ∧ p₄ ⟩ = ⟷-refl ⟨ p₃ ∧ p₄ ⟩
⋀-assoc (∅∥✴ .Skip) (∅∥✴ .Skip) (✴∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✴ .Skip) (✴∥∅ .Skip) (∅∥✴ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✴ .Take) (✴∥∅ .Take) (∅∥✴ .Skip) I ⟨ from ⇒ to ⟩ I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (∅∥✴ ._) (✴∥∅ ._) (∅∥✴ .Skip) I ⟨ p₂ ∧ p₃ ⟩ I = ⟷-refl ⟨ p₂ ∧ p₃ ⟩
⋀-assoc (∅∥✴ .Skip) (✴∥∅ .Skip) (✴∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✴ .Take) (✴∥∅ .Take) (✴∥∅ .Skip) I ⟨ from ⇒ to ⟩ I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (∅∥✴ ._) (✴∥∅ ._) (✴∥∅ .Skip) I ⟨ p₂ ∧ p₃ ⟩ I = ⟷-refl ⟨ p₂ ∧ p₃ ⟩
⋀-assoc (∅∥✴ ._) (Branch-∥ s₂∥s₃ s₂∥s₄) (∅∥✴ ._) I ⟨ p₂ ∧ p₃ ⟩ ⟨ p₄ ∧ p₅ ⟩ =
  ⟷-refl ⟨ (p₂ ⋀ p₄) s₂∥s₃ ∧ (p₃ ⋀ p₅) s₂∥s₄ ⟩
⋀-assoc (✴∥∅ .Skip) (∅∥✴ .Skip) (∅∥✴ .Skip) I I I = ⟷-refl I
⋀-assoc (✴∥∅ .Skip) (∅∥✴ .Take) (∅∥✴ .Take) I I ⟨ from ⇒ to ⟩ = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (✴∥∅ .Skip) (∅∥✴ ._) (∅∥✴ ._) I I ⟨ p₃ ∧ p₄ ⟩ = ⟷-refl ⟨ p₃ ∧ p₄ ⟩
⋀-assoc (✴∥∅ .Skip) (∅∥✴ .Skip) (✴∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (✴∥∅ .Take) (∅∥✴ .Skip) (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (✴∥∅ ._) (∅∥✴ .Skip) (✴∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ I I = ⟷-refl ⟨ p₁ ∧ p₂ ⟩
⋀-assoc (✴∥∅ ._) (∅∥✴ ._) (Branch-∥ s₁∥s₃ s₂∥s₄) ⟨ p₁ ∧ p₂ ⟩ I ⟨ p₃ ∧ p₄ ⟩ 
  with ∥-comm (∥-comm s₁∥s₃) | ∥-comm²≡id s₁∥s₃ 
    | ∥-comm (∥-comm s₂∥s₄) | ∥-comm²≡id s₂∥s₄
... | .s₁∥s₃ | refl | .s₂∥s₄ | refl = 
  ⟷-refl ⟨ (p₁ ⋀ p₃) s₁∥s₃ ∧ (p₂ ⋀ p₄) s₂∥s₄ ⟩
⋀-assoc (✴∥∅ .Skip) (✴∥∅ .Skip) (∅∥✴ .Skip) I I I = ⟷-refl I
⋀-assoc (✴∥∅ .Skip) (✴∥∅ .Skip) (✴∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (✴∥∅ .Take) (✴∥∅ .Skip) (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (✴∥∅ ._) (✴∥∅ .Skip) (✴∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ I I = ⟷-refl ⟨ p₁ ∧ p₂ ⟩
⋀-assoc (Branch-∥ s₁∥s₃ s₂∥s₄) (✴∥∅ ._) (✴∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ I
  with ∥-comm (∥-comm s₁∥s₃) | ∥-comm²≡id s₁∥s₃ 
    | ∥-comm (∥-comm s₂∥s₄) | ∥-comm²≡id s₂∥s₄
... | .s₁∥s₃ | refl | .s₂∥s₄ | refl = 
  ⟷-refl ⟨ (p₁ ⋀ p₃) s₁∥s₃ ∧ (p₂ ⋀ p₄) s₂∥s₄ ⟩
⋀-assoc (Branch-∥ L1∥L2 R1∥R2) (Branch-∥ L2∥L3 R2∥R3) (Branch-∥ L1∥L3 R1∥R3) 
  ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ ⟨ p₅ ∧ p₆ ⟩ = 
    ⟷-branch 
      (⋀-assoc L1∥L2 L2∥L3 L1∥L3 p₁ p₃ p₅) 
      (⋀-assoc R1∥R2 R2∥R3 R1∥R3 p₂ p₄ p₆)
\end{code}


\begin{code}

module asfddsfdsf where

  I⋀x=x : ∀ {s : Form} (p : Patch s)
    → (I ⋀ p) (∅∥✴ s) ≡ p
  I⋀x=x I = refl
  I⋀x=x ⟨ _ ⇒ _ ⟩ = refl
  I⋀x=x ⟨ _ ∧ _ ⟩ = refl

--  ⋀-⋙-lem : ∀ {fᵃ fᵇ fᶜ' fᶜ'' : Form}
--    (c' : Patch fᶜ')(c'' : Patch fᶜ'')
--    (a : Patch fᵃ)(b : Patch fᵇ)
--    (c'∥c'' : fᶜ' ∥ fᶜ'') 
--    (a∥b : fᵃ ∥ fᵇ)
--    (a∧b⋙?c : (a ⋀ b) a∥b ⋙? ((c' ⋀ c'') c'∥c''))
--    (a⋙?c' : a ⋙? c')
--    (b⋙?c'' : b ⋙? c'')
--    → ⋙ a∧b⋙?c 
--      ⟷ ((⋙ a⋙?c') ⋀ (⋙ b⋙?c'')) a∥b
--  ⋀-⋙-lem I I I I (∅∥✴ .Skip) (∅∥✴ .Skip) (✴⋙?I .I) (✴⋙?I .I) (✴⋙?I .I) 
--    = ⟷-refl I
--  ⋀-⋙-lem I I I I (∅∥✴ .Skip) (✴∥∅ .Skip) (✴⋙?I .I) (✴⋙?I .I) (✴⋙?I .I) 
--    = ⟷-refl I
--  ⋀-⋙-lem I I I I (✴∥∅ .Skip) (∅∥✴ .Skip) (✴⋙?I .I) (✴⋙?I .I) (✴⋙?I .I) 
--    = ⟷-refl I
--  ⋀-⋙-lem I I I I (✴∥∅ .Skip) (✴∥∅ .Skip) (✴⋙?I .I) (✴⋙?I .I) (✴⋙?I .I) 
--    = ⟷-refl I
--  ⋀-⋙-lem I I I ⟨ from ⇒ to ⟩ (∅∥✴ .Skip) (∅∥✴ .Take) (✴⋙?I .(⟨ from ⇒ to ⟩)) (✴⋙?I .I) (✴⋙?I .(⟨ from ⇒ to ⟩)) 
--    = ⟷-refl ⟨ from ⇒ to ⟩
--  ⋀-⋙-lem I I I ⟨ from ⇒ to ⟩ (✴∥∅ .Skip) (∅∥✴ .Take) (✴⋙?I .(⟨ from ⇒ to ⟩)) (✴⋙?I .I) (✴⋙?I .(⟨ from ⇒ to ⟩)) 
--    = ⟷-refl ⟨ from ⇒ to ⟩
--  ⋀-⋙-lem I I I ⟨ b ∧ b₁ ⟩ (∅∥✴ .Skip) (∅∥✴ ._) (✴⋙?I .(⟨ b ∧ b₁ ⟩)) (✴⋙?I .I) (✴⋙?I .(⟨ b ∧ b₁ ⟩)) 
--    = ⟷-refl ⟨ b ∧ b₁ ⟩
--  ⋀-⋙-lem I I I ⟨ b ∧ b₁ ⟩ (✴∥∅ .Skip) (∅∥✴ ._) (✴⋙?I .(⟨ b ∧ b₁ ⟩)) (✴⋙?I .I) (✴⋙?I .(⟨ b ∧ b₁ ⟩)) 
--    = ⟷-refl ⟨ b ∧ b₁ ⟩
--  ⋀-⋙-lem I I ⟨ from ⇒ to ⟩ I (∅∥✴ .Skip) (✴∥∅ .Take) (✴⋙?I .(⟨ from ⇒ to ⟩)) (✴⋙?I .(⟨ from ⇒ to ⟩)) (✴⋙?I .I) 
--    = ⟷-refl ⟨ from ⇒ to ⟩
--  ⋀-⋙-lem I I ⟨ from ⇒ to ⟩ I (✴∥∅ .Skip) (✴∥∅ .Take) (✴⋙?I .(⟨ from ⇒ to ⟩)) (✴⋙?I .(⟨ from ⇒ to ⟩)) (✴⋙?I .I) 
--    = ⟷-refl ⟨ from ⇒ to ⟩
--  ⋀-⋙-lem I I ⟨ a ∧ a₁ ⟩ I (∅∥✴ .Skip) (✴∥∅ ._) (✴⋙?I .(⟨ a ∧ a₁ ⟩)) (✴⋙?I .(⟨ a ∧ a₁ ⟩)) (✴⋙?I .I) 
--    = ⟷-refl ⟨ a ∧ a₁ ⟩
--  ⋀-⋙-lem I I ⟨ a ∧ a₁ ⟩ I (✴∥∅ .Skip) (✴∥∅ ._) (✴⋙?I .(⟨ a ∧ a₁ ⟩)) (✴⋙?I .(⟨ a ∧ a₁ ⟩)) (✴⋙?I .I) 
--    = ⟷-refl ⟨ a ∧ a₁ ⟩
--  ⋀-⋙-lem I I ⟨ a ∧ a₁ ⟩ ⟨ b ∧ b₁ ⟩ (∅∥✴ .Skip) (Branch-∥ a∥b a∥b₁) (✴⋙?I .(⟨ (a ⋀ b) a∥b ∧ (a₁ ⋀ b₁) a∥b₁ ⟩)) (✴⋙?I .(⟨ a ∧ a₁ ⟩)) (✴⋙?I .(⟨ b ∧ b₁ ⟩)) 
--    = ⟷-refl ⟨ (a ⋀ b) a∥b ∧ (a₁ ⋀ b₁) a∥b₁ ⟩
--  ⋀-⋙-lem I I ⟨ a ∧ a₁ ⟩ ⟨ b ∧ b₁ ⟩ (✴∥∅ .Skip) (Branch-∥ a∥b a∥b₁) (✴⋙?I .(⟨ (a ⋀ b) a∥b ∧ (a₁ ⋀ b₁) a∥b₁ ⟩)) (✴⋙?I .(⟨ a ∧ a₁ ⟩)) (✴⋙?I .(⟨ b ∧ b₁ ⟩)) 
--    = ⟷-refl ⟨ (a ⋀ b) a∥b ∧ (a₁ ⋀ b₁) a∥b₁ ⟩
--  ⋀-⋙-lem I ⟨ from ⇒ to ⟩ I ⟨ from₁ ⇒ .from ⟩ (∅∥✴ .Take) (∅∥✴ .Take) (Here-⋙? .from₁ .from .to) (✴⋙?I .I) (Here-⋙? .from₁ .from .to) 
--    = ⟷-refl ⟨ from₁ ⇒ to ⟩
--  ⋀-⋙-lem I ⟨ c'' ∧ c''' ⟩ I ⟨ b₁ ∧ b ⟩ (∅∥✴ ._) (∅∥✴ ._) (Branch-⋙? a∧b⋙?c₁ a∧b⋙?c) (✴⋙?I .I) (Branch-⋙? b⋙?c'' b⋙?c''') 
--    = ⟷-branch 
--      (⋙-preserves a∧b⋙?c₁ b⋙?c'') 
--      (⋙-preserves a∧b⋙?c b⋙?c''')
--  ⋀-⋙-lem I (⟨_∧_⟩ {sl}{sr} c''₁ c''₂) ⟨ a₁ ∧ a₂ ⟩ ⟨ b₁ ∧ b₂ ⟩ 
--    (∅∥✴ .(Branch sl sr)) 
--    (Branch-∥ a₁∥b₁ a₂∥b₂) (Branch-⋙? a∧b⋙?c₁ a∧b⋙?c₂) 
--    (✴⋙?I .(⟨ a₁ ∧ a₂ ⟩)) (Branch-⋙? b⋙?c''₁ b⋙?c''₂) 
----    rewrite I⋀x=x c''₁ 
--    with (I ⋀ c''₁) (∅∥✴ sl) | I⋀x=x c''₁ 
--  ... | .c''₁ | refl 
--    = ⟷-branch {!⋀-⋙-lem I c''₁ a₁ b₁ (∅∥✴ sl) a₁∥b₁ !} {!!}
--  ⋀-⋙-lem ⟨ from ⇒ to ⟩ I ⟨ from₁ ⇒ .from ⟩ I (✴∥∅ .Take) (✴∥∅ .Take) (Here-⋙? .from₁ .from .to) (Here-⋙? .from₁ .from .to) (✴⋙?I .I) 
--    = ⟷-refl ⟨ from₁ ⇒ to ⟩
--  ⋀-⋙-lem ⟨ c' ∧ c'' ⟩ I ⟨ a₁ ∧ a ⟩ I (✴∥∅ ._) (✴∥∅ ._) (Branch-⋙? a∧b⋙?c₁ a∧b⋙?c) (Branch-⋙? a⋙?c' a⋙?c'') (✴⋙?I .I) = {!!}
--  ⋀-⋙-lem ⟨ c' ∧ c'' ⟩ I ⟨ a ∧ a₁ ⟩ ⟨ b ∧ b₁ ⟩ (✴∥∅ ._) (Branch-∥ a∥b a∥b₁) (Branch-⋙? a∧b⋙?c a∧b⋙?c₁) (Branch-⋙? a⋙?c' a⋙?c'') (✴⋙?I .(⟨ b ∧ b₁ ⟩)) = {!!}
--  ⋀-⋙-lem ⟨ c' ∧ c'' ⟩ ⟨ c''' ∧ c'''' ⟩ ⟨ a ∧ a₁ ⟩ ⟨ b ∧ b₁ ⟩ (Branch-∥ c'∥c'' c'∥c''') (Branch-∥ a∥b a∥b₁) (Branch-⋙? a∧b⋙?c a∧b⋙?c₁) (Branch-⋙? a⋙?c' a⋙?c'') (Branch-⋙? b⋙?c'' b⋙?c''') = {!!}
\end{code}


\begin{code}
-- -- Фейл, вестимо
-- module ⋙-try1 where
--   data _⋙?_ : {s₁ s₂ : Form} (p₁ : Patch s₁) (p₂ : Patch s₂) → Set where
--     ✴⋙?I : ∀ {s : Form} (p : Patch s) → p ⋙? I
--     Here-⋙? : ∀ (t₁ t₂ t₃ : Tree) → ⟨ t₁ ⇒ t₂ ⟩ ⋙? ⟨ t₂ ⇒ t₃ ⟩
--     There-⋙? : ∀ {s₁ s₂ : Form} {t₁ t₂ : Tree} {p₁ : Patch s₁} {p₂ : Patch s₂}
--       → (t : Tree) → p₁ ⊏ t₁ → p₂ ⊏ t₂ 
--       → ⟨ t ⇒ Branch t₁ t₂ ⟩ ⋙? ⟨ p₁ ∧ p₂ ⟩
--     Branch-⋙? : ∀ {s₁ s₂ s₃ s₄} 
--       → {p₁ : Patch s₁} {p₂ : Patch s₂} {p₃ : Patch s₃} {p₄ : Patch s₄}
--       → (L : p₁ ⋙? p₂) → (R : p₃ ⋙? p₄) → ⟨ p₁ ∧ p₃ ⟩ ⋙? ⟨ p₂ ∧ p₄ ⟩
--   
--   ⋙ : {s₁ s₂ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂}
--     → p₁ ⋙? p₂ → Patch s₁
--   ⋙ (✴⋙?I p₁) = p₁
--   ⋙ (Here-⋙? t₁ t₂ t₃) = ⟨ t₁ ⇒ t₃ ⟩
--   ⋙ {p₁ = ⟨ t ⇒ Branch t₁ t₂ ⟩}{⟨ p₁ ∧ p₂ ⟩} (There-⋙? .t p₁⊏t₁ p₂⊏t₂) = 
--     ⟨ t ⇒ Branch (patch p₁ t₁ p₁⊏t₁) (patch p₂ t₂ p₂⊏t₂)  ⟩
--   ⋙ (Branch-⋙? p₁⋙?p₂ p₃⋙?p₄) = ⟨ ⋙ p₁⋙?p₂ ∧ ⋙ p₃⋙?p₄ ⟩
--   
--   ⋙-assoc : ∀ {s₁ s₂ s₃ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂} {p₃ : Patch s₃}
--     → (1⋙?2 : p₁ ⋙? p₂)
--     → ([1⋙2]⋙?3 : (⋙ 1⋙?2) ⋙? p₃)
--     → (2⋙?3 : p₂ ⋙? p₃)
--     → (1⋙?[2⋙3] : p₁ ⋙? (⋙ 2⋙?3))
--     → (⋙ [1⋙2]⋙?3) ⟷ (⋙ 1⋙?[2⋙3])
--   ⋙-assoc (✴⋙?I p₁) (✴⋙?I .p₁) (✴⋙?I .I) (✴⋙?I .p₁) = ⟷-refl p₁
--   ⋙-assoc (Here-⋙? t₁ t₂ t₃) (✴⋙?I .(⟨ t₁ ⇒ t₃ ⟩)) (✴⋙?I .(⟨ t₂ ⇒ t₃ ⟩)) (Here-⋙? .t₁ .t₂ .t₃) = ⟷-refl ⟨ t₁ ⇒ t₃ ⟩
--   ⋙-assoc (Here-⋙? t₁ t₂ t₃) (Here-⋙? .t₁ .t₃ t₄) (Here-⋙? .t₂ .t₃ .t₄) (Here-⋙? .t₁ .t₂ .t₄) = ⟷-refl ⟨ t₁ ⇒ t₄ ⟩
--   ⋙-assoc (Here-⋙? t₁ t₂ ._) (There-⋙? .t₁ x₁ x) (There-⋙? .t₂ x₂ x₃) (Here-⋙? .t₁ .t₂ ._) = {!⟷-refl!}
--   ⋙-assoc (There-⋙? t x x₁) (✴⋙?I ._) (✴⋙?I ._) (There-⋙? .t x₂ x₃) = {!!}
--   ⋙-assoc (There-⋙? t₃ x x₁) (Here-⋙? .t₃ ._ t₄) () 1⋙?[2⋙3]
--   ⋙-assoc (There-⋙? t x x₁) (There-⋙? .t x₃ x₂) (Branch-⋙? 2⋙?3 2⋙?4) (There-⋙? .t x₄ x₅) = {!!}
--   ⋙-assoc (Branch-⋙? 1⋙?2 1⋙?3) (✴⋙?I .(⟨ ⋙ 1⋙?2 ∧ ⋙ 1⋙?3 ⟩)) (✴⋙?I ._) (Branch-⋙? 1⋙?[2⋙3] 1⋙?[2⋙3]₁) = {!!}
--   ⋙-assoc (Branch-⋙? 1⋙?3 1⋙?2) (Branch-⋙? [1⋙2]⋙?4 [1⋙2]⋙?3) (Branch-⋙? 2⋙?3 2⋙?4) (Branch-⋙? 1⋙?[2⋙3] 1⋙?[2⋙3]₁) = {!!}

\end{code}

