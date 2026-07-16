import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Aula 2: Lógica de Predicados e Conjuntos" =>

%%%
tag := "aula-2"
%%%

Esta aula estende a lógica proposicional com quantificadores e introduz conjuntos, seguindo os capítulos 2 e 3 de [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). Ela apresenta as regras de prova dos quantificadores universal e existencial, as leis que os relacionam sob negação e conjuntos como predicados em Lean.

# Predicados e Quantificadores

A Aula 1 excluiu "x é par" das proposições porque a sua verdade depende da variável livre x. Um *predicado* torna essa dependência explícita. Um predicado sobre um tipo α atribui uma proposição a cada elemento de α, então em Lean um predicado é uma função de tipo `α → Prop`.

```lean (name := checkPred)
#check fun n : Nat => n > 3
```
```leanOutput checkPred
fun n => n > 3 : Nat → Prop
```

Quantificadores ligam a variável de um predicado e produzem uma proposição.{margin}[G. Frege, *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*, Verlag von Louis Nebert, Halle, 1879.] Escrevemos P x para a proposição que o predicado P produz em x.

:::table +header
*
  * Símbolo
  * Nome
  * Leitura
*
  * ∀ x, P x
  * quantificador universal
  * P x vale para todo x
*
  * ∃ x, P x
  * quantificador existencial
  * P x vale para algum x
:::

O quantificador *liga* a sua variável, então ∀ x, P x não depende de variável livre e é uma proposição. A variável percorre um tipo. Por exemplo, `∃ n : Nat, n * n = 9` afirma que algum número natural elevado ao quadrado dá 9. Quando o contexto determina o tipo, Lean o infere e omitimos a anotação.

# O Quantificador Universal

Para provar ∀ x, P x, considere um elemento arbitrário e prove a proposição nele. A tática `intro`, que introduziu implicações na Aula 1, também introduz quantificadores universais.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro a
  exact (h a).left
```

A prova também usa a regra de eliminação. Uma hipótese h : ∀ x, P x ∧ Q x é uma função que retorna uma prova de P a ∧ Q a para cada a, então a aplicação `h a` a *instancia* em a. Isso espelha a Aula 1, em que uma prova de uma implicação era uma função sobre provas. A tática `specialize` instancia uma hipótese universal no próprio contexto.

```lean
example (α : Type) (P Q : α → Prop) (h : ∀ x, P x → Q x)
    (a : α) (hPa : P a) : Q a := by
  specialize h a
  exact h hPa
```

O quantificador universal distribui sobre a conjunção. A prova combina as regras do quantificador com as regras da Aula 1 para a conjunção e o bicondicional.

```lean
theorem forall_and_distrib (α : Type) (P Q : α → Prop) :
    (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro a
      exact (h a).left
    · intro a
      exact (h a).right
  · intro h a
    exact ⟨h.left a, h.right a⟩
```

# O Quantificador Existencial

Para provar ∃ x, P x, exiba uma *testemunha* e prove a proposição nela. O construtor anônimo da Aula 1 emparelha a testemunha com a prova. O termo `rfl` prova uma equação cujos dois lados computam para o mesmo valor.

```lean
example : ∃ n : Nat, n * n = 9 := ⟨3, rfl⟩
```

A tática `exists` fornece a testemunha no modo de táticas e fecha o objetivo restante quando ele vale por computação.

```lean
example : ∃ n : Nat, n * n = 9 := by
  exists 3
```

Para usar uma hipótese h : ∃ x, P x, nomeie uma testemunha e a prova de que ela satisfaz P. A proposição ∃ x, P x tem o único construtor `intro`, então a tática `cases` a trata como tratou a disjunção na Aula 1, agora com um caso.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  cases h with
  | intro a ha => exact ⟨a, ha.left⟩
```

A tática `obtain` desestrutura a hipótese em um passo, com um padrão que espelha o construtor anônimo.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.right⟩
```

O teorema abaixo combina os dois quantificadores. Uma implicação ponto a ponto transporta a existência de P para Q, e a testemunha não muda.

```lean
theorem exists_imp_exists (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, P x) → ∃ x, Q x := by
  intro hex
  obtain ⟨a, hPa⟩ := hex
  exact ⟨a, h a hPa⟩
```

# Leis de Negação dos Quantificadores

As leis de De Morgan da Aula 1 trocam a negação com a conjunção e a disjunção. As leis abaixo trocam a negação com os quantificadores.

:::table +header
*
  * Nome
  * Equivalência
*
  * Negação de ∃
  * ¬(∃ x, P x) ≡ ∀ x, ¬P x
*
  * Negação de ∀
  * ¬(∀ x, P x) ≡ ∃ x, ¬P x
:::

A primeira lei é construtiva nas duas direções.

```lean
theorem not_exists_iff (α : Type) (P : α → Prop) :
    ¬(∃ x, P x) ↔ ∀ x, ¬P x := by
  constructor
  · intro h a hPa
    exact h ⟨a, hPa⟩
  · intro h hex
    obtain ⟨a, hPa⟩ := hex
    exact h a hPa
```

Na segunda lei, a direção de ∃ x, ¬P x para ¬(∀ x, P x) é construtiva, e a direção recíproca requer raciocínio clássico, como a primeira lei de De Morgan na Aula 1. Duas aplicações de `Classical.byContradiction` produzem a testemunha.

```lean
theorem not_forall_exists (α : Type) (P : α → Prop)
    (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  apply Classical.byContradiction
  intro hne
  apply h
  intro a
  apply Classical.byContradiction
  intro hnPa
  exact hne ⟨a, hnPa⟩
```

# A Ordem dos Quantificadores

Quantificadores consecutivos do mesmo tipo comutam, e quantificadores de tipos distintos não comutam. Uma direção da troca vale. Uma testemunha que satisfaz R com todo y em particular satisfaz R com cada y dado.

```lean
theorem exists_forall_swap (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha b⟩
```

A recíproca falha. Sobre os números naturais, tome R x y como x ≥ y. Então ∀ y, ∃ x, R x y vale, pois cada y satisfaz y ≥ y, e ∃ x, ∀ y, R x y afirma que algum número natural é maior ou igual a todo número natural, o que é falso.

# Conjuntos

O capítulo 3 de HTPIwL desenvolve provas sobre conjuntos. Um conjunto de elementos de um tipo α é determinado por quais elementos pertencem a ele, então o predicado de pertinência determina o conjunto. Em Lean, tomamos essa propriedade como a definição.

```savedLean
def Set (α : Type) : Type := α → Prop
```

Todo elemento de um conjunto vem do tipo fixo α. Nesse cenário tipado, a coleção de todos os conjuntos que não contêm a si mesmos não pode ser escrita, então o paradoxo de Russell não surge.{margin}[B. Russell, carta a Frege, 16 de junho de 1902. Em J. van Heijenoort, *From Frege to Gödel: A Source Book in Mathematical Logic, 1879–1931*, Harvard University Press, 1967, pp. 124–125.]

A instância abaixo registra a notação x ∈ s, que se desdobra por definição na aplicação s x. Nesta instância e nas seguintes, Lean liga a variável de tipo livre α automaticamente.

```savedLean
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩
```

Um conjunto dado por uma propriedade é o próprio predicado, e uma prova de pertinência é uma prova da propriedade. A notação matemática escreve tal conjunto por compreensão, como o conjunto de todos os n tais que `∃ k, n = 2 * k`. O núcleo de Lean não tem notação por compreensão, então escrevemos o predicado diretamente.

```lean
def Evens : Set Nat := fun n => ∃ k, n = 2 * k

example : (6 : Nat) ∈ Evens := ⟨3, rfl⟩
```

A inclusão s ⊆ t afirma que todo elemento de s pertence a t.

```savedLean
instance : HasSubset (Set α) :=
  ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩
```

Uma inclusão é uma implicação universalmente quantificada, então as suas provas começam considerando um elemento arbitrário junto com a suposição de que ele pertence ao lado esquerdo. A união e a interseção aplicam os conectivos da Aula 1 ponto a ponto.

```savedLean
instance : Union (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩

instance : Inter (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩
```

A pertinência a uma interseção é por definição uma conjunção, então as projeções da Aula 1 se aplicam a ela.

```lean
theorem inter_subset_left (α : Type) (s t : Set α) :
    s ∩ t ⊆ s := by
  intro x hx
  exact hx.left
```

A pertinência a uma união é uma disjunção, então a tática `cases` a divide.

```lean
theorem union_subset_swap (α : Type) (s t : Set α) :
    s ∪ t ⊆ t ∪ s := by
  intro x hx
  cases hx with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
```

Dois conjuntos com os mesmos elementos são iguais. Provar tal igualdade requer princípios de extensionalidade além da lógica apresentada até aqui, então enunciamos identidades de conjuntos como inclusões.

# Exercícios

Prove cada enunciado em Lean, substituindo `sorry` por uma prova. Baixe o arquivo de exercícios [`Lecture02.lean`](../../example-code/Lectures/Pt/Lecture02.lean) e abra-o no VS Code. O arquivo já contém as definições de `Set`, pertinência, inclusão, união e interseção.

```savedComment
Exercícios da Aula 2: Lógica de Predicados e Conjuntos.
Substitua cada `sorry` por uma prova. As definições acima
vêm da aula.
```

Exercício 1. O quantificador universal distribui sobre a implicação.

```savedLean -keep
theorem exercise1 (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hP : ∀ x, P x) : ∀ x, Q x := by
  sorry
```

Exercício 2. O quantificador existencial distribui sobre a disjunção.

```savedLean -keep
theorem exercise2 (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry
```

Exercício 3. Elimine a hipótese existencial e então instancie a universal na testemunha.

```savedLean -keep
theorem exercise3 (α : Type) (P : α → Prop) (Q : Prop)
    (h : ∃ x, P x → Q) (hP : ∀ x, P x) : Q := by
  sorry
```

Exercício 4. A inclusão é transitiva.

```savedLean -keep
theorem exercise4 (α : Type) (s t u : Set α)
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  sorry
```

Exercício 5. A interseção distribui sobre a união.

```savedLean -keep
theorem exercise5 (α : Type) (s t u : Set α) :
    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  sorry
```
