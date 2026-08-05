/-
Slides da Aula 2, gerados a partir de fontes verificadas. Cada
seção de nível superior é um slide; o título do documento e os
parágrafos introdutórios formam o slide de título. Todo código
Lean é elaborado na construção e é idêntico ao código das notas
de aula (`Lectures/Pt/Lecture02.lean`) onde os dois coincidem.
-/

import VersoManual
import Lectures.Meta.SlideDeck

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lógica de Predicados e Conjuntos" =>

Quantificadores, leis de negação, ordem dos quantificadores e conjuntos como predicados em Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-2___-L___gica-de-Predicados-e-Conjuntos/)

Baseada em [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL), capítulos [2](https://djvelleman.github.io/HTPIwL/Chap2.html) e [3](https://djvelleman.github.io/HTPIwL/Chap3.html).

# §2.1 Predicados e quantificadores

* Um *predicado* sobre um tipo α atribui uma proposição a cada elemento, então em Lean é uma função `α → Prop`.

```lean (name := checkPred)
#check fun n : Nat => n > 3
```
```leanOutput checkPred
fun n => n > 3 : Nat → Prop
```

* Quantificadores *ligam* a variável de um predicado e produzem uma proposição (Frege, 1879). A variável percorre um tipo, inferido quando o contexto o determina.

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

```lean (name := checkQuant)
#check ∃ n : Nat, n > 3
#check ∀ n : Nat, n > 3
```
```leanOutput checkQuant
∃ n, n > 3 : Prop
```
```leanOutput checkQuant
∀ (n : Nat), n > 3 : Prop
```

O quantificador leva o predicado, de tipo `Nat → Prop`, a uma proposição, de tipo `Prop`.

# §2.2 O quantificador universal

* *Introduza* ∀ x, P x considerando um elemento arbitrário: `intro`, a mesma tática que introduz implicações.

* *Elimine* por instanciação. Uma hipótese universal é uma *função*, então `h a` a instancia em `a`; `specialize` faz isso no lugar.

::::cols
:::col
```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro a
  exact (h a).left
```
:::
:::col
```lean
example (α : Type) (P Q : α → Prop) (h : ∀ x, P x → Q x)
    (a : α) (hPa : P a) : Q a := by
  specialize h a
  exact h hPa
```
:::
::::

# §2.2 Distribuição sobre a conjunção

O quantificador universal distribui sobre a conjunção. A prova combina as regras do quantificador com as regras da Aula 1 para conjunção e bicondicional.

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

# §2.3 O quantificador existencial

* *Introduza* ∃ x, P x exibindo uma *testemunha* com a sua prova: o construtor anônimo `⟨3, rfl⟩`, ou a tática `exists`.

* *Elimine* nomeando uma testemunha e a sua prova: `cases` (um caso, construtor `intro`) ou `obtain ⟨a, ha⟩ := h` num só passo.

```lean
example : ∃ n : Nat, n * n = 9 := ⟨3, rfl⟩
```

::::cols
:::col
```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  cases h with
  | intro a ha => exact ⟨a, ha.left⟩
```
:::
:::col
```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.right⟩
```
:::
::::

# §2.3 Implicação ponto a ponto

O teorema abaixo combina os dois quantificadores. Uma implicação ponto a ponto transporta a existência de P para Q, e a testemunha não muda.

```lean
theorem exists_imp_exists (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, P x) → ∃ x, Q x := by
  intro hex
  obtain ⟨a, hPa⟩ := hex
  exact ⟨a, h a hPa⟩
```

# §2.4 Leis de negação dos quantificadores

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

* Elas trocam a negação com os quantificadores, estendendo as *leis de De Morgan* da Aula 1.

* A primeira lei é *construtiva* nas duas direções.

* Na segunda, produzir a testemunha exige *raciocínio clássico*, como na primeira lei de De Morgan: duas aplicações de `Classical.byContradiction`.

# §2.4 As duas leis em Lean

::::cols
:::col
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
:::
:::col
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
:::
::::

# §2.4 Além de intro, obtain e exact

* `intro` aceita o *padrão de construtor anônimo*, introduzindo o existencial e o destruindo num só passo.

* Um objetivo negado é uma *função em False*, então um termo de prova com um `fun` que casa padrões a prova, sem táticas.

::::cols
:::col
{lbl}[Intro com padrão]

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨a, hPa⟩
  exact h a hPa
```
:::
:::col
{lbl}[Termo de prova]

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, P x) : ¬∃ x, ¬P x :=
  fun ⟨a, hnPa⟩ => hnPa (h a)
```
:::
::::

# §2.5 A ordem dos quantificadores

* A ordem *determina o que um enunciado afirma*.

* Em ∀ y, ∃ x, R x y, a testemunha x pode *depender de y*; em ∃ x, ∀ y, R x y, uma única testemunha serve para todo y. A *testemunha uniforme* é o enunciado mais forte.

* Quantificadores do *mesmo tipo* comutam; as trocas para ∀ e ∃ apareceram como exemplos nas §2.2 e §2.3.

* Quantificadores de *tipos distintos* não comutam. Só uma direção vale: a ordem mais forte implica a mais fraca.

# §2.5 A troca e o contraexemplo

```lean
theorem exists_forall_swap (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha b⟩
```

A recíproca falha. Sobre ℕ tome R x y como x ≥ y. As duas afirmações do contraexemplo valem em Lean.

::::cols
:::col
```lean
example : ∀ y : Nat, ∃ x : Nat, x ≥ y := by
  intro b
  exact ⟨b, Nat.le_refl b⟩
```
:::
:::col
```lean
example : ¬∃ x : Nat, ∀ y : Nat, x ≥ y := by
  intro ⟨a, ha⟩
  exact absurd (ha (a + 1)) (Nat.not_succ_le_self a)
```
:::
::::

# §2.6 Conjuntos como predicados

* Um conjunto de elementos de α é determinado por *quais elementos pertencem a ele*, então o predicado de pertinência determina o conjunto. Tomamos isso como definição.

* Um conjunto dado por uma propriedade *é* o predicado, e uma prova de pertinência é uma prova da propriedade.

```lean
def Set (α : Type) : Type := α → Prop
```

```lean -show
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩
```

```lean
def Evens : Set Nat := fun n => ∃ k, n = 2 * k

example : (6 : Nat) ∈ Evens := ⟨3, rfl⟩
```

# §2.6 De onde vem o símbolo ∈

* Uma *classe de tipos* declara uma operação e a deixa sem significado; uma `instance` fornece o significado em um tipo. O símbolo chega aos nossos conjuntos em três passos.

* O símbolo é notação do módulo do núcleo `Init.Notation`, e abrevia uma aplicação. O nome à sua direita é o único campo de uma classe de `Init.Prelude`.

```tree
notation:50 a:50 " ∈ " b:50 => Membership.mem b a

class Membership (α : outParam (Type u)) (γ : Type v) where
  mem : γ → α → Prop
```

* O recipiente vem primeiro em `mem` e vem depois na notação, então `x ∈ s` abrevia `Membership.mem s x`.

* O terceiro passo é nosso. O elaborador procura entre as instâncias registradas uma para o tipo de `s`, e `Set α` é uma definição desta aula, então sem uma instância nossa a busca falha.

# §2.6 Classes de tipos e instâncias

* As instâncias abaixo encerram essa busca: `x ∈ s` é `s x` por definição, e `⊆`, `∪` e `∩` definem-se a partir dela.

```lean
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩

instance : HasSubset (Set α) :=
  ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩

instance : Union (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩

instance : Inter (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩
```

{lbl}[Cada notação desdobra-se na sua definição]

```lean
example (α : Type) (s t : Set α) (h : s ⊆ t)
    (x : α) (hx : x ∈ s) : x ∈ t := h x hx

example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s) : x ∈ s ∪ t := Or.inl hx

example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s ∩ t) : x ∈ t := hx.right
```

# §2.6 O paradoxo de Russell

* A teoria ingênua de conjuntos admite um conjunto para *cada propriedade*. Tome R como o conjunto de todos os conjuntos que não são elementos de si mesmos.

* Então *R ∈ R vale exatamente quando R ∉ R*, uma contradição, e a teoria colapsa.

* Em Lean, s : Set α contém apenas elementos de α, e o próprio s tem tipo Set α, não α, então `s ∈ s` *não é bem tipado*. Não há como enunciar a propriedade que define R, e o paradoxo não ocorre.

{cite}[B. Russell, carta a Frege, 16 de junho de 1902.]

# §2.6 Inclusão, união e interseção

* A inclusão s ⊆ t é uma *implicação universalmente quantificada*, então as suas provas começam com `intro x hx`.

* A pertinência a ∩ é uma *conjunção* e a ∪ uma *disjunção*; as regras dos conectivos da Aula 1 aplicam-se. Identidades de conjuntos são enunciadas como *inclusões*, pois a igualdade exige extensionalidade.

::::cols
:::col
```lean
theorem inter_subset_left (α : Type) (s t : Set α) :
    s ∩ t ⊆ s := by
  intro x hx
  exact hx.left
```
:::
:::col
```lean
theorem union_subset_swap (α : Type) (s t : Set α) :
    s ∪ t ⊆ t ∪ s := by
  intro x hx
  cases hx with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
```
:::
::::

# Resumo

* Um *predicado* é uma função `α → Prop`; quantificadores ligam a sua variável e produzem uma proposição.

* ∀: introduza com `intro`; elimine por instanciação, `h a` ou `specialize`.

* ∃: introduza com uma *testemunha*, `⟨3, rfl⟩` ou `exists`; elimine com `obtain ⟨a, ha⟩ := h`.

* As leis de negação trocam ¬ com os quantificadores; ¬∃ é construtiva nas duas direções, ¬∀ exige `Classical.byContradiction`.

* A ordem dos quantificadores importa: a testemunha uniforme ∃ x, ∀ y é mais forte, e só vale (∃ x, ∀ y) → (∀ y, ∃ x).

* Um conjunto é o seu predicado de pertinência, `Set α := α → Prop`, com instâncias `Membership`, `HasSubset`, `Union`, `Inter` dando a notação.

* Provas de inclusão começam com `intro x hx`; a pertinência a ∩ é uma conjunção e a ∪ uma disjunção, ponto a ponto.

Exercícios: veja as [notas de aula](../pt/Aula-2___-L___gica-de-Predicados-e-Conjuntos/).
