import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option lectures.language "pt"

#doc (Manual) "Aula 2: Lógica de Predicados e Conjuntos" =>

%%%
tag := "aula-2"
%%%

```lean -show
namespace Lecture2
```

Esta aula estende a lógica proposicional com quantificadores e introduz conjuntos, seguindo os capítulos [2](https://djvelleman.github.io/HTPIwL/Chap2.html) e [3](https://djvelleman.github.io/HTPIwL/Chap3.html) de [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). Ela apresenta as regras de prova dos quantificadores universal e existencial, as leis que os relacionam sob negação e conjuntos como predicados em Lean.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-2.pt.html).*

# Predicados e Quantificadores

A Aula 1 excluiu "x é par" das proposições porque a sua verdade depende da variável livre x. Um *predicado* torna essa dependência explícita. Um predicado sobre um tipo α atribui uma proposição a cada elemento de α, então em Lean um predicado é uma função de tipo `α → Prop`.

```lean (name := checkPred)
#check fun n : Nat => n > 3
```
```leanOutput checkPred
fun n => n > 3 : Nat → Prop
```

Quantificadores ligam a variável de um predicado e produzem uma proposição, e a {numref}[tbl-quantifiers] nomeia os dois.{margin}[G. Frege, *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*, Verlag von Louis Nebert, Halle, 1879.] Escrevemos P x para a proposição que o predicado P produz em x.

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

{tabcap "tbl-quantifiers"}[Os dois quantificadores, com os seus símbolos e leituras.]

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

## Exemplos

Os exemplos abaixo combinam as duas regras desta seção com os conectivos da Aula 1.

{ex "ex-universal-quantifier-implication-reflexive-each-element"}[] A implicação é reflexiva em cada elemento.

```lean
example (α : Type) (P : α → Prop) : ∀ x, P x → P x := by
  intro a hPa
  exact hPa
```

{ex "ex-universal-quantifier-universal-hypothesis-instantiates-any"}[] Uma hipótese universal se instancia em qualquer elemento dado. A aplicação `h a` já é a prova, então nenhuma tática é necessária.

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, P x) (a : α) : P a := h a
```

{ex "ex-universal-quantifier-instantiating-both-variables-binary"}[] Instanciar as duas variáveis de um predicado binário no mesmo elemento produz a diagonal. A tática `apply` unifica a hipótese com o objetivo e encontra as duas instanciações.

```lean
example (α : Type) (R : α → α → Prop)
    (h : ∀ x, ∀ y, R x y) : ∀ x, R x x := by
  intro a
  apply h
```

{ex "ex-universal-quantifier-consecutive-universal-quantifiers-commute"}[] Quantificadores universais consecutivos comutam.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∀ x, ∀ y, R x y) : ∀ y, ∀ x, R x y := by
  intro b a
  exact h a b
```

{ex "ex-universal-quantifier-conjunction-commutes-under-quantifier"}[] A conjunção comuta sob o quantificador. A tática `have` registra a hipótese instanciada, e `constructor` divide o objetivo nas duas partes da conjunção.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∧ Q x) : ∀ x, Q x ∧ P x := by
  intro a
  have ha := h a
  constructor
  · exact ha.right
  · exact ha.left
```

{ex "ex-universal-quantifier-disjunct-entails-disjunction-each"}[] Um disjunto implica a disjunção em cada elemento. Aplicar `Or.inl` reduz a disjunção ao seu lado esquerdo.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x) : ∀ x, P x ∨ Q x := by
  intro a
  apply Or.inl
  exact h a
```

{ex "ex-universal-quantifier-pointwise-disjunction-whose-left"}[] Uma disjunção pontual cujo lado esquerdo falha em todo elemento produz o seu lado direito.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∨ Q x) (hn : ∀ x, ¬P x) : ∀ x, Q x := by
  intro a
  cases h a with
  | inl hPa => exact absurd hPa (hn a)
  | inr hQa => exact hQa
```

{ex "ex-universal-quantifier-contraposition-applies-each-element"}[] A contraposição se aplica em cada elemento. A prova raciocina para frente, derivando Q a com `have` antes de chegar à contradição.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hn : ∀ x, ¬Q x) : ∀ x, ¬P x := by
  intro a hPa
  have hQa : Q a := h a hPa
  exact hn a hQa
```

{ex "ex-universal-quantifier-antecedent-does-not-mention"}[] Um antecedente que não menciona a variável quantificada move-se para dentro do quantificador.

```lean
example (α : Type) (P : Prop) (Q : α → Prop)
    (h : P → ∀ x, Q x) : ∀ x, P → Q x := by
  intro a hP
  exact h hP a
```

{ex "ex-universal-quantifier-when-type-has-element"}[] Quando o tipo tem um elemento, ∀ x, P x refuta ∀ x, ¬P x.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (h : ∀ x, P x) : ¬∀ x, ¬P x := by
  intro hn
  exact hn a (h a)
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

## Exemplos

Os exemplos abaixo combinam a regra da testemunha e a eliminação do existencial com os conectivos da Aula 1.

{ex "ex-existential-quantifier-witness-7-proves-concrete"}[] A testemunha 7 prova um existencial concreto por computação.

```lean
example : ∃ n : Nat, n + 5 = 12 := ⟨7, rfl⟩
```

{ex "ex-existential-quantifier-both-0-1-satisfy"}[] Tanto 0 quanto 1 satisfazem `n * n = n`, e a prova escolhe a testemunha 1.

```lean
example : ∃ n : Nat, n * n = n := by
  exists 1
```

{ex "ex-existential-quantifier-element-together-proof-introduction"}[] Um elemento junto com uma prova nele é a regra de introdução empacotada como um par.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (hPa : P a) : ∃ x, P x := ⟨a, hPa⟩
```

{ex "ex-existential-quantifier-inhabited-type-universal-statement"}[] Em um tipo habitado, uma afirmação universal produz uma existencial. A tática `specialize` instancia a hipótese, e `exists` a encontra como hipótese do contexto.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (h : ∀ x, P x) : ∃ x, P x := by
  specialize h a
  exists a
```

{ex "ex-existential-quantifier-proposition-does-not-mention"}[] Uma proposição que não menciona a variável ligada escapa do quantificador.

```lean
example (α : Type) (P : Prop) (h : ∃ _ : α, P) : P := by
  obtain ⟨_, hP⟩ := h
  exact hP
```

{ex "ex-existential-quantifier-conjunction-commutes-under-quantifier"}[] A conjunção comuta sob o quantificador.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro a ha => exact ⟨a, ha.right, ha.left⟩
```

{ex "ex-existential-quantifier-existential-conjunction-splits-two"}[] Um existencial de uma conjunção se divide, e as duas partes compartilham a testemunha. O padrão do `obtain` desestrutura a conjunção sob o quantificador em um só passo.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : (∃ x, P x) ∧ (∃ x, Q x) := by
  obtain ⟨a, hPa, hQa⟩ := h
  constructor
  · exact ⟨a, hPa⟩
  · exact ⟨a, hQa⟩
```

{ex "ex-existential-quantifier-witness-p-x-also"}[] A testemunha de P x também testemunha Q x → P x.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x) : ∃ x, Q x → P x := by
  obtain ⟨a, hPa⟩ := h
  exists a
  intro _hQ
  exact hPa
```

{ex "ex-existential-quantifier-consecutive-existential-quantifiers-commute"}[] Quantificadores existenciais consecutivos comutam.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∃ y, R x y) : ∃ y, ∃ x, R x y := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨b, a, hab⟩
```

{ex "ex-existential-quantifier-existential-disjunction-whose-right"}[] Uma disjunção existencial cujo lado direito falha em todo elemento testemunha o seu lado esquerdo.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∨ Q x) (hn : ∀ x, ¬Q x) : ∃ x, P x := by
  obtain ⟨a, ha⟩ := h
  cases ha with
  | inl hPa => exact ⟨a, hPa⟩
  | inr hQa => exact absurd hQa (hn a)
```

# Leis de Negação dos Quantificadores

As leis de De Morgan da Aula 1 trocam a negação com a conjunção e a disjunção. As leis da {numref}[tbl-quantifier-negation] trocam a negação com os quantificadores.

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

{tabcap "tbl-quantifier-negation"}[As leis de negação dos quantificadores.]

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

## Exemplos

Os exemplos abaixo aplicam as duas leis de negação e as combinam com os conectivos da Aula 1. Os Exemplos 6 e 10 raciocinam classicamente.

{ex "ex-quantifier-negation-laws-property-fails-everywhere-admits"}[] Uma propriedade que falha em toda parte não admite testemunha. Esta é a direção construtiva da primeira lei. O padrão de construtor anônimo em `intro` introduz o existencial e o destrói num só passo, então nenhum `obtain` é necessário.

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨a, hPa⟩
  exact h a hPa
```

{ex "ex-quantifier-negation-laws-conversely-if-no-witness"}[] Reciprocamente, se não existe testemunha, a propriedade falha em cada elemento.

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro a hPa
  exact h ⟨a, hPa⟩
```

{ex "ex-quantifier-negation-laws-witness-refutes-negation-existential"}[] Uma testemunha refuta a negação do existencial.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (hPa : P a) : ¬¬∃ x, P x := by
  intro hn
  exact hn ⟨a, hPa⟩
```

{ex "ex-quantifier-negation-laws-property-holds-everywhere-excludes"}[] Uma propriedade que vale em toda parte exclui qualquer contraexemplo. A prova é um termo de prova, como na Aula 1. Como o objetivo negado é uma função em `False`, um `fun` que casa o padrão da testemunha do contraexemplo o prova.

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, P x) : ¬∃ x, ¬P x :=
  fun ⟨a, hnPa⟩ => hnPa (h a)
```

{ex "ex-quantifier-negation-laws-counterexample-refutes-universal-statement"}[] Um contraexemplo refuta o enunciado universal. Esta é a direção construtiva da segunda lei.

```lean
example (α : Type) (P : α → Prop)
    (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hall
  obtain ⟨a, hnPa⟩ := h
  exact hnPa (hall a)
```

{ex "ex-quantifier-negation-laws-converse-example-4-requires"}[] A recíproca do {numref}[ex-quantifier-negation-laws-property-holds-everywhere-excludes] exige raciocínio clássico. Dada a ausência de contraexemplos, `Classical.byContradiction` prova a propriedade em cada elemento.

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∃ x, ¬P x) : ∀ x, P x := by
  intro a
  apply Classical.byContradiction
  intro hnPa
  exact h ⟨a, hnPa⟩
```

{ex "ex-quantifier-negation-laws-pointwise-implication-transports-absence"}[] Uma implicação ponto a ponto transporta a ausência de testemunhas da conclusão para a premissa. O padrão em `intro` de novo destrói o existencial na introdução.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hn : ¬∃ x, Q x) : ¬∃ x, P x := by
  intro ⟨a, hPa⟩
  exact hn ⟨a, h a hPa⟩
```

{ex "ex-quantifier-negation-laws-when-no-element-satisfies"}[] Quando nenhum elemento satisfaz as duas propriedades, cada elemento que satisfaz a primeira não satisfaz a segunda.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ¬∃ x, P x ∧ Q x) : ∀ x, P x → ¬Q x := by
  intro a hPa hQa
  exact h ⟨a, hPa, hQa⟩
```

{ex "ex-quantifier-negation-laws-negating-existential-disjunction-yields"}[] A negação de um existencial de uma disjunção dá, em cada elemento, a conjunção das negações, o que combina a primeira lei com uma lei de De Morgan.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ¬∃ x, P x ∨ Q x) : ∀ x, ¬P x ∧ ¬Q x := by
  intro a
  constructor
  · intro hPa
    exact h ⟨a, Or.inl hPa⟩
  · intro hQa
    exact h ⟨a, Or.inr hQa⟩
```

{ex "ex-quantifier-negation-laws-theorem-this-section-extracts"}[] O teorema `not_forall_exists` desta seção extrai um contraexemplo, e a implicação ponto a ponto o converte em testemunha.

```lean
example (α : Type) (P Q : α → Prop) (h : ¬∀ x, P x)
    (hq : ∀ x, ¬P x → Q x) : ∃ x, Q x := by
  obtain ⟨a, hnPa⟩ := not_forall_exists α P h
  exact ⟨a, hq a hnPa⟩
```

# A Ordem dos Quantificadores

A ordem dos quantificadores determina o que um enunciado afirma. Em ∀ y, ∃ x, R x y, a testemunha x pode depender de y, e valores distintos de y podem exigir testemunhas distintas. Em ∃ x, ∀ y, R x y, uma única testemunha x satisfaz R com todo y de uma vez. A segunda forma afirma uma testemunha uniforme, então é o enunciado mais forte.

Quantificadores do mesmo tipo comutam, e os exemplos das duas seções anteriores provaram as trocas para ∀ e para ∃. Quantificadores de tipos distintos não comutam, e apenas uma direção da troca vale. A ordem mais forte implica a mais fraca. Uma testemunha que satisfaz R com todo y em particular satisfaz R com cada y dado.

```lean
theorem exists_forall_swap (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha b⟩
```

A recíproca falha. Sobre os números naturais, tome R x y como x ≥ y. Então ∀ y, ∃ x, R x y vale, pois cada y satisfaz y ≥ y, e ∃ x, ∀ y, R x y afirma que algum número natural é maior ou igual a todo número natural, o que é falso.

## Exemplos

Os exemplos abaixo movem quantificadores uns sobre os outros. Os dois últimos provam em Lean as duas afirmações do contraexemplo acima.

{ex "ex-order-quantifiers-witness-relates-every-element"}[] Uma testemunha que se relaciona com todo elemento em particular se relaciona consigo mesma.

```lean
example (α : Type) (R : α → α → Prop)
    (h : ∃ x, ∀ y, R x y) : ∃ x, R x x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha a⟩
```

{ex "ex-order-quantifiers-existential-universal-statement-yields"}[] Um enunciado existencial-universal dá o duplamente existencial quando o tipo interno tem um elemento.

```lean
example (α β : Type) (R : α → β → Prop) (b : β)
    (h : ∃ x, ∀ y, R x y) : ∃ x, ∃ y, R x y := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, b, ha b⟩
```

{ex "ex-order-quantifiers-doubly-universal-statement-yields"}[] Um enunciado duplamente universal dá a ordem mista quando o tipo das testemunhas tem um elemento.

```lean
example (α β : Type) (R : α → β → Prop) (a : α)
    (h : ∀ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  exact ⟨a, h a b⟩
```

{ex "ex-order-quantifiers-theorem-function-applying-hypothesis"}[] O teorema `exists_forall_swap` é uma função, e aplicá-lo a uma hipótese e a um elemento dá a conclusão instanciada. A prova é a própria aplicação.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) (b : β) : ∃ x, R x b :=
  exists_forall_swap α β R h b
```

{ex "ex-order-quantifiers-conjunction-under-two-quantifiers"}[] Uma conjunção sob os dois quantificadores projeta-se na sua parte esquerda, preservando a testemunha.

```lean
example (α β : Type) (R S : α → β → Prop)
    (h : ∃ x, ∀ y, R x y ∧ S x y) : ∃ x, ∀ y, R x y := by
  obtain ⟨a, ha⟩ := h
  exists a
  intro b
  exact (ha b).left
```

{ex "ex-order-quantifiers-two-existential-universal-hypotheses"}[] Duas hipóteses existencial-universais combinam-se numa conjunção duplamente existencial, e cada testemunha instancia o universal da outra.

```lean
example (α β : Type) (R S : α → β → Prop)
    (h1 : ∃ x, ∀ y, R x y) (h2 : ∃ y, ∀ x, S x y) :
    ∃ x, ∃ y, R x y ∧ S x y := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a, b, ha b, hb a⟩
```

{ex "ex-order-quantifiers-three-quantifiers-existential-witness"}[] Com três quantificadores, a testemunha existencial serve para todo z, então o universal externo move-se para a frente.

```lean
example (α β γ : Type) (T : α → β → γ → Prop)
    (h : ∃ x, ∀ y, ∀ z, T x y z) :
    ∀ z, ∃ x, ∀ y, T x y z := by
  intro c
  obtain ⟨a, ha⟩ := h
  exists a
  intro b
  exact ha b c
```

{ex "ex-order-quantifiers-contraposition-transports-negation-opposite"}[] A contraposição de `exists_forall_swap` transporta a negação na direção oposta.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ¬∀ y, ∃ x, R x y) : ¬∃ x, ∀ y, R x y := by
  intro hex
  exact h (exists_forall_swap α β R hex)
```

{ex "ex-order-quantifiers-first-claim-counterexample-above"}[] A primeira afirmação do contraexemplo acima. Cada número natural é maior ou igual a si mesmo.

```lean
example : ∀ y : Nat, ∃ x : Nat, x ≥ y := by
  intro b
  exact ⟨b, Nat.le_refl b⟩
```

{ex "ex-order-quantifiers-second-claim-no-natural"}[] A segunda afirmação. Nenhum número natural é maior ou igual a todo número natural, pois a + 1 excede a. O lema `Nat.not_succ_le_self` refuta a ≥ a + 1.

```lean
example : ¬∃ x : Nat, ∀ y : Nat, x ≥ y := by
  intro ⟨a, ha⟩
  exact absurd (ha (a + 1)) (Nat.not_succ_le_self a)
```

# Conjuntos

O [capítulo 3](https://djvelleman.github.io/HTPIwL/Chap3.html) de HTPIwL desenvolve provas sobre conjuntos. Um conjunto de elementos de um tipo α é determinado por quais elementos pertencem a ele, então o predicado de pertinência determina o conjunto. Em Lean, tomamos essa propriedade como a definição.

```savedLean
def Set (α : Type) : Type := α → Prop
```

Todo elemento de um conjunto vem do tipo fixo α, e essa disciplina de tipos bloqueia o *paradoxo de Russell*.{margin}[B. Russell, carta a Frege, 16 de junho de 1902. Em J. van Heijenoort, *From Frege to Gödel: A Source Book in Mathematical Logic, 1879–1931*, Harvard University Press, 1967, pp. 124–125.] A teoria ingênua de conjuntos admite um conjunto para cada propriedade. Tome R como o conjunto de todos os conjuntos que não são elementos de si mesmos. Então R ∈ R vale exatamente quando R ∉ R, o que é uma contradição, e a teoria colapsa. Em Lean, um conjunto s : Set α contém apenas elementos de α, e o próprio s tem tipo Set α, não α, então a expressão s ∈ s não é bem tipada. Não há como enunciar a propriedade que define R nem formar a coleção, então o paradoxo não ocorre.

Lean resolve notações como x ∈ s por meio de *classes de tipos*. A classe `Membership` declara a notação, e uma declaração `instance` dá o seu significado num tipo particular. Quando Lean elabora x ∈ s, ele procura entre as instâncias registradas uma que cubra o tipo de s. `Set α` é uma definição desta aula, então nenhuma instância a cobre ainda, e a notação falharia. A instância abaixo fornece o significado que falta, e x ∈ s desdobra-se por definição na aplicação s x. Nesta instância e nas seguintes, Lean liga a variável de tipo livre α automaticamente.

```savedLean
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩
```

Um conjunto dado por uma propriedade é o próprio predicado, e uma prova de pertinência é uma prova da propriedade. A notação matemática escreve esse conjunto por compreensão, como o conjunto de todos os n que satisfazem `∃ k, n = 2 * k`. O núcleo de Lean não tem notação por compreensão, então escrevemos o predicado diretamente.

```lean
def Evens : Set Nat := fun n => ∃ k, n = 2 * k

example : (6 : Nat) ∈ Evens := ⟨3, rfl⟩
```

A inclusão s ⊆ t afirma que todo elemento de s pertence a t.

```savedLean
instance : HasSubset (Set α) :=
  ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩
```

A notação desdobra-se na sua definição. Uma hipótese h : s ⊆ t aplica-se a um elemento e a uma prova de pertinência.

```lean
example (α : Type) (s t : Set α) (h : s ⊆ t)
    (x : α) (hx : x ∈ s) : x ∈ t := h x hx
```

Uma inclusão é uma implicação universalmente quantificada, então as suas provas começam considerando um elemento arbitrário junto com a suposição de que ele pertence ao lado esquerdo. A união e a interseção aplicam os conectivos da Aula 1 ponto a ponto.

```savedLean
instance : Union (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩

instance : Inter (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩
```

As duas notações desdobram-se do mesmo modo, então os termos de prova da Aula 1 constroem e usam pertinências diretamente.

```lean
example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s) : x ∈ s ∪ t := Or.inl hx

example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s ∩ t) : x ∈ t := hx.right
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

Dois conjuntos com os mesmos elementos são iguais. Provar essa igualdade requer princípios de extensionalidade além da lógica apresentada até aqui, então enunciamos identidades de conjuntos como inclusões.

## Exemplos

Os exemplos abaixo provam pertinências e inclusões diretamente a partir das definições. Cada prova de inclusão começa introduzindo um elemento e a sua hipótese de pertinência, e as notações desdobram-se nos conectivos e quantificadores das seções anteriores.

{ex "ex-sets-set-given-predicate-contains"}[] Um conjunto dado por um predicado contém um elemento exatamente quando o predicado vale nele. A testemunha 3 prova que 9 é um quadrado.

```lean
def Squares : Set Nat := fun n => ∃ k, n = k * k

example : (9 : Nat) ∈ Squares := ⟨3, rfl⟩
```

{ex "ex-sets-inclusion-reflexive-proof-introduces"}[] A inclusão é reflexiva. A prova introduz um elemento e a sua hipótese de pertinência e devolve a hipótese sem mudança.

```lean
example (α : Type) (s : Set α) : s ⊆ s := by
  intro x hx
  exact hx
```

{ex "ex-sets-union-contains-left-side"}[] A união contém o seu lado esquerdo. A pertinência à união é uma disjunção, e `Or.inl` escolhe o lado esquerdo.

```lean
example (α : Type) (s t : Set α) : s ⊆ s ∪ t := by
  intro x hx
  exact Or.inl hx
```

{ex "ex-sets-intersection-commutes-inclusion-membership"}[] A interseção comuta como inclusão. A pertinência à interseção é uma conjunção, e o construtor anônimo troca as suas partes.

```lean
example (α : Type) (s t : Set α) : s ∩ t ⊆ t ∩ s := by
  intro x hx
  exact ⟨hx.right, hx.left⟩
```

{ex "ex-sets-union-contains-intersection"}[] A união contém a interseção.

```lean
example (α : Type) (s t : Set α) : s ∩ t ⊆ s ∪ t := by
  intro x hx
  exact Or.inl hx.left
```

{ex "ex-sets-when-t-u-both"}[] Quando t e u contêm s, a sua interseção contém s.

```lean
example (α : Type) (s t u : Set α)
    (h1 : s ⊆ t) (h2 : s ⊆ u) : s ⊆ t ∩ u := by
  intro x hx
  exact ⟨h1 x hx, h2 x hx⟩
```

{ex "ex-sets-when-u-contains-both"}[] Quando u contém os dois lados de uma união, u contém a união. A tática `cases` divide a disjunção.

```lean
example (α : Type) (s t u : Set α)
    (h1 : s ⊆ u) (h2 : t ⊆ u) : s ∪ t ⊆ u := by
  intro x hx
  cases hx with
  | inl hs => exact h1 x hs
  | inr ht => exact h2 x ht
```

{ex "ex-sets-union-fixed-set-preserves"}[] A união com um conjunto fixo preserva a inclusão.

```lean
example (α : Type) (s t u : Set α)
    (h : s ⊆ t) : s ∪ u ⊆ t ∪ u := by
  intro x hx
  cases hx with
  | inl hs => exact Or.inl (h x hs)
  | inr hu => exact Or.inr hu
```

{ex "ex-sets-empty-set-whose-membership"}[] O conjunto vazio, cujo predicado de pertinência é `False` em cada elemento, é subconjunto de todo conjunto. `False.elim` fecha o objetivo.

```lean
def EmptySet (α : Type) : Set α := fun _ => False

example (α : Type) (s : Set α) : EmptySet α ⊆ s := by
  intro x hx
  exact False.elim hx
```

{ex "ex-sets-every-set-subset-universal"}[] Todo conjunto é subconjunto do conjunto universo, cujo predicado de pertinência é `True` em cada elemento.

```lean
def UnivSet (α : Type) : Set α := fun _ => True

example (α : Type) (s : Set α) : s ⊆ UnivSet α := by
  intro x _hx
  exact True.intro
```

# Exemplos Resolvidos

Cada exemplo abaixo aparece de duas formas, como um termo de prova e como uma prova por táticas. As duas apresentam a mesma prova, e Lean verifica os dois scripts na construção das notas. As regras dos quantificadores seguem a mesma disciplina de introdução e eliminação dos conectivos da Aula 1, então omitimos as árvores de derivação e deixamos os termos espelhá-las. Estas proposições são disjuntas dos exemplos das seções anteriores e dos exercícios.

## Contraposição sob quantificadores

A testemunha da falha de Q também testemunha a falha de P, pois a implicação naquele elemento leva uma prova de P a a uma prova de Q a. O padrão em `intro` destrói o existencial.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, ¬Q x) → ∃ x, ¬P x :=
  fun ⟨a, hnQa⟩ => ⟨a, fun hPa => hnQa (h a hPa)⟩
```

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, ¬Q x) → ∃ x, ¬P x := by
  intro ⟨a, hnQa⟩
  exists a
  intro hPa
  exact hnQa (h a hPa)
```

## Uma disjunção de universais

Qualquer que seja o lado que valha, a sua instância em cada elemento prova a disjunção ponto a ponto. O termo elimina a disjunção com `.elim`, e a prova por táticas com `cases`.

```lean
example (α : Type) (P Q : α → Prop) :
    (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x :=
  fun h a =>
    h.elim (fun hp => Or.inl (hp a))
      (fun hq => Or.inr (hq a))
```

```lean
example (α : Type) (P Q : α → Prop) :
    (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  intro h a
  cases h with
  | inl hp => exact Or.inl (hp a)
  | inr hq => exact Or.inr (hq a)
```

## A interseção preserva a inclusão

A inclusão aplica-se à parte esquerda da pertinência, e a parte direita passa sem mudança.

```lean
example (α : Type) (s t u : Set α)
    (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x hx => ⟨h x hx.left, hx.right⟩
```

```lean
example (α : Type) (s t u : Set α)
    (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x hx
  constructor
  · exact h x hx.left
  · exact hx.right
```

## Existência clássica

O teorema `not_forall_exists` da seção de leis de negação produz uma testemunha onde ¬P falha, e `Classical.byContradiction` remove a dupla negação, como na Aula 1.

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∀ x, ¬P x) : ∃ x, P x :=
  (not_forall_exists α (fun x => ¬P x) h).elim
    fun a hnnPa => ⟨a, Classical.byContradiction hnnPa⟩
```

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∀ x, ¬P x) : ∃ x, P x := by
  obtain ⟨a, hnnPa⟩ := not_forall_exists α (fun x => ¬P x) h
  exact ⟨a, Classical.byContradiction hnnPa⟩
```

# Exercícios

Prove cada enunciado em Lean, substituindo `sorry` por uma prova. Baixe o arquivo de exercícios [`Lecture02.lean`](example-code/Lectures/Pt/Lecture02.lean) e abra-o no VS Code. O arquivo já contém as definições de `Set`, pertinência, inclusão, união e interseção.

```savedComment
Exercícios da Aula 2: Lógica de Predicados e Conjuntos.
Substitua cada `sorry` por uma prova. As definições acima
vêm da aula.
```

{exercise "exr-universal-quantifier-distributes-over"}[] O quantificador universal distribui sobre a implicação.

```savedLean -keep
theorem exercise1 (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hP : ∀ x, P x) : ∀ x, Q x := by
  sorry
```

{exercise "exr-existential-quantifier-distributes-over"}[] O quantificador existencial distribui sobre a disjunção.

```savedLean -keep
theorem exercise2 (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry
```

{exercise "exr-eliminate-existential-hypothesis-then"}[] Elimine a hipótese existencial e então instancie a universal na testemunha.

```savedLean -keep
theorem exercise3 (α : Type) (P : α → Prop) (Q : Prop)
    (h : ∃ x, P x → Q) (hP : ∀ x, P x) : Q := by
  sorry
```

{exercise "exr-inclusion-transitive"}[] A inclusão é transitiva.

```savedLean -keep
theorem exercise4 (α : Type) (s t u : Set α)
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  sorry
```

{exercise "exr-intersection-distributes-over-union"}[] A interseção distribui sobre a união.

```savedLean -keep
theorem exercise5 (α : Type) (s t u : Set α) :
    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  sorry
```

```lean -show
end Lecture2
```
