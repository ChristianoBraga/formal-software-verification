import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Aula 1: Motivação e Lógica Proposicional" =>

%%%
tag := "aula-1"
%%%

Esta aula motiva a verificação formal de software e revisa a lógica proposicional, seguindo o capítulo 1 de [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). Ela apresenta os conectivos, as equivalências clássicas e as primeiras provas estruturadas em Lean.

# Por que Verificar Software Formalmente?

Software controla aeronaves, dispositivos médicos, sistemas financeiros e redes de comunicação. Erros nesses sistemas custam dinheiro e vidas. O modo usual de encontrar erros é o teste, e o teste examina finitas execuções de um programa que admite infinitas. Dijkstra enunciou a limitação com precisão.{margin}[E. W. Dijkstra, *Notes on Structured Programming*, EWD249, Technological University Eindhoven, 1970.]

> O teste de programas pode ser usado para mostrar a presença de erros, mas nunca para mostrar a sua ausência!

A verificação formal segue o caminho complementar. Enunciamos uma propriedade de um programa como uma proposição matemática e provamos que toda execução a satisfaz. A prova cobre todas as entradas de uma vez, o que nenhum conjunto finito de testes alcança.

Provas sobre programas reais crescem muito, então delegamos a sua checagem a uma máquina. Um *assistente de prova* é um programa que checa cada passo de uma prova com respeito às regras de uma lógica formal e que ajuda o usuário a construir a prova interativamente. Lean, Rocq (antigo Coq), Isabelle/HOL e Agda são assistentes de prova em uso corrente. Resultados marcantes incluem a verificação do micronúcleo de sistema operacional seL4{margin}[G. Klein et al., *seL4: Formal Verification of an OS Kernel*, Proceedings of SOSP 2009, pp. 207–220.] e do compilador otimizante de C CompCert.{margin}[X. Leroy, *Formal Verification of a Realistic Compiler*, Communications of the ACM 52(7), 2009, pp. 107–115.]

Modelos de linguagem escrevem hoje uma parcela crescente do código. Um modelo produz texto plausível, e plausível não é o mesmo que correto. Código gerado pode invocar funções que não existem, tratar apenas os casos que o seu prompt sugere ou desviar do requisito enunciado de maneiras que sobrevivem à revisão de código. A literatura chama esse modo de falha de alucinação.

A verificação formal, em particular quando automatizada, muda o modo como podemos confiar nesse código.{margin}[L. de Moura, [*The Lean Programming Language and Theorem Prover*](https://leodemoura.github.io/static/etaps2026/), ETAPS 2026.] Quando o código gerado chega com uma prova, checada por máquina, de que satisfaz a sua especificação, o assistente de prova checa a prova independentemente de como o código surgiu, então código alucinado ou simplesmente errado não passa. O ônus da correção move-se de ler o código para escrever a especificação certa. As técnicas desta disciplina aplicam-se sem mudança a código gerado, e a automação das aulas finais, com a tática `mvcgen`, aponta para verificação no ritmo da geração de código.

Nesta disciplina usamos [Lean](https://lean-lang.org). Lean é ao mesmo tempo uma linguagem de programação e um assistente de prova, então podemos escrever um programa e provar as suas propriedades no mesmo sistema. As aulas 1 e 2 revisam a lógica clássica e introduzem a linguagem de provas de Lean, seguindo HTPIwL. As aulas 3 a 8 seguem [LoVe](https://github.com/lean-forward/logical_verification_2026) por prova interativa, programação funcional e predicados indutivos. O bloco final trata a semântica de uma linguagem imperativa, a lógica de Hoare e a verificação prática com a tática `mvcgen`.

# Proposições

Uma *proposição* é uma sentença declarativa que é verdadeira ou falsa. "7 é primo" e "todo número par maior que 2 é a soma de dois primos" são proposições. "Feche a porta" e "x é par" não são, a primeira porque ordena em vez de afirmar, a segunda porque a sua verdade depende da variável livre x.

Em Lean, o tipo `Prop` classifica as proposições.

```lean (name := checkTrue)
#check True
```
```leanOutput checkTrue
True : Prop
```

Escrevemos P, Q, R para *variáveis proposicionais*, que representam proposições arbitrárias.

# Conectivos

Conectivos constroem proposições compostas a partir de proposições mais simples.

:::table +header
*
  * Símbolo
  * Nome
  * Leitura
*
  * ¬P
  * negação
  * não P
*
  * P ∧ Q
  * conjunção
  * P e Q
*
  * P ∨ Q
  * disjunção
  * P ou Q
*
  * P → Q
  * implicação
  * se P então Q
*
  * P ↔ Q
  * bicondicional
  * P se e somente se Q
:::

O valor de verdade de uma proposição composta depende apenas dos valores de verdade das suas partes. A tabela abaixo define os cinco conectivos, com V para verdadeiro e F para falso.

:::table +header
*
  * P
  * Q
  * ¬P
  * P ∧ Q
  * P ∨ Q
  * P → Q
  * P ↔ Q
*
  * V
  * V
  * F
  * V
  * V
  * V
  * V
*
  * V
  * F
  * F
  * F
  * V
  * F
  * F
*
  * F
  * V
  * V
  * F
  * V
  * V
  * F
*
  * F
  * F
  * V
  * F
  * F
  * V
  * V
:::

Duas linhas da coluna da implicação merecem atenção. Quando P é falso, P → Q é verdadeira independentemente de Q. Uma implicação nada afirma sobre os casos em que o seu antecedente falha, então esses casos não podem refutá-la. A disjunção é *inclusiva*, então P ∨ Q é verdadeira quando os dois disjuntos o são.

# Equivalência Lógica

Uma *valoração* atribui um valor de verdade a cada variável proposicional. Uma proposição é uma *tautologia* quando é verdadeira sob toda valoração. Duas proposições A e B são *logicamente equivalentes*, escrito A ≡ B, quando têm o mesmo valor de verdade sob toda valoração, isto é, quando A ↔ B é uma tautologia.

As equivalências clássicas abaixo aparecem constantemente em provas.

:::table +header
*
  * Nome
  * Equivalência
*
  * De Morgan
  * ¬(P ∧ Q) ≡ ¬P ∨ ¬Q
*
  * De Morgan
  * ¬(P ∨ Q) ≡ ¬P ∧ ¬Q
*
  * Dupla negação
  * ¬¬P ≡ P
*
  * Contrapositiva
  * P → Q ≡ ¬Q → ¬P
*
  * {hover "A implicação chama-se material porque a sua verdade depende apenas dos valores de verdade de P e Q, e não de alguma conexão de significado ou causalidade entre eles. O termo vem de Russell, The Principles of Mathematics, 1903."}[Implicação material]
  * P → Q ≡ ¬P ∨ Q
:::

Uma tabela-verdade verifica cada equivalência. Para a segunda lei de De Morgan, as colunas de ¬(P ∨ Q) e de ¬P ∧ ¬Q coincidem nas quatro valorações.

:::table +header
*
  * P
  * Q
  * P ∨ Q
  * ¬(P ∨ Q)
  * ¬P
  * ¬Q
  * ¬P ∧ ¬Q
*
  * V
  * V
  * V
  * F
  * F
  * F
  * F
*
  * V
  * F
  * V
  * F
  * F
  * V
  * F
*
  * F
  * V
  * V
  * F
  * V
  * F
  * F
*
  * F
  * F
  * F
  * V
  * V
  * V
  * V
:::

Tabelas-verdade decidem qualquer questão proposicional, mas o seu tamanho cresce exponencialmente no número de variáveis, e elas não se estendem aos quantificadores da Aula 2. Regras de dedução, aplicadas um passo por vez, escalam e generalizam. O restante desta aula desenvolve tais provas em Lean.

# Primeiras Provas em Lean

Em Lean, enunciamos uma proposição e a provamos em uma única declaração. A palavra-chave `example` introduz um enunciado anônimo, e `theorem` introduz um enunciado com nome. As hipóteses aparecem antes dos dois-pontos como suposições nomeadas, e a proposição a provar, o *objetivo*, aparece depois.

A prova mais simples usa uma hipótese diretamente.

```lean
example (P : Prop) (h : P) : P := h
```

Aqui `h` nomeia a suposição de que P vale, e a prova é o próprio `h`. Uma prova de uma proposição é um termo cujo tipo é aquela proposição. A Aula 3 desenvolve essa correspondência entre proposições e tipos.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, em *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980.]

A maioria das provas usa *táticas*, comandos que transformam o objetivo passo a passo. A palavra-chave `by` entra no modo de táticas. Cada conectivo vem com regras para *introduzi-lo*, provando um objetivo daquela forma, e regras para *eliminá-lo*, usando uma hipótese daquela forma.

## Implicação

A tática `intro` introduz uma implicação. Para provar P → Q, suponha P sob um nome escolhido e prove Q.

```lean
example (P Q : Prop) (hQ : Q) : P → Q := by
  intro _hP
  exact hQ
```

A tática `exact` fecha o objetivo com um termo que o prova. Para usar uma implicação, aplique-a a uma prova do seu antecedente. Uma hipótese hPQ de tipo P → Q é uma função de provas de P em provas de Q, então `hPQ hP` prova Q. Esta é a regra de *modus ponens*.

```lean
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := hPQ hP
```

A tática `apply` usa a mesma regra na direção regressiva. Aplicar hPQ ao objetivo Q deixa P como novo objetivo.

```lean
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP
```

A tática `have` raciocina progressivamente, adicionando uma nova hipótese derivada das atuais, e `show` enuncia o objetivo corrente explicitamente. As duas fazem as provas se lerem como argumentos matemáticos estruturados.

```lean
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R)
    (hP : P) : R := by
  have hQ : Q := hPQ hP
  show R
  exact hQR hQ
```

## Conjunção

Para provar P ∧ Q, prove as duas partes. A tática `constructor` divide o objetivo em dois, e o marcador `·` delimita a prova de cada um.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left
```

Para usar uma conjunção, projete as suas partes com `.left` e `.right`. O construtor anônimo `⟨_, _⟩` constrói o par diretamente, dando uma prova em estilo de termo.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩
```

## Disjunção

Para provar P ∨ Q, escolha um lado. `Or.inl` a prova a partir de P, e `Or.inr` a prova a partir de Q. Para usar uma disjunção, raciocine por casos. A tática `cases` produz um objetivo por disjunto.

```lean
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

## Negação

Em Lean, ¬P é *definida* como P → False, onde `False` é a proposição sem prova. Uma prova de ¬P é uma função que transforma qualquer prova de P em uma prova de `False`.

```lean
example (P : Prop) (hP : P) (hnP : ¬P) : False := hnP hP
```

Toda tática para implicação, portanto, funciona para negação. A direção contrapositiva abaixo precisa apenas de `intro` e de aplicação.

```lean
theorem contrapositive (P Q : Prop) (hPQ : P → Q) :
    ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (hPQ hP)
```

Introduzir a dupla negação é igualmente direto.

```lean
example (P : Prop) (hP : P) : ¬¬P := fun hnP => hnP hP
```

A segunda lei de De Morgan combina as regras vistas até aqui. A tática `constructor` também introduz um bicondicional, dividindo-o nas duas implicações.

```lean
theorem deMorgan_or (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP
      exact h (Or.inl hP)
    · intro hQ
      exact h (Or.inr hQ)
  · intro h hPQ
    cases hPQ with
    | inl hP => exact h.left hP
    | inr hQ => exact h.right hQ
```

## Raciocínio Clássico

As regras usadas até aqui são *construtivas*. Dois princípios da lógica clássica não decorrem delas, a lei do terceiro excluído e a eliminação da dupla negação. Lean fornece os dois no namespace `Classical`.

```lean (name := checkEm)
#check Classical.em
```
```leanOutput checkEm
Classical.em (p : Prop) : p ∨ ¬p
```

`Classical.byContradiction` prova P a partir de uma prova de que ¬P é impossível. Com ela, a eliminação da dupla negação está a uma aplicação de distância.

```lean
theorem not_not_elim (P : Prop) (h : ¬¬P) : P := by
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

A primeira lei de De Morgan requer raciocínio clássico. Uma análise de casos sobre `Classical.em P` decide qual disjunto provar.

```lean
theorem deMorgan_and (P Q : Prop) : ¬(P ∧ Q) → ¬P ∨ ¬Q := by
  intro h
  cases Classical.em P with
  | inl hP => exact Or.inr (fun hQ => h ⟨hP, hQ⟩)
  | inr hnP => exact Or.inl hnP
```

# Exercícios

Prove cada enunciado em Lean, substituindo `sorry` por uma prova. Baixe o arquivo de exercícios [`Lecture01.lean`](../../example-code/Lectures/Pt/Lecture01.lean) e abra-o no VS Code.

```savedComment
Exercícios da Aula 1: Motivação e Lógica Proposicional.
Substitua cada `sorry` por uma prova.
```

Exercício 1. A implicação compõe.

```savedLean
theorem exercise1 (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry
```

Exercício 2. A conjunção distribui sobre a disjunção.

```savedLean
theorem exercise2 (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

Exercício 3. A disjunção associa.

```savedLean
theorem exercise3 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry
```

Exercício 4. Esta direção da primeira lei de De Morgan é construtiva.

```savedLean
theorem exercise4 (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry
```

Exercício 5. Lei de Peirce.{margin}[C. S. Peirce, *On the Algebra of Logic: A Contribution to the Philosophy of Notation*, American Journal of Mathematics 7(2), 1885, pp. 180–196.] Ela requer raciocínio clássico; considere uma análise de casos sobre `Classical.em P`.

```savedLean
theorem exercise5 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry
```
