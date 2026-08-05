/-
Slides da Aula 1, gerados a partir de fontes verificadas. Cada
seção de nível superior é um slide. Todo código Lean é elaborado
na construção e é idêntico ao código das notas de aula
(`Lectures/Pt/Lecture01.lean`) onde os dois coincidem. As árvores
de derivação são texto preformatado em blocos `tree`.
-/

import VersoManual
import Lectures.Meta.SlideDeck

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Motivação e Lógica Proposicional" =>

Conectivos, equivalências, dedução natural e provas em Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-1___-Motiva______o-e-L___gica-Proposicional/)

Baseada em [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL), capítulo [1](https://djvelleman.github.io/HTPIwL/Chap1.html).

# §1.1 O teste mostra presença, não ausência

* Software controla aeronaves, dispositivos médicos, sistemas financeiros e redes de comunicação. Erros custam dinheiro e vidas.

* O teste examina *finitas* execuções de um programa que admite *infinitas*.

> O teste de programas pode ser usado para mostrar a presença de erros, mas nunca para mostrar a sua ausência!

{cite}[E. W. Dijkstra, [_Notes on Structured Programming_](https://www.cs.utexas.edu/~EWD/ewd02xx/EWD249.PDF), EWD249, 1970.]

# §1.1 O caminho complementar

* Enunciamos uma propriedade de um programa como uma *proposição matemática*.

* Provamos que *toda execução* a satisfaz; a prova cobre todas as entradas de uma vez.

* Um *assistente de prova* verifica cada passo com respeito às regras de uma lógica formal e ajuda a construir a prova interativamente.

* Em uso corrente: *Lean*, Rocq (antigo Coq), Isabelle/HOL, Agda. Marcos: o micronúcleo [seL4](https://trustworthy.systems/publications/nictaabstracts/Klein_EHACDEEKNSTW_09.abstract) e o compilador [CompCert](https://xavierleroy.org/publi/compcert-CACM.pdf).

# §1.1 Código gerado

* Modelos de linguagem escrevem hoje uma parcela crescente do código. *Plausível não é o mesmo que correto*; o modo de falha é a alucinação.

* O assistente de prova verifica a prova *independentemente de como o código surgiu*, então código errado não passa.

* O ônus da correção move-se de *ler o código* para *escrever a especificação certa*.

# §1.2–1.3 Proposições e conectivos

* Uma *proposição* é uma sentença declarativa que é verdadeira ou falsa. Em Lean o tipo `Prop` as classifica.

* Conectivos constroem proposições compostas: `¬P`, `P ∧ Q`, `P ∨ Q`, `P → Q`, `P ↔ Q`.

* São *funções de verdade*, então o valor de uma proposição composta depende apenas dos valores das suas partes.

* Uma implicação de antecedente falso é verdadeira, diga o que disser o consequente, porque uma implicação nada afirma sobre esses casos.

* A disjunção é *inclusiva*, então `P ∨ Q` também vale quando P e Q valem juntas.

# §1.4 Equivalência lógica

* Uma *valoração* atribui um valor de verdade a cada variável. Uma *tautologia* é verdadeira sob toda valoração.

* A ≡ B quando `A ↔ B` é uma tautologia, isto é, as duas coincidem sob toda valoração.

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
  * Implicação material
  * P → Q ≡ ¬P ∨ Q
:::

A implicação chama-se _material_ porque a sua verdade depende apenas dos valores de verdade de P e Q, e não de alguma conexão de significado entre eles (Russell, 1903).

# §1.4 Uma tabela-verdade verifica a equivalência

Segunda lei de De Morgan: as colunas de ¬(P ∨ Q) e ¬P ∧ ¬Q coincidem nas quatro valorações.

:::table +header
*
  * P
  * Q
  * P ∨ Q
  * ¬(P ∨ Q)
  * ¬P ∧ ¬Q
*
  * V
  * V
  * V
  * F
  * F
*
  * V
  * F
  * V
  * F
  * F
*
  * F
  * V
  * V
  * F
  * F
*
  * F
  * F
  * F
  * V
  * V
:::

Tabelas-verdade decidem qualquer questão proposicional, mas crescem *exponencialmente* no número de variáveis e não se estendem aos quantificadores da Aula 2. Um *cálculo* deriva em vez de computar.

# §1.4 Cálculos lógicos

* Um cálculo fixa *axiomas* e *regras de inferência*. Uma *derivação* aplica as regras, nenhuma valoração aparece nela, e uma máquina pode verificá-la.

* Ele é *correto* quando todo teorema é uma tautologia e *completo* quando toda tautologia é um teorema. Post provou as duas para o cálculo proposicional em 1921.

* Um cálculo *axiomático* tem muitos axiomas e uma regra. Łukasiewicz e Tarski precisam de três esquemas sobre → e ¬, com o modus ponens.

```tree
   A → (B → A)
   (A → (B → C)) → ((A → B) → (A → C))
   (¬A → ¬B) → (B → A)
```

* A *resolução* mantém uma única regra sobre cláusulas, e é com ela que provadores automáticos buscam (Robinson, 1965).

* A *dedução natural* não tem axiomas e tem duas regras por conectivo, uma que o introduz e outra que o elimina. Esta disciplina a usa.

# §1.5 Dedução natural: as regras do jogo

* Cada regra tem *premissas* acima de uma linha e uma *conclusão* abaixo, aplicadas um passo por vez (Gentzen, 1935).

* Regras de *introdução* provam um conectivo; regras de *eliminação* o usam. Algumas regras *descartam* uma suposição, marcada `[P]`.

```tree
   [P]
    ⋮
    Q                   P → Q    P
  ───────  →I          ─────────────  →E
   P → Q                     Q
```

# §1.5 Conjunção e disjunção

```tree
   P    Q              P ∧ Q            P ∧ Q
  ───────  ∧I         ───────  ∧E₁     ───────  ∧E₂
   P ∧ Q                 P                Q
```

```tree
     P                 Q                              [P]     [Q]
  ───────  ∨I₁      ───────  ∨I₂          P ∨ Q         ⋮       ⋮
   P ∨ Q             P ∨ Q                              R       R
                                        ──────────────────────────  ∨E
                                                     R
```

# §1.5 Negação e a regra clássica

A constante ⊥ é o absurdo, e ¬P abrevia P → ⊥.

```tree
   [P]
    ⋮
    ⊥                  P    ¬P               ⊥
  ───────  ¬I         ─────────  ¬E        ─────  ⊥E
    ¬P                    ⊥                   C
```

As regras acima são *construtivas*. A lógica clássica acrescenta mais uma regra, equivalentemente RAA ou o terceiro excluído.

```tree
   [¬P]
     ⋮
     ⊥
  ─────────  RAA               ───────────  EM
     P                          P ∨ ¬P
```

# §1.6 A sintaxe de Lean

* Uma declaração dá nome a um enunciado e apresenta a sua prova. A palavra-chave vem primeiro, depois o nome, depois as hipóteses entre parênteses, depois o enunciado após os dois-pontos, e por fim a prova após `:=`.

::::cols
:::col
{lbl}[Prova por termo]

```lean
theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩
```

* `fun h => e` constrói uma função, e `f a` aplica uma.

* `⟨a, b⟩` é o *construtor anônimo*; `h.left` e `h.right` desmontam uma conjunção.
:::
:::col
{lbl}[Prova por táticas]

```lean
example (P Q : Prop) (h : P ∧ Q) :
    Q ∧ P := by
  exact ⟨h.right, h.left⟩
```

* `by` entra no modo de táticas, `·` foca um objetivo, e `sorry` marca uma prova ausente.

* `#check` imprime o tipo de um termo, e `--` inicia um comentário.
:::
::::

* Os símbolos lógicos são unicode, digitados com uma abreviação de contrabarra: `\to` para →, `\and` para ∧, `\or` para ∨, `\not` para ¬, `\iff` para ↔, `\bot` para ⊥, `\langle` e `\rangle` para ⟨ ⟩, e `\.` para ·.

# §1.7 Dedução natural em Lean

Uma prova de uma proposição é um *termo* cujo tipo é aquela proposição; uma suposição é uma variável daquele tipo. Cada regra constrói ou desmonta um termo.

:::table +header
*
  * Regra
  * Termo em Lean
  * Exemplo
*
  * suposição
  * um nome de hipótese
  * `h`
*
  * →I
  * `fun h => e`
  * `fun h => h`
*
  * →E
  * aplicação
  * `f a`
*
  * ∧I
  * `⟨_, _⟩`
  * `⟨ha, hb⟩`
*
  * ∧E₁, ∧E₂
  * `.left`, `.right`
  * `h.left`, `h.right`
*
  * ∨I₁, ∨I₂
  * `Or.inl`, `Or.inr`
  * `Or.inl h`
*
  * ∨E
  * `Or.elim` ou `match`
  * `h.elim f g`
*
  * ¬I
  * `fun h => e` em `False`
  * `fun hnP => hnP hP`
*
  * ¬E
  * aplicação em `False`
  * `hnP hP`
*
  * ⊥E
  * `False.elim` ou `absurd`
  * `False.elim h`
:::

# §1.7 Termos de prova a partir da derivação

{exh}[1. P ∧ Q → Q ∧ P]

::::cols
:::col
```tree
   [P ∧ Q]        [P ∧ Q]
  ─────────∧E₂   ─────────∧E₁
      Q              P
    ────────────────────── ∧I
          Q ∧ P
  ────────────────────────── →I
       P ∧ Q → Q ∧ P
```
:::
:::col
```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.right, h.left⟩
```

* `fun h =>` é o →I que descarta P ∧ Q

* `h.right` e `h.left` são ∧E₂ e ∧E₁

* `⟨_, _⟩` é o ∧I
:::
::::

{exh}[2. P → P ∨ Q]

::::cols
:::col
```tree
     [P]
   ───────  ∨I₁
    P ∨ Q
  ───────────  →I
   P → P ∨ Q
```
:::
:::col
```lean
example (P Q : Prop) : P → P ∨ Q :=
  fun h => Or.inl h
```

* `fun h =>` é o →I que descarta P

* `Or.inl` é o ∨I₁, escolhendo o disjunto esquerdo
:::
::::

{exh}[3. P → ¬¬P]

::::cols
:::col
```tree
   [¬P]   [P]
  ────────────  ¬E
       ⊥
    ────────  ¬I
       ¬¬P
   ─────────────  →I
     P → ¬¬P
```
:::
:::col
```lean
example (P : Prop) : P → ¬¬P :=
  fun hP hnP => hnP hP
```

* `fun hP =>` é o →I que descarta P

* `fun hnP =>` é o ¬I que descarta ¬P, pois ¬¬P é ¬P → False

* `hnP hP` é o ¬E, aplicando ¬P a P para chegar a ⊥
:::
::::

# §1.8 Provando com táticas

* Uma *tática* transforma o estado de prova, o objetivo junto com as hipóteses em escopo, um passo por vez.

* `by` entra no modo de táticas, e a sequência de táticas elabora para um termo de prova, então uma prova por táticas e uma por termos produzem o *mesmo objeto*.

* `exact` fecha um objetivo com um termo; um passo *regressivo* (`apply`) reduz o objetivo, um passo *progressivo* (`have`) acrescenta uma hipótese.

```lean
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP
```

# §1.8 Táticas por conectivo

:::table +header
*
  * Conectivo
  * Introduzir
  * Eliminar
*
  * →
  * `intro`
  * `apply`, aplicação
*
  * ∧
  * `constructor`
  * `.left`, `.right`, `cases`
*
  * ∨
  * `Or.inl`, `Or.inr`
  * `cases`
*
  * ¬
  * `intro`
  * `apply` para chegar a `False`
*
  * ⊥
  * (nenhum)
  * `exact False.elim`
:::

::::cols
:::col
```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```
:::
:::col
```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```
:::
::::

Táticas de introdução constroem o objetivo; táticas de eliminação usam uma hipótese. O raciocínio clássico acrescenta `Classical.byContradiction` e `Classical.em`, necessários para a eliminação da dupla negação.

# §1.8 Provando com táticas, como um jogo de tabuleiro

Uma prova por táticas se desenrola como um jogo de tabuleiro. Cada elemento do jogo nomeia uma parte precisa da prova.

:::table +header
*
  * Jogo de tabuleiro
  * Prova por táticas
*
  * O tabuleiro
  * o estado de prova, o objetivo junto com as hipóteses em escopo
*
  * Suas peças
  * as hipóteses que você pode usar
*
  * Uma jogada
  * uma tática (`intro`, `apply`, `exact`, `cases`, `constructor`, `have`)
*
  * Dividir o tabuleiro
  * uma tática que abre vários objetivos; cada um precisa ser vencido
*
  * Duas direções
  * `apply` joga regressivamente a partir do objetivo, `have` joga progressivamente a partir das suas peças
*
  * O livro de regras
  * as regras de introdução e eliminação da dedução natural
*
  * Vencer
  * todo objetivo fechado, e o kernel de Lean verifica o termo de prova final
:::

# §1.9 Exemplo resolvido: P ∧ Q → P

::::cols
:::col
{lbl}[Derivação]

```tree
   [P ∧ Q]
  ──────────  ∧E₁
      P
  ────────────  →I
   P ∧ Q → P
```
:::
:::col
{lbl}[Modo de termos]

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

* `fun h =>` é o →I que descarta P ∧ Q

* `h.left` é o ∧E₁, a projeção esquerda

{lbl}[Modo de táticas]

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

* `intro h` é o →I que descarta P ∧ Q

* `exact h.left` fecha o objetivo por ∧E₁
:::
::::

# §1.9 Exemplo resolvido: ⊥ → P

::::cols
:::col
{lbl}[Derivação]

```tree
   [⊥]
  ──────  ⊥E
    P
  ────────  →I
   ⊥ → P
```
:::
:::col
{lbl}[Modo de termos]

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

* `fun h =>` é o →I que descarta ⊥

* `False.elim h` é o ⊥E, dando qualquer P

{lbl}[Modo de táticas]

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

* `intro h` é o →I que descarta ⊥

* `exact False.elim h` fecha o objetivo por ⊥E
:::
::::

# §1.9 Exemplo resolvido: (P → Q) ∧ P → Q

::::cols
:::col
{lbl}[Derivação]

```tree
   [(P→Q)∧P]           [(P→Q)∧P]
  ───────────── ∧E₁    ───────────── ∧E₂
      P → Q                  P
    ────────────────────────────── →E
                 Q
   ──────────────────────────────── →I
        (P → Q) ∧ P → Q
```
:::
:::col
{lbl}[Modo de termos]

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

* `fun h =>` é o →I que descarta (P → Q) ∧ P

* `h.left` e `h.right` são ∧E₁ e ∧E₂

* a aplicação `h.left h.right` é o →E, modus ponens

{lbl}[Modo de táticas]

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

* `intro h` é o →I que descarta (P → Q) ∧ P

* `apply h.left` reduz o objetivo a P por →E

* `exact h.right` fornece P por ∧E₂
:::
::::

# §1.9 Exemplo resolvido: P ∨ Q → Q ∨ P

::::cols
:::col
{lbl}[Derivação]

```tree
               [P]           [Q]
   [P ∨ Q]    ─────── ∨I₂   ─────── ∨I₁
              Q ∨ P         Q ∨ P
  ───────────────────────────────────── ∨E
             Q ∨ P
  ──────────────────────  →I
   P ∨ Q → Q ∨ P
```
:::
:::col
{lbl}[Modo de termos]

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

* `fun h =>` é o →I que descarta P ∨ Q

* `h.elim` é o ∨E, um ramo por disjunto

* `Or.inr` e `Or.inl` são ∨I, trocando os disjuntos

{lbl}[Modo de táticas]

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

* `intro h` é o →I que descarta P ∨ Q

* `cases h` é o ∨E, dividindo nos dois disjuntos

* cada ramo fecha com `Or.inr` / `Or.inl` (∨I)
:::
::::

# §1.9 Exemplo resolvido: ¬¬P → P (clássico)

::::cols
:::col
{lbl}[Derivação]

```tree
   [¬P]  [¬¬P]
  ──────────────  ¬E
        ⊥
    ──────────  RAA
        P
   ───────────────  →I
     ¬¬P → P
```
:::
:::col
{lbl}[Modo de termos]

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

* `fun h =>` é o →I que descarta ¬¬P

* `Classical.byContradiction` é a regra clássica (RAA)

* `fun hnP => h hnP` deriva ⊥ de ¬P e ¬¬P por ¬E

{lbl}[Modo de táticas]

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

* `intro h` é o →I que descarta ¬¬P

* `apply Classical.byContradiction` invoca a RAA

* `intro hnP` e então `exact h hnP` derivam ⊥ por ¬E
:::
::::

# Resumo

* Uma *proposição* é classificada por `Prop`; os conectivos ¬, ∧, ∨, →, ↔ constroem proposições compostas.

* Tabelas-verdade decidem questões proposicionais, mas crescem exponencialmente; a *dedução natural* aplica regras um passo por vez e generaliza.

* Cada conectivo tem regras de *introdução* e *eliminação*; algumas regras descartam suposições.

* Uma prova é um *termo* cujo tipo é a proposição (Curry-Howard): `fun h => e` para →I, aplicação para →E, `⟨_, _⟩` para ∧I, `Or.inl`/`Or.inr` para ∨I.

* *Táticas* transformam o estado de prova: `intro`, `exact`, `apply`, `cases`, `constructor`, `have`; `by` as elabora para o mesmo termo de prova.

* O *raciocínio clássico* acrescenta `Classical.byContradiction` e `Classical.em`, necessários para ¬¬P → P e uma lei de De Morgan.

Exercícios: veja as [notas de aula](../pt/Aula-1___-Motiva______o-e-L___gica-Proposicional/).
