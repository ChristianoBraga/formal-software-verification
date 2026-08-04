import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Figure
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Aula 1: Motivação e Lógica Proposicional" =>

%%%
tag := "aula-1"
%%%

Esta aula motiva a verificação formal de software e revisa a lógica proposicional, seguindo o capítulo 1 de [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). Ela apresenta os conectivos, as equivalências clássicas, as regras de dedução natural, a sua codificação em Lean como termos de prova e as provas com táticas.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-1.pt.html).*

# Por que Verificar Software Formalmente?

Software controla aeronaves, dispositivos médicos, sistemas financeiros e redes de comunicação. Erros nesses sistemas custam dinheiro e vidas. O modo usual de encontrar erros é o teste, e o teste examina finitas execuções de um programa que admite infinitas. Dijkstra enunciou a limitação com precisão.{margin}[E. W. Dijkstra, *Notes on Structured Programming*, EWD249, Technological University Eindhoven, 1970.]

> O teste de programas pode ser usado para mostrar a presença de erros, mas nunca para mostrar a sua ausência!

A verificação formal segue o caminho complementar. Enunciamos uma propriedade de um programa como uma proposição matemática e provamos que toda execução a satisfaz. A prova cobre todas as entradas de uma vez, o que nenhum conjunto finito de testes alcança.

Provas sobre programas reais crescem muito, então delegamos a sua verificação a uma máquina. Um *assistente de prova* é um programa que verifica cada passo de uma prova com respeito às regras de uma lógica formal e que ajuda o usuário a construir a prova interativamente. Lean, Rocq (antigo Coq), Isabelle/HOL e Agda são assistentes de prova em uso corrente. Resultados marcantes incluem a verificação do micronúcleo de sistema operacional seL4{margin}[G. Klein et al., *seL4: Formal Verification of an OS Kernel*, Proceedings of SOSP 2009, pp. 207–220.] e do compilador otimizante de C CompCert.{margin}[X. Leroy, *Formal Verification of a Realistic Compiler*, Communications of the ACM 52(7), 2009, pp. 107–115.]

Modelos de linguagem escrevem hoje uma parcela crescente do código. Um modelo produz texto plausível, e plausível não é o mesmo que correto. Código gerado pode invocar funções que não existem, tratar apenas os casos que o seu prompt sugere ou desviar do requisito enunciado de maneiras que sobrevivem à revisão de código. A literatura chama esse modo de falha de alucinação.

A verificação formal, em particular quando automatizada, muda a maneira como podemos confiar nesse código.{margin}[L. de Moura, [*The Lean Programming Language and Theorem Prover*](https://leodemoura.github.io/static/etaps2026/), ETAPS 2026.] Quando o código gerado chega com uma prova, verificada por máquina, de que satisfaz a sua especificação, o assistente de prova verifica a prova independentemente de como o código surgiu, então código alucinado ou simplesmente errado não passa. O ônus da correção move-se de ler o código para escrever a especificação certa. As técnicas desta disciplina aplicam-se sem mudança a código gerado, e a automação das aulas finais, com a tática `mvcgen`, aponta para verificação no ritmo da geração de código.

Nesta disciplina usamos [Lean](https://lean-lang.org). Lean é ao mesmo tempo uma linguagem de programação e um assistente de prova, então podemos escrever um programa e provar as suas propriedades no mesmo sistema. As aulas 1 e 2 revisam a lógica clássica e introduzem a linguagem de provas de Lean, seguindo HTPIwL. As aulas 3 a 8 seguem [LoVe](https://github.com/lean-forward/logical_verification_2026) por prova interativa, programação funcional e predicados indutivos. O bloco final trata a semântica de uma linguagem imperativa, a lógica de Hoare e a verificação prática com a tática `mvcgen`.

A {figref "fig-verifier-architecture"}[Figura 1.1] mostra a arquitetura do verificador que a disciplina constrói. Um programa e a sua especificação formam uma tripla de Hoare. A semântica operacional big-step dá o significado da tripla. A tática `mvcgen` gera as condições de verificação, que são metas (_goals_) puramente lógicas. Provas por táticas as fecham, e o kernel de Lean verifica cada prova.

{figureAnchor "fig-verifier-architecture"}[![Arquitetura de um verificador de programas em Lean: um programa e uma especificação formam uma tripla de Hoare, cujo significado vem da semântica big-step; a tática mvcgen gera as condições de verificação, provas por táticas as fecham e o kernel de Lean verifica cada prova](verifier-architecture.svg)]

*Figura 1.1. Arquitetura de um verificador de programas em Lean.*

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

## Exemplos

Cada equivalência abaixo é verificada por uma tabela-verdade. Duas proposições são equivalentes quando as suas colunas finais coincidem em toda linha, e uma tautologia tem uma coluna verdadeira em toda linha.

Exemplo 1. A dupla negação devolve a proposição original.

:::table +header
*
  * P
  * ¬P
  * ¬¬P
*
  * V
  * F
  * V
*
  * F
  * V
  * F
:::

Exemplo 2. O terceiro excluído P ∨ ¬P é uma tautologia.

:::table +header
*
  * P
  * ¬P
  * P ∨ ¬P
*
  * V
  * F
  * V
*
  * F
  * V
  * V
:::

Exemplo 3. A não contradição ¬(P ∧ ¬P) é uma tautologia.

:::table +header
*
  * P
  * ¬P
  * P ∧ ¬P
  * ¬(P ∧ ¬P)
*
  * V
  * F
  * F
  * V
*
  * F
  * V
  * F
  * V
:::

Exemplo 4. A primeira lei de De Morgan.

:::table +header
*
  * P
  * Q
  * P ∧ Q
  * ¬(P ∧ Q)
  * ¬P
  * ¬Q
  * ¬P ∨ ¬Q
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
  * F
  * V
  * F
  * V
  * V
*
  * F
  * V
  * F
  * V
  * V
  * F
  * V
*
  * F
  * F
  * F
  * V
  * V
  * V
  * V
:::

Exemplo 5. A disjunção comuta.

:::table +header
*
  * P
  * Q
  * P ∨ Q
  * Q ∨ P
*
  * V
  * V
  * V
  * V
*
  * V
  * F
  * V
  * V
*
  * F
  * V
  * V
  * V
*
  * F
  * F
  * F
  * F
:::

Exemplo 6. A disjunção é idempotente.

:::table +header
*
  * P
  * P ∨ P
*
  * V
  * V
*
  * F
  * F
:::

Exemplo 7. A contrapositiva.

:::table +header
*
  * P
  * Q
  * P → Q
  * ¬Q
  * ¬P
  * ¬Q → ¬P
*
  * V
  * V
  * V
  * F
  * F
  * V
*
  * V
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
*
  * F
  * F
  * V
  * V
  * V
  * V
:::

Exemplo 8. A implicação material.

:::table +header
*
  * P
  * Q
  * P → Q
  * ¬P
  * ¬P ∨ Q
*
  * V
  * V
  * V
  * F
  * V
*
  * V
  * F
  * F
  * F
  * F
*
  * F
  * V
  * V
  * V
  * V
*
  * F
  * F
  * V
  * V
  * V
:::

Exemplo 9. O bicondicional é a conjunção das suas duas implicações.

:::table +header
*
  * P
  * Q
  * P ↔ Q
  * P → Q
  * Q → P
  * (P → Q) ∧ (Q → P)
*
  * V
  * V
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
*
  * F
  * V
  * F
  * V
  * F
  * F
*
  * F
  * F
  * V
  * V
  * V
  * V
:::

Exemplo 10. A negação de uma implicação.

:::table +header
*
  * P
  * Q
  * P → Q
  * ¬(P → Q)
  * ¬Q
  * P ∧ ¬Q
*
  * V
  * V
  * V
  * F
  * F
  * F
*
  * V
  * F
  * F
  * V
  * V
  * V
*
  * F
  * V
  * V
  * F
  * F
  * F
*
  * F
  * F
  * V
  * F
  * V
  * F
:::

Tabelas-verdade decidem qualquer questão proposicional, mas o seu tamanho cresce exponencialmente no número de variáveis, e elas não se estendem aos quantificadores da Aula 2. Regras de dedução, aplicadas um passo por vez, escalam e generalizam. A próxima seção as apresenta, e o restante da aula desenvolve as provas correspondentes em Lean.

# Dedução Natural

A dedução natural deriva uma proposição a partir de suposições por regras que espelham o modo como matemáticos argumentam.{margin}[G. Gentzen, *Untersuchungen über das logische Schließen. I*, Mathematische Zeitschrift 39, 1935, pp. 176–210.] Gerhard Gentzen introduziu o sistema em 1935, e Dag Prawitz deu o seu estudo teórico-demonstrativo.{margin}[D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*, Almqvist & Wiksell, Stockholm, 1965.] Cada regra tem zero ou mais *premissas* acima de uma linha horizontal e uma *conclusão* abaixo dela, e lê-se como segue. Dadas derivações das premissas, a linha licencia a conclusão.

Uma derivação apoia-se em *suposições*. Algumas regras *descartam* uma suposição, então uma proposição suposta no topo de uma subderivação deixa de contar como suposição aberta assim que a regra dispara. Marcamos uma suposição descartada com colchetes, como `[P]`, e escrevemos um ⋮ vertical para a derivação interveniente. Uma proposição provada sem suposições abertas é um *teorema*.

Cada conectivo vem com regras de *introdução*, que provam uma proposição daquela forma, e regras de *eliminação*, que usam uma proposição daquela forma. Essa disciplina de introdução e eliminação é exatamente a estrutura que as táticas de Lean seguem na próxima seção.

## Implicação

Para introduzir P → Q, suponha P, derive Q e descarte a suposição. Para eliminá-la, aplique uma implicação a uma prova do seu antecedente, a regra de *modus ponens*.

```
   [P]
    ⋮
    Q                   P → Q    P
  ───────  →I          ─────────────  →E
   P → Q                     Q
```

## Conjunção

Para introduzir P ∧ Q, prove as duas partes. A eliminação projeta qualquer uma delas.

```
   P    Q              P ∧ Q            P ∧ Q
  ───────  ∧I         ───────  ∧E₁     ───────  ∧E₂
   P ∧ Q                 P                Q
```

## Disjunção

Para introduzir P ∨ Q, prove um disjunto. Para eliminá-la, prove uma conclusão comum R a partir de cada disjunto por vez, descartando o disjunto suposto em cada ramo.

```
     P                 Q                              [P]     [Q]
  ───────  ∨I₁      ───────  ∨I₂          P ∨ Q         ⋮       ⋮
   P ∨ Q             P ∨ Q                              R       R
                                        ──────────────────────────  ∨E
                                                     R
```

## Negação e Falsidade

A constante ⊥ é a *absurdidade*, a proposição sem regra de introdução. A negação abrevia ¬P como P → ⊥, então as regras da negação são as regras da implicação lidas em ⊥. Para introduzir ¬P, suponha P, derive ⊥ e descarte a suposição. Para eliminá-la, uma prova de P e uma prova de ¬P juntas produzem ⊥. A partir de ⊥, a eliminação prova qualquer proposição C, o princípio *ex falso quodlibet*.

```
   [P]
    ⋮
    ⊥                  P    ¬P               ⊥
  ───────  ¬I         ─────────  ¬E        ─────  ⊥E
    ¬P                    ⊥                   C
```

## Regras Construtivas e Clássicas

As regras acima são *construtivas*, então uma derivação de uma disjunção exibe qual disjunto vale e uma derivação de um existencial exibe uma testemunha. Elas não provam a lei do terceiro excluído P ∨ ¬P nem reduzem uma dupla negação ¬¬P a P. A dedução natural *clássica* acrescenta mais uma regra, equivalentemente o terceiro excluído ou a *reductio ad absurdum*, que descarta a suposição ¬P ao derivar ⊥.

```
   [¬P]
     ⋮
     ⊥
  ─────────  RAA               ───────────  EM
     P                          P ∨ ¬P
```

A lei de De Morgan ¬(P ∧ Q) ≡ ¬P ∨ ¬Q e a lei de Peirce dependem dessa regra, como as provas em Lean abaixo tornam precisas.

## Exemplos

As derivações abaixo provam teoremas proposicionais com as regras acima. Um numeral marca cada suposição descartada junto com a regra que a descarta, e cada árvore lê-se das folhas até a raiz.

Exemplo 1. A implicação é reflexiva.

```
   [P]¹
  ──────  →I,¹
   P → P
```

Exemplo 2. Uma conjunção implica cada uma das suas partes.

```
   [P ∧ Q]¹
  ──────────  ∧E₁
      P
  ────────────  →I,¹
   P ∧ Q → P
```

Exemplo 3. Um disjunto implica a disjunção.

```
     [P]¹
   ────────  ∨I₁
    P ∨ Q
  ────────────  →I,¹
   P → P ∨ Q
```

Exemplo 4. Qualquer coisa decorre da absurdidade, o princípio *ex falso quodlibet*.

```
   [⊥]¹
  ──────  ⊥E
    P
  ────────  →I,¹
   ⊥ → P
```

Exemplo 5. Modus ponens, empacotado como uma única implicação.

```
   [(P→Q)∧P]¹            [(P→Q)∧P]¹
  ───────────── ∧E₁     ───────────── ∧E₂
      P → Q                   P
     ───────────────────────────── →E
                  Q
   ─────────────────────────────────── →I,¹
          (P → Q) ∧ P → Q
```

Exemplo 6. A disjunção comuta.

```
                [P]²           [Q]²
   [P ∨ Q]¹    ─────── ∨I₂    ─────── ∨I₁
               Q ∨ P          Q ∨ P
  ────────────────────────────────────── ∨E,²
              Q ∨ P
  ─────────────────────── →I,¹
   P ∨ Q → Q ∨ P
```

Exemplo 7. Introdução da dupla negação.

```
    [¬P]²   [P]¹
   ────────────── ¬E
         ⊥
     ────────── ¬I,²
        ¬¬P
    ────────────── →I,¹
      P → ¬¬P
```

Exemplo 8. Contraposição.

```
               [P→Q]¹  [P]³
   [¬Q]²      ─────────────── →E
                    Q
  ────────────────────── ¬E
           ⊥
     ──────────── ¬I,³
          ¬P
    ───────────────── →I,²
      ¬Q → ¬P
  ──────────────────────────── →I,¹
   (P → Q) → (¬Q → ¬P)
```

Exemplo 9. Eliminação da dupla negação, que requer a regra clássica.

```
    [¬P]²  [¬¬P]¹
   ──────────────── ¬E
          ⊥
     ─────────── RAA,²
          P
    ─────────────── →I,¹
     ¬¬P → P
```

Exemplo 10. O currying transforma uma hipótese conjuntiva em implicações aninhadas.

```
                      [P]²  [Q]³
   [P∧Q→R]¹          ──────────── ∧I
                        P ∧ Q
      ────────────────────────── →E
                  R
               ─────────── →I,³
                Q → R
           ───────────────── →I,²
            P → (Q → R)
    ───────────────────────────────── →I,¹
     (P ∧ Q → R) → (P → (Q → R))
```

# Dedução Natural em Lean

Em Lean, enunciamos uma proposição e a provamos em uma única declaração. A palavra-chave `example` introduz um enunciado anônimo, e `theorem` introduz um enunciado com nome. As hipóteses aparecem antes dos dois-pontos como suposições nomeadas, e a proposição a provar, o *objetivo*, aparece depois.

Lean codifica a dedução natural diretamente. Uma prova de uma proposição é um *termo* cujo tipo é aquela proposição, uma suposição aberta é uma variável daquele tipo, e cada regra de dedução torna-se um modo de construir ou desmontar termos. A prova mais simples usa uma suposição diretamente, a regra de suposição da dedução natural.

```lean
example (P : Prop) (h : P) : P := h
```

Aqui `h` nomeia a suposição de que P vale, e a prova é o próprio `h`. A Aula 3 desenvolve essa correspondência entre proposições e tipos.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, em *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980.]

A tabela mapeia cada regra da seção anterior ao termo de Lean que a realiza. Uma regra de introdução constrói um termo, e uma regra de eliminação o desmonta.

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

Como ¬P abrevia P → False, as regras da negação reutilizam os termos da implicação. Para ver a correspondência em uma derivação completa, tome P ∧ Q → Q ∧ P. Ela descarta a suposição P ∧ Q, projeta cada uma das partes e as remonta na ordem oposta.

```
        [P ∧ Q]            [P ∧ Q]
       ─────────  ∧E₂     ─────────  ∧E₁
           Q                  P
         ───────────────────────────  ∧I
                   Q ∧ P
        ─────────────────────────────  →I
              P ∧ Q → Q ∧ P
```

O termo em Lean segue a derivação passo a passo. A abstração `fun h => …` é o →I que descarta P ∧ Q, as projeções `h.right` e `h.left` são os dois passos ∧E, e o par `⟨_, _⟩` é o ∧I.

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.right, h.left⟩
```

## Exemplos

As provas abaixo codificam as dez derivações da seção anterior como termos de prova. Cada termo espelha a sua derivação, com uma regra de introdução construindo um termo e uma regra de eliminação o desmontando.

Exemplo 1. A implicação é reflexiva.

```lean
example (P : Prop) : P → P :=
  fun h => h
```

Exemplo 2. Uma conjunção implica cada uma das suas partes.

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

Exemplo 3. Um disjunto implica a disjunção.

```lean
example (P Q : Prop) : P → P ∨ Q :=
  fun h => Or.inl h
```

Exemplo 4. Qualquer coisa decorre da absurdidade.

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

Exemplo 5. Modus ponens, empacotado como uma única implicação.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

Exemplo 6. A disjunção comuta.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

Exemplo 7. Introdução da dupla negação.

```lean
example (P : Prop) : P → ¬¬P :=
  fun hP hnP => hnP hP
```

Exemplo 8. Contraposição.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  fun hPQ hnQ hP => hnQ (hPQ hP)
```

Exemplo 9. Eliminação da dupla negação, que requer raciocínio clássico.

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

Exemplo 10. O currying transforma uma hipótese conjuntiva em implicações aninhadas.

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → (Q → R)) :=
  fun h hP hQ => h ⟨hP, hQ⟩
```

# Provando com Táticas

Escrever termos de prova à mão torna-se impraticável à medida que as provas crescem. Uma *tática* é um comando que transforma o *estado de prova*, o objetivo junto com as hipóteses em escopo, um passo por vez. A palavra-chave `by` entra no modo de táticas, e Lean elabora a sequência de táticas em um termo de prova, então uma prova por táticas e uma prova por termos produzem o mesmo objeto subjacente.

A tática `exact` fecha um objetivo com um termo que o prova, o que recupera a prova em modo de termo acima.

```lean
example (P : Prop) (h : P) : P := by
  exact h
```

As táticas raciocinam em duas direções. Um passo *regressivo* reduz o objetivo a subobjetivos mais simples, e um passo *progressivo* deriva novas hipóteses a partir das que estão em escopo. Cada conectivo vem com táticas que o *introduzem*, provando um objetivo daquela forma, e táticas que o *eliminam*, usando uma hipótese daquela forma. Tomamos os conectivos um a um.

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

## Exemplos

As provas abaixo demonstram novamente esses dez teoremas, agora com táticas. Cada uma pode ser lida ao lado do termo de prova da seção anterior.

Exemplo 1. A implicação é reflexiva.

```lean
example (P : Prop) : P → P := by
  intro h
  exact h
```

Exemplo 2. Uma conjunção implica cada uma das suas partes.

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

Exemplo 3. Um disjunto implica a disjunção.

```lean
example (P Q : Prop) : P → P ∨ Q := by
  intro h
  exact Or.inl h
```

Exemplo 4. Qualquer coisa decorre da absurdidade.

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

Exemplo 5. Modus ponens, empacotado como uma única implicação.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

Exemplo 6. A disjunção comuta.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

Exemplo 7. Introdução da dupla negação.

```lean
example (P : Prop) : P → ¬¬P := by
  intro hP hnP
  exact hnP hP
```

Exemplo 8. Contraposição.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hPQ hnQ hP
  exact hnQ (hPQ hP)
```

Exemplo 9. Eliminação da dupla negação, que requer raciocínio clássico.

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

Exemplo 10. O currying transforma uma hipótese conjuntiva em implicações aninhadas.

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → (Q → R)) := by
  intro h hP hQ
  exact h ⟨hP, hQ⟩
```

# Exemplos Resolvidos

Cada exemplo abaixo aparece de três formas, como uma derivação em dedução natural, como um termo de prova e como uma prova por táticas. As três apresentam a mesma prova, e Lean verifica os dois scripts de prova na construção das notas. Estas proposições são disjuntas dos exemplos das seções anteriores e dos exercícios.

## Uma Conjunção Implica uma das suas Partes

A eliminação projeta a parte esquerda, e a implicação descarta a suposição P ∧ Q.

```
   [P ∧ Q]
  ──────────  ∧E₁
      P
  ────────────  →I
   P ∧ Q → P
```

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

## Ex Falso Quodlibet

A partir de uma prova da absurdidade, a eliminação de ⊥ prova qualquer proposição.{margin}[*Ex falso quodlibet* é latim para "de uma falsidade, qualquer coisa se segue".]

```
   [⊥]
  ──────  ⊥E
    P
  ────────  →I
   ⊥ → P
```

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

## Modus Ponens

Uma implicação e o seu antecedente, ambos projetados da conjunção, combinam-se por →E para dar o consequente.{margin}[*Modus ponens* é latim, abreviação de *modus ponendo ponens*, "o modo que afirma afirmando".]

```
   [(P→Q)∧P]           [(P→Q)∧P]
  ───────────── ∧E₁    ───────────── ∧E₂
      P → Q                  P
    ────────────────────────────── →E
                 Q
   ──────────────────────────────── →I
        (P → Q) ∧ P → Q
```

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

## A Disjunção Comuta

A análise de casos sobre a disjunção a remonta com os disjuntos trocados.

```
               [P]           [Q]
   [P ∨ Q]    ─────── ∨I₂   ─────── ∨I₁
              Q ∨ P         Q ∨ P
  ───────────────────────────────────── ∨E
             Q ∨ P
  ──────────────────────  →I
   P ∨ Q → Q ∨ P
```

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

## Eliminação da Dupla Negação

Esta direção requer raciocínio clássico. `Classical.byContradiction` descarta a suposição ¬P após derivar ⊥ dela junto com ¬¬P.{margin}[O passo clássico marcado RAA é *reductio ad absurdum*, latim para "redução ao absurdo".]

```
   [¬P]  [¬¬P]
  ──────────────  ¬E
        ⊥
    ──────────  RAA
        P
   ───────────────  →I
     ¬¬P → P
```

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

# Exercícios

Prove cada enunciado em Lean, substituindo `sorry` por uma prova. Baixe o arquivo de exercícios [`Lecture01.lean`](example-code/Lectures/Pt/Lecture01.lean) e abra-o no VS Code.

```savedComment
Exercícios da Aula 1: Motivação e Lógica Proposicional.
Substitua cada `sorry` por uma prova.
```

Exercício 1. A implicação compõe.

```savedLean -keep
theorem exercise1 (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry
```

Exercício 2. A conjunção distribui sobre a disjunção.

```savedLean -keep
theorem exercise2 (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

Exercício 3. A disjunção associa.

```savedLean -keep
theorem exercise3 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry
```

Exercício 4. Esta direção da primeira lei de De Morgan é construtiva.

```savedLean -keep
theorem exercise4 (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry
```

Exercício 5. Lei de Peirce.{margin}[C. S. Peirce, *On the Algebra of Logic: A Contribution to the Philosophy of Notation*, American Journal of Mathematics 7(2), 1885, pp. 180–196.] Ela requer raciocínio clássico; considere uma análise de casos sobre `Classical.em P`.

```savedLean -keep
theorem exercise5 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry
```

Exercício 6. A disjunção distribui sobre a conjunção.

```savedLean -keep
theorem exercise6 (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry
```

Exercício 7. Uma implicação para uma conjunção divide-se em duas implicações.

```savedLean -keep
theorem exercise7 (P Q R : Prop) :
    (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  sorry
```

Exercício 8. De uma disjunção e da negação de um dos disjuntos, o outro vale.

```savedLean -keep
theorem exercise8 (P Q : Prop) : (P ∨ Q) → ¬P → Q := by
  sorry
```

Exercício 9. Nenhuma proposição é equivalente à sua própria negação.

```savedLean -keep
theorem exercise9 (P : Prop) : ¬(P ↔ ¬P) := by
  sorry
```

Exercício 10. De duas proposições quaisquer, uma implica a outra. Requer raciocínio clássico; considere uma análise de casos sobre `Classical.em P`.

```savedLean -keep
theorem exercise10 (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  sorry
```
