import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Meta.Footnote
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option lectures.language "pt"

#doc (Manual) "Aula 1: Motivação e Lógica Proposicional" =>

%%%
tag := "aula-1"
%%%

```lean -show
namespace Lecture1
```

Esta aula motiva a verificação formal de software e revisa a lógica proposicional, seguindo o capítulo 1 de [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). Ela apresenta os conectivos, as equivalências clássicas, as regras de dedução natural, a sua codificação em Lean como termos de prova e as provas com táticas.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-1.pt.html).*

# Por que Verificar Software Formalmente?

Software controla aeronaves, dispositivos médicos, sistemas financeiros e redes de comunicação. Erros nesses sistemas custam dinheiro e vidas. O modo usual de encontrar erros é o teste, e o teste examina finitas execuções de um programa que admite infinitas. Dijkstra enunciou a limitação com precisão.{margin}[E. W. Dijkstra, [*Notes on Structured Programming*](https://www.cs.utexas.edu/~EWD/ewd02xx/EWD249.PDF), EWD249, Technological University Eindhoven, 1970.]

> O teste de programas pode ser usado para mostrar a presença de erros, mas nunca para mostrar a sua ausência!

A verificação formal segue o caminho complementar. Enunciamos uma propriedade de um programa como uma proposição matemática e provamos que toda execução a satisfaz. A prova cobre todas as entradas de uma vez, o que nenhum conjunto finito de testes alcança.

Provas sobre programas reais crescem muito, então delegamos a sua verificação a uma máquina. Um *assistente de prova* é um programa que verifica cada passo de uma prova com respeito às regras de uma lógica formal e que ajuda o usuário a construir a prova interativamente. Lean, Rocq (antigo Coq), Isabelle/HOL e Agda são assistentes de prova em uso corrente. Resultados marcantes incluem a verificação do micronúcleo de sistema operacional seL4{margin}[G. Klein et al., [*seL4: Formal Verification of an OS Kernel*](https://trustworthy.systems/publications/nictaabstracts/Klein_EHACDEEKNSTW_09.abstract), Proceedings of SOSP 2009, pp. 207–220.] e do compilador otimizante de C CompCert.{margin}[X. Leroy, [*Formal Verification of a Realistic Compiler*](https://xavierleroy.org/publi/compcert-CACM.pdf), Communications of the ACM 52(7), 2009, pp. 107–115.]

Modelos de linguagem escrevem hoje uma parcela crescente do código. Um modelo produz texto plausível, e plausível não é o mesmo que correto. Código gerado pode invocar funções que não existem, tratar apenas os casos que o seu prompt sugere ou desviar do requisito enunciado de maneiras que sobrevivem à revisão de código. A literatura chama esse modo de falha de alucinação.

A verificação formal, em particular quando automatizada, muda a maneira como podemos confiar nesse código.{margin}[L. de Moura, [*The Lean Programming Language and Theorem Prover*](https://leodemoura.github.io/static/etaps2026/), ETAPS 2026.] Quando o código gerado chega com uma prova, verificada por máquina, de que satisfaz a sua especificação, o assistente de prova verifica a prova independentemente de como o código surgiu, então código alucinado ou simplesmente errado não passa. O ônus da correção move-se de ler o código para escrever a especificação certa. As técnicas desta disciplina aplicam-se sem mudança a código gerado, e a automação das aulas finais, com a tática `mvcgen`, aponta para verificação no ritmo da geração de código.

Nesta disciplina usamos [Lean](https://lean-lang.org). Lean é ao mesmo tempo uma linguagem de programação e um assistente de prova, então podemos escrever um programa e provar as suas propriedades no mesmo sistema. As aulas 1 e 2 revisam a lógica clássica e introduzem a linguagem de provas de Lean, seguindo HTPIwL. As aulas 3 a 8 seguem [LoVe](https://github.com/lean-forward/logical_verification_2026){fnref}[lovelib] por prova interativa, programação funcional e predicados indutivos. O bloco final trata a semântica de uma linguagem imperativa, a lógica de Hoare e a verificação prática com a tática `mvcgen`.

A {numref}[fig-lean-components] mostra os componentes de Lean que a disciplina exercita. O analisador sintático lê o texto de um arquivo `.lean` e produz árvores de sintaxe, e o expansor de macros desdobra as notações definidas pelas bibliotecas e pelo código do usuário. O elaborador transforma essas árvores em termos da linguagem núcleo e faz o trabalho que a sintaxe de superfície deixa implícito, inferindo argumentos omitidos, resolvendo instâncias de classes de tipos e executando táticas. As táticas são elas próprias programas Lean e constroem termos, não certificados da própria correção. O kernel reverifica o termo pronto com respeito às regras da teoria de tipos dependentes, então uma tática que produz um termo errado falha aí, e somente o kernel pertence à base confiável. O compilador leva os mesmos termos a código nativo, que é o que `#eval` executa. As bibliotecas fornecem notações, instâncias e lemas a todas as etapas acima do kernel.

![Principais componentes de Lean: um arquivo .lean passa pelo analisador sintático e pelo expansor de macros até o elaborador, que recorre a táticas e bibliotecas e produz termos do núcleo; o kernel verifica esses termos e o compilador os leva a código nativo](lean-components.svg)

{figcap "fig-lean-components"}[Principais componentes de Lean.]

Esses componentes servem a qualquer desenvolvimento em Lean, e a disciplina os usa para um fim específico. A linguagem imperativa das últimas aulas, a sua semântica e a sua lógica de Hoare são definições Lean comuns, as condições de verificação são objetivos (_goals_){fnref}[goal] que as táticas fecham, e o kernel verifica o resultado como verifica qualquer outra prova. O objetivo desta disciplina é mostrar como usar Lean para verificar formalmente programas imperativos, e a {numref}[fig-verifier-architecture] descreve uma arquitetura para isso.

Um programa e a sua especificação formam uma tripla de Hoare. A semântica operacional big-step dá o significado da tripla. A tática `mvcgen` gera as condições de verificação, que são objetivos (_goals_) puramente lógicos. Provas por táticas as fecham, e o kernel de Lean verifica cada prova.

![Arquitetura de um verificador de programas em Lean: um programa e uma especificação formam uma tripla de Hoare, cujo significado vem da semântica big-step; a tática mvcgen gera as condições de verificação, provas por táticas as fecham e o kernel de Lean verifica cada prova](verifier-architecture.svg)

{figcap "fig-verifier-architecture"}[Arquitetura de um verificador de programas em Lean.]

:::footnotes

{fnAnchor "lovelib"}[] LoVe reúne os arquivos Lean que acompanham o *Hitchhiker's Guide to Logical Verification*, edição de 2026. A sua biblioteca de apoio `LoVelib` não é publicada como pacote Lake, então estas notas guardam uma cópia dela em `Lectures/LoVe/`, junto com a licença BSD de três cláusulas. A cópia é literal, com uma única alteração, o atributo `@[reducible]` em `Set.PartialOrder`, exigido pelo linter de definições de Lean v4.32.0 e ausente no original, escrito para Lean v4.24.0.

{fnAnchor "goal"}[] Um *objetivo* é o que falta provar em um ponto da prova. Lean o mostra como as hipóteses em escopo, uma por linha, seguidas do símbolo ⊢ e da proposição a provar. Cada tática ou fecha um objetivo ou o substitui por objetivos mais simples, e a prova termina quando nenhum resta. Provar `Q ∧ P` a partir de uma hipótese `h : P ∧ Q`, por exemplo, começa no objetivo

```
P Q : Prop
h : P ∧ Q
⊢ Q ∧ P
```

que a tática `exact ⟨h.right, h.left⟩` fecha. A {secref}[taticas] retoma o assunto em detalhe.

:::

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

Conectivos constroem proposições compostas a partir de proposições mais simples, e a {numref}[tbl-connectives] nomeia os cinco.

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

{tabcap "tbl-connectives"}[Os cinco conectivos, com os seus símbolos e leituras.]

O valor de verdade de uma proposição composta depende apenas dos valores de verdade das suas partes. A {numref}[tbl-truth-values] define os cinco conectivos, com V para verdadeiro e F para falso.

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

{tabcap "tbl-truth-values"}[Os valores de verdade dos cinco conectivos.]

Duas linhas da coluna da implicação merecem atenção. Quando P é falso, P → Q é verdadeira independentemente de Q. Uma implicação nada afirma sobre os casos em que o seu antecedente falha, então esses casos não podem refutá-la.

A coluna da disjunção merece a mesma atenção. A disjunção é *inclusiva*, então P ∨ Q é verdadeira quando os dois disjuntos o são.

# Equivalência Lógica

Uma *valoração* atribui um valor de verdade a cada variável proposicional. Uma proposição é uma *tautologia* quando é verdadeira sob toda valoração. Duas proposições A e B são *logicamente equivalentes*, escrito A ≡ B, quando têm o mesmo valor de verdade sob toda valoração, isto é, quando A ↔ B é uma tautologia.

As equivalências clássicas da {numref}[tbl-equivalences] aparecem constantemente em provas.

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

{tabcap "tbl-equivalences"}[As equivalências clássicas.]

Uma tabela-verdade verifica cada equivalência. Para a segunda lei de De Morgan, as colunas de ¬(P ∨ Q) e de ¬P ∧ ¬Q coincidem nas quatro valorações, como mostra a {numref}[tbl-demorgan-check].

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

{tabcap "tbl-demorgan-check"}[Tabela-verdade da segunda lei de De Morgan.]

## Exemplos

Cada equivalência abaixo é verificada por uma tabela-verdade. Duas proposições são equivalentes quando as suas colunas finais coincidem em toda linha, e uma tautologia tem uma coluna verdadeira em toda linha.

{ex "ex-logical-equivalence-double-negation-returns-original"}[] A dupla negação devolve a proposição original, verificada na {numref}[tbl-double-negation].

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

{tabcap "tbl-double-negation"}[Tabela-verdade de ¬¬P ≡ P.]

{ex "ex-logical-equivalence-excluded-middle-p-p"}[] O terceiro excluído P ∨ ¬P é uma tautologia, verificada na {numref}[tbl-excluded-middle].

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

{tabcap "tbl-excluded-middle"}[Tabela-verdade de P ∨ ¬P.]

{ex "ex-logical-equivalence-non-contradiction-p-p"}[] A não contradição ¬(P ∧ ¬P) é uma tautologia, verificada na {numref}[tbl-non-contradiction].

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

{tabcap "tbl-non-contradiction"}[Tabela-verdade de ¬(P ∧ ¬P).]

{ex "ex-logical-equivalence-first-de-morgan-law"}[] A primeira lei de De Morgan, verificada na {numref}[tbl-demorgan-first].

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

{tabcap "tbl-demorgan-first"}[Tabela-verdade de ¬(P ∧ Q) ≡ ¬P ∨ ¬Q.]

{ex "ex-logical-equivalence-disjunction-commutes-verified-numref"}[] A disjunção comuta, verificada na {numref}[tbl-or-comm].

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

{tabcap "tbl-or-comm"}[Tabela-verdade de P ∨ Q ≡ Q ∨ P.]

{ex "ex-logical-equivalence-disjunction-idempotent-verified-numref"}[] A disjunção é idempotente, verificada na {numref}[tbl-or-idem].

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

{tabcap "tbl-or-idem"}[Tabela-verdade de P ∨ P ≡ P.]

{ex "ex-logical-equivalence-contrapositive-verified-numref-tbl"}[] A contrapositiva, verificada na {numref}[tbl-contrapositive].

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

{tabcap "tbl-contrapositive"}[Tabela-verdade de P → Q ≡ ¬Q → ¬P.]

{ex "ex-logical-equivalence-material-implication-verified-numref"}[] A implicação material, verificada na {numref}[tbl-material-implication].

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

{tabcap "tbl-material-implication"}[Tabela-verdade de P → Q ≡ ¬P ∨ Q.]

{ex "ex-logical-equivalence-biconditional-conjunction-two-implications"}[] O bicondicional é a conjunção das suas duas implicações, verificada na {numref}[tbl-iff-split].

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

{tabcap "tbl-iff-split"}[Tabela-verdade de P ↔ Q ≡ (P → Q) ∧ (Q → P).]

{ex "ex-logical-equivalence-negation-implication-verified-numref"}[] A negação de uma implicação, verificada na {numref}[tbl-not-implication].

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

{tabcap "tbl-not-implication"}[Tabela-verdade de ¬(P → Q) ≡ P ∧ ¬Q.]

## Cálculos Lógicos

Tabelas-verdade decidem qualquer questão proposicional, mas o seu tamanho cresce exponencialmente no número de variáveis, e elas não se estendem aos quantificadores da Aula 2. Um *cálculo* responde às mesmas questões por derivação, e não por computação.

Um cálculo fixa um conjunto de *axiomas*, que são proposições tomadas como dadas, e um conjunto de *regras de inferência*, cada uma das quais produz uma proposição a partir de proposições já derivadas. Uma *derivação* é uma sequência finita de aplicações de regras, e uma proposição que encerra uma derivação é um *teorema* do cálculo. Valorações não participam disso. Uma derivação reescreve símbolos apenas segundo as regras, e é isso que permite a uma máquina verificá-la.

Duas propriedades ligam um cálculo à semântica das seções anteriores. Um cálculo é *correto* quando todo teorema é uma tautologia, e *completo* quando toda tautologia é um teorema. Post provou as duas para o cálculo proposicional em 1921, no artigo que também introduziu o método das tabelas-verdade.{margin}[E. L. Post, *Introduction to a General Theory of Elementary Propositions*, American Journal of Mathematics 43, 1921, pp. 163–185.]

A lógica proposicional admite vários cálculos, e eles diferem na forma das suas regras, não nos teoremas que provam.

Um cálculo *axiomático*, no estilo de Hilbert e Ackermann,{margin}[D. Hilbert e W. Ackermann, *Grundzüge der theoretischen Logik*, Julius Springer, Berlim, 1928.] tem muitos axiomas e uma regra. O sistema de Łukasiewicz e Tarski precisa de três esquemas de axioma sobre → e ¬, com o modus ponens como única regra.{margin}[J. Łukasiewicz e A. Tarski, *Untersuchungen über den Aussagenkalkül*, Comptes Rendus des Séances de la Société des Sciences et des Lettres de Varsovie, Classe III, 23, 1930, pp. 30–50.]

```
  A → (B → A)
  (A → (B → C)) → ((A → B) → (A → C))
  (¬A → ¬B) → (B → A)
```

Cada esquema representa toda proposição da sua forma, então `P → (Q → P)` e `(P ∧ Q) → (R → (P ∧ Q))` são instâncias do primeiro. Derivar um teorema tão simples quanto P → P leva cinco passos aqui, e encontrar os passos é uma arte.

A *resolução* vai ao outro extremo, com uma única regra sobre proposições escritas como cláusulas, e é com ela que provadores automáticos buscam.{margin}[J. A. Robinson, *A Machine-Oriented Logic Based on the Resolution Principle*, Journal of the ACM 12(1), 1965, pp. 23–41.]

A *dedução natural* fica entre os dois. Ela não tem axiomas e tem duas regras para cada conectivo, uma que introduz o conectivo e outra que o elimina, e as suas derivações podem repousar sobre suposições que uma regra posterior descarta. Gentzen a projetou para seguir os passos que um matemático de fato dá.{margin}[G. Gentzen, *Untersuchungen über das logische Schließen. I*, Mathematische Zeitschrift 39, 1935, pp. 176–210.] O *cálculo de sequentes*, do mesmo artigo, carrega as suposições explicitamente à esquerda do símbolo ⊢ e serve a argumentos de teoria da prova.

## O Cálculo desta Disciplina

Esta disciplina usa dedução natural. As suas regras de introdução e eliminação são as que as táticas de Lean implementam, e um termo de prova em Lean corresponde a uma das suas derivações. A próxima seção apresenta as regras, e o restante da aula desenvolve as provas correspondentes em Lean.

# Dedução Natural

A dedução natural deriva uma proposição a partir de suposições por regras que espelham o modo como matemáticos argumentam. Dag Prawitz deu ao sistema o seu estudo teórico-demonstrativo.{margin}[D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*, Almqvist & Wiksell, Stockholm, 1965.] Cada regra tem zero ou mais *premissas* acima de uma linha horizontal e uma *conclusão* abaixo dela, e lê-se como segue. Dadas derivações das premissas, a linha licencia a conclusão.

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

A constante ⊥ é o *absurdo*, a proposição sem regra de introdução. A negação abrevia ¬P como P → ⊥, então as regras da negação são as regras da implicação lidas em ⊥. Para introduzir ¬P, suponha P, derive ⊥ e descarte a suposição. Para eliminá-la, uma prova de P e uma prova de ¬P juntas produzem ⊥. A partir de ⊥, a eliminação prova qualquer proposição C, o princípio *ex falso quodlibet*.

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

{ex "ex-natural-deduction-implication-reflexive"}[] A implicação é reflexiva.

```
   [P]¹
  ──────  →I,¹
   P → P
```

{ex "ex-natural-deduction-conjunction-entails-each-conjunct"}[] Uma conjunção implica cada uma das suas partes.

```
   [P ∧ Q]¹
  ──────────  ∧E₁
      P
  ────────────  →I,¹
   P ∧ Q → P
```

{ex "ex-natural-deduction-disjunct-entails-disjunction"}[] Um disjunto implica a disjunção.

```
     [P]¹
   ────────  ∨I₁
    P ∨ Q
  ────────────  →I,¹
   P → P ∨ Q
```

{ex "ex-natural-deduction-anything-follows-absurdity-principle"}[] Qualquer coisa decorre do absurdo, o princípio *ex falso quodlibet*.

```
   [⊥]¹
  ──────  ⊥E
    P
  ────────  →I,¹
   ⊥ → P
```

{ex "ex-natural-deduction-modus-ponens-packaged-single"}[] Modus ponens, empacotado como uma única implicação.

```
   [(P→Q)∧P]¹            [(P→Q)∧P]¹
  ───────────── ∧E₁     ───────────── ∧E₂
      P → Q                   P
     ───────────────────────────── →E
                  Q
   ─────────────────────────────────── →I,¹
          (P → Q) ∧ P → Q
```

{ex "ex-natural-deduction-disjunction-commutes"}[] A disjunção comuta.

```
                [P]²           [Q]²
   [P ∨ Q]¹    ─────── ∨I₂    ─────── ∨I₁
               Q ∨ P          Q ∨ P
  ────────────────────────────────────── ∨E,²
              Q ∨ P
  ─────────────────────── →I,¹
   P ∨ Q → Q ∨ P
```

{ex "ex-natural-deduction-double-negation-introduction"}[] Introdução da dupla negação.

```
    [¬P]²   [P]¹
   ────────────── ¬E
         ⊥
     ────────── ¬I,²
        ¬¬P
    ────────────── →I,¹
      P → ¬¬P
```

{ex "ex-natural-deduction-contraposition"}[] Contraposição.

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

{ex "ex-natural-deduction-double-negation-elimination-which"}[] Eliminação da dupla negação, que requer a regra clássica.

```
    [¬P]²  [¬¬P]¹
   ──────────────── ¬E
          ⊥
     ─────────── RAA,²
          P
    ─────────────── →I,¹
     ¬¬P → P
```

{ex "ex-natural-deduction-currying-turns-conjunctive-hypothesis"}[] O currying transforma uma hipótese conjuntiva em implicações aninhadas.

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

# A Sintaxe de Lean

As seções seguintes leem e escrevem Lean, então esta fixa a notação. Ela explica como uma declaração é escrita, não o que torna uma prova correta, assunto das seções posteriores.

Uma declaração dá nome a um enunciado e apresenta a sua prova. A palavra-chave vem primeiro, depois o nome, depois as hipóteses entre parênteses, depois o enunciado após os dois-pontos, e por fim a prova após `:=`.

```lean
theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩
```

Aqui `theorem` dá ao resultado o nome `and_swap`. Os parâmetros `(P Q : Prop)` e `(h : P ∧ Q)` introduzem duas proposições e uma hipótese. O enunciado a provar é `Q ∧ P`, e a prova é o termo após `:=`. A palavra-chave `example` substitui `theorem` quando o resultado dispensa nome.

A {numref}[tbl-lean-syntax] lista as construções de sintaxe que as seções seguintes usam.

:::table +header
*
  * Escrito
  * Lido como
*
  * `example (h : P) : Q := e`
  * enunciado anônimo com hipótese h, provado por e
*
  * `fun h => e`
  * a função que leva h em e
*
  * `f a`
  * f aplicada a a, sem parênteses
*
  * `⟨a, b⟩`
  * o construtor anônimo, aqui um par
*
  * `h.left`, `h.right`
  * as duas componentes de uma conjunção
*
  * `by`
  * entra no modo de táticas, uma tática por linha
*
  * `·`
  * foca o objetivo seguinte dentro de um bloco de táticas
*
  * `sorry`
  * marcador de uma prova ausente
*
  * `-- texto`
  * comentário até o fim da linha
:::

{tabcap "tbl-lean-syntax"}[A sintaxe de declarações, termos e blocos de táticas.]

Os símbolos lógicos são unicode, e a {numref}[tbl-lean-symbols] dá a abreviação que digita cada um. Digitar a abreviação com contrabarra e em seguida espaço ou tabulação insere o caractere no VS Code.

:::table +header
*
  * Símbolo
  * Significado
  * Digitado como
*
  * →
  * implicação
  * `\to`
*
  * ∧
  * conjunção
  * `\and`
*
  * ∨
  * disjunção
  * `\or`
*
  * ¬
  * negação
  * `\not`
*
  * ↔
  * bicondicional
  * `\iff`
*
  * ⊥
  * absurdo
  * `\bot`
*
  * ⟨ ⟩
  * construtor anônimo
  * `\langle`, `\rangle`
*
  * ·
  * foco de objetivo
  * `\.`
:::

{tabcap "tbl-lean-symbols"}[Os símbolos lógicos e as abreviações que os digitam.]

O mesmo enunciado se prova por um termo ou no modo de táticas, e os dois produzem a mesma prova subjacente. As seções seguintes usam ambos.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  exact ⟨h.right, h.left⟩
```

Os comandos que inspecionam uma declaração começam com `#`. O comando `#check` imprime o tipo de um termo, que no caso de uma prova é a proposição que ela prova.

```lean (name := checkAndSwap)
#check fun (P Q : Prop) (h : P ∧ Q) =>
  (⟨h.right, h.left⟩ : Q ∧ P)
```
```leanOutput checkAndSwap
fun P Q h => ⟨h.right, h.left⟩ : ∀ (P Q : Prop), P ∧ Q → Q ∧ P
```

# Dedução Natural em Lean

Em Lean, enunciamos uma proposição e a provamos em uma única declaração. A palavra-chave `example` introduz um enunciado anônimo, e `theorem` introduz um enunciado com nome. As hipóteses aparecem antes dos dois-pontos como suposições nomeadas, e a proposição a provar, o *objetivo*, aparece depois.

Lean codifica a dedução natural diretamente. Uma prova de uma proposição é um *termo* cujo tipo é aquela proposição, uma suposição aberta é uma variável daquele tipo, e cada regra de dedução torna-se um modo de construir ou desmontar termos. A prova mais simples usa uma suposição diretamente, a regra de suposição da dedução natural.

```lean
example (P : Prop) (h : P) : P := h
```

Aqui `h` nomeia a suposição de que P vale, e a prova é o próprio `h`. A Aula 3 desenvolve essa correspondência entre proposições e tipos.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, em *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980.]

A {numref}[tbl-rules-to-lean] mapeia cada regra da seção de dedução natural ao termo de Lean que a realiza. Uma regra de introdução constrói um termo, e uma regra de eliminação o desmonta.

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

{tabcap "tbl-rules-to-lean"}[As regras de dedução natural e os termos de Lean que as realizam.]

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

{ex "ex-natural-deduction-lean-implication-reflexive"}[] A implicação é reflexiva.

```lean
example (P : Prop) : P → P :=
  fun h => h
```

{ex "ex-natural-deduction-lean-conjunction-entails-each-conjunct"}[] Uma conjunção implica cada uma das suas partes.

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

{ex "ex-natural-deduction-lean-disjunct-entails-disjunction"}[] Um disjunto implica a disjunção.

```lean
example (P Q : Prop) : P → P ∨ Q :=
  fun h => Or.inl h
```

{ex "ex-natural-deduction-lean-anything-follows-absurdity"}[] Qualquer coisa decorre do absurdo.

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

{ex "ex-natural-deduction-lean-modus-ponens-packaged-single"}[] Modus ponens, empacotado como uma única implicação.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

{ex "ex-natural-deduction-lean-disjunction-commutes"}[] A disjunção comuta.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

{ex "ex-natural-deduction-lean-double-negation-introduction"}[] Introdução da dupla negação.

```lean
example (P : Prop) : P → ¬¬P :=
  fun hP hnP => hnP hP
```

{ex "ex-natural-deduction-lean-contraposition"}[] Contraposição.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  fun hPQ hnQ hP => hnQ (hPQ hP)
```

{ex "ex-natural-deduction-lean-double-negation-elimination-which"}[] Eliminação da dupla negação, que requer raciocínio clássico.

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

{ex "ex-natural-deduction-lean-currying-turns-conjunctive-hypothesis"}[] O currying transforma uma hipótese conjuntiva em implicações aninhadas.

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → (Q → R)) :=
  fun h hP hQ => h ⟨hP, hQ⟩
```

# Provando com Táticas
%%%
tag := "taticas"
%%%

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

{ex "ex-proving-tactics-implication-reflexive"}[] A implicação é reflexiva.

```lean
example (P : Prop) : P → P := by
  intro h
  exact h
```

{ex "ex-proving-tactics-conjunction-entails-each-conjunct"}[] Uma conjunção implica cada uma das suas partes.

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

{ex "ex-proving-tactics-disjunct-entails-disjunction"}[] Um disjunto implica a disjunção.

```lean
example (P Q : Prop) : P → P ∨ Q := by
  intro h
  exact Or.inl h
```

{ex "ex-proving-tactics-anything-follows-absurdity"}[] Qualquer coisa decorre do absurdo.

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

{ex "ex-proving-tactics-modus-ponens-packaged-single"}[] Modus ponens, empacotado como uma única implicação.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

{ex "ex-proving-tactics-disjunction-commutes"}[] A disjunção comuta.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

{ex "ex-proving-tactics-double-negation-introduction"}[] Introdução da dupla negação.

```lean
example (P : Prop) : P → ¬¬P := by
  intro hP hnP
  exact hnP hP
```

{ex "ex-proving-tactics-contraposition"}[] Contraposição.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hPQ hnQ hP
  exact hnQ (hPQ hP)
```

{ex "ex-proving-tactics-double-negation-elimination-which"}[] Eliminação da dupla negação, que requer raciocínio clássico.

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

{ex "ex-proving-tactics-currying-turns-conjunctive-hypothesis"}[] O currying transforma uma hipótese conjuntiva em implicações aninhadas.

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

A partir de uma prova do absurdo, a eliminação de ⊥ prova qualquer proposição.{fnref}[exfalso]

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

Uma implicação e o seu antecedente, ambos projetados da conjunção, combinam-se por →E para dar o consequente.{fnref}[modusponens]

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

Esta direção requer raciocínio clássico. `Classical.byContradiction` descarta a suposição ¬P após derivar ⊥ dela junto com ¬¬P.{fnref}[raa]

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

:::footnotes

{fnAnchor "exfalso"}[] *Ex falso quodlibet* é latim para "de uma falsidade, qualquer coisa se segue".

{fnAnchor "modusponens"}[] *Modus ponens* é latim, abreviação de *modus ponendo ponens*, "o modo que afirma afirmando".

{fnAnchor "raa"}[] O passo clássico marcado RAA é *reductio ad absurdum*, latim para "redução ao absurdo".

:::

# Exercícios

Prove cada enunciado em Lean, substituindo `sorry` por uma prova. Baixe o arquivo de exercícios [`Lecture01.lean`](example-code/Lectures/Pt/Lecture01.lean) e abra-o no VS Code.

```savedComment
Exercícios da Aula 1: Motivação e Lógica Proposicional.
Substitua cada `sorry` por uma prova.
```

{exercise "exr-implication-composes"}[] A implicação compõe.

```savedLean -keep
theorem exercise1 (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry
```

{exercise "exr-conjunction-distributes-over-disjunction"}[] A conjunção distribui sobre a disjunção.

```savedLean -keep
theorem exercise2 (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

{exercise "exr-disjunction-associates"}[] A disjunção associa.

```savedLean -keep
theorem exercise3 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry
```

{exercise "exr-this-direction-first-de"}[] Esta direção da primeira lei de De Morgan é construtiva.

```savedLean -keep
theorem exercise4 (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry
```

{exercise "exr-peirce-s-law-margin"}[] Lei de Peirce.{margin}[C. S. Peirce, *On the Algebra of Logic: A Contribution to the Philosophy of Notation*, American Journal of Mathematics 7(2), 1885, pp. 180–196.] Ela requer raciocínio clássico; considere uma análise de casos sobre `Classical.em P`.

```savedLean -keep
theorem exercise5 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry
```

{exercise "exr-disjunction-distributes-over-conjunction"}[] A disjunção distribui sobre a conjunção.

```savedLean -keep
theorem exercise6 (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry
```

{exercise "exr-implication-conjunction-splits-two"}[] Uma implicação para uma conjunção divide-se em duas implicações.

```savedLean -keep
theorem exercise7 (P Q R : Prop) :
    (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  sorry
```

{exercise "exr-disjunction-negation-one-disjunct"}[] De uma disjunção e da negação de um dos disjuntos, o outro vale.

```savedLean -keep
theorem exercise8 (P Q : Prop) : (P ∨ Q) → ¬P → Q := by
  sorry
```

{exercise "exr-no-proposition-equivalent-own"}[] Nenhuma proposição é equivalente à sua própria negação.

```savedLean -keep
theorem exercise9 (P : Prop) : ¬(P ↔ ¬P) := by
  sorry
```

{exercise "exr-any-two-propositions-one"}[] De duas proposições quaisquer, uma implica a outra. Requer raciocínio clássico; considere uma análise de casos sobre `Classical.em P`.

```savedLean -keep
theorem exercise10 (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  sorry
```

```lean -show
end Lecture1
```
