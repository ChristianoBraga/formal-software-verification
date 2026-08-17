import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers
import Lectures.Pt.Lecture03

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Aula 4: Provas Regressivas" =>

%%%
tag := "aula-4"
%%%

Esta aula fornece o método de prova que a Aula 3 adiou, seguindo o capítulo 3 do *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, edição de 2026, capítulo 3.] Ela apresenta o modo de táticas, as táticas básicas, as regras dos conectivos, dos quantificadores e da igualdade, as táticas de reescrita `rw` e `simp` e as provas por indução matemática, e descarrega os enunciados que a Aula 3 deixou com `sorry`.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-4.pt.html).*

# Provas Regressivas

Uma *tática* opera sobre um objetivo de prova e o prova ou cria novos subobjetivos. Um *objetivo* consiste em um *contexto local*, que lista declarações de variáveis x : σ e hipóteses h : P, e uma *conclusão*, a proposição por provar. Escrevemos o objetivo como o *sequente* C ⊢ Q, cujo *antecedente* C é o contexto de hipóteses e cujo *consequente* Q é a conclusão.{margin}[J. Avigad, L. de Moura, S. Kong, S. Ullrich, *Theorem Proving in Lean 4*, capítulo 5.]

Táticas são um mecanismo de prova *regressivo*. Uma prova regressiva parte do objetivo e trabalha em direção às hipóteses e aos teoremas disponíveis, e a sua frase característica é "basta provar". Uma prova *progressiva* parte das hipóteses e trabalha em direção ao objetivo, e a Aula 5 a desenvolve. Dadas as hipóteses ha : a, hab : a → b, hbc : b → c e a conclusão c, as duas direções se leem assim.

```
Regressiva, a partir do objetivo:
  para provar c, por hbc basta provar b;
  para provar b, por hab basta provar a;
  e ha prova a.

Progressiva, a partir das hipóteses:
  de ha e hab, temos b;
  de b e hbc, temos c.
```

Uma derivação na dedução natural da Aula 1 se escreve empilhando aplicações de regras, com as premissas de cada regra acima do traço de inferência e a sua conclusão abaixo dele. As fórmulas do topo, que nenhuma regra deriva, são as suposições e os axiomas, e a fórmula final, embaixo, é a conclusão da derivação. A derivação admite as duas leituras, progressiva das suposições para a conclusão e regressiva da conclusão para as suposições.{margin}[G. Gentzen, *Investigations into Logical Deduction*, in M. E. Szabo (ed.), *The Collected Papers of Gerhard Gentzen*, North-Holland, 1969, pp. 68–131.]

A palavra-chave `by` entra no modo de táticas, e cada linha depois dela é uma tática. A prova abaixo introduz as variáveis universalmente quantificadas e as duas hipóteses, e fecha o objetivo. As linhas `trace_state` imprimem o objetivo entre os passos, e as saídas seguem o código.

```lean (name := fstOfTwo)
namespace Backward

theorem fst_of_two_props :
    ∀ a b : Prop, a → b → a := by
  intro a b
  trace_state
  intro ha hb
  trace_state
  apply ha

end Backward
```

Depois de `intro a b`, as duas proposições entraram no contexto, e a conclusão é a implicação que resta.

```leanOutput fstOfTwo
a b : Prop
⊢ a → b → a
```

Depois de `intro ha hb`, as duas hipóteses estão disponíveis, e a conclusão é a.

```leanOutput fstOfTwo
a b : Prop
ha : a
hb : b
⊢ a
```

A prova abaixo encadeia duas implicações. Leia-a como três passos de "basta provar": para provar c, por hbc basta provar b; para provar b, por hab basta provar a; e ha prova a.

```lean
namespace Backward

theorem prop_comp (a b c : Prop) (hab : a → b)
    (hbc : b → c) : a → c := by
  intro ha
  apply hbc
  apply hab
  apply ha

end Backward
```

# Táticas Básicas

As táticas básicas desta aula são `intro`, `apply`, `exact`, `assumption`, `sorry`, `clear` e `rename`. Elas são básicas porque cada uma realiza uma única transformação elementar do estado da prova e porque nenhuma depende de um conectivo, de um quantificador ou de uma teoria em particular. Quase toda prova por táticas as utiliza.

A tática `intro` move a variável ligada por ∀ à frente, ou a suposição à frente de uma implicação, da conclusão para o contexto local, sob um nome escolhido. Dado um objetivo demonstrável, ela sempre produz um objetivo demonstrável.

A tática `apply` casa a conclusão do objetivo com a conclusão de um teorema ou de uma hipótese, a menos de computação, e adiciona as suposições do teorema como novos objetivos. Ela pode transformar um objetivo demonstrável em um indemonstrável. A tática `exact` fecha o objetivo com um termo que o prova. Quando as duas fecham o objetivo, `exact` declara a intenção com mais clareza. A tática `assumption` procura no contexto local uma hipótese que case com a conclusão.

Lean insere os parâmetros escritos à esquerda dos dois-pontos no contexto local do objetivo inicial, então as provas abaixo não precisam de `intro`.

```lean
namespace Backward

theorem fst_of_two_props_params (a b : Prop)
    (ha : a) (hb : b) : a := by
  apply ha

theorem fst_of_two_props_exact (a b : Prop)
    (ha : a) (hb : b) : a := by
  exact ha

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) : a := by
  assumption

end Backward
```

A tática `sorry` fecha qualquer objetivo sem prová-lo, exatamente como o termo `sorry` fez na Aula 3, e Lean marca cada uso. O exemplo abaixo mostra como `apply` transforma um objetivo demonstrável em um indemonstrável. A conclusão `a ∨ b` segue da hipótese `hb` pela regra `Or.inr`, mas `apply Or.inl` se compromete com o disjunto esquerdo e deixa o objetivo `a`, que nenhuma hipótese prova.

```lean (name := unsafeApply)
example (a b : Prop) (hb : b) : a ∨ b := by
  apply Or.inl
  trace_state
  sorry
```

```leanOutput unsafeApply
a b : Prop
hb : b
⊢ a
```

Com a regra `Or.inr` a prova fecha o objetivo.

```lean
example (a b : Prop) (hb : b) : a ∨ b := by
  apply Or.inr
  exact hb
```

Duas táticas limpam o contexto local. A tática `clear` descarta variáveis ou hipóteses de que o resto da prova não precisa, e `rename` renomeia uma hipótese, selecionada pela sua proposição.

```lean
namespace Backward

theorem drop_unused (p q : Prop) (hp : p) (hq : q)
    (hpq : p → q) : q := by
  clear hp hpq p
  rename q => hgoal
  exact hgoal

end Backward
```

## Exemplos

Os exemplos abaixo exercitam `intro`, `apply`, `exact`, `assumption`, `sorry`, `clear` e `rename`, e distinguem as táticas que preservam a demonstrabilidade das que podem perdê-la.

{ex "ex-basic-tactics-intro-forall-goal-trace"}[] `intro` em um objetivo com ∀ move a variável ligada para o contexto. O trace mostra o objetivo antes e depois.

```lean (name := exIntroForall)
example : ∀ n : ℕ, add n 0 = n := by
  trace_state
  intro n
  trace_state
  exact rfl
```

```leanOutput exIntroForall
⊢ ∀ (n : ℕ), add n 0 = n
```

```leanOutput exIntroForall
n : ℕ
⊢ add n 0 = n
```

{ex "ex-basic-tactics-one-intro-several-names"}[] Um `intro` com vários nomes abrevia vários `intro`s. Os dois roteiros provam o mesmo teorema.

```lean
example : ∀ a b : Prop, a → a := by
  intro a b ha
  exact ha

example : ∀ a b : Prop, a → a := by
  intro a
  intro b
  intro ha
  exact ha
```

{ex "ex-basic-tactics-parameters-left-colon-context"}[] Parâmetros à esquerda dos dois-pontos dispensam `intro`, pois Lean os insere no contexto local do objetivo inicial.

```lean
example : ∀ a : Prop, a → a := by
  intro a ha
  exact ha

example (a : Prop) (ha : a) : a := by
  exact ha
```

{ex "ex-basic-tactics-exact-apply-same-goal"}[] `exact h` e `apply h` fecham o mesmo objetivo, e `exact` diz mais.

```lean
example (a b : Prop) (hab : a → b) (ha : a) : b := by
  exact hab ha

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  apply hab ha
```

{ex "ex-basic-tactics-assumption-closes-without-naming"}[] `assumption` fecha o objetivo sem nomear a hipótese.

```lean
example (a b c : Prop) (ha : a) (hb : b) (hc : c) : b := by
  assumption
```

{ex "ex-basic-tactics-two-applys-walk-backwards"}[] Dois `apply`s em sequência aplicam duas implicações regressivamente.

```lean
example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  apply hbc
  apply hab
  exact ha
```

{ex "ex-basic-tactics-unsafe-apply-provable-unprovable"}[] `apply` pode perder um objetivo demonstrável. Escolher o disjunto errado deixa uma conclusão que nenhuma hipótese prova, e só `sorry` o fecha.

```lean
example (a b : Prop) (ha : a) : a ∨ b := by
  apply Or.inr
  sorry
```

{ex "ex-basic-tactics-sorry-closes-print-axioms"}[] `sorry` fecha qualquer objetivo, e `#print axioms` relata o uso de `sorryAx`, como na Aula 3.

```lean (name := exSorryAxioms)
namespace Backward

theorem unproved (a : Prop) : a := by
  sorry

end Backward

#print axioms Backward.unproved
```

```leanOutput exSorryAxioms
'Backward.unproved' depends on axioms: [sorryAx]
```

{ex "ex-basic-tactics-clear-removes-unused"}[] `clear` remove uma hipótese e uma variável que a prova não usa.

```lean
example (a b : Prop) (ha : a) (hb : b) : b := by
  clear ha a
  exact hb
```

{ex "ex-basic-tactics-rename-by-proposition"}[] `rename` renomeia uma hipótese, selecionada pela sua proposição.

```lean
example (a b : Prop) (h : a ∧ b) : a ∧ b := by
  rename a ∧ b => hab
  exact hab
```

# Raciocínio sobre Conectivos e Quantificadores

A Aula 1 apresentou as regras dos conectivos como figuras de inferência. Cada figura é um teorema ordinário de Lean. Uma *regra de introdução* tem o conectivo como símbolo mais externo da sua conclusão e diz como prová-lo, e uma *regra de eliminação* tem o conectivo em uma suposição e diz como essa prova deve ter sido construída. O quadro abaixo lista as regras de ∧, ∨ e ↔, com metavariáveis nos lugares que as regras deixam em aberto.

```
And.intro : ?a → ?b → ?a ∧ ?b
And.left  : ?a ∧ ?b → ?a
And.right : ?a ∧ ?b → ?b
Or.inl    : ?a → ?a ∨ ?b
Or.inr    : ?b → ?a ∨ ?b
Or.elim   : ?a ∨ ?b → (?a → ?c) → (?b → ?c) → ?c
Iff.intro : (?a → ?b) → (?b → ?a) → (?a ↔ ?b)
Iff.mp    : (?a ↔ ?b) → ?a → ?b
Iff.mpr   : (?a ↔ ?b) → ?b → ?a
```

As regras dos quantificadores, a verdade, a falsidade e os princípios clássicos completam a lista. A negação dispensa regras próprias, pois ¬a é *definida* como a → False, então `intro` se aplica a uma conclusão negada, como a Aula 1 mostrou. `True.intro` é a única regra da verdade, `False.elim` é a única regra da falsidade, e a lógica de Lean é clássica por meio de `Classical.em` e `Classical.byContradiction`, usados desde a Aula 1 e agora aplicáveis regressivamente.

```
Exists.intro : ∀ (w : ?α), ?p w → ∃ x, ?p x
Exists.elim  : (∃ x, ?p x) → (∀ (w : ?α), ?p w → ?b) → ?b
True.intro   : True
False.elim   : False → ?c
Classical.em : ∀ (p : Prop), p ∨ ¬p
Classical.byContradiction : (¬?a → False) → ?a
```

Uma *metavariável* ?a representa um termo ainda por determinar. Quando `apply` casa a conclusão do objetivo com a conclusão de uma regra, a *unificação* determina algumas metavariáveis e deixa as demais como novos objetivos, que em geral desaparecem conforme a prova avança. A prova abaixo aplica a regra de introdução de ∧ regressivamente e fecha cada subobjetivo com uma regra de eliminação.

```lean
namespace Backward

theorem And_swap (a b : Prop) : a ∧ b → b ∧ a := by
  intro hab
  apply And.intro
  apply And.right
  exact hab
  apply And.left
  exact hab

end Backward
```

O marcador `·`, usado desde a Aula 1, foca cada subobjetivo, e a *justaposição* instancia uma regra progressivamente, passando a hipótese diretamente em vez de esperar que ela apareça como subobjetivo. Esse é um pequeno passo progressivo dentro de uma prova regressiva, e ele evita as metavariáveis que `apply` deixa para trás.

```lean
namespace Backward

theorem and_swap_bullets :
    ∀ a b : Prop, a ∧ b → b ∧ a := by
  intro a b hab
  apply And.intro
  · exact And.right hab
  · exact And.left hab

end Backward
```

A justaposição também instancia uma hipótese universal, exatamente como na Aula 2.

```lean
namespace Backward

opaque fixedFun : ℕ → ℕ

theorem fixedFun_at_seven (h : ∀ n : ℕ, fixedFun n = 0) :
    fixedFun 7 = 0 := by
  exact h 7

end Backward
```

A regra de eliminação de ∨ realiza a análise de casos que a tática `cases` realizou na Aula 1, e `modus_ponens` e `Not_Not_intro` combinam as regras vistas até aqui.

```lean
namespace Backward

theorem Or_swap (a b : Prop) : a ∨ b → b ∨ a := by
  intro hab
  apply Or.elim hab
  · intro ha
    exact Or.inr ha
  · intro hb
    exact Or.inl hb

theorem modus_ponens (a b : Prop) : (a → b) → a → b := by
  intro hab ha
  apply hab
  exact ha

theorem Not_Not_intro (a : Prop) : a → ¬¬ a := by
  intro ha hna
  apply hna
  exact ha

end Backward
```

Para provar enunciados de lógica proposicional, o guia oferece as estratégias a seguir.

* Olhe a conclusão. Se ela é uma implicação ou uma negação, `intro` faz progresso.
* Olhe as hipóteses. Uma conjunção oferece `And.left` e `And.right`, uma disjunção oferece `Or.elim`, e uma equivalência oferece `Iff.mp` e `Iff.mpr`.
* Case a conclusão do objetivo com a conclusão de uma regra de introdução e a aplique com `apply`.
* Prefira táticas que preservam a demonstrabilidade enquanto elas fizerem progresso, e registre os pontos de escolha em que uma tática se compromete com um lado.
* Quando um subobjetivo repete uma hipótese, `exact` ou `assumption` o fecha.
* Quando nada construtivo se aplica, considere uma análise de casos sobre `Classical.em`.
* Se a prova não progride, retroceda até o último ponto de escolha e tente a outra opção.

## Exemplos

Os exemplos abaixo aplicam as regras regressivamente com `apply`, as instanciam progressivamente por justaposição e observam as metavariáveis que aparecem pelo caminho.

{ex "ex-connectives-quantifiers-and-intro-splits-goals"}[] `apply And.intro` divide a conjunção em dois objetivos, e o trace mostra os dois.

```lean (name := exAndIntroSplit)
example (a b : Prop) (hab : a ∧ b) : b ∧ a := by
  apply And.intro
  trace_state
  · exact And.right hab
  · exact And.left hab
```

```leanOutput exAndIntroSplit
case left
a b : Prop
hab : a ∧ b
⊢ b

case right
a b : Prop
hab : a ∧ b
⊢ a
```

{ex "ex-connectives-quantifiers-juxtaposition-closes-projection"}[] A justaposição fecha um objetivo em um passo, passando a hipótese à regra de eliminação.

```lean
example (a b : Prop) (hab : a ∧ b) : b := by
  exact And.right hab
```

{ex "ex-connectives-quantifiers-metavariable-appears-instantiated"}[] Aplicar a regra de eliminação regressivamente deixa uma metavariável ?a na conclusão, e até um segundo objetivo pedindo a própria ?a. O `exact` final instancia os dois de uma vez.

```lean (name := exMetaRight)
example (a b : Prop) (hab : a ∧ b) : b := by
  apply And.right
  trace_state
  exact hab
```

```leanOutput exMetaRight
case self
a b : Prop
hab : a ∧ b
⊢ ?a ∧ b

case a
a b : Prop
hab : a ∧ b
⊢ Prop
```

{ex "ex-connectives-quantifiers-or-inl-chooses-side"}[] `apply Or.inl` escolhe o lado esquerdo e deixa a sua prova como objetivo.

```lean
example (a b : Prop) (ha : a) : a ∨ b := by
  apply Or.inl
  exact ha
```

{ex "ex-connectives-quantifiers-or-elim-one-goal-per-disjunct"}[] `apply Or.elim h` produz um subobjetivo por disjunto, e um marcador fecha cada um.

```lean
example (a b c : Prop) (h : a ∨ b) (hac : a → c)
    (hbc : b → c) : c := by
  apply Or.elim h
  · intro ha
    exact hac ha
  · intro hb
    exact hbc hb
```

{ex "ex-connectives-quantifiers-iff-intro-two-implications"}[] `apply Iff.intro` divide uma equivalência nas suas duas implicações.

```lean
example (a : Prop) : a ∧ a ↔ a := by
  apply Iff.intro
  · intro haa
    exact And.left haa
  · intro ha
    exact And.intro ha ha
```

{ex "ex-connectives-quantifiers-iff-mp-mpr-directions"}[] `Iff.mp` e `Iff.mpr` extraem as duas direções de uma hipótese de equivalência por justaposição.

```lean
example (a b : Prop) (hab : a ↔ b) (ha : a) : b := by
  exact Iff.mp hab ha

example (a b : Prop) (hab : a ↔ b) (hb : b) : a := by
  exact Iff.mpr hab hb
```

{ex "ex-connectives-quantifiers-exists-intro-witness"}[] `apply Exists.intro` fornece uma testemunha, e a hipótese na testemunha fecha o que resta.

```lean
example (P : ℕ → Prop) (h : P 3) : ∃ n, P n := by
  apply Exists.intro 3
  exact h
```

{ex "ex-connectives-quantifiers-exists-elim-names-witness"}[] `apply Exists.elim h` consome uma hipótese existencial e nomeia a sua testemunha.

```lean
example (α : Type) (P : α → Prop) (Q : Prop)
    (hex : ∃ x, P x) (h : ∀ x, P x → Q) : Q := by
  apply Exists.elim hex
  intro a hPa
  exact h a hPa
```

{ex "ex-connectives-quantifiers-negation-truth-falsehood"}[] Três provas de uma linha. `intro` se aplica a uma conclusão negada, `True.intro` é a única regra da verdade, e `apply False.elim` fecha qualquer objetivo a partir de uma prova de `False`, pois a falsidade não tem regra de introdução.

```lean
example : ¬False := by
  intro h
  exact h

example : True := by
  exact True.intro

example (a : Prop) (h : False) : a := by
  apply False.elim
  exact h
```

# Raciocínio sobre Igualdade

A tática `rfl` prova uma conclusão l = r quando os dois lados se tornam sintaticamente idênticos sob computação, e ela tem sucesso exatamente onde um matemático diz "por definição". O termo `rfl` da Aula 3 é a sua forma de termo. A computação aqui nomeia seis *conversões*.

:::table +header
*
  * Conversão
  * O que ela faz
*
  * α
  * renomeia uma variável ligada
*
  * β
  * aplica uma função anônima ao seu argumento
*
  * δ
  * desdobra uma definição
*
  * ζ
  * substitui um `let`
*
  * η
  * identifica `fun x => f x` com f
*
  * ι
  * projeta uma aplicação de construtor
:::

A igualdade também é um conjunto de regras. `Eq.refl` a introduz, `Eq.symm` e `Eq.trans` dizem que ela é uma relação de equivalência, e `Eq.subst` substitui iguais por iguais em um contexto que uma metavariável representa. Uma nota de sintaxe: `=` liga mais forte que os conectivos, então `a = b ∧ c = d` se lê `(a = b) ∧ (c = d)`.

```
Eq.refl  : ∀ (a : ?α), a = a
Eq.symm  : ?a = ?b → ?b = ?a
Eq.trans : ?a = ?b → ?b = ?c → ?a = ?c
Eq.subst : ?a = ?b → ?P ?a → ?P ?b
```

```lean
namespace Backward

theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c := by
  apply Eq.trans
  · exact hab
  · apply Eq.symm
    exact hcb

end Backward
```

A tática `ac_rfl` estende `rfl` com associatividade e comutatividade para os operadores registrados como associativos e comutativos, e a §4.6 registra o nosso `add` entre eles.

## Exemplos

Os exemplos abaixo nomeiam a conversão que cada `rfl` realiza e então raciocinam com as regras da igualdade. A definição de `double` sustenta a conversão δ.

```lean
namespace Backward

def double (n : ℕ) : ℕ := n + n

end Backward
```

{ex "ex-equality-alpha-conversion-renames-bound"}[] A conversão α renomeia a variável ligada.

```lean
namespace Backward

theorem α_example {α β : Type} (f : α → β) :
    (fun x => f x) = (fun y => f y) := by
  rfl

end Backward
```

{ex "ex-equality-beta-conversion-applies-function"}[] A conversão β aplica uma função anônima ao seu argumento.

```lean
namespace Backward

theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x => f x) a = f a := by
  rfl

end Backward
```

{ex "ex-equality-delta-conversion-unfolds-definition"}[] A conversão δ desdobra a definição de `double`.

```lean
namespace Backward

theorem δ_example : double 5 = 5 + 5 := by
  rfl

end Backward
```

{ex "ex-equality-zeta-conversion-substitutes-let"}[] A conversão ζ substitui o `let` de escopo local.

```lean
namespace Backward

theorem ζ_example :
    (let n : ℕ := 2
     n + n) = 4 := by
  rfl

end Backward
```

{ex "ex-equality-eta-conversion-identifies-fun"}[] A conversão η identifica `fun x => f x` com a própria f.

```lean
namespace Backward

theorem η_example {α β : Type} (f : α → β) :
    (fun x => f x) = f := by
  rfl

end Backward
```

{ex "ex-equality-iota-conversion-projects-constructor"}[] A conversão ι projeta um componente de uma aplicação de construtor.

```lean
namespace Backward

theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a := by
  rfl

end Backward
```

{ex "ex-equality-rfl-depends-recursion-pattern"}[] `rfl` prova `add m 0 = m` e não `add 0 m = m`, pois `add` recorre sobre o seu segundo argumento, como o terceiro exemplo trabalhado da Aula 3 mostrou. O segundo enunciado espera a §4.6.

```lean
example (m : ℕ) : add m 0 = m := by
  rfl

example (m : ℕ) : add 0 m = m := by
  sorry
```

{ex "ex-equality-ac-rfl-addition"}[] `ac_rfl` prova uma equação a menos de associatividade e comutatividade de `+`.

```lean
example (a b c : ℕ) : a + b + c = c + b + a := by
  ac_rfl
```

{ex "ex-equality-ac-rfl-multiplication"}[] A mesma forma vale para `*`, também registrado como associativo e comutativo.

```lean
example (a b c : ℕ) : a * b * c = c * b * a := by
  ac_rfl
```

{ex "ex-equality-eq-subst-arbitrary-context"}[] `apply Eq.subst` substitui iguais por iguais sob um predicado arbitrário, que a unificação recupera.

```lean
example (α : Type) (P : α → Prop) (a b : α)
    (hab : a = b) (hPa : P a) : P b := by
  apply Eq.subst hab
  exact hPa
```

# Táticas de Reescrita

A tática `rw` aplica uma equação como regra de reescrita da esquerda para a direita, uma vez. Ela encontra o primeiro subtermo que casa com o lado esquerdo, instancia as variáveis da equação de acordo, substitui toda ocorrência daquele subtermo instanciado e então tenta `rfl`. Um `←` à frente usa a equação da direita para a esquerda, `at h` reescreve a hipótese h em vez da conclusão, e `at *` reescreve em toda parte. Dado o nome de uma constante em vez de uma equação, `rw` usa as equações que definem a constante, e é assim que `rw [Not]` expande uma negação e `rw [add]` desdobra o nosso `add`.

```lean
namespace Backward

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c := by
  rw [hab]
  rw [hcb]

theorem not_intro_demo (a : Prop) : (a → False) → ¬ a := by
  rw [Not]
  intro h
  exact h

end Backward
```

A tática `simp` aplica um conjunto padrão de regras de reescrita, o *conjunto simp*, exaustivamente. A sintaxe `simp [t₁, …, tₙ]` adiciona teoremas ou constantes por uma invocação, `simp [-t]` remove um, `simp [*] at *` usa cada hipótese sobre cada hipótese e sobre a conclusão, e o atributo `@[simp]` registra um teorema permanentemente.

```lean
namespace Backward

theorem simp_congruence {α : Type} (a b : α)
    (k : α → ℕ → ℕ) (hab : a = b) :
    k a (2 + 3) = k b 5 := by
  simp [hab]

end Backward
```

A reescrita é onde as provas deixam de ser previsíveis. O conselho do guia é tentar uma tática, estudar os subobjetivos que surgem e ajustar, em vez de planejar cada passo de antemão. Nas palavras do próprio guia, NÃO ENTRE EM PÂNICO.

## Exemplos

Os exemplos abaixo reescrevem na conclusão e nas hipóteses, nas duas direções, e comparam `rw` com `simp` sobre o mesmo objetivo.

{ex "ex-rewriting-rw-left-to-right"}[] `rw [h]` reescreve a conclusão da esquerda para a direita e o fecha com o `rfl` que tenta ao final.

```lean
example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) :
    f a = f b := by
  rw [h]
```

{ex "ex-rewriting-rw-right-to-left"}[] `rw [←h]` usa a mesma equação da direita para a esquerda.

```lean
example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) :
    f b = f a := by
  rw [←h]
```

{ex "ex-rewriting-rw-two-equations-in-turn"}[] `rw [h₁, h₂]` aplica duas equações, uma após a outra.

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  rw [h₁, h₂]
```

{ex "ex-rewriting-rw-at-hypothesis"}[] `rw [h₂] at h₁` reescreve a hipótese, e a hipótese reescrita fecha o objetivo.

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  rw [h₂] at h₁
  exact h₁
```

{ex "ex-rewriting-rw-closes-by-rfl"}[] `rw` fecha o objetivo sozinho quando os dois lados coincidem, porque tenta `rfl` depois de reescrever.

```lean
example (a b : ℕ) (h : a = b) : a = b := by
  rw [h]
```

{ex "ex-rewriting-rw-constant-unfolds-equation"}[] `rw [add]` desdobra uma equação que define o nosso `add`.

```lean
example (m n : ℕ) :
    add m (Nat.succ n) = Nat.succ (add m n) := by
  rw [add]
```

{ex "ex-rewriting-rw-not-expands-negation"}[] `rw [Not] at h` expande a negação em uma hipótese, que então se aplica como implicação.

```lean
example (a : Prop) (h : ¬a) : a → False := by
  rw [Not] at h
  exact h
```

{ex "ex-rewriting-simp-closes-arithmetic"}[] `simp` sozinho fecha um objetivo aritmético a partir do conjunto simp padrão.

```lean
example (n : ℕ) : n + 0 + 0 = n := by
  simp
```

{ex "ex-rewriting-simp-every-occurrence-rw-first"}[] `simp [h]` reescreve toda ocorrência, enquanto `rw [h]` reescreve apenas as ocorrências do primeiro subtermo que casa. O primeiro roteiro precisa de duas reescritas, uma por instância do padrão, e o segundo precisa de um `simp`.

```lean
example (f : ℕ → ℕ) (hf : ∀ x, f x = 0) :
    f 1 + f 2 = 0 := by
  rw [hf]
  rw [hf]

example (f : ℕ → ℕ) (hf : ∀ x, f x = 0) :
    f 1 + f 2 = 0 := by
  simp [hf]
```

{ex "ex-rewriting-simp-star-at-star"}[] `simp [*] at *` usa cada hipótese em toda parte e fecha um objetivo a partir de duas hipóteses encadeadas.

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  simp [*] at *
```

# Provas por Indução Matemática

A tática `induction` realiza indução estrutural sobre uma variável, produzindo um subobjetivo nomeado por construtor do seu tipo. Para ℕ, construído com `Nat.zero` e `Nat.succ`, a indução estrutural é a indução matemática ordinária. Os nomes depois de um construtor ligam os seus argumentos e a hipótese de indução, então o ramo `| succ n' ih` fornece o predecessor n' e a hipótese ih sobre ele. A forma geral para ℕ se lê assim.

```
induction n with
| zero       => (prova do caso base)
| succ n' ih => (prova do caso do passo)
```

A seção relembra `add` e `mul` da Aula 3 e prova as leis que a computação deixou em aberto lá. O arquivo de exercícios extraído repete as definições, então ele é autônomo.

```savedLean -keep
namespace Backward

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => 0
  | m, Nat.succ n => add m (mul m n)

end Backward
```

Os dois primeiros teoremas fornecem as equações recursivas que faltam a `add`, sobre o seu primeiro argumento. Cada prova induz sobre a variável que a recursão consome e fecha o caso do passo com `simp`, usando as equações que definem `add` e a hipótese de indução.

```savedLean
namespace Backward

theorem add_zero (n : ℕ) : add 0 n = n := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

end Backward
```

Comutatividade e associatividade seguem, com os dois teoremas acima descarregando o caso base e o caso do passo da primeira. Estes são `SorryTheorems.add_comm` e `SorryTheorems.add_assoc` da Aula 3, agora com provas de verdade.

```savedLean
namespace Backward

theorem add_comm (m n : ℕ) : add m n = add n m := by
  induction n with
  | zero       => simp [add, add_zero]
  | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

end Backward
```

As duas instâncias abaixo registram `add` como associativo e comutativo, que é o que `ac_rfl` consulta. O comando `instance` é o que a Aula 2 usou para `Membership` e companhia, e o capítulo 5 do guia explica o mecanismo, na semana 6 da disciplina.

```savedLean
namespace Backward

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

end Backward
```

A distributividade fecha a seção, com `ac_rfl` terminando o que `simp` deixa.

```savedLean
namespace Backward

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) := by
  induction n with
  | zero       => rfl
  | succ n' ih =>
    simp [add, mul, ih]
    ac_rfl

end Backward
```

O guia oferece duas dicas. Induza sobre o argumento que a recursão consome, e leia um caso base difícil como sinal de variável de indução errada ou de um teorema auxiliar que falta.[^addzero]

[^addzero]: O guia chama `add 0 n = n` de `add_zero`, embora `add` recorra sobre o seu segundo argumento e a convenção usual leia o zero do enunciado, o que daria `zero_add`. O terceiro exemplo trabalhado da Aula 3 chamou o mesmo enunciado de `zero_add`. Estas notas mantêm os nomes do guia.

## Exemplos

Os exemplos abaixo induzem sobre ℕ e uma vez sobre listas, observam os dois subobjetivos e verificam sobre o que as provas terminadas repousam.

{ex "ex-induction-two-branches-trace"}[] `induction n with` produz um ramo por construtor, e o trace mostra os objetivos do caso base e do passo.

```lean (name := exInductionTrace)
example (n : ℕ) : add 0 n = n := by
  induction n with
  | zero =>
    trace_state
    rfl
  | succ n' ih =>
    trace_state
    simp [add, ih]
```

```leanOutput exInductionTrace
case zero
⊢ add 0 0 = 0
```

```leanOutput exInductionTrace
case succ
n' : ℕ
ih : add 0 n' = n'
⊢ add 0 (n' + 1) = n' + 1
```

{ex "ex-induction-base-case-rfl"}[] O caso base sozinho. O zero à direita casa com a primeira equação de `add`, então `rfl` o fecha.

```lean
example : add 0 0 = 0 := by
  rfl
```

{ex "ex-induction-step-case-simp"}[] O caso do passo sozinho, a partir da sua hipótese de indução.

```lean
example (n' : ℕ) (ih : add 0 n' = n') :
    add 0 (Nat.succ n') = Nat.succ n' := by
  simp [add, ih]
```

{ex "ex-induction-add-succ-two-variables"}[] `add_succ` segue o mesmo padrão em um enunciado com duas variáveis, induzindo sobre a segunda, que a recursão consome.

```lean
example (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]
```

{ex "ex-induction-add-assoc-last-variable"}[] A associatividade, induzindo sobre a última variável.

```lean
example (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]
```

{ex "ex-induction-wrong-variable-stalls"}[] A variável de indução errada impede o progresso da prova. Induzir sobre m deixa objetivos que nem `rfl` nem a hipótese de indução alcançam, e os traces mostram por quê: a recursão de `add` consome n, que os dois objetivos deixam intocado.

```lean (name := exWrongVariable)
example (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  induction m with
  | zero =>
    trace_state
    sorry
  | succ m' ih =>
    trace_state
    sorry
```

```leanOutput exWrongVariable
case zero
n : ℕ
⊢ add (Nat.succ 0) n = (add 0 n).succ
```

```leanOutput exWrongVariable
case succ
n m' : ℕ
ih : add m'.succ n = (add m' n).succ
⊢ add (m' + 1).succ n = (add (m' + 1) n).succ
```

{ex "ex-induction-ac-rfl-registered-add"}[] Com as duas instâncias registradas, `ac_rfl` raciocina sobre `add` como raciocina sobre `+`.

```lean
example (a b c : ℕ) :
    add (add a b) c = add c (add b a) := by
  ac_rfl
```

{ex "ex-induction-mul-zero-first-argument"}[] A equação recursiva de `mul` sobre o seu primeiro argumento, por indução sobre o segundo.

```lean
example (n : ℕ) : mul 0 n = 0 := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [mul, add, ih]
```

{ex "ex-induction-list-append-nil"}[] A indução sobre uma lista tem um ramo por construtor de `List`, com `nil` como base e `cons` como passo. As semanas 6 e 7 tratam a indução estrutural sobre tipos indutivos arbitrários.

```lean
namespace Backward

theorem append_nil {α : Type} (xs : List α) :
    appendPretty xs [] = xs := by
  induction xs with
  | nil          => rfl
  | cons x xs' ih => simp [appendPretty, ih]

end Backward
```

{ex "ex-induction-print-axioms-propext"}[] A prova terminada repousa sobre `propext`, que `simp` usa, e não sobre `sorryAx`, fechando o ciclo com o terceiro exemplo da seção de teoremas da Aula 3.

```lean (name := exAxiomsAddComm)
#print axioms Backward.add_comm
```

```leanOutput exAxiomsAddComm
'Backward.add_comm' depends on axioms: [propext]
```

# Exemplos Trabalhados

Cada exemplo abaixo é realizado por completo e verbalizado, como o guia faz. Eles são disjuntos dos exercícios, e Lean verifica cada linha quando as notas são construídas.

## Distribuir uma conjunção sobre uma disjunção

O enunciado a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) usa apenas `intro`, `apply`, `exact` e marcadores. A regra de eliminação de ∨ conduz a prova, e a justaposição a instancia com o conjunto direito da hipótese.

```lean
namespace Backward

theorem and_or_distrib (a b c : Prop) :
    a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) := by
  intro habc
  apply Or.elim (And.right habc)
  · intro hb
    apply Or.inl
    apply And.intro
    · exact And.left habc
    · exact hb
  · intro hc
    apply Or.inr
    apply And.intro
    · exact And.left habc
    · exact hc

end Backward
```

Em palavras. Suponha a ∧ (b ∨ c). O seu conjunto direito é uma disjunção, e basta provar a conclusão a partir de cada disjunto. Se b vale, basta provar o disjunto esquerdo a ∧ b, cujas partes são o conjunto esquerdo da hipótese e o próprio b. Se c vale, o disjunto direito a ∧ c segue do mesmo modo. Cada marcador fecha um ramo, e a prova se lê exatamente como a sua contraparte de papel e caneta.

## Um objetivo indemonstrável e um retrocesso

A disjunção do enunciado a ∧ b → a ∨ c admite duas regras de introdução, e apenas uma conduz a uma prova. `Or.inl` e `Or.inr` podem transformar um objetivo demonstrável em um indemonstrável. A primeira tentativa se compromete com o disjunto direito, e o trace mostra uma conclusão c que nenhuma hipótese prova, então só `sorry` fecha o bloco.

```lean (name := deadEnd)
example (a b c : Prop) : a ∧ b → a ∨ c := by
  intro hab
  apply Or.inr
  trace_state
  sorry
```

```leanOutput deadEnd
a b c : Prop
hab : a ∧ b
⊢ c
```

O remédio é lembrar o ponto de escolha e retroceder. A segunda tentativa se compromete com o disjunto esquerdo, e o conjunto esquerdo da hipótese o fecha.

```lean
namespace Backward

theorem and_imp_or (a b c : Prop) : a ∧ b → a ∨ c := by
  intro hab
  apply Or.inl
  exact And.left hab

end Backward
```

## `rw` versus `simp`

Dados f e a equação hf : ∀ x, f x = x + 1, qualquer das duas táticas prova a conclusão f (f 0) = 2, de modos diferentes. `rw [hf]` reescreve as ocorrências do primeiro subtermo que casa, aqui a aplicação externa, e precisa de uma segunda invocação para a interna, após a qual o `rfl` que ela tenta fecha o objetivo. `simp [hf]` reescreve exaustivamente e precisa de uma invocação.

```lean
example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) :
    f (f 0) = 2 := by
  rw [hf, hf]

example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) :
    f (f 0) = 2 := by
  simp [hf]
```

O objetivo residual torna concreto o "primeiro subtermo que casa". Um `rw [hf]` reescreve a aplicação externa e deixa a interna no lugar.

```lean (name := rwResidual)
example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) :
    f (f 0) = 2 := by
  rw [hf]
  trace_state
  rw [hf]
```

```leanOutput rwResidual
f : ℕ → ℕ
hf : ∀ (x : ℕ), f x = x + 1
⊢ f 0 + 1 = 2
```

## Descarregar `reverse_cons`

O último exemplo trabalhado da Aula 3 enunciou `reverse (x :: xs) = snoc (reverse xs) x` e o deixou com `sorry`. Desdobrar `reverse` transforma o lado esquerdo em `appendPretty (reverse xs) [x]`, então o enunciado mistura `appendPretty` e `snoc`, e a peça que falta é o teorema que os relaciona. Esta é a dica do guia em ação: um caso difícil costuma sinalizar um teorema auxiliar que falta.

```lean
namespace Backward

theorem append_snoc {α : Type} (ys : List α) (x : α) :
    appendPretty ys [x] = snoc ys x := by
  induction ys with
  | nil           => rfl
  | cons y ys' ih => simp [appendPretty, snoc, ih]

theorem reverse_cons {α : Type} (x : α) (xs : List α) :
    reverse (x :: xs) = snoc (reverse xs) x := by
  simp [reverse, append_snoc]

end Backward
```

O teorema auxiliar induz sobre a lista que a recursão de `appendPretty` consome, e o teorema principal fica então a um `simp` de distância, usando as equações que definem `reverse` e o teorema auxiliar como regras de reescrita.

# Exercícios

Prove cada enunciado em Lean, substituindo `sorry`. Baixe o arquivo de exercícios [`Lecture04.lean`](example-code/Lectures/Pt/Lecture04.lean) e abra-o no VS Code. O arquivo já contém as definições de `add` e `mul` e os teoremas da §4.6, então os exercícios de indução podem se apoiar neles. Os exercícios 1 a 6 usam apenas `intro`, `apply` e `exact`; os exercícios 7 a 9 usam `induction`, `simp` e `rw`; o exercício 10 é opcional.

```savedImport
import Mathlib.Data.Nat.Notation
```

```savedComment
Exercícios da Aula 4: Provas Regressivas.
Substitua cada `sorry` por uma prova. Os exercícios 1 a 6
usam apenas `intro`, `apply` e `exact`. Os exercícios 7 a 9
usam `induction`, `simp` e `rw`. O exercício 10 é opcional.
As definições e os teoremas acima vêm da aula.
```

{exercise "exr-contraction-and-pull"}[] Duas maneiras de alimentar hipóteses a uma função. A primeira fornece a mesma premissa duas vezes; a segunda reordena as premissas antes de aplicar.

```savedLean -keep
namespace Backward

theorem contract (a b : Prop) :
    (a → a → b) → a → b :=
  sorry

theorem pull (a b c : Prop) :
    a → (a → b → c) → b → c :=
  sorry

end Backward
```

{exercise "exr-implication-into-conjunction"}[] Uma implicação cuja conclusão é uma conjunção se divide em uma implicação para cada parte.

```savedLean -keep
namespace Backward

theorem imp_into_and (a b c : Prop) :
    (a → b) → (a → c) → a → b ∧ c :=
  sorry

end Backward
```

{exercise "exr-two-injections"}[] Duas provas do mesmo enunciado, diferindo na injeção que escolhem.

```savedLean -keep
namespace Backward

theorem left_choice (a : Prop) :
    a → a ∨ a :=
  sorry

-- Dê uma resposta diferente da de `left_choice`:
theorem right_choice (a : Prop) :
    a → a ∨ a :=
  sorry

end Backward
```

{exercise "exr-relay-chain"}[] Um revezamento de três implicações leva a primeira hipótese à última conclusão.

```savedLean -keep
namespace Backward

theorem relay (a b c d : Prop) :
    (a → b) → (b → c) → (c → d) → a → d :=
  sorry

end Backward
```

{exercise "exr-absurd-implication"}[] Uma proposição junto com a sua negação prova qualquer coisa. Lembre que ¬a abrevia a → False.

```savedLean -keep
namespace Backward

theorem absurd_imp (a b : Prop) :
    a → ¬ a → b :=
  sorry

end Backward
```

{exercise "exr-existential-currying"}[] Uma implicação a partir de um existencial é o mesmo que uma implicação universalmente quantificada.

```savedLean -keep
namespace Backward

theorem exists_imp {α : Type} (p : α → Prop) (q : Prop) :
    ((∃ x, p x) → q) → ∀ x, p x → q :=
  sorry

end Backward
```

{exercise "exr-one-left-identity-mul"}[] Um é a identidade à esquerda de `mul`, por indução no segundo argumento.

```savedLean -keep
namespace Backward

theorem one_mul (n : ℕ) :
    mul 1 n = n :=
  sorry

end Backward
```

{exercise "exr-add-left-commute"}[] A parcela à esquerda de uma soma aninhada passa pela do meio, reescrevendo com associatividade e comutatividade.

```savedLean -keep
namespace Backward

theorem add_left_comm (l m n : ℕ) :
    add l (add m n) = add m (add l n) :=
  sorry

end Backward
```

{exercise "exr-add-right-commute"}[] A parcela à direita de uma soma aninhada passa pela do meio.

```savedLean -keep
namespace Backward

theorem add_right_comm (l m n : ℕ) :
    add (add l m) n = add (add l n) m :=
  sorry

end Backward
```

{exercise "exr-double-is-times-two"}[] Opcional. Somar um número a si mesmo é igual a multiplicá-lo por dois, e os dois lados já coincidem por computação.

```savedLean -keep
namespace Backward

theorem two_mul (n : ℕ) :
    add n n = mul n 2 :=
  sorry

end Backward
```
