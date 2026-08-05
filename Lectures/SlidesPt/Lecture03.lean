/-
Slides da Aula 3, gerados a partir de fontes verificadas. Cada
seção de nível superior é um slide; o título do documento e os
parágrafos introdutórios formam o slide de título. Todo código
Lean é elaborado na construção e é idêntico ao código das notas
de aula (`Lectures/Pt/Lecture03.lean`) onde os dois coincidem.

Só as notações ℕ e ℤ vêm de Mathlib. A biblioteca completa traria
o seu próprio `Set`, que colide com o `Set` do deck da Aula 2 na
construção conjunta dos dois decks.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Programas e Teoremas" =>

Tipos indutivos, funções recursivas, avaliação e o enunciado de teoremas em Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-3___-Programas-e-Teoremas/)

Baseada no [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), capítulo 2.

# §3.1 Das provas aos programas

* A Aula 1 leu uma prova como um *termo cujo tipo é a proposição* que ela prova. A mesma teoria de tipos classifica *dados*.

* Um tipo como ℕ reúne valores, e um termo de tipo ℕ → ℕ é um *programa*. O `#check` abaixo se lê como o `#check` de um termo de prova, com tipos no lugar de proposições.

```lean (name := checkFun)
#check fun n : ℕ => n + 1
```
```leanOutput checkFun
fun n => n + 1 : ℕ → ℕ
```

* Esta aula *define* tipos e funções e *enuncia* teoremas sobre eles. As provas esperam pela indução estrutural, nas próximas aulas.

# §3.2 Tipos indutivos

* O comando `inductive` define um tipo listando os seus *construtores*. O tipo contém exatamente os valores construídos por finitas aplicações de construtores, e nada mais.

::::cols
:::col
{lbl}[Números naturais]

```lean
namespace MyNat

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

end MyNat
```
:::
:::col
{lbl}[Listas sobre um tipo qualquer]

```lean
namespace MyList

inductive List (α : Type) : Type where
  | nil  : List α
  | cons : α → List α → List α

end MyList
```
:::
::::

* Lean já fornece `Nat` e `List`, então cada reconstrução vive em um espaço de nomes.

# §3.2 Sintaxe abstrata

* Os construtores carregam dados de outros tipos. `AExp` é a *sintaxe abstrata* das expressões aritméticas, e a linguagem imperativa das últimas aulas a estende.

::::cols
:::col
```lean
inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp
```
:::
:::col
{lbl}[A expressão `(x + 3) * y`]

```lean (name := exAExp)
#check AExp.mul
  (AExp.add (AExp.var "x") (AExp.num 3))
  (AExp.var "y")
```
```leanOutput exAExp
((AExp.var "x").add (AExp.num 3)).mul (AExp.var "y") : AExp
```
:::
::::

# §3.3 Funções por casamento de padrões

* Uma função sobre um tipo indutivo se define por *casamento de padrões*, uma equação por forma de construtor.

* A recursão é *estrutural* quando cada chamada recursiva descasca um construtor. Lean aceita essas definições, já que elas terminam.

::::cols
:::col
```lean
def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => 0
  | m, Nat.succ n => add m (mul m n)
```
:::
:::col
```lean
def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)
```
:::
::::

* Os padrões são mais ricos que construtores nus: `n + 2` abrevia duas aplicações de `succ`. Um argumento que nenhuma equação inspeciona vai para a *esquerda dos dois-pontos*, como o `m` acima.

# §3.4 Polimorfismo e argumentos implícitos

* Uma definição pode receber um *tipo como argumento*, dado explicitamente em cada chamada, ou *implicitamente* entre chaves e inferido pelo elaborador. O prefixo `@` restaura a forma explícita.

::::cols
:::col
{lbl}[Argumento de tipo explícito]

```lean
def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)
```

```lean (name := checkAppend)
#check @append
```
```leanOutput checkAppend
append : (α : Type) → List α → List α → List α
```
:::
:::col
{lbl}[Implícito, com a notação de listas]

```lean
def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => appendPretty (reverse xs) [x]
```
:::
::::

* A notação escreve `List.nil` como `[]` e `List.cons x xs` como `x :: xs`, então a definição se lê como a sua própria especificação.

# §3.5 Avaliação

* `#eval` executa um programa pelo *compilador*; `#reduce` normaliza um termo simbolicamente no *kernel*. Use `#eval` em escala.

* Um *ambiente* leva nomes de variáveis a valores, e `eval` reduz uma expressão ao seu valor.

::::cols
:::col
```lean
def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂
```
:::
:::col
```lean (name := evalAdd)
#eval add 2 7
```
```leanOutput evalAdd
9
```

```lean (name := evalDiv)
#eval eval (fun _ => 7)
  (AExp.div (AExp.var "y") (AExp.num 0))
```
```leanOutput evalDiv
0
```
:::
::::

* A divisão por zero não falha. A divisão inteira é *total*, com x / 0 = 0. O comando `#eval` e a nossa função `eval` não têm relação, apesar dos nomes.

# §3.5 A computação como método de prova

* Uma equação cujos dois lados *avaliam para o mesmo valor* vale por `rfl`, o termo que a Aula 2 usou para `n * n = 9` na testemunha 3.

* Esta é a *computação definicional*. Ela resolve qualquer equação *fechada*, sem variáveis, e nada além.

```lean
example : add 2 7 = 9 := rfl

example : eval (fun _ => 7)
    (AExp.div (AExp.var "y") (AExp.num 0)) = 0 := rfl
```

* Em `add m n = add n m` as variáveis bloqueiam a computação, então a lei geral precisa de *indução estrutural*.

# §3.6 Enunciados de teoremas

* Um `theorem` é uma definição cujo *tipo é uma proposição*. Enunciá-lo não exige prova, e `sorry` fica onde a prova entrará.

::::cols
:::col
```lean
namespace SorryTheorems

theorem add_comm (m n : ℕ) :
    add m n = add n m := by
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs := by
  sorry

end SorryTheorems
```
:::
:::col
{lbl}[Lean assinala cada uso de sorry]

```lean (name := axiomsAddComm)
#print axioms SorryTheorems.add_comm
```
```leanOutput axiomsAddComm
'SorryTheorems.add_comm' depends on axioms: [sorryAx]
```
:::
::::

* `#print axioms` informa em que uma prova se apoia. Uma prova por computação não depende de *axioma nenhum*.

# §3.6 Axiomas

* Uma constante `opaque` tem *tipo e nenhuma definição*; um `axiom` afirma uma proposição *sem prova nenhuma*.

```lean
opaque a : ℤ
opaque b : ℤ

axiom a_less_b : a < b
```

* Nada verifica um axioma, então um axioma inconsistente *quebra silenciosamente todo o desenvolvimento*. A disciplina enuncia axiomas apenas para discuti-los.

# Resumo

* Dados e provas compartilham uma teoria de tipos: um *programa* é um termo cujo tipo é um tipo de função.

* `inductive` define um tipo pelos seus *construtores*; os valores são exatamente as aplicações finitas de construtores.

* As funções vêm do *casamento de padrões* com *recursão estrutural*, uma equação por forma de construtor.

* Os argumentos de tipo são *explícitos* `(α : Type)` ou *implícitos* `{α : Type}`, inferidos pelo elaborador e restaurados por `@`.

* `#eval` executa pelo compilador, `#reduce` normaliza no kernel, e `rfl` transforma computação em prova de qualquer equação *fechada*.

* Um `theorem` enuncia uma proposição; `sorry` adia a prova e `#print axioms` expõe o adiamento como `sorryAx`.

* As leis gerais sobre variáveis precisam de *indução estrutural*, o assunto da próxima aula.

Exercícios: veja as [notas de aula](../pt/Aula-3___-Programas-e-Teoremas/).
