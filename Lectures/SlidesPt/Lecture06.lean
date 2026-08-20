/-
Slides da Aula 6, gerados a partir de fontes verificadas. Cada
seção de nível superior é um slide; o título do documento e os
parágrafos de introdução formam o slide de título. Todo o código
Lean é elaborado no momento da compilação e é idêntico ao código
das notas de aula (`Lectures/Pt/Lecture06.lean`) onde os dois se
sobrepõem.

O deck da Aula 5 fornece os tipos de dados anteriores e as
notações de ℕ e ℤ. Tudo o que é novo é declarado dentro de
`namespace Func`.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesPt.Lecture05

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Programação Funcional" =>

Tipos indutivos, recursão, estruturas e classes de tipos

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-6___-Programa______o-Funcional/)

Baseado no [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), capítulo 5.

# §6.1 Tipos indutivos e seus princípios

* Um tipo indutivo é a sua lista de *construtores*, e todo valor é construído aplicando-os, cada um de uma única maneira.

* Para um tipo de dados, Lean gera quatro princípios: o *recursor* `T.rec`, o `casesOn` não recursivo, a *injetividade* de cada construtor e a *disjunção* de construtores distintos.

```lean (name := injEq)
#check @Nat.succ.injEq
```

```leanOutput injEq
Nat.succ.injEq : ∀ (u v : ℕ), (u.succ = v.succ) = (u = v)
```

* O recursor é a forma bruta da recursão estrutural e, lido sobre uma proposição, a indução estrutural, que a Aula 7 deriva.

# §6.1 Recursão e análise de casos a partir do recursor

* O casamento de padrões e a tática `cases` são sintaxe de superfície que o compilador de equações e `cases` traduzem no recursor.

::::cols
:::col
```lean
namespace Func

def usingRec (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ)
    0 (fun _ ih => ih + 2) n

example : usingRec 3 = 6 := rfl

end Func
```
:::
:::col
```lean
namespace Func

example (m n : ℕ)
    (h : Nat.succ m = Nat.succ n) :
    m = n := by
  injection h

example (n : ℕ) :
    Nat.succ n ≠ 0 :=
  Nat.succ_ne_zero n

end Func
```
:::
::::

# §6.2 Recursão estrutural

* Cada chamada recursiva é sobre um argumento estruturalmente menor, então a definição termina e se traduz no recursor.

```lean
namespace Func

def fact : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fact n

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

end Func
```

# §6.2 Por que a terminação

* Uma definição total expõe a sua equação como teorema utilizável, então aceitar `loopy = loopy + 1` provaria `False`. Lean rejeita tais definições; um laço genuíno precisa de `partial def`, que fica opaco.

::::cols
:::col
{lbl}[A equação falsa dá False]

```lean -keep
namespace Func

opaque loopy : ℕ
axiom loopy_eq :
  loopy = loopy + 1

theorem loopy_false : False := by
  have h := loopy_eq
  omega

end Func
```
:::
:::col
{lbl}[Rejeitada: nenhum argumento diminui]

```
def loopForever {α : Type} :
    List α → List α
  | []      => []
  | x :: xs =>
      loopForever (x :: xs)
```

* A saída de emergência `termination_by` fica para depois; esta aula é estrutural.
:::
::::

# §6.3 Casamento de padrões como expressão

* `match` e `if` trazem o casamento de padrões para um termo. Um `match` se traduz pelo recursor do tipo, e `if` ramifica sobre uma instância `Decidable`. `Option` empacota um resultado parcial.

::::cols
:::col
```lean
namespace Func

def classify (n : ℕ) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | _ => "many"

def isZero (n : ℕ) : Bool :=
  if n = 0 then true else false

end Func
```
:::
:::col
```lean
namespace Func

def pred? : ℕ → Option ℕ
  | 0     => none
  | n + 1 => some n

example : pred? 0 = none := rfl

end Func
```

* Os padrões são tentados de cima para baixo; o coringa `_` casa com qualquer coisa.
:::
::::

# §6.4 Estruturas

* Uma estrutura é um tipo indutivo de único construtor com campos nomeados, e Lean deriva uma projeção para cada um.

::::cols
:::col
```lean
namespace Func

structure Segment where
  lo : ℤ
  hi : ℤ

def width (s : Segment) : ℤ :=
  s.hi - s.lo

def seg1 : Segment :=
  { lo := 1, hi := 5 }

end Func
```
:::
:::col
```lean
namespace Func

example : seg1 = ⟨1, 5⟩ := rfl

example : width seg1 = 4 := by
  decide

end Func
```

* `{ … }` e `⟨…⟩` constroem o mesmo valor.
:::
::::

# §6.4 Estendendo registros

* `extends` constrói um registro maior sobre um menor, e `{ r with … }` copia um registro mudando um campo.

::::cols
:::col
```lean
namespace Func

structure NamedSegment
    extends Segment where
  name : String

def ns1 : NamedSegment :=
  { lo := 0, hi := 2, name := "a" }

end Func
```
:::
:::col
```lean
namespace Func

example : ns1.lo = 0 := by decide

example : ns1.name = "a" := rfl

def widen (s : Segment) : Segment :=
  { s with hi := s.hi + 1 }

end Func
```

* Os campos herdados permanecem acessíveis.
:::
::::

# §6.5 Classes de tipos

* Uma `class` declara operações parametrizadas por um ou mais argumentos, uma `instance` as fornece, e a resolução encontra a instância a partir desses argumentos. `Std.Associative op` é indexada por uma operação, não só por um tipo.

::::cols
:::col
```lean
namespace Func

class Size (α : Type) where
  size : α → ℕ

instance {α : Type} :
    Size (List α) where
  size xs := xs.length

instance {α : Type} :
    Size (Option α) where
  size
    | none   => 0
    | some _ => 1

end Func
```
:::
:::col
```lean (name := usize)
namespace Func

def usize {α : Type} [Size α]
    (a : α) : ℕ :=
  Size.size a

#eval usize [1, 2, 3]

end Func
```

```leanOutput usize
3
```
:::
::::

# §6.5 As classes que já usamos

* O `∈` da Aula 2 e a associatividade e a comutatividade da Aula 4 são classes de tipos resolvidas por tipo.

```lean
#check @Membership.mem

#check @Std.Associative
```

* `Membership` dá ao `∈` o seu significado por meio de uma instância escolhida pelo tipo do contêiner, e `Std.Associative` e `Std.Commutative` são as instâncias que `ac_rfl` consultou.

# §6.6 Árvores binárias

* Uma árvore é uma `leaf` ou uma `branch` com um valor e duas subárvores; as funções recorrem sobre as subárvores.

::::cols
:::col
```lean
namespace Func

inductive Tree (α : Type) where
  | leaf
  | branch (l : Tree α) (x : α)
      (r : Tree α)

def mirror {α : Type} :
    Tree α → Tree α
  | .leaf => .leaf
  | .branch l x r =>
      .branch (mirror r) x
        (mirror l)

end Func
```
:::
:::col
```lean (name := tsize)
namespace Func

def treeSize {α : Type} :
    Tree α → ℕ
  | .leaf => 0
  | .branch l _ r =>
      treeSize l + 1 + treeSize r

def t1 : Tree ℕ :=
  .branch (.branch .leaf 1 .leaf)
    2 .leaf

#eval treeSize t1

end Func
```

```leanOutput tsize
2
```
:::
::::

# §6.6 Opções, somas e vetores dependentes

* O mesmo esquema constrói opções, tipos soma e tipos dependentes que carregam informação no seu próprio tipo.

::::cols
:::col
```lean
namespace Func

def mapOption {α β : Type}
    (f : α → β) :
    Option α → Option β
  | none   => none
  | some a => some (f a)

def fromSum : ℕ ⊕ Bool → ℕ
  | .inl n => n
  | .inr b => if b then 1 else 0

end Func
```
:::
:::col
```lean
namespace Func

inductive Vec (α : Type) :
    ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} :
      α → Vec α n → Vec α (n + 1)

end Func
```

* Um `Vec α n` é uma lista de comprimento `n`. As semanas seguintes desenvolvem os tipos dependentes.
:::
::::

# §6.7 Exemplo resolvido: expressões aritméticas

* Uma expressão é uma constante, uma variável, uma soma ou um produto, e um avaliador computa o seu valor sob um ambiente.

::::cols
:::col
```lean
namespace Func

inductive AExp where
  | const (i : ℤ)
  | var (x : String)
  | add (a b : AExp)
  | mul (a b : AExp)

def eval (env : String → ℤ) :
    AExp → ℤ
  | .const i => i
  | .var x   => env x
  | .add a b => eval env a + eval env b
  | .mul a b => eval env a * eval env b

end Func
```
:::
:::col
```lean (name := evalRun)
namespace Func

def sampleEnv : String → ℤ :=
  fun s => if s = "x" then 3 else 0

def e1 : AExp :=
  .add (.const 2)
    (.mul (.var "x") (.const 5))

#eval eval sampleEnv e1

end Func
```

```leanOutput evalRun
17
```

* A sintaxe de uma pequena linguagem; o seu ambiente é o estado.
:::
::::

# §6.7 Exemplo resolvido: uma classe de tipos para tamanho

* Mais uma instância estende `Size` a árvores, e uma função mede uma lista inteira de valores dimensionáveis por resolução.

::::cols
:::col
```lean
namespace Func

instance {α : Type} :
    Size (Tree α) where
  size := treeSize

def totalSize {α : Type} [Size α] :
    List α → ℕ
  | []      => 0
  | x :: xs =>
      Size.size x + totalSize xs

end Func
```
:::
:::col
```lean (name := total)
namespace Func

#eval totalSize [t1, mirror t1]

end Func
```

```leanOutput total
4
```

* A resolução encontra a instância de árvore porque os elementos são árvores, o mesmo mecanismo de `Membership`.
:::
::::

# §6.7 Exemplo resolvido: um registro com uma extensão

* Uma conta se estende a uma conta nomeada, mantendo os dois campos herdados e acrescentando um.

```lean
namespace Func

structure Account where
  owner : String
  balance : ℤ

structure NamedAccount extends Account where
  nickname : String

def acc : NamedAccount :=
  { owner := "A", balance := 100, nickname := "main" }

example : acc.owner = "A" := rfl

end Func
```

* O único construtor de uma estrutura é o `And.intro` da Aula 1, com campos nomeados em vez de posicionais.

# §6.7 Exemplo resolvido: espelhando uma árvore

* Espelhar duas vezes devolve a árvore original. Sobre uma árvore fechada isso vale por computação.

```lean
namespace Func

example : mirror (mirror t1) = t1 := rfl

end Func
```

* A lei geral `mirror (mirror t) = t`, para toda árvore, não é uma computação. Ela precisa de indução estrutural, com as chamadas recursivas de `mirror` fornecendo as hipóteses de indução, e é o primeiro exemplo resolvido da Aula 7.

# Resumo

* Um tipo indutivo é os seus construtores, e o núcleo deriva um recursor, `casesOn`, injetividade e disjunção.

* A recursão estrutural termina, e Lean admite apenas definições que terminam.

* `match` e `if` são casamento de padrões como expressão, e `Option` empacota um resultado parcial.

* Uma estrutura é um tipo indutivo de único construtor com campos nomeados, construída com `⟨…⟩` ou `{ … }` e estendida com `extends`.

* Uma classe de tipos é uma estrutura de operações resolvida por tipo, o mecanismo por trás do `∈` e do `ac_rfl` das aulas anteriores.

* O mesmo esquema constrói árvores, opções, somas e vetores dependentes.

* A Aula 7 deriva a indução estrutural do recursor e prova as leis enunciadas aqui.

Exercícios: veja as [notas de aula](../pt/Aula-6___-Programa______o-Funcional/).
