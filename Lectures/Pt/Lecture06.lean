import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers
import Lectures.Pt.Lecture05

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Aula 6: Programação Funcional" =>

%%%
tag := "aula-6"
%%%

A Aula 3 introduziu os tipos indutivos por exemplo, reconstruindo ℕ e `List` e definindo funções sobre eles por casamento de padrões. Esta aula retoma esse material e apresenta o mecanismo geral, seguindo o capítulo 5 do *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, edição de 2026, capítulo 5.] Ela lê uma definição indutiva como uma lista de construtores e nomeia o que o núcleo deriva deles, define funções totais por recursão estrutural e explica por que Lean exige a terminação, empacota dados em estruturas e explica as classes de tipos, o mecanismo que a Aula 2 usou para `Membership` e a Aula 4 usou para a associatividade e a comutatividade que `ac_rfl` consulta.

O curso passa duas semanas neste capítulo. Esta aula é o lado dos programas, definindo dados e funções. A Aula 7 é o lado das provas, derivando o princípio de indução estrutural e provando as propriedades desses programas. Assim, esta aula enuncia as leis das suas funções e prova apenas aquelas que a computação ou uma única análise de casos resolve, e adia para a Aula 7 toda prova que precisa de indução, exatamente como a Aula 5 adiou a teoria geral da indução estrutural.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-6.pt.html).*

# Tipos Indutivos e Seus Princípios

Um tipo indutivo é definido listando os seus *construtores*. Todo valor do tipo é construído aplicando esses construtores, e cada valor é construído de uma única maneira. A Aula 3 usou isso para construir ℕ a partir de `Nat.zero` e `Nat.succ` e `List` a partir de `List.nil` e `List.cons`. Para um tipo de dados como ℕ, Lean gera dos construtores quatro princípios, e nomeá-los explica de onde vêm as ferramentas das aulas anteriores.

O *recursor* `T.rec` é o princípio primitivo do tipo. É a forma bruta da recursão estrutural e, lido sobre um motivo que devolve uma proposição, a forma bruta da indução estrutural. O seu tipo para ℕ mostra os dois casos que uma função sobre ℕ deve fornecer, um para `Nat.zero` e um para `Nat.succ`, e o segundo caso recebe o valor no predecessor, que é o resultado recursivo.

```lean (name := natRec)
#check @Nat.rec
#check @Nat.succ.injEq
```

```leanOutput natRec
@Nat.rec : {motive : ℕ → Sort u_1} → motive Nat.zero → ((n : ℕ) → motive n → motive n.succ) → (t : ℕ) → motive t
```

O princípio `casesOn` é o caso especial não recursivo do recursor, aquele em que a tática `cases` da Aula 1 se traduz. O casamento de padrões e o compilador de equações transformam a sintaxe de superfície da Aula 3 em aplicações do recursor. A definição abaixo computa com `Nat.rec` diretamente, e a mesma função por casamento de padrões é a que a Aula 3 teria escrito; as duas são iguais.

```lean
namespace Func

def usingRec (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => ih + 2) n

example : usingRec 3 = 6 := rfl

end Func
```

Os dois princípios restantes dizem respeito aos próprios construtores. Cada construtor é *injetivo*, então aplicações iguais de construtores têm argumentos iguais, e Lean gera a equação `Nat.succ.injEq` que registra isso. Construtores distintos são *disjuntos*, então nenhuma aplicação de `Nat.succ` é igual a `Nat.zero`. A injetividade e a disjunção valem para um tipo de dados como ℕ; para um tipo de provas, onde todas as provas de uma proposição são iguais, elas não valem. A segunda saída acima é a equação de injetividade, e os dois exemplos abaixo usam a injetividade e a disjunção.

```leanOutput natRec
Nat.succ.injEq : ∀ (u v : ℕ), (u.succ = v.succ) = (u = v)
```

```lean
namespace Func

example (m n : ℕ) (h : Nat.succ m = Nat.succ n) :
    m = n := by
  injection h

example (n : ℕ) : Nat.succ n ≠ 0 :=
  Nat.succ_ne_zero n

end Func
```

A tática `induction` da Aula 4 é o recursor lido sobre uma proposição, e a Aula 7 o deriva em geral e prova as leis que esta aula enuncia. Aqui o recursor é apenas nomeado, como a origem da recursão e da análise de casos já em uso.

Notas de margem. O Guia, capítulo 5. Avigad, de Moura, Kong, Ullrich, *Theorem Proving in Lean 4*, o capítulo sobre tipos indutivos. A referência da linguagem Lean sobre o comando `inductive`.

# Recursão Estrutural e Terminação

Uma função é definida por *recursão estrutural* quando cada chamada recursiva é sobre um argumento estruturalmente menor, um construtor mais perto de um caso base. Tal definição termina, e o compilador de equações a transforma em uma aplicação do recursor. O fatorial recorre sobre o predecessor, e Fibonacci tem dois casos base e recorre sobre os dois predecessores.

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

Lean admite como definições comuns apenas aquelas que consegue mostrar que terminam, e a razão é a consistência. Uma definição total expõe as suas equações de definição como teoremas utilizáveis e reduz durante a verificação de tipos, então uma equação recursiva como `loopy = loopy + 1`, se Lean a aceitasse, provaria `False` por si só. O bloco abaixo postula exatamente essa equação como axioma e deriva a contradição, para mostrar o que uma definição não terminante irrestrita concederia. Lean não gera tal axioma, e rejeita as definições que o produziriam, e é por isso que toda função acima termina. Uma computação que de fato entra em laço ainda pode ser escrita com `partial def`, mas Lean então mantém a função opaca e não expõe equação alguma, então nenhuma contradição segue.

```lean -keep
namespace Func

opaque loopy : ℕ
axiom loopy_eq : loopy = loopy + 1

theorem loopy_false : False := by
  have h := loopy_eq
  omega

end Func
```

Para uma recursão que termina por uma razão que Lean não enxerga estruturalmente, `termination_by` com `decreasing_by` fornece uma medida e a sua prova, o que o guia trata mais adiante; esta aula fica dentro da recursão estrutural.

## Exemplos

Os exemplos abaixo definem funções por recursão estrutural, variam o argumento recursivo e marcam as definições que Lean rejeita.

{ex "ex-recursion-factorial"}[] O fatorial e o seu valor em 4.

```lean (name := exFact)
namespace Func

#eval fact 4

end Func
```

```leanOutput exFact
24
```

{ex "ex-recursion-fibonacci"}[] Fibonacci precisa de dois casos base, então o seu caso do passo lê os dois valores precedentes.

```lean
namespace Func

example : fib 6 = 8 := rfl

end Func
```

{ex "ex-recursion-sum-to"}[] Uma soma dos números de `0` a `n`, recorrendo sobre o predecessor.

```lean
namespace Func

def sumTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

example : sumTo 5 = 15 := rfl

end Func
```

{ex "ex-recursion-accumulator"}[] A mesma soma com um argumento acumulador, carregando o total corrente para a frente.

```lean
namespace Func

def sumAcc : ℕ → ℕ → ℕ
  | 0,     acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

example : sumAcc 5 0 = 15 := rfl

end Func
```

{ex "ex-recursion-power-recall"}[] `power` da Aula 3 é uma recursão aninhada, o seu caso do passo chamando `mul` sobre o resultado recursivo.

```lean
example : power 2 3 = 8 := rfl
```

{ex "ex-recursion-first-argument"}[] Uma função pode recorrer sobre o seu primeiro argumento, ao contrário do `add` da Aula 3 que recorre sobre o segundo.

```lean
namespace Func

def countDown : ℕ → List ℕ
  | 0     => []
  | n + 1 => (n + 1) :: countDown n

example : countDown 3 = [3, 2, 1] := rfl

end Func
```

{ex "ex-recursion-mutual"}[] Duas funções podem recorrer uma através da outra, declaradas juntas com `mutual`.

```lean
namespace Func

mutual
  def evn : ℕ → Bool
    | 0     => true
    | n + 1 => od n
  def od : ℕ → Bool
    | 0     => false
    | n + 1 => evn n
end

example : evn 4 = true := rfl

end Func
```

{ex "ex-recursion-option-total"}[] Uma função total sobre `Option`, devolvendo um resultado para os dois construtores.

```lean
namespace Func

def orZeroList : Option (List ℕ) → List ℕ
  | none    => []
  | some xs => xs

example : orZeroList none = [] := rfl

end Func
```

{ex "ex-recursion-rejected"}[] Uma definição que Lean rejeita. A chamada recursiva é sobre a mesma lista, então nenhum argumento diminui, Lean não consegue ver que ela termina, e não aceita esta equação como uma definição total. O bloco é mostrado, mas não elaborado.

```
def loopForever {α : Type} : List α → List α
  | []      => []
  | x :: xs => loopForever (x :: xs)
```

{ex "ex-recursion-zero-base"}[] Um caso base em `0` e um passo em `n + 1` é a forma de toda recursão sobre ℕ, aqui duplicando por adição repetida.

```lean
namespace Func

def twice : ℕ → ℕ
  | 0     => 0
  | n + 1 => twice n + 2

example : twice 5 = 10 := rfl

end Func
```

# Casamento de Padrões como Expressão

A Aula 3 escreveu uma função como equações de nível superior, uma por forma de construtor. O mesmo poder está disponível como uma expressão `match` usável onde quer que um termo seja esperado, e como `if c then … else …` para uma condição decidível. Um `match` se traduz por meio do recursor do tipo, o seu `casesOn` da §6.1 nos casos mais simples, e `if` ramifica sobre uma instância `Decidable` da sua condição. Os padrões são tentados de cima para baixo, então um padrão anterior encobre um posterior, e o coringa `_` casa com qualquer coisa.

```lean
namespace Func

def classify (n : ℕ) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | _ => "many"

def pred? : ℕ → Option ℕ
  | 0     => none
  | n + 1 => some n

end Func
```

O tipo `Option` empacota um resultado parcial, `some x` para um valor e `none` para a sua ausência, então `pred?` é total embora o predecessor de `0` seja indefinido.

## Exemplos

Os exemplos abaixo usam `match` e `if` dentro de um corpo, sobre números, pares, listas e opções.

{ex "ex-match-classify"}[] Um `match` devolvendo uma classificação, o seu coringa capturando todos os casos restantes.

```lean
namespace Func

example : classify 7 = "many" := rfl

end Func
```

{ex "ex-match-if-decidable"}[] `if` testa uma condição decidível, aqui se um número é zero.

```lean
namespace Func

def isZero (n : ℕ) : Bool :=
  if n = 0 then true else false

example : isZero 0 = true := rfl

end Func
```

{ex "ex-match-nested-pair"}[] Um `match` sobre um par inspeciona as duas componentes de uma vez.

```lean
namespace Func

def bothZero (p : ℕ × ℕ) : Bool :=
  match p with
  | (0, 0) => true
  | _      => false

example : bothZero (0, 3) = false := rfl

end Func
```

{ex "ex-match-option-predecessor"}[] `pred?` devolve `none` em zero, então o resultado está sempre definido.

```lean
namespace Func

example : pred? 0 = none := rfl

end Func
```

{ex "ex-match-list-head"}[] Um `match` sobre uma lista devolve a cabeça como uma opção.

```lean
namespace Func

def firstOpt {α : Type} : List α → Option α
  | []     => none
  | x :: _ => some x

example : firstOpt [3, 1] = some 3 := rfl

end Func
```

{ex "ex-match-unpack-option"}[] Um `match` sobre uma opção desempacota `some` e fornece um padrão para `none`.

```lean
namespace Func

def orZero : Option ℕ → ℕ
  | none   => 0
  | some n => n

example : orZero (some 5) = 5 := rfl

end Func
```

{ex "ex-match-wildcard-order"}[] Os padrões são tentados de cima para baixo, então o caso específico precede o coringa.

```lean
namespace Func

def sign (n : ℤ) : String :=
  match n with
  | 0 => "zero"
  | _ => "nonzero"

example : sign 0 = "zero" := rfl

end Func
```

{ex "ex-match-inside-term"}[] Um `match` pode aparecer dentro de um termo maior, aqui dentro de uma adição.

```lean
namespace Func

def bump (o : Option ℕ) : ℕ :=
  1 + (match o with
       | none   => 0
       | some n => n)

example : bump (some 4) = 5 := rfl

end Func
```

{ex "ex-match-if-versus-match"}[] `if` e um `match` de dois ramos decidem a mesma condição.

```lean
namespace Func

def isZeroMatch (n : ℕ) : Bool :=
  match n with
  | 0 => true
  | _ => false

example : isZeroMatch 0 = isZero 0 := rfl

end Func
```

{ex "ex-match-guarded-default"}[] Uma divisão segura devolvendo `none` quando o divisor é zero.

```lean
namespace Func

def safeDiv (m n : ℕ) : Option ℕ :=
  if n = 0 then none else some (m / n)

example : safeDiv 6 0 = none := rfl

end Func
```

# Estruturas e Registros

Uma *estrutura* é um tipo indutivo com um único construtor e campos nomeados, e Lean deriva uma projeção para cada campo. É a forma natural para um registro de valores relacionados. O construtor anônimo `⟨…⟩`, a sintaxe de campos `{ … }` e a sintaxe de atualização `{ r with … }` constroem ou modificam uma estrutura, e `extends` constrói uma estrutura maior sobre uma menor. O `And.intro` da Aula 1 e o par da Aula 3 são eles próprios estruturas de um único construtor.

```lean
namespace Func

structure Segment where
  lo : ℤ
  hi : ℤ

def width (s : Segment) : ℤ := s.hi - s.lo

structure NamedSegment extends Segment where
  name : String

end Func
```

Um `NamedSegment` carrega os dois campos de `Segment` e mais um, e uma projeção alcança os campos herdados diretamente.

## Exemplos

Os exemplos abaixo constroem, projetam, atualizam e estendem registros.

{ex "ex-structure-project"}[] Uma projeção lê um campo, e `width` computa a partir de dois deles.

```lean
namespace Func

def seg1 : Segment := { lo := 1, hi := 5 }

example : width seg1 = 4 := by decide

end Func
```

{ex "ex-structure-field-syntax"}[] A sintaxe de campos `{ … }` e o construtor anônimo `⟨…⟩` constroem o mesmo valor.

```lean
namespace Func

def seg2 : Segment := ⟨1, 5⟩

example : seg1 = seg2 := rfl

end Func
```

{ex "ex-structure-update"}[] A sintaxe de atualização `{ r with … }` copia um registro e muda um campo.

```lean
namespace Func

def widen (s : Segment) : Segment :=
  { s with hi := s.hi + 1 }

example : (widen seg1).hi = 6 := by decide

end Func
```

{ex "ex-structure-extends-inherited"}[] `extends` acrescenta um campo, e os campos herdados permanecem acessíveis.

```lean
namespace Func

def ns1 : NamedSegment :=
  { lo := 0, hi := 2, name := "a" }

example : ns1.lo = 0 := by decide

end Func
```

{ex "ex-structure-inherited-name"}[] O novo campo é alcançado como qualquer outro.

```lean
namespace Func

example : ns1.name = "a" := rfl

end Func
```

{ex "ex-structure-field-function"}[] Um campo pode ser ele próprio uma função, e a projeção o recupera.

```lean
namespace Func

structure Handler where
  run : ℕ → ℕ

def dbl : Handler := { run := fun n => n + n }

example : dbl.run 3 = 6 := rfl

end Func
```

{ex "ex-structure-projection-rfl"}[] Construir um registro e projetar um campo devolve o campo, por computação.

```lean
namespace Func

example : (⟨1, 5⟩ : Segment).lo = 1 := rfl

end Func
```

{ex "ex-structure-derived-function"}[] Uma função de um registro computada a partir dos seus campos.

```lean
namespace Func

def midpoint (s : Segment) : ℤ :=
  (s.lo + s.hi) / 2

example : midpoint ⟨0, 4⟩ = 2 := by decide

end Func
```

{ex "ex-structure-prod-recall"}[] `Prod` é a estrutura canônica de dois campos, com `Prod.fst` e `Prod.snd` as suas projeções.

```lean
example : (Prod.fst (3, 5) : ℕ) = 3 := rfl
```

{ex "ex-structure-anonymous-and"}[] O `And.intro` da Aula 1 é uma estrutura de dois campos, e o construtor anônimo o constrói.

```lean
example (a b : Prop) (ha : a) (hb : b) : a ∧ b :=
  ⟨ha, hb⟩
```

# Classes de Tipos

Uma *classe de tipos* é uma estrutura de operações parametrizada por um ou mais argumentos, em geral tipos. Uma `class` declara as operações, uma `instance` as fornece para argumentos particulares, e a *resolução de instâncias* encontra a instância certa a partir desses argumentos sempre que uma função a pede com `[C α]`. Algumas classes são indexadas por mais do que um tipo, e `Std.Associative op` da Aula 4 é indexada por uma operação. É o mecanismo que a Aula 2 usou para dar ao `∈` o seu significado por meio de uma instância de `Membership` e a Aula 4 usou para registrar `add` como associativo e comutativo para `ac_rfl`.

```lean
namespace Func

class Size (α : Type) where
  size : α → ℕ

instance {α : Type} : Size (List α) where
  size xs := xs.length

instance {α : Type} : Size (Option α) where
  size
    | none   => 0
    | some _ => 1

def usize {α : Type} [Size α] (a : α) : ℕ :=
  Size.size a

end Func
```

A função `usize` não nomeia nenhuma instância. Ela pede `[Size α]`, e a resolução fornece a instância de lista ou a instância de opção conforme o tipo no ponto de chamada.

## Exemplos

Os exemplos abaixo declaram instâncias, observam a resolução escolher por tipo e nomeiam as classes que as aulas anteriores usaram.

{ex "ex-class-list-instance"}[] A instância de lista mede uma lista pelo seu comprimento.

```lean (name := exUsizeList)
namespace Func

#eval usize [1, 2, 3]

end Func
```

```leanOutput exUsizeList
3
```

{ex "ex-class-option-instance"}[] A instância de opção mede a presença, `1` ou `0`.

```lean (name := exUsizeOption)
namespace Func

#eval usize (some 7)

end Func
```

```leanOutput exUsizeOption
1
```

{ex "ex-class-product-instance"}[] Uma instância pode depender de outras instâncias, como um produto depende dos seus fatores.

```lean (name := exUsizeProd)
namespace Func

instance {α β : Type} [Size α] [Size β] :
    Size (α × β) where
  size p := Size.size p.1 + Size.size p.2

#eval usize ([1, 2], some 3)

end Func
```

```leanOutput exUsizeProd
3
```

{ex "ex-class-resolution-by-type"}[] A resolução escolhe a instância a partir do tipo apenas, o que `inferInstance` torna explícito.

```lean
namespace Func

#check (inferInstance : Size (List ℕ))

end Func
```

{ex "ex-class-default-field"}[] Uma classe pode dar a um campo um valor padrão, que uma instância pode deixar intocado ou substituir.

```lean (name := exGreet)
namespace Func

class Greet (α : Type) where
  label : String := "item"

instance : Greet Bool where

instance : Greet ℕ where
  label := "number"

#eval (Greet.label (α := Bool))
#eval (Greet.label (α := ℕ))

end Func
```

```leanOutput exGreet
"item"
```

```leanOutput exGreet
"number"
```

{ex "ex-class-membership-recall"}[] O `∈` da Aula 2 é o método da classe `Membership`, resolvido pelo tipo do contêiner.

```lean
#check @Membership.mem
```

{ex "ex-class-deriving"}[] Lean pode construir algumas instâncias automaticamente com `deriving`, aqui a igualdade e uma forma textual para um tipo finito.

```lean (name := exCoin)
namespace Func

inductive Coin where
  | heads
  | tails
  deriving Repr, DecidableEq

#eval Coin.heads

end Func
```

```leanOutput exCoin
Func.Coin.heads
```

{ex "ex-class-deriving-decide"}[] A igualdade derivada permite a `decide` resolver uma desigualdade concreta.

```lean
namespace Func

example : Coin.heads ≠ Coin.tails := by decide

end Func
```

{ex "ex-class-method-implicit"}[] Um método de classe carrega um argumento de instância implícito, que `#check` exibe.

```lean
namespace Func

#check @Size.size

end Func
```

{ex "ex-class-associativity-recall"}[] A associatividade e a comutatividade que `ac_rfl` consultou na Aula 4 são instâncias de `Std.Associative` e `Std.Commutative`.

```lean
#check @Std.Associative

#check @Std.Commutative
```

# Construindo Novos Tipos de Dados

O mesmo esquema constrói tipos mais ricos. Uma árvore binária é uma `leaf` ou uma `branch` carregando um valor e duas subárvores, e as funções sobre ela recorrem sobre as subárvores. A seção define `size`, `height` e `mirror` e enuncia as suas leis, provando apenas as instâncias fechadas por computação; as leis gerais são da Aula 7, pois precisam de indução.

```lean
namespace Func

inductive Tree (α : Type) where
  | leaf
  | branch (l : Tree α) (x : α) (r : Tree α)

def treeSize {α : Type} : Tree α → ℕ
  | .leaf         => 0
  | .branch l _ r => treeSize l + 1 + treeSize r

def height {α : Type} : Tree α → ℕ
  | .leaf         => 0
  | .branch l _ r => max (height l) (height r) + 1

def mirror {α : Type} : Tree α → Tree α
  | .leaf         => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

end Func
```

O recursor de `Tree` mostra o esquema geral sobre um tipo novo. Ele toma um valor para o caso `leaf` e, para o caso `branch`, uma função que recebe as duas subárvores, o valor armazenado e os resultados recursivos sobre as duas subárvores, que se tornam as hipóteses de indução de uma prova por indução.

```lean (name := treeRec)
namespace Func

#check @Tree.rec

end Func
```

```leanOutput treeRec
@Tree.rec : {α : Type} →
  {motive : Tree α → Sort u_1} →
    motive Tree.leaf →
      ((l : Tree α) → (x : α) → (r : Tree α) → motive l → motive r → motive (l.branch x r)) → (t : Tree α) → motive t
```

As leis gerais que esta seção enuncia e a Aula 7 prova são `mirror (mirror t) = t`, `treeSize (mirror t) = treeSize t` e a lei de contagem que relaciona as folhas e as ramificações de uma árvore. Cada uma precisa de indução, então esta seção prova apenas as suas instâncias fechadas.

## Exemplos

Os exemplos abaixo constroem uma árvore, computam com ela e leem os outros tipos de dados que o esquema produz.

{ex "ex-datatype-build-tree"}[] Uma árvore pequena com um valor na raiz e um na sua subárvore esquerda.

```lean
namespace Func

def t1 : Tree ℕ :=
  .branch (.branch .leaf 1 .leaf) 2 .leaf

end Func
```

{ex "ex-datatype-size"}[] `size` conta as ramificações, recorrendo sobre as duas subárvores.

```lean (name := exTreeSize)
namespace Func

#eval treeSize t1

end Func
```

```leanOutput exTreeSize
2
```

{ex "ex-datatype-height"}[] `height` toma a maior das duas alturas de subárvore e soma um.

```lean (name := exHeight)
namespace Func

#eval height t1

end Func
```

```leanOutput exHeight
2
```

{ex "ex-datatype-mirror"}[] `mirror` troca as duas subárvores em cada ramificação, e esta lei de construtor vale para toda árvore por computação, sem indução.

```lean
namespace Func

example {α : Type} (l : Tree α) (x : α) (r : Tree α) :
    mirror (.branch l x r)
      = .branch (mirror r) x (mirror l) := rfl

end Func
```

A lei do duplo espelhamento `mirror (mirror t) = t`, para toda árvore, é diferente, pois precisa de indução, e é um exemplo resolvido da Aula 7.

{ex "ex-datatype-mirror-leaf"}[] Espelhar uma folha nada muda.

```lean
namespace Func

example : mirror (Tree.leaf : Tree ℕ) = Tree.leaf := rfl

end Func
```

{ex "ex-datatype-size-mirror"}[] Espelhar preserva o tamanho, aqui na árvore fechada; a lei geral espera a Aula 7.

```lean
namespace Func

example : treeSize (mirror t1) = treeSize t1 := rfl

end Func
```

{ex "ex-datatype-sum"}[] Um tipo soma `α ⊕ β` guarda um valor de um lado ou do outro, e um `match` sobre `inl`/`inr` o consome.

```lean
namespace Func

def fromSum : ℕ ⊕ Bool → ℕ
  | .inl n => n
  | .inr b => if b then 1 else 0

example : fromSum (.inl 4) = 4 := rfl

end Func
```

{ex "ex-datatype-option-map"}[] `Option` é o tipo anulável canônico, e uma função pode mapear sobre o seu valor. A lei para `some` vale para toda função e argumento por computação, sem indução.

```lean
namespace Func

def mapOption {α β : Type} (f : α → β) :
    Option α → Option β
  | none   => none
  | some a => some (f a)

example {α β : Type} (f : α → β) (a : α) :
    mapOption f (some a) = some (f a) := rfl

end Func
```

{ex "ex-datatype-vec"}[] Um tipo indutivo dependente carrega informação no seu próprio tipo. Um `Vec α n` é uma lista de comprimento `n`, e os seus construtores registram o comprimento. Isto é uma prévia somente de leitura; as semanas seguintes desenvolvem os tipos dependentes.

```lean
namespace Func

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n → Vec α (n + 1)

end Func
```

{ex "ex-datatype-vec-head"}[] Como o tipo de `vhead` exige um vetor não vazio, o caso vazio não pode ocorrer, e a função é total sem uma opção.

```lean (name := exVhead)
namespace Func

def vhead {α : Type} {n : ℕ} : Vec α (n + 1) → α
  | .cons x _ => x

def v1 : Vec ℕ 2 := .cons 3 (.cons 4 .nil)

#eval vhead v1

end Func
```

```leanOutput exVhead
3
```

# Exemplos Resolvidos

Cada exemplo abaixo é conduzido por extenso e verbalizado. Eles são disjuntos dos exemplos das seções e dos exercícios, e Lean verifica cada linha quando as notas são compiladas.

## Expressões aritméticas e sua avaliação

Uma expressão aritmética é uma constante, uma variável, uma soma ou um produto, e isto é um tipo indutivo com quatro construtores, dois deles recursivos. Um avaliador toma um ambiente que dá um valor a cada variável e computa o valor de uma expressão por recursão sobre a sua estrutura.

```lean
namespace Func

inductive AExp where
  | const (i : ℤ)
  | var (x : String)
  | add (a b : AExp)
  | mul (a b : AExp)

def eval (env : String → ℤ) : AExp → ℤ
  | .const i => i
  | .var x   => env x
  | .add a b => eval env a + eval env b
  | .mul a b => eval env a * eval env b

end Func
```

A expressão abaixo lê `2 + x × 5`, e sob um ambiente que dá a `x` o valor `3` ela avalia para `17`.

```lean (name := exEval)
namespace Func

def sampleEnv : String → ℤ :=
  fun s => if s = "x" then 3 else 0

def e1 : AExp :=
  .add (.const 2) (.mul (.var "x") (.const 5))

#eval eval sampleEnv e1

end Func
```

```leanOutput exEval
17
```

A equação de definição para uma soma dá a lei `eval env (add a b) = eval env a + eval env b`, e ela vale por computação, já que a equação é exatamente o passo da recursão.

```lean
namespace Func

example (env : String → ℤ) (a b : AExp) :
    eval env (.add a b)
      = eval env a + eval env b := rfl

end Func
```

Essas expressões são a sintaxe de uma pequena linguagem, e o ambiente é o seu estado. A semântica operacional das semanas de lógica de Hoare se apoia exatamente nesta forma.

## Uma classe de tipos para tamanho

A classe `Size` da §6.5 se estende a árvores com mais uma instância, e uma função então mede uma lista inteira de valores dimensionáveis. A resolução fornece a instância de árvore para cada elemento e a estrutura da lista conduz a recursão.

```lean
namespace Func

instance {α : Type} : Size (Tree α) where
  size := treeSize

def totalSize {α : Type} [Size α] : List α → ℕ
  | []      => 0
  | x :: xs => Size.size x + totalSize xs

end Func
```

A lista abaixo guarda uma árvore e o seu espelho, cada uma de tamanho `2`, então o total é `4`.

```lean (name := exTotal)
namespace Func

#eval totalSize [t1, mirror t1]

end Func
```

```leanOutput exTotal
4
```

A função pede `[Size α]` uma vez, e a resolução encontra a instância de árvore porque os elementos são árvores. A instância de `Membership` da Aula 2 e a instância de associatividade da Aula 4 são o mesmo mecanismo visto às claras, uma operação atada a um tipo e encontrada pelo seu tipo.

## Um registro com uma extensão

Um registro reúne campos relacionados sob um nome, e `extends` constrói um registro especializado sobre um geral. Uma conta tem um titular e um saldo, e uma conta nomeada acrescenta um apelido mantendo os dois campos herdados.

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

example : acc.balance = 100 := by decide

end Func
```

Construir o registro com a sintaxe de campos e projetar um campo devolve esse campo, por computação. O único construtor de uma estrutura é a mesma ideia do `And.intro` da Aula 1, um construtor reunindo vários argumentos, com os campos nomeados em vez de posicionais.

## Espelhando uma árvore

O `mirror` da §6.6 troca as subárvores em cada ramificação, então espelhar duas vezes deve devolver a árvore original. Sobre uma árvore fechada isso vale por computação.

```lean
namespace Func

example : mirror (mirror t1) = t1 := rfl

end Func
```

A lei geral `mirror (mirror t) = t`, para toda árvore `t`, não é uma computação. Ela precisa de indução estrutural, com as chamadas recursivas de `mirror` fornecendo as hipóteses de indução para as duas subárvores, e é o primeiro exemplo resolvido da Aula 7. Isto fecha o ciclo com o `reverse_reverse` da Aula 5, que provou o análogo para listas por recursão, e prepara a indução que virá.

# Exercícios

Defina cada função e prove cada lei em Lean, substituindo `sorry`. Baixe o arquivo de exercícios [`Lecture06.lean`](example-code/Lectures/Pt/Lecture06.lean) e o abra no VS Code. Cada tipo é dado; a sua tarefa são as funções e as provas. As leis aqui se resolvem por `rfl` ou `decide` sobre valores fechados, já que as provas por indução pertencem à Aula 7. Os exercícios 9 e 10 são opcionais.

```savedImport
import Lectures.LoVe.LoVelib
```

```savedComment
Exercícios da Aula 6: Programação Funcional.
Cada tipo é dado. Defina as funções e prove as leis,
substituindo `sorry`. Toda lei aqui vale por `rfl` ou `decide`.
Os exercícios 9 e 10 são opcionais.
```

{exercise "exr-direction"}[] Defina `turnRight` sobre as quatro direções da bússola, e prove por `decide` que virar à direita quatro vezes devolve o norte.

```savedLean -keep
namespace FuncEx

inductive Direction where
  | north | east | south | west
  deriving DecidableEq

def turnRight : Direction → Direction :=
  sorry

theorem turn_four :
    turnRight (turnRight (turnRight
      (turnRight Direction.north))) = Direction.north :=
  sorry

end FuncEx
```

{exercise "exr-last-opt"}[] Defina `lastOpt`, o último elemento de uma lista como uma opção, e prove o seu valor sobre a lista vazia e sobre uma lista concreta.

```savedLean -keep
namespace FuncEx

def lastOpt {α : Type} : List α → Option α :=
  sorry

theorem last_opt_nil {α : Type} :
    lastOpt ([] : List α) = none :=
  sorry

theorem last_opt_example :
    lastOpt [3, 1, 4] = some 4 :=
  sorry

end FuncEx
```

{exercise "exr-rectangle"}[] Defina a área de um retângulo e prove uma área concreta.

```savedLean -keep
namespace FuncEx

structure Rectangle where
  width : ℕ
  height : ℕ

def area (r : Rectangle) : ℕ :=
  sorry

theorem area_example :
    area { width := 3, height := 4 } = 12 :=
  sorry

end FuncEx
```

{exercise "exr-box"}[] Estenda o retângulo a uma caixa com uma profundidade, e defina o seu volume a partir dos campos herdados.

```savedLean -keep
namespace FuncExBox

structure Rectangle where
  width : ℕ
  height : ℕ

structure Box extends Rectangle where
  depth : ℕ

def volume (b : Box) : ℕ :=
  sorry

theorem volume_example :
    volume { width := 2, height := 3, depth := 4 } = 24 :=
  sorry

end FuncExBox
```

{exercise "exr-doubler"}[] Complete as instâncias de `Doubler`, dobrando um número por adição e uma lista por autoconcatenação, e o seletor, depois prove o valor dobrado para ℕ.

```savedLean -keep
namespace FuncEx

class Doubler (α : Type) where
  dup : α → α

instance : Doubler ℕ :=
  sorry

instance {α : Type} : Doubler (List α) :=
  sorry

def applyDup {α : Type} [Doubler α] (a : α) : α :=
  sorry

theorem dup_nat : applyDup (3 : ℕ) = 6 :=
  sorry

end FuncEx
```

{exercise "exr-leaves-nodes"}[] Conte as folhas e as ramificações de uma árvore binária, e verifique a relação entre elas sobre uma árvore concreta.

```savedLean -keep
namespace FuncEx

inductive Tree (α : Type) where
  | leaf
  | branch (l : Tree α) (x : α) (r : Tree α)

def leaves {α : Type} : Tree α → ℕ :=
  sorry

def nodes {α : Type} : Tree α → ℕ :=
  sorry

def tx : Tree ℕ :=
  .branch (.branch .leaf 1 .leaf) 2 .leaf

theorem leaves_nodes : leaves tx = nodes tx + 1 :=
  sorry

end FuncEx
```

{exercise "exr-replicate"}[] Defina `replicate`, a lista de `n` cópias de um valor, e prove o seu valor em `0`.

```savedLean -keep
namespace FuncEx

def replicate {α : Type} : ℕ → α → List α :=
  sorry

theorem replicate_zero {α : Type} (x : α) :
    replicate 0 x = [] :=
  sorry

end FuncEx
```

{exercise "exr-is-empty"}[] Defina `isEmpty` por um `match`, e prove as suas duas leis computacionais.

```savedLean -keep
namespace FuncEx

def isEmpty {α : Type} : List α → Bool :=
  sorry

theorem is_empty_nil {α : Type} :
    isEmpty ([] : List α) = true :=
  sorry

theorem is_empty_cons {α : Type} (x : α)
    (xs : List α) : isEmpty (x :: xs) = false :=
  sorry

end FuncEx
```

{exercise "exr-rose"}[] Opcional. Uma árvore rosa ramifica em uma lista de subárvores. Defina `rsize`, o número dos seus nós, notando a recursão aninhada através de `List`.

```savedLean -keep
namespace FuncEx

inductive Rose (α : Type) where
  | node (x : α) (children : List (Rose α))

def rsize {α : Type} : Rose α → ℕ :=
  sorry

end FuncEx
```

{exercise "exr-vec-head"}[] Opcional. Um vetor indexado pelo comprimento exclui o caso vazio no seu tipo. Defina a cabeça total de um vetor não vazio e a avalie.

```savedLean -keep
namespace FuncEx

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n → Vec α (n + 1)

def vhead {α : Type} {n : ℕ} : Vec α (n + 1) → α :=
  sorry

def vx : Vec ℕ 2 := .cons 3 (.cons 4 .nil)

end FuncEx
```
