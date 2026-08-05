import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Figure
import Lectures.Papers
import Lectures.LoVe.LoVelib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Aula 3: Programas e Teoremas" =>

%%%
tag := "aula-3"
%%%

Esta aula passa de provar a programar, seguindo o capítulo 2 do *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, edição de 2026, capítulo 2.] Ela apresenta tipos indutivos, definições de funções por casamento de padrões e recursão, avaliação e o enunciado de teoremas sobre programas, sem realizar prova alguma ainda.

# Das Provas aos Programas

A Aula 1 apresentou uma prova como um termo cujo tipo é a proposição que ela prova. A mesma teoria de tipos classifica dados. Um tipo como ℕ reúne valores, e um termo de tipo ℕ → ℕ é um programa que consome e produz valores. O `#check` abaixo se lê exatamente como o `#check` de um termo de prova, com tipos no lugar de proposições.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, em *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980, pp. 479–490.]

```lean (name := checkFun)
#check fun n : ℕ => n + 1
```
```leanOutput checkFun
fun n => n + 1 : ℕ → ℕ
```

Esta aula define tipos e funções e enuncia teoremas sobre eles. As provas desses teoremas esperam pelas próximas aulas, que desenvolvem a indução estrutural. Esta aula também importa a biblioteca LoVe e, por meio dela, [Mathlib](https://github.com/leanprover-community/mathlib4), a biblioteca matemática da comunidade Lean.{margin}[The mathlib Community, *The Lean Mathematical Library*, em *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, pp. 367–381.] Mathlib é um desenvolvimento monolítico único que formaliza álgebra, teoria da ordem, topologia, análise e as estruturas de dados usuais, e fornece as notações, os lemas e as táticas de que o restante destas aulas depende. As notações ℕ e ℤ para os números naturais e os inteiros vêm dela e são usadas daqui em diante.

# Tipos Indutivos

O comando `inductive` define um tipo novo listando os seus *construtores*. O tipo contém exatamente os valores construídos por finitas aplicações de construtores, e nada mais. A definição abaixo reconstrói os números naturais dentro de um espaço de nomes, já que o nome `Nat` pertence a Lean.

```savedLean
namespace MyNat

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

end MyNat
```

Os comandos `#check` e `#print` inspecionam o resultado. O construtor `succ` recebe um `Nat` e constrói o seguinte.

```lean (name := checkMyNat)
#check MyNat.Nat.succ
```
```leanOutput checkMyNat
MyNat.Nat.succ : MyNat.Nat → MyNat.Nat
```

```lean (name := printMyNat)
#print MyNat.Nat
```
```leanOutput printMyNat
inductive MyNat.Nat : Type
number of parameters: 0
constructors:
MyNat.Nat.zero : MyNat.Nat
MyNat.Nat.succ : MyNat.Nat → MyNat.Nat
```

Construtores podem carregar dados de outros tipos. O tipo abaixo representa expressões aritméticas com constantes inteiras, variáveis nomeadas por cadeias de caracteres e quatro operadores. Ele é a sintaxe abstrata de uma linguagem pequena, e a linguagem imperativa das últimas aulas o estende.

```savedLean
inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp
```

Por fim, as listas. Uma lista sobre α é vazia ou é um elemento seguido de uma lista. Como no caso de `Nat`, Lean já fornece `List`, então a reconstrução vive em um espaço de nomes.

```savedLean
namespace MyList

inductive List (α : Type) : Type where
  | nil  : List α
  | cons : α → List α → List α

end MyList
```

## Exemplos

Os exemplos abaixo constroem valores dos tipos indutivos desta seção e os inspecionam com `#check` e `#print`.

Exemplo 1. O numeral três são três aplicações de `succ` a `zero`.

```lean (name := exThree)
#check MyNat.Nat.succ
  (MyNat.Nat.succ (MyNat.Nat.succ MyNat.Nat.zero))
```
```leanOutput exThree
MyNat.Nat.zero.succ.succ.succ : MyNat.Nat
```

Exemplo 2. Uma enumeração é um tipo indutivo cujos construtores não carregam dados.

```lean (name := exAnswer)
inductive Answer : Type where
  | yes   : Answer
  | no    : Answer
  | maybe : Answer

#check Answer.maybe
```
```leanOutput exAnswer
Answer.maybe : Answer
```

Exemplo 3. A expressão `(x + 3) * y` é um valor de `AExp`. As aplicações de construtores espelham a forma da expressão.

```lean (name := exAExp)
#check AExp.mul
  (AExp.add (AExp.var "x") (AExp.num 3))
  (AExp.var "y")
```
```leanOutput exAExp
((AExp.var "x").add (AExp.num 3)).mul (AExp.var "y") : AExp
```

Exemplo 4. A lista que contém 3 e 7 são duas aplicações de `cons` terminadas em `nil`.

```lean (name := exList)
#check MyList.List.cons 3
  (MyList.List.cons 7 MyList.List.nil)
```
```leanOutput exList
MyList.List.cons 3 (MyList.List.cons 7 MyList.List.nil) : MyList.List ℕ
```

Exemplo 5. Um construtor pode receber vários argumentos. O tipo abaixo empacota dois inteiros.

```lean (name := exInterval)
inductive Interval : Type where
  | mk : ℤ → ℤ → Interval

#check Interval.mk 1 5
```
```leanOutput exInterval
Interval.mk 1 5 : Interval
```

Exemplo 6. `#print` lista os construtores de um tipo.

```lean (name := printList)
#print MyList.List
```
```leanOutput printList
inductive MyList.List : Type → Type
number of parameters: 1
constructors:
MyList.List.nil : {α : Type} → MyList.List α
MyList.List.cons : {α : Type} → α → MyList.List α → MyList.List α
```

Exemplo 7. Aplicações de construtores se aninham a qualquer profundidade. O valor abaixo é a expressão x / 0, um trecho de sintaxe legítimo cuja avaliação as próximas seções discutem.

```lean (name := exDiv)
#check AExp.div (AExp.var "x") (AExp.num 0)
```
```leanOutput exDiv
(AExp.var "x").div (AExp.num 0) : AExp
```

Exemplo 8. Os numerais do próprio Lean elaboram para o `Nat` do núcleo. A reconstrução e o original são tipos distintos.

```lean (name := exCoreNat)
#check (3 : ℕ)
```
```leanOutput exCoreNat
3 : ℕ
```

Exemplo 9. A lista vazia sobre ℤ exige uma anotação de tipo, já que `nil` sozinho não determina α.

```lean (name := exNil)
#check (MyList.List.nil : MyList.List ℤ)
```
```leanOutput exNil
MyList.List.nil : MyList.List ℤ
```

Exemplo 10. Os quatro pontos cardeais como uma enumeração, impressos.

```lean (name := exDirection)
inductive Direction : Type where
  | north : Direction
  | south : Direction
  | east  : Direction
  | west  : Direction

#print Direction
```
```leanOutput exDirection
inductive Direction : Type
number of parameters: 0
constructors:
Direction.north : Direction
Direction.south : Direction
Direction.east : Direction
Direction.west : Direction
```

# Funções por Casamento de Padrões e Recursão

Uma função sobre um tipo indutivo se define por *casamento de padrões*, uma equação por forma de construtor. A recursão é *estrutural* quando cada chamada recursiva descasca um construtor, e Lean aceita essas definições, já que elas terminam. As definições abaixo trabalham sobre o ℕ do núcleo, cujos construtores são `Nat.zero` e `Nat.succ`.

```lean
def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => 0
  | m, Nat.succ n => add m (mul m n)

def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)
```

Os padrões são mais ricos que construtores nus. A função de Fibonacci casa zero, um e todo número da forma n + 2, que abrevia duas aplicações de `succ`.

```lean
def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n
```

Um argumento que nenhuma equação inspeciona pode ir para a esquerda dos dois-pontos, onde se torna um parâmetro fixo ao longo da recursão.

```lean
def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)
```

## Exemplos

Os exemplos abaixo definem funções por casamento de padrões e recursão estrutural sobre ℕ e sobre `Bool`.

Exemplo 1. A metade descarta um de cada par, casando a forma n + 2.

```lean
def half : ℕ → ℕ
  | 0     => 0
  | 1     => 0
  | n + 2 => half n + 1
```

Exemplo 2. Uma definição não recursiva dispensa o casamento de padrões. O quadrado reaproveita `mul`.

```lean
def square (n : ℕ) : ℕ := mul n n
```

Exemplo 3. O teste de zero devolve um `Bool`, e as duas equações cobrem os dois construtores.

```lean
def isZero : ℕ → Bool
  | Nat.zero   => true
  | Nat.succ _ => false
```

Exemplo 4. O fatorial recursa sobre a forma n + 1, e a forma com parâmetro mantém a multiplicação explícita.

```lean
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => mul (n + 1) (factorial n)
```

Exemplo 5. Casamento de padrões em dois argumentos ao mesmo tempo. O menor de dois números desce em ambos.

```lean
def smaller : ℕ → ℕ → ℕ
  | _,     0     => 0
  | 0,     _     => 0
  | m + 1, n + 1 => smaller m n + 1
```

Exemplo 6. Os números de Lucas seguem a recursão de Fibonacci a partir de valores iniciais diferentes.

```lean
def lucas : ℕ → ℕ
  | 0     => 2
  | 1     => 1
  | n + 2 => lucas (n + 1) + lucas n
```

Exemplo 7. A conjunção sobre `Bool` casa apenas o seu primeiro argumento.

```lean
def conj : Bool → Bool → Bool
  | true,  b => b
  | false, _ => false
```

Exemplo 8. A paridade recursa de dois em dois, então a chamada recursiva descasca dois construtores.

```lean
def evenb : ℕ → Bool
  | 0     => true
  | 1     => false
  | n + 2 => evenb n
```

Exemplo 9. A soma dos n primeiros números recursa sobre n + 1.

```lean
def sumTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n
```

Exemplo 10. As potências de dois como uma instância da recursão de `power`, com a base fixa.

```lean
def twoPow : ℕ → ℕ
  | 0     => 1
  | n + 1 => mul 2 (twoPow n)
```

# Polimorfismo e Argumentos Implícitos

Uma definição pode receber um tipo como argumento. A função abaixo concatena duas listas sobre um tipo α qualquer, dado explicitamente em cada chamada, e o `_` de Lean pede ao elaborador que o infira. O elaborador é a etapa de Lean que transforma o texto que escrevemos em um termo da linguagem núcleo, e a inferência é parte do seu trabalho, junto com a resolução de instâncias de classes de tipos e a execução de táticas. A {figref "fig-lean-components"}[Figura 1.1] o situa entre os demais componentes. Escrever `_` afirma, portanto, que o argumento está determinado pelo resto da chamada, e o elaborador o recupera por unificação.

```lean
def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

#eval append ℕ [3, 1] [4, 1, 5]
```

As chaves tornam o argumento de tipo *implícito*, inferido a cada uso. O prefixo `@` restaura a forma explícita quando necessário.

```lean
def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]
#check @appendImplicit
```

A notação de listas de Lean escreve `List.nil` como `[]`, `List.cons x xs` como `x :: xs`, e cadeias de `cons` como `[x₁, x₂, x₃]`. Com ela, a definição se lê como a sua própria especificação.

```savedLean
def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys
```

A reversão segue a mesma forma, concatenando a cabeça na outra ponta.

```savedLean
def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => appendPretty (reverse xs) [x]
```

# Avaliação

O comando `#eval` executa um programa pelo compilador de Lean, e `#reduce` normaliza um termo simbolicamente no kernel. Ambos computam 9 abaixo, e `#eval` é o comando a usar em escala.

```lean (name := evalAdd)
#eval add 2 7
```
```leanOutput evalAdd
9
```

```lean (name := reduceAdd)
#reduce add 2 7
```
```leanOutput reduceAdd
9
```

A avaliação dá significado às expressões aritméticas de `AExp`. Um *ambiente* leva nomes de variáveis a valores inteiros, e `eval` reduz uma expressão ao seu valor.

```savedLean
def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂
```

A divisão por zero não falha. A divisão inteira de Lean é total, com x / 0 = 0, e a avaliação abaixo computa de acordo. O comando `#eval` e a nossa função `eval` não têm relação, apesar dos nomes.

```lean (name := evalDiv)
#eval eval (fun _ => 7)
  (AExp.div (AExp.var "y") (AExp.num 0))
```
```leanOutput evalDiv
0
```

A computação também é um método de prova. Uma equação cujos dois lados avaliam para o mesmo valor vale por `rfl`, o termo que a Aula 2 usou para `n * n = 9` na testemunha 3. Esta é a computação definicional, e ela resolve qualquer equação *fechada*, isto é, sem variáveis.

```lean
example : add 2 7 = 9 := rfl

example : eval (fun _ => 7)
    (AExp.div (AExp.var "y") (AExp.num 0)) = 0 := rfl
```

# Enunciados de Teoremas

Um `theorem` é uma definição cujo tipo é uma proposição. Enunciá-lo não exige prova; o marcador `sorry` fica onde a prova entrará, e Lean assinala cada uso dele. Os enunciados abaixo especificam as funções desta aula, e o espaço de nomes evita que seus nomes colidam com os de Mathlib.

```lean
namespace SorryTheorems

theorem add_comm (m n : ℕ) :
    add m n = add n m := by
  sorry

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  sorry

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m := by
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := by
  sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) := by
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs := by
  sorry

end SorryTheorems
```

A computação não os prova. `rfl` resolve `add 2 7 = add 7 2`, pois os dois lados computam para 9, mas em `add m n = add n m` as variáveis bloqueiam a computação, e a lei geral precisa de *indução estrutural*, o assunto das próximas aulas.

Os axiomas são a outra maneira de afirmar sem provar, e merecem mais desconfiança. Uma constante `opaque` tem tipo e nenhuma definição, e um `axiom` afirma uma proposição sem prova nenhuma. Nada o verifica, então um axioma inconsistente quebra silenciosamente todo o desenvolvimento. A disciplina enuncia axiomas apenas para discuti-los.

```lean
opaque a : ℤ
opaque b : ℤ

axiom a_less_b : a < b
```

# Exercícios

Defina cada função e prove ou enuncie cada teorema, substituindo `sorry`. Baixe o arquivo de exercícios [`Lecture03.lean`](example-code/Lectures/Pt/Lecture03.lean) e abra-o no VS Code. O arquivo já contém as definições de `AExp`, `eval`, `appendPretty` e `reverse` da aula.

```savedImport
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation
```

```savedComment
Exercícios da Aula 3: Programas e Teoremas.
Substitua cada `sorry` por uma definição, uma prova ou um
enunciado, conforme cada exercício pede. As definições
acima vêm da aula.
```

Exercício 1. Defina a função predecessor, com `pred 0 = 0`.

```savedLean -keep
def pred : ℕ → ℕ := sorry

-- Esperado: #eval pred 5 dá 4, #eval pred 0 dá 0.
```

Exercício 2. Defina a duplicação por recursão, sem `*`, e prove a equação fechada por computação.

```savedLean -keep
def double : ℕ → ℕ := sorry

theorem double_five : double 5 = 10 := sorry
```

Exercício 3. Defina o ambiente que leva "x" a 3, "y" a 17 e todo outro nome a 201, e prove as duas avaliações por computação.

```savedLean -keep
def someEnv : String → ℤ := sorry

theorem eval_sub :
    eval someEnv
      (AExp.sub (AExp.var "y") (AExp.var "x")) = 14 :=
  sorry

theorem eval_div_zero :
    eval someEnv
      (AExp.div (AExp.var "y") (AExp.num 0)) = 0 :=
  sorry
```

Exercício 4. Defina a subtração truncada por casamento de padrões nos dois argumentos, de modo que `sub 3 5 = 0`.

```savedLean -keep
def sub : ℕ → ℕ → ℕ := sorry
```

Exercício 5. Defina o comprimento de uma lista, com argumento de tipo implícito, e prove a equação fechada por computação.

```savedLean -keep
def length {α : Type} : List α → ℕ := sorry

theorem length_three : length [1, 2, 3] = 3 := sorry
```

Exercício 6. Defina `map`, que aplica uma função a cada elemento, e enuncie, com `sorry`, as suas duas leis funtoriais. Mapear a função identidade não muda nada, e mapear uma composição equivale a compor os mapeamentos.

```savedLean -keep
def map {α β : Type} (f : α → β) : List α → List β :=
  sorry

-- Enuncie as duas leis aqui como teoremas provados por
-- sorry:
-- map_ident : mapear (fun x => x) sobre xs dá xs.
-- map_comp  : map g (map f xs) é igual a mapear a
--             composição das duas sobre xs.
```

Exercício 7. Defina `snoc`, que acrescenta um elemento ao final de uma lista, e enuncie, com `sorry`, o teorema `reverse_cons`, que relaciona `reverse (x :: xs)` com `snoc (reverse xs) x`.

```savedLean -keep
def snoc {α : Type} : List α → α → List α := sorry

-- Enuncie reverse_cons aqui como um teorema provado por
-- sorry.
```

Exercício 8. Complete `simplify`, que remove as somas com 0, os produtos por 1 e as divisões por 1, seguindo os casos dados, e enuncie, com `sorry`, a sua correção. Simplificar preserva o valor sob todo ambiente.

```savedLean -keep
def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e₂ => simplify e₂
  | AExp.add e₁ (AExp.num 0) => simplify e₁
  | AExp.sub e₁ e₂           => sorry
  | AExp.mul e₁ e₂           => sorry
  | AExp.div e₁ e₂           => sorry
  | AExp.add e₁ e₂           =>
      AExp.add (simplify e₁) (simplify e₂)
  | e                        => e

-- Enuncie simplify_correct aqui como um teorema provado
-- por sorry: para todo env e todo e, eval env
-- (simplify e) é igual a eval env e.
```

Exercício 9. Defina o tamanho de uma expressão, contando cada construtor, e a sua profundidade, contando a maior cadeia de construtores, e enuncie, com `sorry`, que a profundidade nunca excede o tamanho.

```savedLean -keep
def size : AExp → ℕ := sorry

def depth : AExp → ℕ := sorry

theorem depth_le_size (e : AExp) :
    depth e ≤ size e := sorry
```

Exercício 10. Defina `mirror`, que troca os operandos de cada soma e de cada produto e deixa o resto inalterado, e enuncie, com `sorry`, que espelhar preserva o valor sob todo ambiente.

```savedLean -keep
def mirror : AExp → AExp := sorry

-- Enuncie mirror_eval aqui como um teorema provado por
-- sorry.
```
