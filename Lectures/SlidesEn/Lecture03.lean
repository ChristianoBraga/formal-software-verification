/-
Slides for Lecture 3, generated from checked sources. Each
top-level section is one slide; the document title and the intro
paragraphs form the title slide. All Lean code is elaborated at
build time and is identical to the code in the lecture notes
(`Lectures/En/Lecture03.lean`) where the two overlap.

Only the ℕ and ℤ notations are imported from Mathlib. The full
library would bring its own `Set`, which clashes with the `Set`
of the Lecture 2 deck once both decks build together.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Programs and Theorems" =>

Inductive types, recursive functions, evaluation, and the statement of theorems in Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Open the lecture notes](../en/Lecture-3___-Programs-and-Theorems/)

Based on the [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), chapter 2.

# §3.1 From proofs to programs

* Lecture 1 read a proof as a *term whose type is the proposition* it proves. The same type theory classifies *data*.

* A type such as ℕ collects values, and a term of type ℕ → ℕ is a *program*. The `#check` below reads like the `#check` of a proof term, with types in place of propositions.

```lean (name := checkFun)
#check fun n : ℕ => n + 1
```
```leanOutput checkFun
fun n => n + 1 : ℕ → ℕ
```

* This lecture *defines* types and functions and *states* theorems about them. The proofs wait for structural induction, in the coming lectures.

# §3.2 Inductive types

* An `inductive` command defines a type by listing its *constructors*. The type contains exactly the values built by finitely many constructor applications, and nothing else.

::::cols
:::col
{lbl}[Natural numbers]

```lean
namespace MyNat

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

end MyNat
```
:::
:::col
{lbl}[Lists over any type]

```lean
namespace MyList

inductive List (α : Type) : Type where
  | nil  : List α
  | cons : α → List α → List α

end MyList
```
:::
::::

* Lean already provides `Nat` and `List`, so each reconstruction lives in a namespace.

# §3.2 Abstract syntax

* Constructors carry data of other types. `AExp` is the *abstract syntax* of arithmetic expressions, and the imperative language of the final lectures extends it.

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
{lbl}[The expression `(x + 3) * y`]

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

# §3.3 Functions by pattern matching

* A function on an inductive type is defined by *pattern matching*, one equation per constructor shape.

* Recursion is *structural* when each recursive call peels off one constructor. Lean accepts such definitions, since they terminate.

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

* Patterns are richer than bare constructors: `n + 2` abbreviates two applications of `succ`. An argument that no equation inspects moves to the *left of the colon*, as `m` does above.

# §3.4 Polymorphism and implicit arguments

* A definition can take a *type as an argument*, given explicitly at each call, or *implicitly* in curly braces and inferred by the elaborator. The `@` prefix restores the explicit form.

::::cols
:::col
{lbl}[Explicit type argument]

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
{lbl}[Implicit, with list notation]

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

* The notation writes `List.nil` as `[]` and `List.cons x xs` as `x :: xs`, so the definition reads like its own specification.

# §3.5 Evaluation

* `#eval` runs a program through the *compiler*; `#reduce` normalizes a term symbolically in the *kernel*. Use `#eval` at scale.

* An *environment* maps variable names to values, and `eval` folds an expression down to its value.

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

* Division by zero does not fail. Integer division is *total*, with x / 0 = 0. The command `#eval` and our function `eval` are unrelated, despite the names.

# §3.5 Computation as a proof method

* An equation whose two sides *evaluate to the same value* holds by `rfl`, the term Lecture 2 used for `n * n = 9` at the witness 3.

* This is *definitional computation*. It settles any *ground* equation, one without variables, and nothing more.

```lean
example : add 2 7 = 9 := rfl

example : eval (fun _ => 7)
    (AExp.div (AExp.var "y") (AExp.num 0)) = 0 := rfl
```

* In `add m n = add n m` the variables block computation, so the general law needs *structural induction*.

# §3.6 Theorem statements

* A `theorem` is a definition whose *type is a proposition*. Stating it requires no proof, and `sorry` stands where the proof will go.

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
{lbl}[Lean flags every use of sorry]

```lean (name := axiomsAddComm)
#print axioms SorryTheorems.add_comm
```
```leanOutput axiomsAddComm
'SorryTheorems.add_comm' depends on axioms: [sorryAx]
```
:::
::::

* `#print axioms` reports what a proof rests on. A proof by computation depends on *no axioms at all*.

# §3.6 Axioms

* An `opaque` constant has a *type and no definition*; an `axiom` asserts a proposition *with no proof at all*.

```lean
opaque a : ℤ
opaque b : ℤ

axiom a_less_b : a < b
```

* Nothing checks an axiom, so an inconsistent one *silently breaks the whole development*. The course states axioms only to discuss them.

# Worked example: truncated subtraction

Define `sub` on ℕ so that `sub 3 7 = 0`, since ℕ has no negative values.

::::cols
:::col
{lbl}[Choosing the equations]

* Recursion peels one `succ` from *each* argument, so the recursive case is `m + 1, n + 1`.

* Two base cases stop it. Subtracting zero returns the first argument, and subtracting from zero returns zero.

* The first matching equation wins, so `0, 0` falls to the first one.

```lean
def sub : ℕ → ℕ → ℕ
  | m,     0     => m
  | 0,     _     => 0
  | m + 1, n + 1 => sub m n
```
:::
:::col
{lbl}[Checking it]

```lean (name := evalSub)
#eval sub 7 3
```
```leanOutput evalSub
4
```

```lean (name := evalSubTrunc)
#eval sub 3 7
```
```leanOutput evalSubTrunc
0
```

* Each check is also a theorem, since both sides are *ground*.

```lean
example : sub 3 7 = 0 := rfl
```
:::
::::

# Worked example: evaluating `(x + 3) * y`

::::cols
:::col
{lbl}[Unfolding eval, one equation at a time]

```tree
eval env ((x + 3) * y)
  = eval env (x + 3) * eval env y
  = (eval env x + eval env 3) * env "y"
  = (env "x" + 3) * env "y"
  = (2 + 3) * 4
  = 20
```

* Each step is one equation of `eval`: the `mul` case, then `add`, then `var` and `num`.

* The environment supplies the two variables, and ℤ does the rest.
:::
:::col
{lbl}[The same computation in Lean]

```lean
def someEnv : String → ℤ
  | "x" => 2
  | "y" => 4
  | _   => 0
```

```lean (name := evalWorked)
#eval eval someEnv
  (AExp.mul (AExp.add (AExp.var "x") (AExp.num 3))
    (AExp.var "y"))
```
```leanOutput evalWorked
20
```

```lean
example : eval someEnv
    (AExp.mul (AExp.add (AExp.var "x") (AExp.num 3))
      (AExp.var "y")) = 20 := rfl
```
:::
::::

# Worked example: what computation settles

Three claims about `add`, which recurses on its *second* argument.

::::cols
:::col
{lbl}[Settled by rfl]

```lean
example : add 2 7 = 9 := rfl

example (m : ℕ) : add m 0 = m := rfl
```

* The first is *ground*, so both sides compute to 9.

* The second is general, yet `add m 0` matches the *first equation* of `add` whatever m is, and reduces to m in one step.
:::
:::col
{lbl}[Not settled by rfl]

```lean
namespace Worked

theorem zero_add (m : ℕ) : add 0 m = m := by
  sorry

end Worked
```

* Here the *second* argument is the variable, so no equation of `add` applies and the term is stuck.

* The claim is true, and proving it needs *structural induction on m*, in the next lecture.

* The pattern of the recursion, not the shape of the statement, decides which side computes.
:::
::::

# Worked example: from a definition to its statement

Append one element at the end of a list, then relate it to `reverse`.

::::cols
:::col
{lbl}[The definition]

```lean
def snoc {α : Type} : List α → α → List α
  | [],      y => [y]
  | x :: xs, y => x :: snoc xs y
```

```lean (name := evalSnoc)
#eval snoc [1, 2] 3
```
```leanOutput evalSnoc
[1, 2, 3]
```
:::
:::col
{lbl}[The statement it suggests]

```lean
namespace Worked

theorem reverse_cons {α : Type} (x : α) (xs : List α) :
    reverse (x :: xs) = snoc (reverse xs) x := by
  sorry

end Worked
```

* `reverse (x :: xs)` unfolds to `appendPretty (reverse xs) [x]`, and `snoc (reverse xs) x` is stuck on the variable list, so `rfl` fails.

* Stating a law is *free*; proving it is the work of the coming lectures. Writing the statement first is how a development grows.
:::
::::

# Summary

* Data and proofs share one type theory: a *program* is a term whose type is a function type.

* `inductive` defines a type by its *constructors*; values are exactly the finite constructor applications.

* Functions come from *pattern matching* with *structural recursion*, one equation per constructor shape.

* Type arguments are *explicit* `(α : Type)` or *implicit* `{α : Type}`, inferred by the elaborator and restored by `@`.

* `#eval` runs through the compiler, `#reduce` normalizes in the kernel, and `rfl` turns computation into a proof of any *ground* equation.

* A `theorem` states a proposition; `sorry` defers the proof and `#print axioms` exposes the deferral as `sorryAx`.

* General laws over variables need *structural induction*, the subject of the next lecture.

Exercises: see the [lecture notes](../en/Lecture-3___-Programs-and-Theorems/).
