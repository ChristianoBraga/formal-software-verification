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

#doc (Manual) "Lecture 3: Programs and Theorems" =>

%%%
tag := "lecture-3"
%%%

This lecture moves from proving to programming, following chapter 2 of the *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 2.] It presents inductive types, function definitions by pattern matching and recursion, evaluation, and the statement of theorems about programs, without carrying out any proofs yet.

*This lecture is also available as [presentation slides](../slides/lecture-3.en.html).*

# From Proofs to Programs

Lecture 1 presented a proof as a term whose type is the proposition it proves. The same type theory classifies data. A type such as ℕ collects values, and a term of type ℕ → ℕ is a program that consumes and produces values. The `#check` below reads exactly like the `#check` of a proof term, with types in place of propositions.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980, pp. 479–490.]

```lean (name := checkFun)
#check fun n : ℕ => n + 1
```
```leanOutput checkFun
fun n => n + 1 : ℕ → ℕ
```

This lecture defines types and functions and states theorems about them. The proofs of those theorems wait for the coming lectures, which develop structural induction. This lecture also imports the LoVe library, and through it [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical library of the Lean community.{margin}[The mathlib Community, *The Lean Mathematical Library*, in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, pp. 367–381.] Mathlib is a single monolithic development that formalises algebra, order theory, topology, analysis and the standard data structures, and supplies the notations, lemmas and tactics that the rest of these lectures rely on. The notations ℕ and ℤ for the natural numbers and the integers come from it and are used from here on.

# Inductive Types

An `inductive` command defines a new type by listing its *constructors*. The type contains exactly the values built by finitely many constructor applications, and nothing else. The definition below reconstructs the natural numbers inside a namespace, since the name `Nat` already belongs to Lean.

```savedLean
namespace MyNat

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

end MyNat
```

The commands `#check` and `#print` inspect the result. The constructor `succ` takes a `Nat` and builds the next one.

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

Constructors can carry data of other types. The type below represents arithmetic expressions with integer constants, variables named by strings, and four operators. It is the abstract syntax of a small language, and the imperative language of the final lectures extends it.

```savedLean
inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp
```

Finally, lists. A list over α is either empty or an element followed by a list. As with `Nat`, Lean already provides `List`, so the reconstruction lives in a namespace.

```savedLean
namespace MyList

inductive List (α : Type) : Type where
  | nil  : List α
  | cons : α → List α → List α

end MyList
```

## Examples

The examples below build values of the inductive types of this section and inspect them with `#check` and `#print`.

Example 1. The numeral three is three applications of `succ` to `zero`.

```lean (name := exThree)
#check MyNat.Nat.succ
  (MyNat.Nat.succ (MyNat.Nat.succ MyNat.Nat.zero))
```
```leanOutput exThree
MyNat.Nat.zero.succ.succ.succ : MyNat.Nat
```

Example 2. An enumeration is an inductive type whose constructors carry no data.

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

Example 3. The expression `(x + 3) * y` is a value of `AExp`. The constructor applications mirror the shape of the expression.

```lean (name := exAExp)
#check AExp.mul
  (AExp.add (AExp.var "x") (AExp.num 3))
  (AExp.var "y")
```
```leanOutput exAExp
((AExp.var "x").add (AExp.num 3)).mul (AExp.var "y") : AExp
```

Example 4. The list containing 3 and 7 is two applications of `cons` ending in `nil`.

```lean (name := exList)
#check MyList.List.cons 3
  (MyList.List.cons 7 MyList.List.nil)
```
```leanOutput exList
MyList.List.cons 3 (MyList.List.cons 7 MyList.List.nil) : MyList.List ℕ
```

Example 5. A constructor can take several arguments. The type below packs two integers.

```lean (name := exInterval)
inductive Interval : Type where
  | mk : ℤ → ℤ → Interval

#check Interval.mk 1 5
```
```leanOutput exInterval
Interval.mk 1 5 : Interval
```

Example 6. `#print` lists the constructors of a type.

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

Example 7. Constructor applications nest to any depth. The value below is the expression x / 0, a legal piece of syntax whose evaluation the next sections discuss.

```lean (name := exDiv)
#check AExp.div (AExp.var "x") (AExp.num 0)
```
```leanOutput exDiv
(AExp.var "x").div (AExp.num 0) : AExp
```

Example 8. Lean's own numerals elaborate to the core `Nat`. The reconstruction and the original are distinct types.

```lean (name := exCoreNat)
#check (3 : ℕ)
```
```leanOutput exCoreNat
3 : ℕ
```

Example 9. The empty list over ℤ requires a type annotation, since `nil` alone does not determine α.

```lean (name := exNil)
#check (MyList.List.nil : MyList.List ℤ)
```
```leanOutput exNil
MyList.List.nil : MyList.List ℤ
```

Example 10. The four cardinal directions as an enumeration, printed.

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

# Functions by Pattern Matching and Recursion

A function on an inductive type is defined by *pattern matching*, one equation per constructor shape. Recursion is *structural* when each recursive call peels off one constructor, and Lean accepts such definitions, since they terminate. The definitions below work on the core ℕ, whose constructors are `Nat.zero` and `Nat.succ`.

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

Patterns are richer than bare constructors. The Fibonacci function matches zero, one, and every number of the shape n + 2, which abbreviates two applications of `succ`.

```lean
def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n
```

An argument that no equation inspects can move to the left of the colon, where it becomes a parameter fixed across the recursion.

```lean
def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)
```

## Examples

The examples below define functions by pattern matching and structural recursion on ℕ and on `Bool`.

Example 1. Halving discards one from every pair, matching the shape n + 2.

```lean
def half : ℕ → ℕ
  | 0     => 0
  | 1     => 0
  | n + 2 => half n + 1
```

Example 2. A non-recursive definition needs no pattern matching. Squaring reuses `mul`.

```lean
def square (n : ℕ) : ℕ := mul n n
```

Example 3. Testing for zero returns a `Bool`, and the two equations cover the two constructors.

```lean
def isZero : ℕ → Bool
  | Nat.zero   => true
  | Nat.succ _ => false
```

Example 4. The factorial recurses on the shape n + 1, and the parameter form keeps the multiplication explicit.

```lean
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => mul (n + 1) (factorial n)
```

Example 5. Pattern matching on two arguments at once. The smaller of two numbers descends on both.

```lean
def smaller : ℕ → ℕ → ℕ
  | _,     0     => 0
  | 0,     _     => 0
  | m + 1, n + 1 => smaller m n + 1
```

Example 6. The Lucas numbers follow the Fibonacci recursion from different initial values.

```lean
def lucas : ℕ → ℕ
  | 0     => 2
  | 1     => 1
  | n + 2 => lucas (n + 1) + lucas n
```

Example 7. Conjunction on `Bool` matches only its first argument.

```lean
def conj : Bool → Bool → Bool
  | true,  b => b
  | false, _ => false
```

Example 8. Evenness recurses by two, so the recursive call peels two constructors.

```lean
def evenb : ℕ → Bool
  | 0     => true
  | 1     => false
  | n + 2 => evenb n
```

Example 9. The sum of the first n numbers recurses on n + 1.

```lean
def sumTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n
```

Example 10. Powers of two as an instance of the recursion of `power`, with the base fixed.

```lean
def twoPow : ℕ → ℕ
  | 0     => 1
  | n + 1 => mul 2 (twoPow n)
```

# Polymorphism and Implicit Arguments

A definition can take a type as an argument. The function below appends two lists over any type α, given explicitly at each call, and Lean's `_` asks the elaborator to infer it. The elaborator is the stage of Lean that turns the text we write into a term of the core language, and inference is part of its work, together with the resolution of type class instances and the execution of tactics. {figref "fig-lean-components"}[Figure 1.1] places it among the other components. Writing `_` therefore states that the argument is determined by the rest of the call, and the elaborator recovers it by unification.

```lean
def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

#eval append ℕ [3, 1] [4, 1, 5]
```

Curly braces make the type argument *implicit*, inferred at every use. The `@` prefix restores the explicit form when needed.

```lean
def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]
#check @appendImplicit
```

Lean's list notation writes `List.nil` as `[]`, `List.cons x xs` as `x :: xs`, and chains of `cons` as `[x₁, x₂, x₃]`. With it, the definition reads like its own specification.

```savedLean
def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys
```

Reversal follows the same shape, appending the head at the far end.

```savedLean
def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => appendPretty (reverse xs) [x]
```

## Examples

The examples below compare explicit and implicit type arguments and define polymorphic functions over lists and pairs.

Example 1. With an explicit type argument, the type appears in the signature as an ordinary argument.

```lean (name := checkAppendPoly)
#check @append
```
```leanOutput checkAppendPoly
append : (α : Type) → List α → List α → List α
```

Example 2. Curly braces mark the argument as implicit, and `@` displays it.

```lean (name := checkAppendPretty)
#check @appendPretty
```
```leanOutput checkAppendPretty
@appendPretty : {α : Type} → List α → List α → List α
```

Example 3. At a call, the implicit argument comes from the type of the lists.

```lean (name := evalAppendNat)
#eval appendPretty [1, 2] [3]
```
```leanOutput evalAppendNat
[1, 2, 3]
```

Example 4. The same definition serves another type without change.

```lean (name := evalAppendStr)
#eval appendImplicit ["a"] ["b"]
```
```leanOutput evalAppendStr
["a", "b"]
```

Example 5. The `@` prefix restores the explicit form, useful when inference has nothing to work with.

```lean (name := evalAppendAt)
#eval @appendImplicit ℕ [1] [2]
```
```leanOutput evalAppendAt
[1, 2]
```

Example 6. The identity function is polymorphic and returns its argument unchanged.

```lean (name := checkIdPoly)
def idPoly {α : Type} (x : α) : α := x

#check @idPoly
```
```leanOutput checkIdPoly
@idPoly : {α : Type} → α → α
```

Example 7. Building a one-element list works at every type.

```lean (name := evalSingleton)
def singletonList {α : Type} (x : α) : List α := [x]

#eval singletonList 5
```
```leanOutput evalSingleton
[5]
```

Example 8. A definition can take two type arguments. Swapping the components of a pair exchanges them.

```lean (name := evalSwap)
def swapPair {α β : Type} : α × β → β × α
  | (x, y) => (y, x)

#eval swapPair (1, "x")
```
```leanOutput evalSwap
("x", 1)
```

Example 9. The length of a list ignores the elements, so the type argument never appears in the result.

```lean (name := evalLengthPoly)
def lengthPoly {α : Type} : List α → ℕ
  | []      => 0
  | _ :: xs => lengthPoly xs + 1

#eval lengthPoly ["a", "b", "c"]
```
```leanOutput evalLengthPoly
3
```

Example 10. An empty list carries no element to infer from, and a type ascription fixes the implicit argument.

```lean (name := checkNilAscribed)
#check ([] : List ℕ)
```
```leanOutput checkNilAscribed
[] : List ℕ
```

# Evaluation

The command `#eval` runs a program through Lean's compiler, and `#reduce` normalizes a term symbolically in the kernel. Both compute 9 below, and `#eval` is the one to reach for at scale.

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

Evaluation gives the arithmetic expressions of `AExp` their meaning. An *environment* maps variable names to integer values, and `eval` folds an expression down to its value.

```savedLean
def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂
```

Division by zero does not fail. Lean's integer division is total, with x / 0 = 0, and the evaluation below computes accordingly. The command `#eval` and our function `eval` are unrelated, despite the names.

```lean (name := evalDiv)
#eval eval (fun _ => 7)
  (AExp.div (AExp.var "y") (AExp.num 0))
```
```leanOutput evalDiv
0
```

Computation is also a proof method. An equation whose two sides evaluate to the same value holds by `rfl`, the term that Lecture 2 used for `n * n = 9` at the witness 3. This is definitional computation, and it settles any *ground* equation, one without variables.

```lean
example : add 2 7 = 9 := rfl

example : eval (fun _ => 7)
    (AExp.div (AExp.var "y") (AExp.num 0)) = 0 := rfl
```

## Examples

The examples below run the functions of this lecture and inspect the arithmetic that `eval` inherits from ℤ.

Example 1. The tenth Fibonacci number, computed by the compiler.

```lean (name := evalFib)
#eval fib 10
```
```leanOutput evalFib
55
```

Example 2. The factorial of five, through the recursion of `mul` and `add`.

```lean (name := evalFactorial)
#eval factorial 5
```
```leanOutput evalFactorial
120
```

Example 3. Two to the tenth, through the recursion of `power`.

```lean (name := evalPower)
#eval power 2 10
```
```leanOutput evalPower
1024
```

Example 4. `#reduce` normalizes in the kernel and reaches the same value.

```lean (name := reduceHalf)
#reduce half 7
```
```leanOutput reduceHalf
3
```

Example 5. A function into `Bool` evaluates to a Boolean value.

```lean (name := evalEvenb)
#eval evenb 10
```
```leanOutput evalEvenb
true
```

Example 6. Evaluation runs polymorphic functions as well.

```lean (name := evalReverse)
#eval reverse [1, 2, 3]
```
```leanOutput evalReverse
[3, 2, 1]
```

Example 7. The environment supplies the value of each variable, and the rest is arithmetic.

```lean (name := evalEnvX)
#eval eval (fun x => if x = "x" then 3 else 0)
  (AExp.add (AExp.var "x") (AExp.num 4))
```
```leanOutput evalEnvX
7
```

Example 8. Integer division truncates, so 5 / 2 evaluates to 2.

```lean (name := evalDivTrunc)
#eval eval (fun _ => 0)
  (AExp.div (AExp.num 5) (AExp.num 2))
```
```leanOutput evalDivTrunc
2
```

Example 9. Division on ℤ follows the Euclidean convention, whose remainder is never negative, so −7 / 2 evaluates to −4 rather than −3.

```lean (name := evalDivNeg)
#eval eval (fun _ => 0)
  (AExp.div (AExp.num (-7)) (AExp.num 2))
```
```leanOutput evalDivNeg
-4
```

Example 10. Every evaluation above also serves as a proof, since `rfl` closes an equation whose sides compute to the same value.

```lean
example : sumTo 10 = 55 := rfl

example : twoPow 8 = 256 := rfl
```

# Theorem Statements

A `theorem` is a definition whose type is a proposition. Stating it requires no proof; the placeholder `sorry` stands where the proof will go, and Lean flags every use of it. The statements below specify the functions of this lecture, and the namespace keeps their names from clashing with Mathlib's.

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

Computation cannot prove them. `rfl` settles `add 2 7 = add 7 2`, since both sides compute to 9, but in `add m n = add n m` the variables block computation, and the general law needs *structural induction*, the subject of the coming lectures.

Axioms are the other way to assert without proving, and they deserve more suspicion. An `opaque` constant has a type and no definition, and an `axiom` asserts a proposition with no proof at all. Nothing checks it, so an inconsistent axiom silently breaks the whole development. The course states axioms only to discuss them.

```lean
opaque a : ℤ
opaque b : ℤ

axiom a_less_b : a < b
```

## Examples

The examples below read the statements back, separate what computation settles from what it does not, and track which axioms a proof rests on. The namespace `MoreTheorems` keeps the new names clear of Mathlib.

Example 1. A statement with named binders is a universally quantified proposition.

```lean (name := checkAddComm)
#check @SorryTheorems.add_comm
```
```leanOutput checkAddComm
SorryTheorems.add_comm : ∀ (m n : ℕ), add m n = add n m
```

Example 2. An implicit binder appears in braces, and the statement quantifies over the type as well.

```lean (name := checkRevRev)
#check @SorryTheorems.reverse_reverse
```
```leanOutput checkRevRev
@SorryTheorems.reverse_reverse : ∀ {α : Type} (xs : List α), reverse (reverse xs) = xs
```

Example 3. The command `#print axioms` reports what a proof rests on, and `sorry` leaves the trace `sorryAx`.

```lean (name := axiomsAddComm)
#print axioms SorryTheorems.add_comm
```
```leanOutput axiomsAddComm
'SorryTheorems.add_comm' depends on axioms: [sorryAx]
```

Example 4. A law that computation settles needs no induction. Zero on the right matches the first equation of `add`, so `rfl` proves it for every n.

```lean (name := axiomsAddZero)
namespace MoreTheorems

theorem add_zero_right (n : ℕ) : add n 0 = n := rfl

end MoreTheorems

#print axioms MoreTheorems.add_zero_right
```
```leanOutput axiomsAddZero
'MoreTheorems.add_zero_right' does not depend on any axioms
```

Example 5. The same holds for the first equation of `eval`, whatever the environment.

```lean (name := checkEvalNum)
namespace MoreTheorems

theorem eval_num (env : String → ℤ) (i : ℤ) :
    eval env (AExp.num i) = i := rfl

end MoreTheorems

#check @MoreTheorems.eval_num
```
```leanOutput checkEvalNum
MoreTheorems.eval_num : ∀ (env : String → ℤ) (i : ℤ), eval env (AExp.num i) = i
```

Example 6. A ground equation deserves a name as much as a general law does.

```lean
namespace MoreTheorems

theorem fib_seven : fib 7 = 13 := rfl

theorem reverse_nil : reverse ([] : List ℕ) = [] := rfl

end MoreTheorems
```

Example 7. Binders to the left of the colon and an explicit ∀ state the same proposition.

```lean (name := checkAllAddZero)
namespace MoreTheorems

theorem all_add_zero : ∀ n : ℕ, add n 0 = n :=
  fun _ => rfl

end MoreTheorems

#check @MoreTheorems.all_add_zero
```
```leanOutput checkAllAddZero
MoreTheorems.all_add_zero : ∀ (n : ℕ), add n 0 = n
```

Example 8. Applying a stated theorem to arguments instantiates the statement, whether or not a proof exists yet.

```lean (name := checkAddCommInst)
#check SorryTheorems.add_comm 2 3
```
```leanOutput checkAddCommInst
SorryTheorems.add_comm 2 3 : add 2 3 = add 3 2
```

Example 9. Whatever a proof uses, `#print axioms` shows. The proof below rests on the axiom of this section, and on `propext`, which Mathlib's lemma uses.

```lean (name := axiomsANeB)
namespace MoreTheorems

theorem a_ne_b : a ≠ b := ne_of_lt a_less_b

end MoreTheorems

#print axioms MoreTheorems.a_ne_b
```
```leanOutput axiomsANeB
'MoreTheorems.a_ne_b' depends on axioms: [a_less_b, propext]
```

Example 10. Variables block computation, so the law below waits for structural induction and carries `sorryAx` in the meantime.

```lean (name := axiomsHalfDouble)
namespace MoreTheorems

theorem half_double (n : ℕ) : half (add n n) = n := by
  sorry

end MoreTheorems

#print axioms MoreTheorems.half_double
```
```leanOutput axiomsHalfDouble
'MoreTheorems.half_double' depends on axioms: [sorryAx]
```

# Worked Examples

Each example below is carried out in full, from the choice of the equations to the checks that follow. They are disjoint from the exercises, and Lean checks every line when the notes are built.

## Truncated subtraction

Subtraction on ℕ has no negative results, so `sub 3 7` must be 0. The recursion peels one `succ` from each argument at once, which makes `m + 1, n + 1` the recursive equation. Two base cases stop it. Subtracting zero returns the first argument, and subtracting from zero returns zero. The equations are tried in order, so the pair `0, 0` falls to the first one and never reaches the second.

```lean
def sub : ℕ → ℕ → ℕ
  | m,     0     => m
  | 0,     _     => 0
  | m + 1, n + 1 => sub m n
```

The first check runs the recursive equation three times, and the second exhausts the first argument before the second.

```lean (name := evalSubWorked)
#eval sub 7 3
```
```leanOutput evalSubWorked
4
```

```lean (name := evalSubTruncWorked)
#eval sub 3 7
```
```leanOutput evalSubTruncWorked
0
```

Both checks are ground equations, so each is also a theorem that `rfl` proves.

```lean
example : sub 3 7 = 0 := rfl
```

## Evaluating an expression step by step

Take the expression `(x + 3) * y` of §3.2 and an environment that sends "x" to 2 and "y" to 4. Each step below applies one equation of `eval`, first the `mul` case, then the `add` case, then the `var` and `num` cases, and the arithmetic of ℤ finishes the computation.

```
eval env ((x + 3) * y)
  = eval env (x + 3) * eval env y
  = (eval env x + eval env 3) * env "y"
  = (env "x" + 3) * env "y"
  = (2 + 3) * 4
  = 20
```

The environment is a function from names to integers, and pattern matching on strings defines it.

```lean
def workedEnv : String → ℤ
  | "x" => 2
  | "y" => 4
  | _   => 0
```

Lean performs the same computation.

```lean (name := evalWorkedNotes)
#eval eval workedEnv
  (AExp.mul (AExp.add (AExp.var "x") (AExp.num 3))
    (AExp.var "y"))
```
```leanOutput evalWorkedNotes
20
```

The expression contains no variables of Lean, only variable *names* that the environment resolves, so the equation is ground and `rfl` proves it.

```lean
example : eval workedEnv
    (AExp.mul (AExp.add (AExp.var "x") (AExp.num 3))
      (AExp.var "y")) = 20 := rfl
```

## What computation settles

The function `add` recurses on its second argument. That single fact decides which equations `rfl` proves. The first equation below is ground, so both sides compute to 9. The second is general, yet `add m 0` matches the first equation of `add` whatever m is, and reduces to m in one step.

```lean
example : add 2 7 = 9 := rfl

example (m : ℕ) : add m 0 = m := rfl
```

Exchanging the arguments changes everything. In `add 0 m` the variable sits where the recursion looks, no equation applies, and the term is stuck. The claim is true and `rfl` cannot prove it.

```lean
namespace Worked

theorem zero_add (m : ℕ) : add 0 m = m := by
  sorry

end Worked
```

The proof needs structural induction on m, the subject of a coming lecture. The lesson generalises. What computation settles depends on the pattern of the recursion, not on the shape of the statement.

## From a definition to its statement

A definition usually suggests the laws it should satisfy. Appending one element at the end of a list is the mirror image of `cons`, so it recurses on the list and rebuilds it around the recursive call.

```lean
def snoc {α : Type} : List α → α → List α
  | [],      y => [y]
  | x :: xs, y => x :: snoc xs y
```

```lean (name := evalSnocWorked)
#eval snoc [1, 2] 3
```
```leanOutput evalSnocWorked
[1, 2, 3]
```

Reversal and `snoc` should agree: reversing `x :: xs` puts x at the end of the reversal of xs. Stating the law costs nothing, and the statement is what a coming lecture proves.

```lean
namespace Worked

theorem reverse_cons {α : Type} (x : α) (xs : List α) :
    reverse (x :: xs) = snoc (reverse xs) x := by
  sorry

end Worked
```

Computation does not settle it. The left side unfolds to `appendPretty (reverse xs) [x]`, the right side is stuck on the variable list, and the two meet only under induction. Writing the statement first, and proving it later, is how a development grows.

# Exercises

Define each function and prove or state each theorem, replacing `sorry`. Download the exercise file [`Lecture03.lean`](example-code/Lectures/En/Lecture03.lean) and open it in VS Code. The file already contains the definitions of `AExp`, `eval`, `appendPretty`, and `reverse` from the lecture.

```savedImport
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation
```

```savedComment
Exercises for Lecture 3: Programs and Theorems.
Replace each `sorry` with a definition, a proof, or a
statement, as each exercise asks. The definitions above
come from the lecture.
```

Exercise 1. Define the predecessor function, with `pred 0 = 0`.

```savedLean -keep
def pred : ℕ → ℕ := sorry

-- Expected: #eval pred 5 gives 4, #eval pred 0 gives 0.
```

Exercise 2. Define doubling by recursion, without `*`, and prove the ground equation by computation.

```savedLean -keep
def double : ℕ → ℕ := sorry

theorem double_five : double 5 = 10 := sorry
```

Exercise 3. Define the environment that maps "x" to 3, "y" to 17, and every other name to 201, and prove the two evaluations by computation.

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

Exercise 4. Define the sum of a list of natural numbers, and prove the ground equation by computation.

```savedLean -keep
def sumList : List ℕ → ℕ := sorry

theorem sumList_example : sumList [1, 2, 3] = 6 := sorry
```

Exercise 5. Define the length of a list, with an implicit type argument, and prove the ground equation by computation.

```savedLean -keep
def length {α : Type} : List α → ℕ := sorry

theorem length_three : length [1, 2, 3] = 3 := sorry
```

Exercise 6. Define `map`, which applies a function to every element, then state, with `sorry`, its two functorial laws. Mapping the identity function changes nothing, and mapping a composition equals composing the maps.

```savedLean -keep
def map {α β : Type} (f : α → β) : List α → List β :=
  sorry

-- State the two laws here as theorems proved by sorry:
-- map_ident : mapping (fun x => x) over xs gives xs.
-- map_comp  : map g (map f xs) equals mapping their
--             composition over xs.
```

Exercise 7. Define `flatten`, which concatenates a list of lists with `appendPretty`, then state, with `sorry`, that the length of the result is the sum of the lengths of the inner lists, using `length`, `map` and `sumList` of the exercises above.

```savedLean -keep
def flatten {α : Type} : List (List α) → List α := sorry

-- State flatten_length here as a theorem proved by sorry:
-- length (flatten xss) equals sumList (map length xss).
```

Exercise 8. Complete `simplify`, which removes additions of 0, multiplications by 1, and divisions by 1, following the given cases, then state, with `sorry`, its correctness. Simplifying preserves the value under every environment.

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

-- State simplify_correct here as a theorem proved by
-- sorry: for every env and e, eval env (simplify e)
-- equals eval env e.
```

Exercise 9. Define the size of an expression, counting every constructor, and its depth, counting the longest constructor chain, then state, with `sorry`, that the depth never exceeds the size.

```savedLean -keep
def size : AExp → ℕ := sorry

def depth : AExp → ℕ := sorry

theorem depth_le_size (e : AExp) :
    depth e ≤ size e := sorry
```

Exercise 10. Define `mirror`, which swaps the operands of every addition and multiplication and leaves the rest unchanged, then state, with `sorry`, that mirroring preserves the value under every environment.

```savedLean -keep
def mirror : AExp → AExp := sorry

-- State mirror_eval here as a theorem proved by sorry.
```
