/-
Slides for Lecture 6, generated from checked sources. Each
top-level section is one slide; the document title and the intro
paragraphs form the title slide. All Lean code is elaborated at
build time and is identical to the code in the lecture notes
(`Lectures/En/Lecture06.lean`) where the two overlap.

The Lecture 5 deck supplies the earlier datatypes and the ℕ, ℤ
notations. Everything new is declared inside `namespace Func`.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesEn.Lecture05

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Functional Programming" =>

Inductive types, recursion, structures, and type classes

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Open the lecture notes](../en/Lecture-6___-Functional-Programming/)

Based on the [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), chapter 5.

# §6.1 Inductive types and their principles

* An inductive type is its list of *constructors*, and every value is built by applying them, each in just one way.

* For a data type, Lean generates four principles: the *recursor* `T.rec`, the non-recursive `casesOn`, the *injectivity* of each constructor, and the *disjointness* of distinct constructors.

```lean (name := injEq)
#check @Nat.succ.injEq
```

```leanOutput injEq
Nat.succ.injEq : ∀ (u v : ℕ), (u.succ = v.succ) = (u = v)
```

* The recursor is the raw form of structural recursion, and read on a proposition it is structural induction, which Lecture 7 derives.

# §6.1 Recursion and case analysis from the recursor

* Pattern matching and the `cases` tactic are surface syntax that the equation compiler and `cases` elaborate into the recursor.

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

# §6.2 Structural recursion

* Each recursive call is on a structurally smaller argument, so the definition terminates and elaborates to the recursor.

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

# §6.2 Why termination

* A total definition exposes its equation as a usable theorem, so accepting `loopy = loopy + 1` would prove `False`. Lean rejects such definitions; a genuine loop needs `partial def`, which stays opaque.

::::cols
:::col
{lbl}[The bogus equation gives False]

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
{lbl}[Rejected: no argument decreases]

```
def loopForever {α : Type} :
    List α → List α
  | []      => []
  | x :: xs =>
      loopForever (x :: xs)
```

* The escape hatch `termination_by` is for later; this lecture stays structural.
:::
::::

# §6.3 Pattern matching expressions

* `match` and `if` bring pattern matching into a term. A `match` elaborates through the type's recursor, and `if` branches on a `Decidable` instance. `Option` packages a partial result.

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

* Patterns are tried top to bottom; the wildcard `_` matches anything.
:::
::::

# §6.4 Structures

* A structure is a single-constructor inductive type with named fields, and Lean derives a projection for each.

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

* `{ … }` and `⟨…⟩` build the same value.
:::
::::

# §6.4 Extending records

* `extends` builds a larger record on a smaller one, and `{ r with … }` copies a record changing one field.

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

* The inherited fields stay accessible.
:::
::::

# §6.5 Type classes

* A `class` declares operations parameterised by one or more arguments, an `instance` supplies them, and resolution finds the instance from those arguments. `Std.Associative op` is indexed by an operation, not only a type.

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

# §6.5 The classes we already used

* The `∈` of Lecture 2 and the associativity and commutativity of Lecture 4 are type classes resolved by type.

```lean
#check @Membership.mem

#check @Std.Associative
```

* `Membership` gives `∈` its meaning through an instance chosen by the type of the container, and `Std.Associative` and `Std.Commutative` are the instances `ac_rfl` consulted.

# §6.6 Binary trees

* A tree is a `leaf` or a `branch` with a value and two subtrees; functions recurse on the subtrees.

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

# §6.6 Options, sums, and dependent vectors

* The same schema builds options, sum types, and dependent types that carry information in their own type.

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

* A `Vec α n` is a list of length `n`. The later weeks develop dependent types.
:::
::::

# §6.7 Worked example: arithmetic expressions

* An expression is a constant, a variable, a sum, or a product, and an evaluator computes its value under an environment.

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

* The syntax of a small language; its environment is the state.
:::
::::

# §6.7 Worked example: a type class for size

* One more instance extends `Size` to trees, and a function measures a whole list of sized values by resolution.

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

* Resolution finds the tree instance because the elements are trees, the same mechanism as `Membership`.
:::
::::

# §6.7 Worked example: a record with an extension

* An account extends to a named account, keeping both inherited fields and adding one.

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

* The single constructor of a structure is the `And.intro` of Lecture 1, with named fields instead of positional ones.

# §6.7 Worked example: mirroring a tree

* Mirroring twice returns the original tree. On a closed tree this holds by computation.

```lean
namespace Func

example : mirror (mirror t1) = t1 := rfl

end Func
```

* The general law `mirror (mirror t) = t`, for every tree, is not a computation. It needs structural induction, with the recursive calls of `mirror` supplying the induction hypotheses, and it is the first worked example of Lecture 7.

# Summary

* An inductive type is its constructors, and the kernel derives a recursor, `casesOn`, injectivity, and disjointness.

* Structural recursion terminates, and Lean admits only terminating definitions.

* `match` and `if` are pattern matching as expressions, and `Option` packages a partial result.

* A structure is a single-constructor inductive type with named fields, built with `⟨…⟩` or `{ … }` and extended with `extends`.

* A type class is a structure of operations resolved by type, the mechanism behind the `∈` and the `ac_rfl` of the earlier lectures.

* The same schema builds trees, options, sums, and dependent vectors.

* Lecture 7 derives structural induction from the recursor and proves the laws stated here.

Exercises: see the [lecture notes](../en/Lecture-6___-Functional-Programming/).
