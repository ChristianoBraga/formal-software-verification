import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers
import Lectures.En.Lecture05

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Lecture 6: Functional Programming" =>

%%%
tag := "lecture-6"
%%%

Lecture 3 introduced inductive types by example, reconstructing ℕ and `List` and defining functions on them by pattern matching. This lecture returns to that material and gives the general mechanism, following chapter 5 of the *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 5.] It reads an inductive definition as a list of constructors and names what the kernel derives from them, it defines total functions by structural recursion and explains why Lean insists on termination, it packages data in structures, and it explains type classes, the mechanism that Lecture 2 used for `Membership` and Lecture 4 used for the associativity and commutativity that `ac_rfl` consults.

The course spends two weeks on this chapter. This lecture is the programs side, defining data and functions. Lecture 7 is the proofs side, deriving the structural induction principle and proving the properties of these programs. So this lecture states the laws of its functions and proves only those that computation or a single case analysis settles, and it defers every proof that needs induction to Lecture 7, exactly as Lecture 5 deferred the general theory of structural induction.

*This lecture is also available as [presentation slides](../slides/lecture-6.en.html).*

# Inductive Types and Their Principles

An inductive type is defined by listing its *constructors*. Every value of the type is built by applying those constructors, and each value is built in just one way. Lecture 3 used this to build ℕ from `Nat.zero` and `Nat.succ` and `List` from `List.nil` and `List.cons`. For a type of data such as ℕ, Lean generates from the constructors four principles, and naming them explains where the tools of the earlier lectures come from.

The *recursor* `T.rec` is the primitive principle of the type. It is the raw form of structural recursion, and read on a proposition-valued motive it is the raw form of structural induction. Its type for ℕ shows the two cases a function on ℕ must supply, one for `Nat.zero` and one for `Nat.succ`, and the second case receives the value at the predecessor, which is the recursive result.

```lean (name := natRec)
#check @Nat.rec
#check @Nat.succ.injEq
```

```leanOutput natRec
@Nat.rec : {motive : ℕ → Sort u_1} → motive Nat.zero → ((n : ℕ) → motive n → motive n.succ) → (t : ℕ) → motive t
```

The `casesOn` principle is the non-recursive special case of the recursor, the one that the `cases` tactic of Lecture 1 elaborates into. Pattern matching and the equation compiler turn the surface syntax of Lecture 3 into applications of the recursor. The definition below computes with `Nat.rec` directly, and the same function by pattern matching is the one Lecture 3 would have written; the two are equal.

```lean
namespace Func

def usingRec (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => ih + 2) n

example : usingRec 3 = 6 := rfl

end Func
```

The remaining two principles concern the constructors themselves. Each constructor is *injective*, so equal constructor applications have equal arguments, and Lean generates the equation `Nat.succ.injEq` recording this. Distinct constructors are *disjoint*, so no application of `Nat.succ` equals `Nat.zero`. Injectivity and disjointness hold for a type of data like ℕ; for a type of proofs, where all proofs of one proposition are equal, they do not. The second output above is the injectivity equation, and the two examples below use injectivity and disjointness.

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

The `induction` tactic of Lecture 4 is the recursor read on a proposition, and Lecture 7 derives it in general and proves the laws that this lecture states. Here the recursor is only named, as the source of the recursion and case analysis already in use.

Margin notes. The Guide, chapter 5. Avigad, de Moura, Kong, Ullrich, *Theorem Proving in Lean 4*, the chapter on inductive types. The Lean language reference on the `inductive` command.

# Structural Recursion and Termination

A function is defined by *structural recursion* when each recursive call is on a structurally smaller argument, one constructor closer to a base case. Such a definition terminates, and the equation compiler turns it into an application of the recursor. Factorial recurses on the predecessor, and Fibonacci has two base cases and recurses on the two predecessors.

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

Lean admits as ordinary definitions only those it can show terminate, and the reason is soundness. A total definition exposes its defining equations as usable theorems and reduces during type checking, so a recursive equation such as `loopy = loopy + 1`, were Lean to accept it, would itself prove `False`. The block below posits exactly that equation as an axiom and derives the contradiction, to show what an unrestricted non-terminating definition would grant. Lean generates no such axiom, and it rejects the definitions that would produce it, which is why every function above terminates. A genuinely looping computation is still writable with `partial def`, but Lean then keeps the function opaque and exposes no equation, so no contradiction follows.

```lean -keep
namespace Func

opaque loopy : ℕ
axiom loopy_eq : loopy = loopy + 1

theorem loopy_false : False := by
  have h := loopy_eq
  omega

end Func
```

For a recursion that terminates for a reason Lean cannot see structurally, `termination_by` with `decreasing_by` supplies a measure and its proof, which the guide treats later; this lecture stays within structural recursion.

## Examples

The examples below define functions by structural recursion, vary the recursive argument, and mark the definitions Lean rejects.

{ex "ex-recursion-factorial"}[] Factorial and its value at 4.

```lean (name := exFact)
namespace Func

#eval fact 4

end Func
```

```leanOutput exFact
24
```

{ex "ex-recursion-fibonacci"}[] Fibonacci needs two base cases, so its step case reads the two preceding values.

```lean
namespace Func

example : fib 6 = 8 := rfl

end Func
```

{ex "ex-recursion-sum-to"}[] A sum of the numbers from `0` to `n`, recursing on the predecessor.

```lean
namespace Func

def sumTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

example : sumTo 5 = 15 := rfl

end Func
```

{ex "ex-recursion-accumulator"}[] The same sum with an accumulator argument, carrying the running total forwards.

```lean
namespace Func

def sumAcc : ℕ → ℕ → ℕ
  | 0,     acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

example : sumAcc 5 0 = 15 := rfl

end Func
```

{ex "ex-recursion-power-recall"}[] `power` from Lecture 3 is a nested recursion, its step case calling `mul` on the recursive result.

```lean
example : power 2 3 = 8 := rfl
```

{ex "ex-recursion-first-argument"}[] A function may recurse on its first argument, unlike the `add` of Lecture 3 which recurses on its second.

```lean
namespace Func

def countDown : ℕ → List ℕ
  | 0     => []
  | n + 1 => (n + 1) :: countDown n

example : countDown 3 = [3, 2, 1] := rfl

end Func
```

{ex "ex-recursion-mutual"}[] Two functions may recurse through each other, declared together with `mutual`.

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

{ex "ex-recursion-option-total"}[] A total function on `Option`, returning a result for both constructors.

```lean
namespace Func

def orZeroList : Option (List ℕ) → List ℕ
  | none    => []
  | some xs => xs

example : orZeroList none = [] := rfl

end Func
```

{ex "ex-recursion-rejected"}[] A definition Lean rejects. The recursive call is on the same list, so no argument grows smaller, Lean cannot see that it terminates, and it does not accept this equation as a total definition. The block is shown but not elaborated.

```
def loopForever {α : Type} : List α → List α
  | []      => []
  | x :: xs => loopForever (x :: xs)
```

{ex "ex-recursion-zero-base"}[] A base case at `0` and a step at `n + 1` is the shape of every recursion on ℕ, here doubling by repeated addition.

```lean
namespace Func

def twice : ℕ → ℕ
  | 0     => 0
  | n + 1 => twice n + 2

example : twice 5 = 10 := rfl

end Func
```

# Pattern Matching Expressions

Lecture 3 wrote a function as top-level equations, one per constructor shape. The same power is available as a `match` expression usable wherever a term is expected, and as `if c then … else …` for a decidable condition. A `match` elaborates through the type's recursor, its `casesOn` of §6.1 in the simplest cases, and `if` branches on a `Decidable` instance for its condition. Patterns are tried top to bottom, so an earlier pattern shadows a later one, and the wildcard `_` matches anything.

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

The `Option` type packages a partial result, `some x` for a value and `none` for its absence, so `pred?` is total although the predecessor of `0` is undefined.

## Examples

The examples below use `match` and `if` inside a body, on numbers, pairs, lists, and options.

{ex "ex-match-classify"}[] A `match` returning a classification, its wildcard catching every remaining case.

```lean
namespace Func

example : classify 7 = "many" := rfl

end Func
```

{ex "ex-match-if-decidable"}[] `if` tests a decidable condition, here whether a number is zero.

```lean
namespace Func

def isZero (n : ℕ) : Bool :=
  if n = 0 then true else false

example : isZero 0 = true := rfl

end Func
```

{ex "ex-match-nested-pair"}[] A `match` on a pair inspects both components at once.

```lean
namespace Func

def bothZero (p : ℕ × ℕ) : Bool :=
  match p with
  | (0, 0) => true
  | _      => false

example : bothZero (0, 3) = false := rfl

end Func
```

{ex "ex-match-option-predecessor"}[] `pred?` returns `none` at zero, so the result is always defined.

```lean
namespace Func

example : pred? 0 = none := rfl

end Func
```

{ex "ex-match-list-head"}[] A `match` on a list returns the head as an option.

```lean
namespace Func

def firstOpt {α : Type} : List α → Option α
  | []     => none
  | x :: _ => some x

example : firstOpt [3, 1] = some 3 := rfl

end Func
```

{ex "ex-match-unpack-option"}[] A `match` on an option unpacks `some` and supplies a default for `none`.

```lean
namespace Func

def orZero : Option ℕ → ℕ
  | none   => 0
  | some n => n

example : orZero (some 5) = 5 := rfl

end Func
```

{ex "ex-match-wildcard-order"}[] Patterns are tried top to bottom, so the specific case precedes the wildcard.

```lean
namespace Func

def sign (n : ℤ) : String :=
  match n with
  | 0 => "zero"
  | _ => "nonzero"

example : sign 0 = "zero" := rfl

end Func
```

{ex "ex-match-inside-term"}[] A `match` may appear inside a larger term, here inside an addition.

```lean
namespace Func

def bump (o : Option ℕ) : ℕ :=
  1 + (match o with
       | none   => 0
       | some n => n)

example : bump (some 4) = 5 := rfl

end Func
```

{ex "ex-match-if-versus-match"}[] `if` and a two-branch `match` decide the same condition.

```lean
namespace Func

def isZeroMatch (n : ℕ) : Bool :=
  match n with
  | 0 => true
  | _ => false

example : isZeroMatch 0 = isZero 0 := rfl

end Func
```

{ex "ex-match-guarded-default"}[] A safe division returning `none` when the divisor is zero.

```lean
namespace Func

def safeDiv (m n : ℕ) : Option ℕ :=
  if n = 0 then none else some (m / n)

example : safeDiv 6 0 = none := rfl

end Func
```

# Structures and Records

A *structure* is an inductive type with a single constructor and named fields, and Lean derives a projection for each field. It is the natural shape for a record of related values. The anonymous constructor `⟨…⟩`, the field syntax `{ … }`, and the update syntax `{ r with … }` all build or modify a structure, and `extends` builds a larger structure on a smaller one. The `And.intro` of Lecture 1 and the pair of Lecture 3 are themselves single-constructor structures.

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

A `NamedSegment` carries the two fields of `Segment` and one more, and a projection reaches the inherited fields directly.

## Examples

The examples below build, project, update, and extend records.

{ex "ex-structure-project"}[] A projection reads a field, and `width` computes from two of them.

```lean
namespace Func

def seg1 : Segment := { lo := 1, hi := 5 }

example : width seg1 = 4 := by decide

end Func
```

{ex "ex-structure-field-syntax"}[] The field syntax `{ … }` and the anonymous constructor `⟨…⟩` build the same value.

```lean
namespace Func

def seg2 : Segment := ⟨1, 5⟩

example : seg1 = seg2 := rfl

end Func
```

{ex "ex-structure-update"}[] The update syntax `{ r with … }` copies a record and changes one field.

```lean
namespace Func

def widen (s : Segment) : Segment :=
  { s with hi := s.hi + 1 }

example : (widen seg1).hi = 6 := by decide

end Func
```

{ex "ex-structure-extends-inherited"}[] `extends` adds a field, and the inherited fields stay accessible.

```lean
namespace Func

def ns1 : NamedSegment :=
  { lo := 0, hi := 2, name := "a" }

example : ns1.lo = 0 := by decide

end Func
```

{ex "ex-structure-inherited-name"}[] The new field is reached like any other.

```lean
namespace Func

example : ns1.name = "a" := rfl

end Func
```

{ex "ex-structure-field-function"}[] A field may itself be a function, and the projection recovers it.

```lean
namespace Func

structure Handler where
  run : ℕ → ℕ

def dbl : Handler := { run := fun n => n + n }

example : dbl.run 3 = 6 := rfl

end Func
```

{ex "ex-structure-projection-rfl"}[] Building a record and projecting a field returns the field, by computation.

```lean
namespace Func

example : (⟨1, 5⟩ : Segment).lo = 1 := rfl

end Func
```

{ex "ex-structure-derived-function"}[] A function of a record computed from its fields.

```lean
namespace Func

def midpoint (s : Segment) : ℤ :=
  (s.lo + s.hi) / 2

example : midpoint ⟨0, 4⟩ = 2 := by decide

end Func
```

{ex "ex-structure-prod-recall"}[] `Prod` is the canonical two-field structure, with `Prod.fst` and `Prod.snd` its projections.

```lean
example : (Prod.fst (3, 5) : ℕ) = 3 := rfl
```

{ex "ex-structure-anonymous-and"}[] The `And.intro` of Lecture 1 is a two-field structure, and the anonymous constructor builds it.

```lean
example (a b : Prop) (ha : a) (hb : b) : a ∧ b :=
  ⟨ha, hb⟩
```

# Type Classes

A *type class* is a structure of operations parameterised by one or more arguments, usually types. A `class` declares the operations, an `instance` supplies them for particular arguments, and *instance resolution* finds the right instance from those arguments whenever a function requests one with `[C α]`. Some classes are indexed by more than a type, and `Std.Associative op` of Lecture 4 is indexed by an operation. This is the mechanism Lecture 2 used to give `∈` its meaning through a `Membership` instance and Lecture 4 used to register `add` as associative and commutative for `ac_rfl`.

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

The function `usize` names no instance. It requests `[Size α]`, and resolution supplies the list instance or the option instance according to the type at the call site.

## Examples

The examples below declare instances, watch resolution choose by type, and name the classes the earlier lectures used.

{ex "ex-class-list-instance"}[] The list instance measures a list by its length.

```lean (name := exUsizeList)
namespace Func

#eval usize [1, 2, 3]

end Func
```

```leanOutput exUsizeList
3
```

{ex "ex-class-option-instance"}[] The option instance measures presence, `1` or `0`.

```lean (name := exUsizeOption)
namespace Func

#eval usize (some 7)

end Func
```

```leanOutput exUsizeOption
1
```

{ex "ex-class-product-instance"}[] An instance may depend on other instances, as a product depends on its factors.

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

{ex "ex-class-resolution-by-type"}[] Resolution chooses the instance from the type alone, which `inferInstance` makes explicit.

```lean
namespace Func

#check (inferInstance : Size (List ℕ))

end Func
```

{ex "ex-class-default-field"}[] A class may give a field a default, which an instance may leave untouched or override.

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

{ex "ex-class-membership-recall"}[] The `∈` of Lecture 2 is the method of the `Membership` class, resolved by the type of the container.

```lean
#check @Membership.mem
```

{ex "ex-class-deriving"}[] Lean can build some instances automatically with `deriving`, here equality and a textual form for a finite type.

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

{ex "ex-class-deriving-decide"}[] The derived equality lets `decide` settle a concrete disequality.

```lean
namespace Func

example : Coin.heads ≠ Coin.tails := by decide

end Func
```

{ex "ex-class-method-implicit"}[] A class method carries an implicit instance argument, which `#check` displays.

```lean
namespace Func

#check @Size.size

end Func
```

{ex "ex-class-associativity-recall"}[] The associativity and commutativity that `ac_rfl` consulted in Lecture 4 are instances of `Std.Associative` and `Std.Commutative`.

```lean
#check @Std.Associative

#check @Std.Commutative
```

# Building New Datatypes

The same schema builds richer types. A binary tree is either a `leaf` or a `branch` carrying a value and two subtrees, and functions on it recurse on the subtrees. The section defines `size`, `height`, and `mirror` and states their laws, proving only the closed instances by computation; the general laws are Lecture 7's, since they need induction.

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

The recursor of `Tree` shows the general schema on a fresh type. It takes a value for the `leaf` case and, for the `branch` case, a function that receives the two subtrees, the stored value, and the recursive results on the two subtrees, which become the induction hypotheses of a proof by induction.

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

The general laws this section states and Lecture 7 proves are `mirror (mirror t) = t`, `treeSize (mirror t) = treeSize t`, and the counting law relating the leaves and the branches of a tree. Each needs induction, so this section proves only their closed instances.

## Examples

The examples below build a tree, compute with it, and read the other datatypes the schema produces.

{ex "ex-datatype-build-tree"}[] A small tree with one value at the root and one in its left subtree.

```lean
namespace Func

def t1 : Tree ℕ :=
  .branch (.branch .leaf 1 .leaf) 2 .leaf

end Func
```

{ex "ex-datatype-size"}[] `size` counts the branches, recursing on both subtrees.

```lean (name := exTreeSize)
namespace Func

#eval treeSize t1

end Func
```

```leanOutput exTreeSize
2
```

{ex "ex-datatype-height"}[] `height` takes the greater of the two subtree heights and adds one.

```lean (name := exHeight)
namespace Func

#eval height t1

end Func
```

```leanOutput exHeight
2
```

{ex "ex-datatype-mirror"}[] `mirror` swaps the two subtrees at every branch, and this constructor law holds for every tree by computation, with no induction.

```lean
namespace Func

example {α : Type} (l : Tree α) (x : α) (r : Tree α) :
    mirror (.branch l x r)
      = .branch (mirror r) x (mirror l) := rfl

end Func
```

The doubly-mirrored law `mirror (mirror t) = t`, for every tree, is different, since it needs induction, and it is a worked example of Lecture 7.

{ex "ex-datatype-mirror-leaf"}[] Mirroring a leaf changes nothing.

```lean
namespace Func

example : mirror (Tree.leaf : Tree ℕ) = Tree.leaf := rfl

end Func
```

{ex "ex-datatype-size-mirror"}[] Mirroring preserves the size, here on the closed tree; the general law waits for Lecture 7.

```lean
namespace Func

example : treeSize (mirror t1) = treeSize t1 := rfl

end Func
```

{ex "ex-datatype-sum"}[] A sum type `α ⊕ β` holds a value from one side or the other, and a `match` on `inl`/`inr` consumes it.

```lean
namespace Func

def fromSum : ℕ ⊕ Bool → ℕ
  | .inl n => n
  | .inr b => if b then 1 else 0

example : fromSum (.inl 4) = 4 := rfl

end Func
```

{ex "ex-datatype-option-map"}[] `Option` is the canonical nullable type, and a function may map over its value. The law for `some` holds for every function and argument by computation, with no induction.

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

{ex "ex-datatype-vec"}[] A dependent inductive type carries information in its own type. A `Vec α n` is a list of length `n`, and its constructors record the length. This is a read-only preview; the later weeks develop dependent types.

```lean
namespace Func

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n → Vec α (n + 1)

end Func
```

{ex "ex-datatype-vec-head"}[] Because the type of `vhead` demands a nonempty vector, the empty case cannot arise, and the function is total without an option.

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

# Worked Examples

Each example below is carried out in full and verbalised. They are disjoint from the section examples and the exercises, and Lean checks every line when the notes are built.

## Arithmetic expressions and their evaluation

An arithmetic expression is a constant, a variable, a sum, or a product, and this is an inductive type with four constructors, two of them recursive. An evaluator takes an environment giving a value to each variable and computes the value of an expression by recursion on its structure.

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

The expression below reads `2 + x × 5`, and under an environment giving `x` the value `3` it evaluates to `17`.

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

The defining equation for a sum gives the law `eval env (add a b) = eval env a + eval env b`, and it holds by computation, since the equation is exactly the recursion step.

```lean
namespace Func

example (env : String → ℤ) (a b : AExp) :
    eval env (.add a b)
      = eval env a + eval env b := rfl

end Func
```

These expressions are the syntax of a small language, and the environment is its state. The operational semantics of the Hoare-logic weeks builds on exactly this shape.

## A type class for size

The `Size` class of §6.5 extends to trees with one more instance, and a function then measures a whole list of sized values. Resolution supplies the tree instance for each element and the list structure drives the recursion.

```lean
namespace Func

instance {α : Type} : Size (Tree α) where
  size := treeSize

def totalSize {α : Type} [Size α] : List α → ℕ
  | []      => 0
  | x :: xs => Size.size x + totalSize xs

end Func
```

The list below holds a tree and its mirror, each of size `2`, so the total is `4`.

```lean (name := exTotal)
namespace Func

#eval totalSize [t1, mirror t1]

end Func
```

```leanOutput exTotal
4
```

The function requests `[Size α]` once, and resolution finds the tree instance because the elements are trees. The `Membership` instance of Lecture 2 and the associativity instance of Lecture 4 are the same mechanism seen plainly, an operation attached to a type and found by its type.

## A record with an extension

A record collects related fields under one name, and `extends` builds a specialised record on a general one. An account has an owner and a balance, and a named account adds a nickname while keeping both inherited fields.

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

Building the record with the field syntax and projecting a field returns that field, by computation. The single constructor of a structure is the same idea as the `And.intro` of Lecture 1, one constructor gathering several arguments, with the fields named instead of positional.

## Mirroring a tree

The `mirror` of §6.6 swaps the subtrees at every branch, so mirroring twice should return the original tree. On a closed tree this holds by computation.

```lean
namespace Func

example : mirror (mirror t1) = t1 := rfl

end Func
```

The general law `mirror (mirror t) = t`, for every tree `t`, is not a computation. It needs structural induction, with the recursive calls of `mirror` supplying the induction hypotheses for the two subtrees, and it is the first worked example of Lecture 7. This closes the loop with Lecture 5's `reverse_reverse`, which proved the list analogue by recursion, and it sets up the induction to come.

# Exercises

Define each function and prove each law in Lean, replacing `sorry`. Download the exercise file [`Lecture06.lean`](example-code/Lectures/En/Lecture06.lean) and open it in VS Code. Each type is given; your task is the functions and the proofs. The laws here are settled by `rfl` or `decide` on closed values, since the proofs by induction belong to Lecture 7. Exercises 9 and 10 are optional.

```savedImport
import Lectures.LoVe.LoVelib
```

```savedComment
Exercises for Lecture 6: Functional Programming.
Each type is given. Define the functions and prove the laws,
replacing `sorry`. Every law here holds by `rfl` or `decide`.
Exercises 9 and 10 are optional.
```

{exercise "exr-direction"}[] Define `turnRight` on the four compass directions, and prove by `decide` that turning right four times returns north.

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

{exercise "exr-last-opt"}[] Define `lastOpt`, the last element of a list as an option, and prove its value on the empty list and on a concrete list.

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

{exercise "exr-rectangle"}[] Define the area of a rectangle and prove a concrete area.

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

{exercise "exr-box"}[] Extend the rectangle to a box with a depth, and define its volume from the inherited fields.

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

{exercise "exr-doubler"}[] Complete the `Doubler` instances, doubling a number by addition and a list by self-append, and the selector, then prove the doubled value for ℕ.

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

{exercise "exr-leaves-nodes"}[] Count the leaves and the branches of a binary tree, and check the relation between them on a concrete tree.

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

{exercise "exr-replicate"}[] Define `replicate`, the list of `n` copies of a value, and prove its value at `0`.

```savedLean -keep
namespace FuncEx

def replicate {α : Type} : ℕ → α → List α :=
  sorry

theorem replicate_zero {α : Type} (x : α) :
    replicate 0 x = [] :=
  sorry

end FuncEx
```

{exercise "exr-is-empty"}[] Define `isEmpty` by a `match`, and prove its two computational laws.

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

{exercise "exr-rose"}[] Optional. A rose tree branches into a list of subtrees. Define `rsize`, the number of its nodes, noting the nested recursion through `List`.

```savedLean -keep
namespace FuncEx

inductive Rose (α : Type) where
  | node (x : α) (children : List (Rose α))

def rsize {α : Type} : Rose α → ℕ :=
  sorry

end FuncEx
```

{exercise "exr-vec-head"}[] Optional. A length-indexed vector rules out the empty case in its type. Define the total head of a nonempty vector and evaluate it.

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
