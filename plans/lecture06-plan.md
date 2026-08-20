# Plan for Lecture 6: Functional Programming

Syllabus week 6, "Programação funcional; tipos indutivos e recursão | LoVe05" (`ementas/Ementa-VerificacaoFormalSoftware.md`, line 62). Source material is chapter 5 of the *Hitchhiker's Guide to Logical Verification*, 2026 edition, "Functional Programming", together with `lean/LoVe/LoVe05_FunctionalProgramming_Demo.lean` and `lean/LoVe/LoVe05_FunctionalProgramming_ExerciseSheet.lean` in [lean-forward/logical_verification_2026](https://github.com/lean-forward/logical_verification_2026). The demo and exercise sheet were read from the public repository at planning time; every Lean snippet below must be compiled during writing before its output is trusted.

The course spends two weeks on LoVe05. Week 6, this lecture, is the *programs* side. It defines data with inductive types, defines functions by structural recursion and pattern matching, packages data in structures, and overloads notation with type classes. Week 7, Lecture 7, is the *proofs* side. It derives the structural induction principle from an inductive type and proves properties of the programs defined here. This lecture therefore states laws and proves the ones that computation or a single case analysis settles, and it defers every proof that needs induction to Lecture 7, with an explicit pointer, exactly as Lecture 5 deferred the general theory of structural induction.

Lectures 3 to 5 already gave a first contact with inductive types. Lecture 3 reconstructed ℕ and `List` with the `inductive` command, defined `add`, `mul`, `reverse` and their companions by pattern matching, and stated their laws with `sorry`. Lecture 4 introduced the `induction` tactic on ℕ and lists and discharged those laws. Lecture 5 read a recursive proof as a proof by induction under the PAT principle. Lecture 6 turns from those particular examples to the general mechanism, and it introduces the two constructs the earlier lectures used without explaining, the `instance` command of Lecture 2 and the associativity and commutativity instances of Lecture 4.

## Confirmed scope of LoVe05

The demo file opens `namespace LoVe` and is organised in nine sections.

- **Inductive Types.** `#print Nat`. The general schema, illustrated on the type Lecture 3 reconstructed. An inductive type is given by its constructors, and the kernel derives from them a recursor, a `casesOn` principle, the injectivity of each constructor, and the disjointness of distinct constructors.
- **Structural Induction.** `Nat.succ_neq_self (n : ℕ) : Nat.succ n ≠ n` by the `induction` tactic. Placed here in the demo, but in this course the general treatment is week 7, so Lecture 6 mentions it only as the counterpart of structural recursion and moves the proof to Lecture 7.
- **Structural Recursion.** `fact`, `factThreeCases`, and the cautionary pair `immoral`/`immoral_eq` that derives `False` from a non-terminating equation, motivating why Lean requires every definition to terminate.
- **Pattern Matching Expressions.** `bcount` and `min`, showing `match` and `if` inside a function body rather than as top-level equations.
- **Structures.** `RGB`, `RGBA extends RGB`, `shuffle`, `shufflePattern`, and `shuffle_shuffle_shuffle` proved by computation. Single-constructor inductive types with named fields.
- **Type Classes.** `Inhabited`, instances for ℕ, `List`, functions and products, `head` using `[Inhabited α]`, and `Std.Associative`/`Std.Commutative`, the classes Lecture 4 fed to `ac_rfl`.
- **Lists.** `map`, `mapArgs`, the map laws by induction, `tail`, `headOpt` returning `Option`, `headPre` with a dependent precondition, `zip`, `length`, `min_add_add`, `length_zip`, `map_zip`.
- **Binary Trees.** `Tree`, `mirror`, `mirror_mirror`, `mirror_mirror_calc`, `mirror_Eq_nil_Iff`.
- **Dependent Inductive Types (optional).** `Vec α n`, `listOfVec`, `vecOfList`, `length_listOfVec`.

The exercise sheet sets three questions. Q1 asks for an accumulator-based `reverseAccu` and proofs relating it to `reverse`, including a paper proof by structural induction. Q2 defines `take` beside a given `drop` and proves `drop_drop`, `take_take`, `take_drop`. Q3 defines an inductive type `Term` for the untyped λ-calculus with `var`, `lam`, `app`, and an optional `Repr` instance.

**The exercise sheet is used only to understand the chapter's scope, never as a source of exercises.** Lecture 6's exercises are wholly original, listed in the Exercises section below, and drawn neither from this sheet nor from HTPIwL nor from Lean's documentation. Canonical datatypes such as binary trees, options, and arithmetic expressions are used freely; copied problems are not.

The demo's map laws (`map_ident`, `map_comp`, `map_append`), `length_zip`, `mirror_mirror`, and `length_listOfVec` all proceed by the `induction` tactic. These are proofs of properties of programs, so in this course they belong to week 7. Lecture 6 defines `map`, `zip`, `mirror` and the rest and states their laws, and Lecture 7 proves them. This is the same division Lecture 5 announced when it deferred "the general theory of structural induction over arbitrary inductive types" to weeks 6 and 7.

## What the lecture may assume, and what it must not repeat

Lectures 1 to 5 use the `inductive` command with constructors, pattern-matching function definitions, structural recursion, polymorphism with implicit and explicit type arguments, `#eval`, `#check`, `#print`, the `induction … with` tactic on ℕ and lists, `cases`, `rfl`, `rw`, `simp`, `decide`, the anonymous constructor `⟨…, …⟩`, and the rule names for the connectives and quantifiers. Lecture 2 used the `instance` command for `Membership` and its companions without explaining it. Lecture 4 registered `Std.Associative` and `Std.Commutative` instances for `ac_rfl` without explaining them. Lecture 5 introduced structured recursion as a proof device and previewed a rejected non-terminating definition.

New in Lecture 6:

| New | Already known |
| --- | --- |
| the general inductive schema, and what the kernel derives from it | the `inductive` command on ℕ and `List` (Lecture 3) |
| the recursor and `casesOn` as the origin of recursion and case analysis | pattern matching and the `cases` tactic (Lectures 3, 4) |
| injectivity and disjointness of constructors | the constructors of ℕ and `List` (Lecture 3) |
| the termination requirement and why a non-terminating definition is unsound | the rejected `loopForever` preview (Lecture 5) |
| `match` and `if` as expressions inside a function body | top-level pattern-matching equations (Lecture 3) |
| `structure`, named fields, projections, `extends`, record update | the anonymous constructor for `∧` and `∃` (Lectures 1, 2) |
| `class`, `instance`, instance resolution `[C α]`, default fields | the `instance` command, used silently (Lectures 2, 4) |
| `Option`, `Prod` as a structure, sum types, and dependent `Vec` | polymorphic `List` and pairs (Lecture 3) |
| arithmetic expressions and their evaluation as a running example | recursive functions on ℕ and lists (Lecture 3) |

The general structural induction principle, the derivation of the induction hypothesis from the recursor, and every proof by induction about the functions defined here stay in Lecture 7. Lecture 6 proves only what `rfl`, `decide`, `simp` on closed terms, or a single `cases` settles, and it marks each deferred law with a pointer to week 7.

## Learning goals

After this lecture the student can

1. read an inductive definition as a list of constructors and name what the kernel derives from it, the recursor, `casesOn`, injectivity, and disjointness;
2. define a total function by structural recursion, explain why Lean requires termination, and recognise a definition that Lean rejects;
3. use `match` and `if` as expressions inside a function body, with nested patterns, wildcards, and `Option`;
4. define a `structure`, project its fields, extend it with `extends`, and build and update records;
5. declare a type `class`, give `instance`s, and explain how instance resolution finds them, connecting this to the `Membership` instance of Lecture 2 and the associativity and commutativity instances of Lecture 4;
6. define richer datatypes, binary trees, options, sums, and read a dependent inductive type such as `Vec`;
7. state the laws of a functional program and prove those that computation or a single case analysis settles, deferring the inductive proofs to Lecture 7.

Place in the course. Lecture 3 introduced inductive types by example; Lecture 6 gives the general mechanism and the two constructs, structures and type classes, that the earlier lectures used silently. Lecture 7 then derives structural induction from the recursor and proves the laws Lecture 6 states, closing LoVe05. The datatypes and functions defined here are the running material of Lecture 7, and the arithmetic expressions foreshadow the operational semantics of the Hoare-logic weeks.

## Module layout and naming

`Lectures/En/Lecture06.lean` **imports `Lectures.En.Lecture05`**. This keeps the linear chain and gives `add`, `mul`, `reverse`, and the earlier namespaces without redefinition. Lecture 7 will import Lecture 06 to reuse the datatypes and functions defined here, so every declaration Lecture 7 needs must **persist**, that is, live in a plain `lean` block, not a `-keep` one.

All new named declarations go inside `namespace Func … end Func`, reopened per code block, as Lectures 4 and 5 used `Backward` and `Forward`. `Func.Tree`, `Func.AExp`, `Func.Size` and the rest then coexist with the earlier namespaces and with Mathlib's root names. Do not define a root `Tree`, `map`, `zip`, or `size`, since Mathlib and the earlier lectures already own several of those names; keep everything under `Func`. Verify before writing that `Lectures/En.lean` still elaborates once Lecture 6 is added, and that the four single-language targets build, since the root `Lectures` aggregate is no longer built after the recent build change.

`Lectures/Pt/Lecture06.lean` imports `Lectures.Pt.Lecture05` and uses the same `Func` namespace; the two language trees never share an environment, so the reuse of names across languages is safe.

## Section-by-section outline

Six sections, matching the shape of Lectures 3 to 5. One opening section without examples, then five sections each closing with `## Examples` containing exactly ten examples, for fifty examples in total.

### 6.1 Inductive Types and Their Principles | Tipos Indutivos e Seus Princípios (no Examples subsection)

Teaches the general schema. An inductive type is defined by listing its constructors, and its values are exactly the finite applications of those constructors. From this list the kernel derives four things automatically, and the section names each. The *recursor* `T.rec` is the primitive form of structural recursion and, read on propositions, of structural induction; `T.casesOn` is the non-recursive special case that the `cases` tactic uses; each constructor is *injective*; and distinct constructors are *disjoint*, which the demo calls no confusion. Lecture 3 built ℕ and `List` and used pattern matching and `cases` without saying where they come from; this section says the recursor is the source, and pattern matching and `cases` are the surface syntax the equation compiler and the `cases` tactic elaborate into it.

Lean code shown. `#print Nat` and `#check @Nat.rec` to display the recursor of a known type, with the output copied from the build. `#check @List.rec`. A one-line `example` using `Nat.rec` directly, to make the recursor concrete, then the same computation by pattern matching, noting the two are the same. The injectivity and disjointness principles stated as the automatically generated `Nat.succ.injEq` and the fact that `Nat.zero ≠ Nat.succ n`, checked with `#check`. No new datatype is introduced here; the section reflects on the ones already known.

Margin notes. The Guide, chapter 5. Avigad, de Moura, Kong, Ullrich, *Theorem Proving in Lean 4*, the chapter on inductive types. The Lean language reference on the `inductive` command.

### 6.2 Structural Recursion and Termination | Recursão Estrutural e Terminação (10 examples)

Teaches structural recursion in general and why Lean requires it. A structurally recursive definition calls itself only on structurally smaller arguments, so it terminates, and the equation compiler turns it into an application of the recursor. Lean accepts only definitions it can show terminate, and the section explains the stakes with an original cautionary example, an `axiom` positing a non-terminating fixpoint `f x = f x + 1` from which `False` follows, which is why the kernel admits no such definition. It mentions `termination_by` and `decreasing_by` in one sentence as the escape hatch for well-founded but non-structural recursion, without teaching them.

Lean code shown. Factorial `Func.fact` and Fibonacci `Func.fib` by structural recursion on ℕ; a polynomial evaluator or a `sumTo` by recursion; the original non-termination cautionary tale as an `axiom` block deriving `False`, with `#print axioms` showing the dependence; the rejected non-structural definition of Lecture 5 recalled in one line.

The ten examples. Factorial and its `#eval`; Fibonacci with two base cases; a `sumTo n` summing `0` to `n`; a recursion with an accumulator argument; a function recursing on the *first* argument contrasted with `add` of Lecture 3 on the second; `power` recalled from Lecture 3 as a nested recursion; a definition Lean rejects because no argument decreases, shown in a plain block with the error described; a `#print axioms` on the cautionary `False`; a total function on `Option`; a mutually recursive `even`/`odd` pair by `mutual`, with a one-sentence note.

### 6.3 Pattern Matching Expressions | Casamento de Padrões como Expressão (10 examples)

Teaches `match` and `if` inside a function body. Lecture 3 wrote functions as top-level equations; here the same power appears as a `match` expression usable anywhere a term is expected, and `if c then … else …` for decidable conditions. The section covers nested patterns, overlapping patterns resolved top to bottom, the wildcard `_`, and the `Option` type for partial results, and it notes that a `match` is elaborated to `casesOn`, tying back to 6.1.

Lean code shown. A `match` expression computing a classification of a number; an `if` with a decidable test; a function returning `Option` for an out-of-range input; a nested `match` on a pair; the same function written as top-level equations and as one `match`, shown to be equal.

The ten examples. A `match` returning a Boolean classification; an `if` on `n = 0`; a nested `match` on two arguments; a wildcard catch-all; overlapping patterns and the top-to-bottom rule; `Option` for a safe predecessor; `match` on a `List` head; a `match` inside a larger term; `if` versus `match` on the same decidable test; a `match` on an `Option` unpacking `some`/`none`.

### 6.4 Structures and Records | Estruturas e Registros (10 examples)

Teaches `structure`. A structure is an inductive type with a single constructor and named fields, and Lean derives a projection for each field. The section defines an original record, projects its fields, builds values with the field syntax `{ … }` and the anonymous constructor `⟨…⟩`, updates a record with `{ r with … }`, and extends one structure with another by `extends`. It connects the anonymous constructor to the one used for `∧` and `∃` in Lectures 1 and 2, which are themselves single-constructor inductive types.

Lean code shown. `structure Func.Segment where (lo hi : ℤ)` with a `width` function; a value built two ways; a record update; `structure Func.NamedSegment extends Segment where (name : String)` with a projection reaching the inherited field.

The ten examples. Define a record and project a field; build a value with `{ … }`; build the same value with `⟨…⟩`; a record update with `{ r with … }`; a function taking a record and returning a field; a structure with a derived function; `extends` and access to an inherited field; a proof by `rfl` that a projection of a built record is the field; a structure whose field is a function; `Prod` recalled as the canonical two-field structure with `Prod.fst` and `Prod.snd`.

### 6.5 Type Classes | Classes de Tipos (10 examples)

Teaches type classes, the mechanism Lectures 2 and 4 used silently. A `class` is a structure of operations parameterised by a type, an `instance` supplies those operations for a particular type, and instance resolution finds the right instance from the type alone when a function requests one with `[C α]`. The section declares an original class with a method, gives instances for two types, defines a function that consumes the class, and explains resolution, then names the earlier silent uses, the `Membership` instance of Lecture 2 and the `Std.Associative`/`Std.Commutative` instances of Lecture 4 that `ac_rfl` consults. It mentions `deriving` in one sentence for the automatic instances Lean can build.

Lean code shown. `class Func.Size (α : Type) where (size : α → ℕ)`; instances `Func.Size (List α)` and `Func.Size (Tree α)`; a function `[Func.Size α] → α → ℕ` calling `size`; `#eval` selecting each instance; a one-line recall of `Std.Commutative`.

The ten examples. Declare the class; an instance for lists; an instance for a second type; a function that requests the class with `[Size α]`; instance resolution choosing by type at two `#eval`s; a default field in a class; an instance depending on another instance, as products depend on their factors; the `Membership` instance of Lecture 2 named as the same mechanism; `deriving` an instance automatically; `#check` on a class method to show the implicit instance argument.

### 6.6 Building New Datatypes | Construindo Novos Tipos de Dados (10 examples)

Teaches richer inductive types. The section defines binary trees, uses `Option` and sum types, and reads a dependent inductive type. It defines functions over trees by structural recursion, `Func.size`, `Func.height`, `Func.mirror`, states their laws, and proves only the closed-term instances by `rfl` or `decide`, deferring `mirror (mirror t) = t` and the counting laws to Lecture 7. It closes with `Vec α n`, a list carrying its length in its type, as a one-example preview of dependent types, with a pointer to the later weeks.

Lean code shown. `inductive Func.Tree (α : Type) where | leaf | branch (l : Tree α) (x : α) (r : Tree α)`; `Func.size`, `Func.height`, `Func.mirror` by recursion; a `#eval` on a small tree; `inductive Func.Vec (α : Type) : ℕ → Type` with `nil` and `cons`, and its constructors' types.

The ten examples. Define the tree type; build a small tree; `size` by recursion; `height` by recursion; `mirror` by recursion; `#eval size`/`height`/`mirror` on a closed tree; `mirror (mirror t) = t` on a closed tree by `rfl`, with the general law stated and deferred; a sum type `α ⊕ β` with a function by `match`; `Option` as the canonical nullable type; `Vec` with its length-indexed constructors, read but not used, pointing to later weeks.

## Worked Examples (4)

Each is carried out in full and verbalised, disjoint from the section examples and the exercises, and each foreshadows a proof that Lecture 7 will complete.

### 1. Arithmetic expressions and their evaluation | Expressões aritméticas e sua avaliação

`inductive Func.AExp` with `const (i : ℤ)`, `var (x : String)`, `add (a b : AExp)`, `mul (a b : AExp)`, and an evaluator `Func.eval (env : String → ℤ) : AExp → ℤ` by structural recursion. The example builds a concrete expression, evaluates it under a sample environment with `#eval`, and states a law, `eval env (add a b) = eval env a + eval env b`, that holds by `rfl` from the defining equation. The prose points to the operational semantics of the Hoare-logic weeks, where expressions like these carry the state of a program.

### 2. A type class for size | Uma classe de tipos para tamanho

`class Func.Size` with `size`, instances for `List` and `Tree`, and a function `totalSize [Size α] : List α → ℕ` summing the sizes of the elements. The example shows instance resolution choosing the list instance for the outer call and the element instance for each element, and it evaluates a mixed example with `#eval`. It names the `Membership` and associativity instances of the earlier lectures as the same mechanism seen plainly.

### 3. A record with an extension | Um registro com uma extensão

`structure Func.Account` with fields, `structure Func.NamedAccount extends Account`, a function that reads an inherited field, and a proof by `rfl` that building and projecting returns the field. The example shows the anonymous constructor, the field syntax, the record update, and `extends`, and it relates the single-constructor structure to the `And.intro` of Lecture 1.

### 4. Mirroring a tree | Espelhando uma árvore

`Func.mirror` on `Func.Tree`, defined by recursion, with the law `mirror (mirror t) = t` stated. The example proves the law on a concrete closed tree by `rfl`, then states the general law and defers it to Lecture 7, naming the recursive call as the induction hypothesis of the proof to come. This closes the loop with Lecture 5's `reverse_reverse`, which proved the list analogue by recursion, and it sets up Lecture 7's first induction.

## Exercises (10)

Disjoint from the section examples, from the worked examples, from Lectures 1 to 5, and from the LoVe05 exercise sheet. The whole set is original. Canonical datatypes are used freely, but no statement is taken from LoVe, HTPIwL, or Lean's documentation, and none repeats an exercise of Lectures 1 to 5. Exercises 1 to 8 define types and functions and prove the laws that computation or a single case analysis settles; the inductive proofs of the remaining laws are Lecture 7's exercises. Exercises 9 and 10 are optional.

The exercise file needs the datatypes the questions build on, so those go in `savedLean` blocks without `-keep`, inside `namespace Func`, and the import is `import Lectures.LoVe.LoVelib`, which supplies ℕ and ℤ notation and the tactics. Every skeleton is wrapped in `namespace Func … end Func` in the lecture module, and every statement is verified provable, or every definition well-typed, in a scratch file before the `sorry` skeleton ships, exactly as Lectures 4 and 5 were verified.

1. Define an inductive type `Direction` with four constructors and a function `turnRight : Direction → Direction`, then prove by `decide` that turning right four times is the identity on a given direction.
2. Define `Func.count` counting the elements of a `List` that satisfy a decidable predicate, and prove a closed-term instance by `rfl`.
3. Define a `structure Func.Rectangle` with width and height and a function `area`, and prove by `rfl` that the area of a concrete rectangle is the product.
4. Extend `Rectangle` to `Func.Box` with a depth field by `extends`, and define `volume` reaching the inherited fields.
5. Declare a `class Func.Default` with a `dflt` value, give instances for ℕ and for `List`, and define a function selecting the default by type.
6. Define `Func.leaves` counting the leaves of a `Func.Tree` and `Func.nodes` counting its branches, and state the law relating them, proving a closed-term instance by `rfl`.
7. Define `Func.replicate : ℕ → α → List α` by structural recursion and prove `replicate 0 x = []` by `rfl`.
8. Define a `match`-based `Func.isEmpty : List α → Bool` and prove `isEmpty [] = true` and `isEmpty (x :: xs) = false` by `rfl`.
9 (optional). Define an inductive type `Func.Rose` of rose trees whose children are a `List` of rose trees, and a function `Func.rsize` counting its nodes, noting the nested recursion through `List`.
10 (optional). Define a dependent `Func.Vec` of length-indexed lists and a total `Func.vhead : Vec α (n + 1) → α`, and evaluate it on a small vector, observing that the type rules out the empty case.

Progression runs from a finite enumeration and case analysis (1), through list and structure definitions (2 to 4), a type class (5), tree functions (6), simple recursions (7, 8), to the optional nested and dependent types (9, 10). None repeats an exercise of Lectures 1 to 5, and none is taken from the LoVe05 sheet, whose `reverseAccu`, `take`/`drop`, and `Term` problems are avoided.

## Slide deck outline

`Lectures/SlidesEn/Lecture06.lean` and `Lectures/SlidesPt/Lecture06.lean`, in the style of `SlidesEn/Lecture05.lean`, with `::::cols`/`:::col`, `{lbl}[…]`, and `lean`/`leanOutput`. Register the deck in `SlidesEnMain.lean` and `SlidesPtMain.lean` with `fileName := "lecture-6.en.html"`, `prevLink` to lecture 5, and update lecture 5's `nextLink`. Import `Lectures.SlidesEn.Lecture05` to reuse its datatypes, and keep the deck's Mathlib imports to `Mathlib.Data.Nat.Notation` and `Mathlib.Data.Int.Notation`. This lecture needs no `fix`/`assume` parsers, so the local parser section of the Lecture 5 deck is unnecessary here.

Give the two §6.5 and §6.6 heading pairs distinct wording so their slugs differ, since the slide build rejects duplicate slugs, as the Lecture 5 deck required for its two §5.3 slides.

Title slide. "Functional Programming" / "Programação Funcional", subtitle "Inductive types, recursion, structures, and type classes", the author line, the link back to the notes, and the LoVe chapter 5 attribution.

1. §6.1 Inductive types and their principles. Constructors, the recursor, `casesOn`, injectivity, disjointness, with `#print Nat` and `#check @Nat.rec`.
2. §6.1 Recursion and case analysis from the recursor. Pattern matching and `cases` as surface syntax for the recursor.
3. §6.2 Structural recursion. `fact`, `fib`, the equation compiler, structural decrease.
4. §6.2 Why termination. The original non-terminating axiom deriving `False`, and the rejected definition.
5. §6.3 Pattern matching expressions. `match` and `if` in a body, nested patterns, `Option`.
6. §6.4 Structures. `structure`, fields, projections, the anonymous constructor.
7. §6.4 Extending records. `extends`, record update, inherited fields.
8. §6.5 Type classes. `class`, `instance`, resolution with `[C α]`.
9. §6.5 The classes we already used. `Membership` of Lecture 2 and the associativity and commutativity instances of Lecture 4.
10. §6.6 Binary trees. `Tree`, `size`, `height`, `mirror` by recursion.
11. §6.6 Options, sums, and dependent vectors. `Option`, `α ⊕ β`, `Vec` read as a preview.
12. Worked example. Arithmetic expressions and their evaluation.
13. Worked example. A type class for size, with resolution.
14. Worked example. A record with an extension.
15. Worked example. Mirroring a tree, the law stated and deferred to Lecture 7.

Summary slide. Seven bullets. An inductive type is its constructors, and the kernel derives a recursor, `casesOn`, injectivity, and disjointness. Structural recursion terminates, and Lean admits only terminating definitions. `match` and `if` are pattern matching as expressions. A structure is a single-constructor inductive type with named fields. A type class is a structure of operations resolved by type, the mechanism behind the notation of the earlier lectures. Richer datatypes, trees, options, sums, and dependent vectors, follow the same schema. Lecture 7 derives structural induction from the recursor and proves the laws stated here. Closing line linking to the exercises in the notes.

## Risks and gotchas

**Name collisions with Mathlib and earlier lectures.** `Tree`, `map`, `zip`, `size`, `length`, `AExp` and similar are owned by Mathlib or defined in Lectures 3 to 5. Keep every Lecture 6 declaration inside `namespace Func`, and verify `Lectures/En.lean` and the four single-language targets build with Lecture 6 present. The root `Lectures` aggregate is no longer built, so the only collisions that matter are within one language tree.

**Recursor output byte for byte.** `#print Nat`, `#check @Nat.rec`, and `#check @List.rec` print long, version-sensitive types. Copy every output from the build, and prefer the shorter `#check` forms; if an output is unwieldy, describe it in prose rather than pinning fragile bytes, as the Lecture 5 termination error was kept out of an output block.

**The termination cautionary tale.** Deriving `False` from an `axiom` is sound to *display* but must stay inside its own block and never leak a usable `False` into the environment. Use `-keep` so the axiom and its consequence roll back, and confirm no later block sees them, so the rest of the lecture does not silently become inconsistent.

**Rejected definitions.** A non-structural definition that Lean rejects cannot go in an elaborated `lean` block without failing the build. Show it in a plain, non-elaborated block and describe the error in prose, exactly as Lecture 5 showed its rejected recursion.

**Structures and the anonymous constructor.** `{ field := … }`, `⟨…⟩`, and `{ r with … }` are three syntaxes for the same constructor. Show all three and state they are equal, and keep field names clear of Mathlib's `Prod` fields when reusing `Prod`.

**Type class instances leaking.** An `instance` persists globally and can change resolution elsewhere in the combined build. Keep instances inside `namespace Func`, name them, and confirm they do not shadow a Mathlib instance for a standard type. Prefer instances on `Func`-owned types.

**Dependent types kept to a preview.** `Vec` and length-indexed types are genuinely harder and belong to the later weeks. Keep §6.6's dependent example to a single read-only illustration with a pointer, and do not prove anything about `Vec` here.

**Induction deferred, not smuggled.** Lecture 6 must not prove `mirror (mirror t) = t`, the map laws, or `length_zip` by induction, since those are Lecture 7. Prove only closed-term instances by `rfl` or `decide`, and mark each general law as deferred, so the two lectures stay distinct.

**Bilingual delivery.** Write English first, then Portuguese with byte-identical code and translated prose. Portuguese: "tipo indutivo", "construtor", "recursor" glossed as "eliminador", "recursão estrutural", "terminação", "casamento de padrões", "estrutura" and "registro" for structure and record, "classe de tipos" and "instância", "árvore binária", "tipo dependente". Follow Lectures 3 to 5.

## Verified references

- A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 5, "Functional Programming". Structure and declarations taken from `lean/LoVe/LoVe05_FunctionalProgramming_Demo.lean` and `lean/LoVe/LoVe05_FunctionalProgramming_ExerciseSheet.lean` in the public repository; the PDF must be read in full during writing to confirm section prose.
- J. Blanchette et al., LoVe demo 5 and exercise sheet 5, in [lean-forward/logical_verification_2026](https://github.com/lean-forward/logical_verification_2026), read from the repository at planning time.
- J. Avigad, L. de Moura, S. Kong, S. Ullrich, *Theorem Proving in Lean 4*, the chapters on inductive types and on type classes (verify the chapter numbers in the current edition before a margin note).
- *The Lean Language Reference*, the sections on the `inductive`, `structure`, and `class` commands (verify the section titles before a margin note).
