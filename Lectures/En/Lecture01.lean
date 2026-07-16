import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lecture 1: Motivation and Propositional Logic" =>

%%%
tag := "lecture-1"
%%%

This lecture motivates formal software verification and reviews propositional logic, following chapter 1 of [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). It presents the connectives, the classical equivalences, and the first structured proofs in Lean.

# Why Verify Software Formally?

Software controls aircraft, medical devices, financial systems, and communication networks. Errors in such systems cost money and lives. The standard way to find errors is testing, and testing examines finitely many executions of a program that admits infinitely many. Dijkstra stated the limitation precisely.{margin}[E. W. Dijkstra, *Notes on Structured Programming*, EWD249, Technological University Eindhoven, 1970.]

> Program testing can be used to show the presence of bugs, but never to show their absence!

Formal verification takes the complementary route. We state a property of a program as a mathematical proposition and prove that every execution satisfies it. The proof covers all inputs at once, which no finite test suite achieves.

Proofs about real programs grow large, so we delegate their checking to a machine. A *proof assistant* is a program that checks every step of a proof with respect to the rules of a formal logic, and that helps the user construct the proof interactively. Lean, Rocq (formerly Coq), Isabelle/HOL, and Agda are proof assistants in current use. Landmark results include the verification of the seL4 operating-system microkernel{margin}[G. Klein et al., *seL4: Formal Verification of an OS Kernel*, Proceedings of SOSP 2009, pp. 207–220.] and of the CompCert optimizing C compiler.{margin}[X. Leroy, *Formal Verification of a Realistic Compiler*, Communications of the ACM 52(7), 2009, pp. 107–115.]

Language models now write a growing share of code. A model produces plausible text, and plausible is not the same as correct. Generated code can invoke functions that do not exist, handle only the cases that its prompt suggests, or drift from the stated requirement in ways that survive code review. The literature calls this failure mode hallucination.

Formal verification, in particular when automated, changes how we can trust such code.{margin}[L. de Moura, [*The Lean Programming Language and Theorem Prover*](https://leodemoura.github.io/static/etaps2026/), ETAPS 2026.] When generated code arrives with a machine-checked proof that it satisfies its specification, the proof assistant checks the proof independently of how the code came to be, so hallucinated or simply wrong code cannot pass. The burden of correctness moves from reading the code to writing the right specification. The techniques of this course apply unchanged to generated code, and the automation of the final lectures, with the `mvcgen` tactic, points toward verification at the pace of code generation.

In this course we use [Lean](https://lean-lang.org). Lean is at once a programming language and a proof assistant, so we can write a program and prove its properties in the same system. Lectures 1 and 2 review classical logic while introducing Lean's proof language, following HTPIwL. Lectures 3 to 8 follow [LoVe](https://github.com/lean-forward/logical_verification_2026) through interactive proving, functional programming, and inductive predicates. The final block treats the semantics of an imperative language, Hoare logic, and practical verification with the `mvcgen` tactic.

# Propositions

A *proposition* is a declarative sentence that is either true or false. "7 is prime" and "every even number greater than 2 is the sum of two primes" are propositions. "Close the door" and "x is even" are not, the first because it commands rather than states, the second because its truth depends on the unbound variable x.

In Lean, the type `Prop` classifies propositions.

```lean (name := checkTrue)
#check True
```
```leanOutput checkTrue
True : Prop
```

We write P, Q, R for *propositional variables*, which stand for arbitrary propositions.

# Connectives

Connectives build compound propositions from simpler ones.

:::table +header
*
  * Symbol
  * Name
  * Reading
*
  * ¬P
  * negation
  * not P
*
  * P ∧ Q
  * conjunction
  * P and Q
*
  * P ∨ Q
  * disjunction
  * P or Q
*
  * P → Q
  * implication
  * if P then Q
*
  * P ↔ Q
  * biconditional
  * P if and only if Q
:::

The truth value of a compound proposition depends only on the truth values of its parts. The table below defines the five connectives, with T for true and F for false.

:::table +header
*
  * P
  * Q
  * ¬P
  * P ∧ Q
  * P ∨ Q
  * P → Q
  * P ↔ Q
*
  * T
  * T
  * F
  * T
  * T
  * T
  * T
*
  * T
  * F
  * F
  * F
  * T
  * F
  * F
*
  * F
  * T
  * T
  * F
  * T
  * T
  * F
*
  * F
  * F
  * T
  * F
  * F
  * T
  * T
:::

Two rows of the implication column deserve attention. When P is false, P → Q is true regardless of Q. An implication claims nothing about cases where its antecedent fails, so those cases cannot refute it. Disjunction is *inclusive*, so P ∨ Q is true when both disjuncts are.

# Logical Equivalence

A *valuation* assigns a truth value to each propositional variable. A proposition is a *tautology* when it is true under every valuation. Two propositions A and B are *logically equivalent*, written A ≡ B, when they have the same truth value under every valuation, that is, when A ↔ B is a tautology.

The classical equivalences below appear constantly in proofs.

:::table +header
*
  * Name
  * Equivalence
*
  * De Morgan
  * ¬(P ∧ Q) ≡ ¬P ∨ ¬Q
*
  * De Morgan
  * ¬(P ∨ Q) ≡ ¬P ∧ ¬Q
*
  * Double negation
  * ¬¬P ≡ P
*
  * Contrapositive
  * P → Q ≡ ¬Q → ¬P
*
  * {hover "The implication is called material because its truth depends only on the truth values of P and Q, and not on any connection of meaning or causality between them. The term comes from Russell, The Principles of Mathematics, 1903."}[Material implication]
  * P → Q ≡ ¬P ∨ Q
:::

A truth table verifies each equivalence. For the second De Morgan law, the columns for ¬(P ∨ Q) and ¬P ∧ ¬Q agree on all four valuations.

:::table +header
*
  * P
  * Q
  * P ∨ Q
  * ¬(P ∨ Q)
  * ¬P
  * ¬Q
  * ¬P ∧ ¬Q
*
  * T
  * T
  * T
  * F
  * F
  * F
  * F
*
  * T
  * F
  * T
  * F
  * F
  * T
  * F
*
  * F
  * T
  * T
  * F
  * T
  * F
  * F
*
  * F
  * F
  * F
  * T
  * T
  * T
  * T
:::

Truth tables decide any propositional question, but their size grows exponentially in the number of variables, and they do not extend to the quantifiers of Lecture 2. Deduction rules, applied one step at a time, scale and generalize. The rest of this lecture develops such proofs in Lean.

# First Proofs in Lean

In Lean, we state a proposition and prove it in one declaration. The `example` keyword introduces an anonymous statement, and `theorem` introduces a named one. Hypotheses appear before the colon as named assumptions, and the proposition to prove, the *goal*, appears after it.

The simplest proof uses a hypothesis directly.

```lean
example (P : Prop) (h : P) : P := h
```

Here `h` names the assumption that P holds, and the proof is `h` itself. A proof of a proposition is a term whose type is that proposition. Lecture 3 develops this correspondence between propositions and types.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980.]

Most proofs use *tactics*, commands that transform the goal step by step. The keyword `by` enters tactic mode. Each connective comes with rules to *introduce* it, proving a goal of that shape, and rules to *eliminate* it, using a hypothesis of that shape.

## Implication

The tactic `intro` introduces an implication. To prove P → Q, assume P under a chosen name and prove Q.

```lean
example (P Q : Prop) (hQ : Q) : P → Q := by
  intro _hP
  exact hQ
```

The tactic `exact` closes the goal with a term that proves it. To use an implication, apply it to a proof of its antecedent. A hypothesis hPQ of type P → Q is a function from proofs of P to proofs of Q, so `hPQ hP` proves Q. This is the rule of *modus ponens*.

```lean
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := hPQ hP
```

The tactic `apply` uses the same rule in the backward direction. Applying hPQ to the goal Q leaves P as the new goal.

```lean
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP
```

The tactic `have` reasons forward, adding a new hypothesis derived from the current ones, and `show` states the current goal explicitly. Both make proofs read like structured mathematical arguments.

```lean
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R)
    (hP : P) : R := by
  have hQ : Q := hPQ hP
  show R
  exact hQR hQ
```

## Conjunction

To prove P ∧ Q, prove both parts. The tactic `constructor` splits the goal in two, and the bullet `·` delimits the proof of each.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left
```

To use a conjunction, project its parts with `.left` and `.right`. The anonymous constructor `⟨_, _⟩` builds the pair directly, giving a term-style proof.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩
```

## Disjunction

To prove P ∨ Q, choose a side. `Or.inl` proves it from P, and `Or.inr` proves it from Q. To use a disjunction, reason by cases. The tactic `cases` produces one goal per disjunct.

```lean
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

## Negation

In Lean, ¬P is *defined* as P → False, where `False` is the proposition with no proof. A proof of ¬P is a function that turns any proof of P into a proof of `False`.

```lean
example (P : Prop) (hP : P) (hnP : ¬P) : False := hnP hP
```

Every tactic for implication therefore works for negation. The contrapositive direction below needs only `intro` and application.

```lean
theorem contrapositive (P Q : Prop) (hPQ : P → Q) :
    ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (hPQ hP)
```

Introducing double negation is equally direct.

```lean
example (P : Prop) (hP : P) : ¬¬P := fun hnP => hnP hP
```

The second De Morgan law combines the rules seen so far. The tactic `constructor` also introduces a biconditional, splitting it into the two implications.

```lean
theorem deMorgan_or (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP
      exact h (Or.inl hP)
    · intro hQ
      exact h (Or.inr hQ)
  · intro h hPQ
    cases hPQ with
    | inl hP => exact h.left hP
    | inr hQ => exact h.right hQ
```

## Classical Reasoning

The rules used so far are *constructive*. Two principles of classical logic do not follow from them, the law of excluded middle and the elimination of double negation. Lean provides both in the `Classical` namespace.

```lean (name := checkEm)
#check Classical.em
```
```leanOutput checkEm
Classical.em (p : Prop) : p ∨ ¬p
```

`Classical.byContradiction` proves P from a proof that ¬P is impossible. With it, double negation elimination is one application away.

```lean
theorem not_not_elim (P : Prop) (h : ¬¬P) : P := by
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

The first De Morgan law requires classical reasoning. A case analysis on `Classical.em P` decides which disjunct to prove.

```lean
theorem deMorgan_and (P Q : Prop) : ¬(P ∧ Q) → ¬P ∨ ¬Q := by
  intro h
  cases Classical.em P with
  | inl hP => exact Or.inr (fun hQ => h ⟨hP, hQ⟩)
  | inr hnP => exact Or.inl hnP
```

# Exercises

Prove each statement in Lean, replacing `sorry` with a proof. Download the exercise file [`Lecture01.lean`](../../example-code/Lectures/En/Lecture01.lean) and open it in VS Code.

```savedComment
Exercises for Lecture 1: Motivation and Propositional Logic.
Replace each `sorry` with a proof.
```

Exercise 1. Implication composes.

```savedLean
theorem exercise1 (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry
```

Exercise 2. Conjunction distributes over disjunction.

```savedLean
theorem exercise2 (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

Exercise 3. Disjunction associates.

```savedLean
theorem exercise3 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry
```

Exercise 4. This direction of the first De Morgan law is constructive.

```savedLean
theorem exercise4 (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry
```

Exercise 5. Peirce's law.{margin}[C. S. Peirce, *On the Algebra of Logic: A Contribution to the Philosophy of Notation*, American Journal of Mathematics 7(2), 1885, pp. 180–196.] It requires classical reasoning; consider a case analysis on `Classical.em P`.

```savedLean
theorem exercise5 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry
```
