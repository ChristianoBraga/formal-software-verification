/-
Slides for Lecture 1, generated from checked sources. Each
top-level section is one slide. All Lean code is elaborated at
build time and is identical to the code in the lecture notes
(`Lectures/En/Lecture01.lean`) where the two overlap. Derivation
trees are preformatted text in `tree` blocks.
-/

import VersoManual
import Lectures.Meta.SlideDeck

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Motivation and Propositional Logic" =>

Connectives, equivalences, natural deduction, and proofs in Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Open the lecture notes](../en/Lecture-1___-Motivation-and-Propositional-Logic/)

Based on [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL), chapter [1](https://djvelleman.github.io/HTPIwL/Chap1.html).

# Testing shows presence, not absence

* Software controls aircraft, medical devices, financial systems, and communication networks. Errors cost money and lives.

* Testing examines *finitely many* executions of a program that admits *infinitely many*.

> Program testing can be used to show the presence of bugs, but never to show their absence!

{cite}[E. W. Dijkstra, _Notes on Structured Programming_, EWD249, 1970.]

# The complementary route

* State a property of a program as a *mathematical proposition*.

* Prove that *every execution* satisfies it; the proof covers all inputs at once.

* A *proof assistant* checks every step against the rules of a formal logic and helps build the proof interactively.

* In current use: *Lean*, Rocq (formerly Coq), Isabelle/HOL, Agda. Landmarks: the *seL4* microkernel and the *CompCert* C compiler.

# Generated code

* Language models write a growing share of code. *Plausible is not the same as correct*; the failure mode is hallucination.

* A machine-checked proof is verified *independently of how the code was produced*, so wrong code cannot pass.

* The burden of correctness moves from *reading the code* to *writing the right specification*.

# Propositions and connectives

* A *proposition* is a declarative sentence that is either true or false. In Lean the type `Prop` classifies them.

* Connectives build compound propositions: `¬P`, `P ∧ Q`, `P ∨ Q`, `P → Q`, `P ↔ Q`.

* They are *truth-functional*. An implication is true whenever its antecedent is false, and disjunction is *inclusive*.

# §1.4 Logical equivalence

* A *valuation* assigns a truth value to each variable. A *tautology* is true under every valuation.

* A ≡ B when `A ↔ B` is a tautology, that is, the two agree under every valuation.

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
  * Material implication
  * P → Q ≡ ¬P ∨ Q
:::

The implication is called _material_ because its truth depends only on the truth values of P and Q, not on any connection of meaning between them (Russell, 1903).

# §1.4 A truth table verifies equivalence

Second De Morgan law: the columns for ¬(P ∨ Q) and ¬P ∧ ¬Q agree on all four valuations.

:::table +header
*
  * P
  * Q
  * P ∨ Q
  * ¬(P ∨ Q)
  * ¬P ∧ ¬Q
*
  * T
  * T
  * T
  * F
  * F
*
  * T
  * F
  * T
  * F
  * F
*
  * F
  * T
  * T
  * F
  * F
*
  * F
  * F
  * F
  * T
  * T
:::

Truth tables decide any propositional question, but grow *exponentially* in the number of variables and do not extend to the quantifiers of Lecture 2. Deduction rules scale and generalize.

# §1.5 Natural deduction: the rules of the game

* Each rule has *premises* above a line and a *conclusion* below, applied one step at a time (Gentzen, 1935).

* *Introduction* rules prove a connective; *elimination* rules use it. Some rules *discharge* an assumption, marked `[P]`.

```tree
   [P]
    ⋮
    Q                   P → Q    P
  ───────  →I          ─────────────  →E
   P → Q                     Q
```

# §1.5 Conjunction and disjunction

```tree
   P    Q              P ∧ Q            P ∧ Q
  ───────  ∧I         ───────  ∧E₁     ───────  ∧E₂
   P ∧ Q                 P                Q
```

```tree
     P                 Q                              [P]     [Q]
  ───────  ∨I₁      ───────  ∨I₂          P ∨ Q         ⋮       ⋮
   P ∨ Q             P ∨ Q                              R       R
                                        ──────────────────────────  ∨E
                                                     R
```

# §1.5 Negation and the classical rule

The constant ⊥ is absurdity, and ¬P abbreviates P → ⊥.

```tree
   [P]
    ⋮
    ⊥                  P    ¬P               ⊥
  ───────  ¬I         ─────────  ¬E        ─────  ⊥E
    ¬P                    ⊥                   C
```

The rules above are *constructive*. Classical logic adds one further rule, equivalently RAA or excluded middle.

```tree
   [¬P]
     ⋮
     ⊥
  ─────────  RAA               ───────────  EM
     P                          P ∨ ¬P
```

# §1.6 Natural deduction in Lean

A proof of a proposition is a *term* whose type is that proposition; an assumption is a variable of that type. Each rule builds or takes apart a term.

:::table +header
*
  * Rule
  * Lean term
  * Example
*
  * assumption
  * a hypothesis name
  * `h`
*
  * →I
  * `fun h => e`
  * `fun h => h`
*
  * →E
  * application
  * `f a`
*
  * ∧I
  * `⟨_, _⟩`
  * `⟨ha, hb⟩`
*
  * ∧E₁, ∧E₂
  * `.left`, `.right`
  * `h.left`, `h.right`
*
  * ∨I₁, ∨I₂
  * `Or.inl`, `Or.inr`
  * `Or.inl h`
*
  * ∨E
  * `Or.elim` or `match`
  * `h.elim f g`
*
  * ¬I
  * `fun h => e` into `False`
  * `fun hnP => hnP hP`
*
  * ¬E
  * application into `False`
  * `hnP hP`
*
  * ⊥E
  * `False.elim` or `absurd`
  * `False.elim h`
:::

# §1.6 Proof terms from the derivation

{exh}[1. P ∧ Q → Q ∧ P]

::::cols
:::col
```tree
   [P ∧ Q]        [P ∧ Q]
  ─────────∧E₂   ─────────∧E₁
      Q              P
    ────────────────────── ∧I
          Q ∧ P
  ────────────────────────── →I
       P ∧ Q → Q ∧ P
```
:::
:::col
```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.right, h.left⟩
```

* `fun h =>` is the →I discharging P ∧ Q

* `h.right` and `h.left` are ∧E₂ and ∧E₁

* `⟨_, _⟩` is the ∧I
:::
::::

{exh}[2. P → P ∨ Q]

::::cols
:::col
```tree
     [P]
   ───────  ∨I₁
    P ∨ Q
  ───────────  →I
   P → P ∨ Q
```
:::
:::col
```lean
example (P Q : Prop) : P → P ∨ Q :=
  fun h => Or.inl h
```

* `fun h =>` is the →I discharging P

* `Or.inl` is ∨I₁, choosing the left disjunct
:::
::::

{exh}[3. P → ¬¬P]

::::cols
:::col
```tree
   [¬P]   [P]
  ────────────  ¬E
       ⊥
    ────────  ¬I
       ¬¬P
   ─────────────  →I
     P → ¬¬P
```
:::
:::col
```lean
example (P : Prop) : P → ¬¬P :=
  fun hP hnP => hnP hP
```

* `fun hP =>` is the →I discharging P

* `fun hnP =>` is the ¬I discharging ¬P, since ¬¬P is ¬P → False

* `hnP hP` is the ¬E, applying ¬P to P to reach ⊥
:::
::::

# §1.7 Proving with tactics

* A *tactic* transforms the proof state, the goal together with the hypotheses in scope, one step at a time.

* `by` enters tactic mode, and the tactic sequence elaborates to a proof term, so a tactic proof and a term proof yield the *same object*.

* `exact` closes a goal with a term; a *backward* step (`apply`) reduces the goal, a *forward* step (`have`) adds a hypothesis.

```lean
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP
```

# §1.7 Tactics per connective

:::table +header
*
  * Connective
  * Introduce
  * Eliminate
*
  * →
  * `intro`
  * `apply`, application
*
  * ∧
  * `constructor`
  * `.left`, `.right`, `cases`
*
  * ∨
  * `Or.inl`, `Or.inr`
  * `cases`
*
  * ¬
  * `intro`
  * `apply` to reach `False`
*
  * ⊥
  * (none)
  * `exact False.elim`
:::

::::cols
:::col
```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```
:::
:::col
```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```
:::
::::

Introduction tactics build the goal; elimination tactics use a hypothesis. Classical reasoning adds `Classical.byContradiction` and `Classical.em`, needed for double negation elimination.

# §1.7 Proving with tactics, as a board game

A tactic proof plays out like a board game. Each element of the game names a precise part of the proof.

:::table +header
*
  * Board game
  * Tactic proof
*
  * The board
  * the proof state, the goal together with the hypotheses in scope
*
  * Your pieces
  * the hypotheses you may use
*
  * A move
  * a tactic (`intro`, `apply`, `exact`, `cases`, `constructor`, `have`)
*
  * Splitting the board
  * a tactic that opens several goals; each must be won
*
  * Two directions
  * `apply` plays backward from the goal, `have` plays forward from your pieces
*
  * The rulebook
  * the introduction and elimination rules of natural deduction
*
  * Winning
  * every goal closed, and Lean's kernel checks the final proof term
:::

# §1.8 Worked example: P ∧ Q → P

::::cols
:::col
{lbl}[Derivation]

```tree
   [P ∧ Q]
  ──────────  ∧E₁
      P
  ────────────  →I
   P ∧ Q → P
```
:::
:::col
{lbl}[Term mode]

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

* `fun h =>` is the →I discharging P ∧ Q

* `h.left` is ∧E₁, the left projection

{lbl}[Tactic mode]

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

* `intro h` is the →I discharging P ∧ Q

* `exact h.left` closes the goal by ∧E₁
:::
::::

# §1.8 Worked example: ⊥ → P

::::cols
:::col
{lbl}[Derivation]

```tree
   [⊥]
  ──────  ⊥E
    P
  ────────  →I
   ⊥ → P
```
:::
:::col
{lbl}[Term mode]

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

* `fun h =>` is the →I discharging ⊥

* `False.elim h` is ⊥E, giving any P

{lbl}[Tactic mode]

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

* `intro h` is the →I discharging ⊥

* `exact False.elim h` closes the goal by ⊥E
:::
::::

# §1.8 Worked example: (P → Q) ∧ P → Q

::::cols
:::col
{lbl}[Derivation]

```tree
   [(P→Q)∧P]           [(P→Q)∧P]
  ───────────── ∧E₁    ───────────── ∧E₂
      P → Q                  P
    ────────────────────────────── →E
                 Q
   ──────────────────────────────── →I
        (P → Q) ∧ P → Q
```
:::
:::col
{lbl}[Term mode]

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

* `fun h =>` is the →I discharging (P → Q) ∧ P

* `h.left` and `h.right` are ∧E₁ and ∧E₂

* the application `h.left h.right` is →E, modus ponens

{lbl}[Tactic mode]

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

* `intro h` is the →I discharging (P → Q) ∧ P

* `apply h.left` reduces the goal to P by →E

* `exact h.right` supplies P by ∧E₂
:::
::::

# §1.8 Worked example: P ∨ Q → Q ∨ P

::::cols
:::col
{lbl}[Derivation]

```tree
               [P]           [Q]
   [P ∨ Q]    ─────── ∨I₂   ─────── ∨I₁
              Q ∨ P         Q ∨ P
  ───────────────────────────────────── ∨E
             Q ∨ P
  ──────────────────────  →I
   P ∨ Q → Q ∨ P
```
:::
:::col
{lbl}[Term mode]

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

* `fun h =>` is the →I discharging P ∨ Q

* `h.elim` is ∨E, one branch per disjunct

* `Or.inr` and `Or.inl` are ∨I, swapping the disjuncts

{lbl}[Tactic mode]

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

* `intro h` is the →I discharging P ∨ Q

* `cases h` is ∨E, splitting into the two disjuncts

* each branch closes with `Or.inr` / `Or.inl` (∨I)
:::
::::

# §1.8 Worked example: ¬¬P → P (classical)

::::cols
:::col
{lbl}[Derivation]

```tree
   [¬P]  [¬¬P]
  ──────────────  ¬E
        ⊥
    ──────────  RAA
        P
   ───────────────  →I
     ¬¬P → P
```
:::
:::col
{lbl}[Term mode]

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

* `fun h =>` is the →I discharging ¬¬P

* `Classical.byContradiction` is the classical rule (RAA)

* `fun hnP => h hnP` derives ⊥ from ¬P and ¬¬P by ¬E

{lbl}[Tactic mode]

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

* `intro h` is the →I discharging ¬¬P

* `apply Classical.byContradiction` invokes RAA

* `intro hnP` then `exact h hnP` derive ⊥ by ¬E
:::
::::

# Summary

* A *proposition* is classified by `Prop`; the connectives ¬, ∧, ∨, →, ↔ build compound propositions.

* Truth tables decide propositional questions but grow exponentially; *natural deduction* applies rules one step at a time and generalizes.

* Each connective has *introduction* and *elimination* rules; some rules discharge assumptions.

* A proof is a *term* whose type is the proposition (Curry-Howard): `fun h => e` for →I, application for →E, `⟨_, _⟩` for ∧I, `Or.inl`/`Or.inr` for ∨I.

* *Tactics* transform the proof state: `intro`, `exact`, `apply`, `cases`, `constructor`, `have`; `by` elaborates them to the same proof term.

* *Classical reasoning* adds `Classical.byContradiction` and `Classical.em`, needed for ¬¬P → P and one De Morgan law.

Exercises: see the [lecture notes](../en/Lecture-1___-Motivation-and-Propositional-Logic/).
