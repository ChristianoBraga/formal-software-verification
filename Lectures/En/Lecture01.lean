import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Figure
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lecture 1: Motivation and Propositional Logic" =>

%%%
tag := "lecture-1"
%%%

```lean -show
namespace Lecture1
```

This lecture motivates formal software verification and reviews propositional logic, following chapter 1 of [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). It presents the connectives, the classical equivalences, the natural deduction rules, their encoding in Lean as proof terms, and proofs with tactics.

*This lecture is also available as [presentation slides](../slides/lecture-1.en.html).*

# Why Verify Software Formally?

Software controls aircraft, medical devices, financial systems, and communication networks. Errors in such systems cost money and lives. The standard way to find errors is testing, and testing examines finitely many executions of a program that admits infinitely many. Dijkstra stated the limitation precisely.{margin}[E. W. Dijkstra, *Notes on Structured Programming*, EWD249, Technological University Eindhoven, 1970.]

> Program testing can be used to show the presence of bugs, but never to show their absence!

Formal verification takes the complementary route. We state a property of a program as a mathematical proposition and prove that every execution satisfies it. The proof covers all inputs at once, which no finite test suite achieves.

Proofs about real programs grow large, so we delegate their checking to a machine. A *proof assistant* is a program that checks every step of a proof with respect to the rules of a formal logic, and that helps the user construct the proof interactively. Lean, Rocq (formerly Coq), Isabelle/HOL, and Agda are proof assistants in current use. Landmark results include the verification of the seL4 operating-system microkernel{margin}[G. Klein et al., *seL4: Formal Verification of an OS Kernel*, Proceedings of SOSP 2009, pp. 207–220.] and of the CompCert optimizing C compiler.{margin}[X. Leroy, *Formal Verification of a Realistic Compiler*, Communications of the ACM 52(7), 2009, pp. 107–115.]

Language models now write a growing share of code. A model produces plausible text, and plausible is not the same as correct. Generated code can invoke functions that do not exist, handle only the cases that its prompt suggests, or drift from the stated requirement in ways that survive code review. The literature calls this failure mode hallucination.

Formal verification, in particular when automated, changes how we can trust such code.{margin}[L. de Moura, [*The Lean Programming Language and Theorem Prover*](https://leodemoura.github.io/static/etaps2026/), ETAPS 2026.] When generated code arrives with a machine-checked proof that it satisfies its specification, the proof assistant checks the proof independently of how the code came to be, so hallucinated or simply wrong code cannot pass. The burden of correctness moves from reading the code to writing the right specification. The techniques of this course apply unchanged to generated code, and the automation of the final lectures, with the `mvcgen` tactic, points toward verification at the pace of code generation.

In this course we use [Lean](https://lean-lang.org). Lean is at once a programming language and a proof assistant, so we can write a program and prove its properties in the same system. Lectures 1 and 2 review classical logic while introducing Lean's proof language, following HTPIwL. Lectures 3 to 8 follow [LoVe](https://github.com/lean-forward/logical_verification_2026){margin}[LoVe collects the Lean files that accompany the *Hitchhiker's Guide to Logical Verification*, 2026 edition. Its support library `LoVelib` is not published as a Lake package, so these notes keep a copy of it under `Lectures/LoVe/`, together with its BSD 3-clause licence. The copy is verbatim except for the attribute `@[reducible]` on `Set.PartialOrder`, which the definition linter of Lean v4.32.0 requires and the original, written for Lean v4.24.0, does not carry.] through interactive proving, functional programming, and inductive predicates. The final block treats the semantics of an imperative language, Hoare logic, and practical verification with the `mvcgen` tactic.

{figref "fig-lean-components"}[Figure 1.1] shows the components of Lean that the course exercises. The parser reads the text of a `.lean` file into syntax trees, and the macro expander unfolds the notations that libraries and user code define. The elaborator turns those trees into terms of the core language, and it does the work that the surface syntax leaves implicit, inferring omitted arguments, resolving type class instances, and running tactics. Tactics are themselves Lean programs, and they build terms rather than certificates of their own correctness. The kernel rechecks the finished term with respect to the rules of dependent type theory, so a tactic that produces a wrong term fails here, and only the kernel belongs to the trusted base. The compiler takes the same terms to native code, which is what `#eval` runs. The libraries supply notations, instances and lemmas to every stage above the kernel.

{figureAnchor "fig-lean-components"}[![Main components of Lean: a .lean file goes through the parser and macro expander to the elaborator, which draws on tactics and libraries and produces core terms; the kernel checks those terms and the compiler turns them into native code](lean-components.svg)]

*Figure 1.1. The main components of Lean.*

{figref "fig-verifier-architecture"}[Figure 1.2] shows the architecture of the verifier that the course builds. A program and its specification form a Hoare triple. The big-step operational semantics gives the triple its meaning. The `mvcgen` tactic generates the verification conditions, which are purely logical goals. Tactic proofs discharge them, and the Lean kernel checks every proof.

{figureAnchor "fig-verifier-architecture"}[![Architecture of a program verifier in Lean: a program and a specification form a Hoare triple, whose meaning comes from the big-step semantics; the mvcgen tactic generates verification conditions, tactic proofs discharge them, and the Lean kernel checks every proof](verifier-architecture.svg)]

*Figure 1.2. Architecture of a program verifier in Lean.*

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

## Examples

Each equivalence below is verified by a truth table. Two propositions are equivalent when their final columns agree in every row, and a tautology has a column that is true in every row.

Example 1. Double negation returns the original proposition.

:::table +header
*
  * P
  * ¬P
  * ¬¬P
*
  * T
  * F
  * T
*
  * F
  * T
  * F
:::

Example 2. The excluded middle P ∨ ¬P is a tautology.

:::table +header
*
  * P
  * ¬P
  * P ∨ ¬P
*
  * T
  * F
  * T
*
  * F
  * T
  * T
:::

Example 3. Non-contradiction ¬(P ∧ ¬P) is a tautology.

:::table +header
*
  * P
  * ¬P
  * P ∧ ¬P
  * ¬(P ∧ ¬P)
*
  * T
  * F
  * F
  * T
*
  * F
  * T
  * F
  * T
:::

Example 4. The first De Morgan law.

:::table +header
*
  * P
  * Q
  * P ∧ Q
  * ¬(P ∧ Q)
  * ¬P
  * ¬Q
  * ¬P ∨ ¬Q
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
  * F
  * T
  * F
  * T
  * T
*
  * F
  * T
  * F
  * T
  * T
  * F
  * T
*
  * F
  * F
  * F
  * T
  * T
  * T
  * T
:::

Example 5. Disjunction commutes.

:::table +header
*
  * P
  * Q
  * P ∨ Q
  * Q ∨ P
*
  * T
  * T
  * T
  * T
*
  * T
  * F
  * T
  * T
*
  * F
  * T
  * T
  * T
*
  * F
  * F
  * F
  * F
:::

Example 6. Disjunction is idempotent.

:::table +header
*
  * P
  * P ∨ P
*
  * T
  * T
*
  * F
  * F
:::

Example 7. The contrapositive.

:::table +header
*
  * P
  * Q
  * P → Q
  * ¬Q
  * ¬P
  * ¬Q → ¬P
*
  * T
  * T
  * T
  * F
  * F
  * T
*
  * T
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
*
  * F
  * F
  * T
  * T
  * T
  * T
:::

Example 8. Material implication.

:::table +header
*
  * P
  * Q
  * P → Q
  * ¬P
  * ¬P ∨ Q
*
  * T
  * T
  * T
  * F
  * T
*
  * T
  * F
  * F
  * F
  * F
*
  * F
  * T
  * T
  * T
  * T
*
  * F
  * F
  * T
  * T
  * T
:::

Example 9. The biconditional is the conjunction of its two implications.

:::table +header
*
  * P
  * Q
  * P ↔ Q
  * P → Q
  * Q → P
  * (P → Q) ∧ (Q → P)
*
  * T
  * T
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
*
  * F
  * T
  * F
  * T
  * F
  * F
*
  * F
  * F
  * T
  * T
  * T
  * T
:::

Example 10. The negation of an implication.

:::table +header
*
  * P
  * Q
  * P → Q
  * ¬(P → Q)
  * ¬Q
  * P ∧ ¬Q
*
  * T
  * T
  * T
  * F
  * F
  * F
*
  * T
  * F
  * F
  * T
  * T
  * T
*
  * F
  * T
  * T
  * F
  * F
  * F
*
  * F
  * F
  * T
  * F
  * T
  * F
:::

Truth tables decide any propositional question, but their size grows exponentially in the number of variables, and they do not extend to the quantifiers of Lecture 2. Deduction rules, applied one step at a time, scale and generalize. The next section presents them, and the rest of the lecture develops the corresponding proofs in Lean.

# Natural Deduction

Natural deduction derives a proposition from assumptions by rules that mirror how mathematicians argue.{margin}[G. Gentzen, *Untersuchungen über das logische Schließen. I*, Mathematische Zeitschrift 39, 1935, pp. 176–210.] Gerhard Gentzen introduced the system in 1935, and Dag Prawitz gave its proof-theoretic study.{margin}[D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*, Almqvist & Wiksell, Stockholm, 1965.] Each rule has zero or more *premises* above a horizontal line and one *conclusion* below it, and it reads as follows. Given derivations of the premises, the line licenses the conclusion.

A derivation stands on *assumptions*. Some rules *discharge* an assumption, so a proposition assumed at the top of a subderivation no longer counts as an open assumption once the rule fires. We mark a discharged assumption with brackets, as `[P]`, and write a vertical ⋮ for the intervening derivation. A proposition proved with no open assumptions is a *theorem*.

Each connective comes with *introduction* rules, which prove a proposition of that shape, and *elimination* rules, which use a proposition of that shape. This introduction and elimination discipline is exactly the structure that Lean's tactics follow in the next section.

## Implication

To introduce P → Q, assume P, derive Q, and discharge the assumption. To eliminate it, apply an implication to a proof of its antecedent, the rule of *modus ponens*.

```
   [P]
    ⋮
    Q                   P → Q    P
  ───────  →I          ─────────────  →E
   P → Q                     Q
```

## Conjunction

To introduce P ∧ Q, prove both conjuncts. Elimination projects either conjunct.

```
   P    Q              P ∧ Q            P ∧ Q
  ───────  ∧I         ───────  ∧E₁     ───────  ∧E₂
   P ∧ Q                 P                Q
```

## Disjunction

To introduce P ∨ Q, prove one disjunct. To eliminate it, prove a common conclusion R from each disjunct in turn, discharging the disjunct assumed in each branch.

```
     P                 Q                              [P]     [Q]
  ───────  ∨I₁      ───────  ∨I₂          P ∨ Q         ⋮       ⋮
   P ∨ Q             P ∨ Q                              R       R
                                        ──────────────────────────  ∨E
                                                     R
```

## Negation and Falsehood

The constant ⊥ is the *absurdity*, the proposition with no introduction rule. Negation abbreviates ¬P as P → ⊥, so the rules for negation are the implication rules read at ⊥. To introduce ¬P, assume P, derive ⊥, and discharge the assumption. To eliminate it, a proof of P and a proof of ¬P together yield ⊥. From ⊥, elimination proves any proposition C, the principle *ex falso quodlibet*.

```
   [P]
    ⋮
    ⊥                  P    ¬P               ⊥
  ───────  ¬I         ─────────  ¬E        ─────  ⊥E
    ¬P                    ⊥                   C
```

## Constructive and Classical Rules

The rules above are *constructive*, so a derivation of a disjunction exhibits which disjunct holds and a derivation of an existential exhibits a witness. They do not prove the law of excluded middle P ∨ ¬P or reduce a double negation ¬¬P to P. *Classical* natural deduction adds one further rule, equivalently the excluded middle or *reductio ad absurdum*, which discharges the assumption ¬P upon deriving ⊥.

```
   [¬P]
     ⋮
     ⊥
  ─────────  RAA               ───────────  EM
     P                          P ∨ ¬P
```

The De Morgan law ¬(P ∧ Q) ≡ ¬P ∨ ¬Q and Peirce's law depend on this rule, as the Lean proofs below make precise.

## Examples

The derivations below prove propositional theorems with the rules above. A numeral marks each discharged assumption together with the rule that discharges it, and each tree reads from its leaves down to its root.

Example 1. Implication is reflexive.

```
   [P]¹
  ──────  →I,¹
   P → P
```

Example 2. A conjunction entails each conjunct.

```
   [P ∧ Q]¹
  ──────────  ∧E₁
      P
  ────────────  →I,¹
   P ∧ Q → P
```

Example 3. A disjunct entails the disjunction.

```
     [P]¹
   ────────  ∨I₁
    P ∨ Q
  ────────────  →I,¹
   P → P ∨ Q
```

Example 4. Anything follows from absurdity, the principle *ex falso quodlibet*.

```
   [⊥]¹
  ──────  ⊥E
    P
  ────────  →I,¹
   ⊥ → P
```

Example 5. Modus ponens, packaged as a single implication.

```
   [(P→Q)∧P]¹            [(P→Q)∧P]¹
  ───────────── ∧E₁     ───────────── ∧E₂
      P → Q                   P
     ───────────────────────────── →E
                  Q
   ─────────────────────────────────── →I,¹
          (P → Q) ∧ P → Q
```

Example 6. Disjunction commutes.

```
                [P]²           [Q]²
   [P ∨ Q]¹    ─────── ∨I₂    ─────── ∨I₁
               Q ∨ P          Q ∨ P
  ────────────────────────────────────── ∨E,²
              Q ∨ P
  ─────────────────────── →I,¹
   P ∨ Q → Q ∨ P
```

Example 7. Double negation introduction.

```
    [¬P]²   [P]¹
   ────────────── ¬E
         ⊥
     ────────── ¬I,²
        ¬¬P
    ────────────── →I,¹
      P → ¬¬P
```

Example 8. Contraposition.

```
               [P→Q]¹  [P]³
   [¬Q]²      ─────────────── →E
                    Q
  ────────────────────── ¬E
           ⊥
     ──────────── ¬I,³
          ¬P
    ───────────────── →I,²
      ¬Q → ¬P
  ──────────────────────────── →I,¹
   (P → Q) → (¬Q → ¬P)
```

Example 9. Double negation elimination, which needs the classical rule.

```
    [¬P]²  [¬¬P]¹
   ──────────────── ¬E
          ⊥
     ─────────── RAA,²
          P
    ─────────────── →I,¹
     ¬¬P → P
```

Example 10. Currying turns a conjunctive hypothesis into nested implications.

```
                      [P]²  [Q]³
   [P∧Q→R]¹          ──────────── ∧I
                        P ∧ Q
      ────────────────────────── →E
                  R
               ─────────── →I,³
                Q → R
           ───────────────── →I,²
            P → (Q → R)
    ───────────────────────────────── →I,¹
     (P ∧ Q → R) → (P → (Q → R))
```

# Natural Deduction in Lean

In Lean, we state a proposition and prove it in one declaration. The `example` keyword introduces an anonymous statement, and `theorem` introduces a named one. Hypotheses appear before the colon as named assumptions, and the proposition to prove, the *goal*, appears after it.

Lean encodes natural deduction directly. A proof of a proposition is a *term* whose type is that proposition, an open assumption is a variable of that type, and each deduction rule becomes a way to build or take apart such a term. The simplest proof uses an assumption directly, the assumption rule of natural deduction.

```lean
example (P : Prop) (h : P) : P := h
```

Here `h` names the assumption that P holds, and the proof is `h` itself. Lecture 3 develops this correspondence between propositions and types.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980.]

The table maps each rule of the previous section to the Lean term that realizes it. An introduction rule builds a term, and an elimination rule takes one apart.

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

Because ¬P abbreviates P → False, the negation rules reuse the terms for implication. To see the correspondence on a full derivation, take P ∧ Q → Q ∧ P. It discharges the assumption P ∧ Q, projects each conjunct, and reassembles them in the opposite order.

```
        [P ∧ Q]            [P ∧ Q]
       ─────────  ∧E₂     ─────────  ∧E₁
           Q                  P
         ───────────────────────────  ∧I
                   Q ∧ P
        ─────────────────────────────  →I
              P ∧ Q → Q ∧ P
```

The Lean term follows the derivation step for step. The abstraction `fun h => …` is the →I that discharges P ∧ Q, the projections `h.right` and `h.left` are the two ∧E steps, and the pair `⟨_, _⟩` is the ∧I.

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.right, h.left⟩
```

## Examples

The proofs below encode the ten derivations of the previous section as proof terms. Each term mirrors its derivation, with an introduction rule building a term and an elimination rule taking one apart.

Example 1. Implication is reflexive.

```lean
example (P : Prop) : P → P :=
  fun h => h
```

Example 2. A conjunction entails each conjunct.

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

Example 3. A disjunct entails the disjunction.

```lean
example (P Q : Prop) : P → P ∨ Q :=
  fun h => Or.inl h
```

Example 4. Anything follows from absurdity.

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

Example 5. Modus ponens, packaged as a single implication.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

Example 6. Disjunction commutes.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

Example 7. Double negation introduction.

```lean
example (P : Prop) : P → ¬¬P :=
  fun hP hnP => hnP hP
```

Example 8. Contraposition.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  fun hPQ hnQ hP => hnQ (hPQ hP)
```

Example 9. Double negation elimination, which needs classical reasoning.

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

Example 10. Currying turns a conjunctive hypothesis into nested implications.

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → (Q → R)) :=
  fun h hP hQ => h ⟨hP, hQ⟩
```

# Proving with Tactics

Writing proof terms by hand becomes impractical as proofs grow. A *tactic* is a command that transforms the *proof state*, the goal together with the hypotheses in scope, one step at a time. The keyword `by` enters tactic mode, and Lean elaborates the tactic sequence into a proof term, so a tactic proof and a term proof yield the same underlying object.

The tactic `exact` closes a goal with a term that proves it, which recovers the term-mode proof above.

```lean
example (P : Prop) (h : P) : P := by
  exact h
```

Tactics reason in two directions. A *backward* step reduces the goal to simpler subgoals, and a *forward* step derives new hypotheses from those in scope. Each connective comes with tactics that *introduce* it, proving a goal of that shape, and tactics that *eliminate* it, using a hypothesis of that shape. We take the connectives in turn.

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

## Examples

The proofs below prove those same ten theorems again, now with tactics. Each can be read alongside the proof term of the previous section.

Example 1. Implication is reflexive.

```lean
example (P : Prop) : P → P := by
  intro h
  exact h
```

Example 2. A conjunction entails each conjunct.

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

Example 3. A disjunct entails the disjunction.

```lean
example (P Q : Prop) : P → P ∨ Q := by
  intro h
  exact Or.inl h
```

Example 4. Anything follows from absurdity.

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

Example 5. Modus ponens, packaged as a single implication.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

Example 6. Disjunction commutes.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

Example 7. Double negation introduction.

```lean
example (P : Prop) : P → ¬¬P := by
  intro hP hnP
  exact hnP hP
```

Example 8. Contraposition.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hPQ hnQ hP
  exact hnQ (hPQ hP)
```

Example 9. Double negation elimination, which needs classical reasoning.

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

Example 10. Currying turns a conjunctive hypothesis into nested implications.

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → (Q → R)) := by
  intro h hP hQ
  exact h ⟨hP, hQ⟩
```

# Worked Examples

Each example below appears three ways, as a natural deduction derivation, as a proof term, and as a tactic proof. The three present the same proof, and Lean checks both proof scripts when the notes are built. These propositions are disjoint from the examples of the earlier sections and from the exercises.

## A conjunction entails a conjunct

Elimination projects the left conjunct, and the implication discharges the assumption P ∧ Q.

```
   [P ∧ Q]
  ──────────  ∧E₁
      P
  ────────────  →I
   P ∧ Q → P
```

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

## Ex Falso Quodlibet

From a proof of the absurdity, ⊥ elimination proves any proposition.{margin}[*Ex falso quodlibet* is Latin for "from a falsehood, anything follows".]

```
   [⊥]
  ──────  ⊥E
    P
  ────────  →I
   ⊥ → P
```

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

## Modus Ponens

An implication and its antecedent, both projected from the conjunction, combine by →E to give the consequent.{margin}[*Modus ponens* is Latin, short for *modus ponendo ponens*, "the mode that affirms by affirming".]

```
   [(P→Q)∧P]           [(P→Q)∧P]
  ───────────── ∧E₁    ───────────── ∧E₂
      P → Q                  P
    ────────────────────────────── →E
                 Q
   ──────────────────────────────── →I
        (P → Q) ∧ P → Q
```

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

## Disjunction Commutes

Case analysis on the disjunction rebuilds it with the disjuncts exchanged.

```
               [P]           [Q]
   [P ∨ Q]    ─────── ∨I₂   ─────── ∨I₁
              Q ∨ P         Q ∨ P
  ───────────────────────────────────── ∨E
             Q ∨ P
  ──────────────────────  →I
   P ∨ Q → Q ∨ P
```

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

## Double Negation Elimination

This direction requires classical reasoning. `Classical.byContradiction` discharges the assumption ¬P after deriving ⊥ from it together with ¬¬P.{margin}[The classical step marked RAA is *reductio ad absurdum*, Latin for "reduction to absurdity".]

```
   [¬P]  [¬¬P]
  ──────────────  ¬E
        ⊥
    ──────────  RAA
        P
   ───────────────  →I
     ¬¬P → P
```

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

# Exercises

Prove each statement in Lean, replacing `sorry` with a proof. Download the exercise file [`Lecture01.lean`](example-code/Lectures/En/Lecture01.lean) and open it in VS Code.

```savedComment
Exercises for Lecture 1: Motivation and Propositional Logic.
Replace each `sorry` with a proof.
```

Exercise 1. Implication composes.

```savedLean -keep
theorem exercise1 (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry
```

Exercise 2. Conjunction distributes over disjunction.

```savedLean -keep
theorem exercise2 (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

Exercise 3. Disjunction associates.

```savedLean -keep
theorem exercise3 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry
```

Exercise 4. This direction of the first De Morgan law is constructive.

```savedLean -keep
theorem exercise4 (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry
```

Exercise 5. Peirce's law.{margin}[C. S. Peirce, *On the Algebra of Logic: A Contribution to the Philosophy of Notation*, American Journal of Mathematics 7(2), 1885, pp. 180–196.] It requires classical reasoning; consider a case analysis on `Classical.em P`.

```savedLean -keep
theorem exercise5 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry
```

Exercise 6. Disjunction distributes over conjunction.

```savedLean -keep
theorem exercise6 (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry
```

Exercise 7. An implication into a conjunction splits into two implications.

```savedLean -keep
theorem exercise7 (P Q R : Prop) :
    (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  sorry
```

Exercise 8. From a disjunction and the negation of one disjunct, the other holds.

```savedLean -keep
theorem exercise8 (P Q : Prop) : (P ∨ Q) → ¬P → Q := by
  sorry
```

Exercise 9. No proposition is equivalent to its own negation.

```savedLean -keep
theorem exercise9 (P : Prop) : ¬(P ↔ ¬P) := by
  sorry
```

Exercise 10. Of any two propositions, one implies the other. It requires classical reasoning; consider a case analysis on `Classical.em P`.

```savedLean -keep
theorem exercise10 (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  sorry
```

```lean -show
end Lecture1
```
