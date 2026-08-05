import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Meta.Footnote
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

Software controls aircraft, medical devices, financial systems, and communication networks. Errors in such systems cost money and lives. The standard way to find errors is testing, and testing examines finitely many executions of a program that admits infinitely many. Dijkstra stated the limitation precisely.{margin}[E. W. Dijkstra, [*Notes on Structured Programming*](https://www.cs.utexas.edu/~EWD/ewd02xx/EWD249.PDF), EWD249, Technological University Eindhoven, 1970.]

> Program testing can be used to show the presence of bugs, but never to show their absence!

Formal verification takes the complementary route. We state a property of a program as a mathematical proposition and prove that every execution satisfies it. The proof covers all inputs at once, which no finite test suite achieves.

Proofs about real programs grow large, so we delegate their checking to a machine. A *proof assistant* is a program that checks every step of a proof with respect to the rules of a formal logic, and that helps the user construct the proof interactively. Lean, Rocq (formerly Coq), Isabelle/HOL, and Agda are proof assistants in current use. Landmark results include the verification of the seL4 operating-system microkernel{margin}[G. Klein et al., [*seL4: Formal Verification of an OS Kernel*](https://trustworthy.systems/publications/nictaabstracts/Klein_EHACDEEKNSTW_09.abstract), Proceedings of SOSP 2009, pp. 207–220.] and of the CompCert optimizing C compiler.{margin}[X. Leroy, [*Formal Verification of a Realistic Compiler*](https://xavierleroy.org/publi/compcert-CACM.pdf), Communications of the ACM 52(7), 2009, pp. 107–115.]

Language models now write a growing share of code. A model produces plausible text, and plausible is not the same as correct. Generated code can invoke functions that do not exist, handle only the cases that its prompt suggests, or drift from the stated requirement in ways that survive code review. The literature calls this failure mode hallucination.

Formal verification, in particular when automated, changes how we can trust such code.{margin}[L. de Moura, [*The Lean Programming Language and Theorem Prover*](https://leodemoura.github.io/static/etaps2026/), ETAPS 2026.] When generated code arrives with a machine-checked proof that it satisfies its specification, the proof assistant checks the proof independently of how the code came to be, so hallucinated or simply wrong code cannot pass. The burden of correctness moves from reading the code to writing the right specification. The techniques of this course apply unchanged to generated code, and the automation of the final lectures, with the `mvcgen` tactic, points toward verification at the pace of code generation.

In this course we use [Lean](https://lean-lang.org). Lean is at once a programming language and a proof assistant, so we can write a program and prove its properties in the same system. Lectures 1 and 2 review classical logic while introducing Lean's proof language, following HTPIwL. Lectures 3 to 8 follow [LoVe](https://github.com/lean-forward/logical_verification_2026){fnref}[lovelib] through interactive proving, functional programming, and inductive predicates. The final block treats the semantics of an imperative language, Hoare logic, and practical verification with the `mvcgen` tactic.

{numref}[fig-lean-components] shows the components of Lean that the course exercises. The parser reads the text of a `.lean` file into syntax trees, and the macro expander unfolds the notations that libraries and user code define. The elaborator turns those trees into terms of the core language, and it does the work that the surface syntax leaves implicit, inferring omitted arguments, resolving type class instances, and running tactics. Tactics are themselves Lean programs, and they build terms rather than certificates of their own correctness. The kernel rechecks the finished term with respect to the rules of dependent type theory, so a tactic that produces a wrong term fails here, and only the kernel belongs to the trusted base. The compiler takes the same terms to native code, which is what `#eval` runs. The libraries supply notations, instances and lemmas to every stage above the kernel.

![Main components of Lean: a .lean file goes through the parser and macro expander to the elaborator, which draws on tactics and libraries and produces core terms; the kernel checks those terms and the compiler turns them into native code](lean-components.svg)

{figcap "fig-lean-components"}[The main components of Lean.]

These components serve any Lean development, and the course uses them for one specific end. The imperative language of the final lectures, its semantics and its Hoare logic are ordinary Lean definitions, the verification conditions are goals{fnref}[goal] that tactics discharge, and the kernel checks the result as it checks any other proof. The objective of this course is to show how to use Lean to verify imperative programs formally, and {numref}[fig-verifier-architecture] describes an architecture for it.

A program and its specification form a Hoare triple. The big-step operational semantics gives the triple its meaning. The `mvcgen` tactic generates the verification conditions, which are purely logical goals. Tactic proofs discharge them, and the Lean kernel checks every proof.

![Architecture of a program verifier in Lean: a program and a specification form a Hoare triple, whose meaning comes from the big-step semantics; the mvcgen tactic generates verification conditions, tactic proofs discharge them, and the Lean kernel checks every proof](verifier-architecture.svg)

{figcap "fig-verifier-architecture"}[Architecture of a program verifier in Lean.]

:::footnotes

{fnAnchor "lovelib"}[] LoVe collects the Lean files that accompany the *Hitchhiker's Guide to Logical Verification*, 2026 edition. Its support library `LoVelib` is not published as a Lake package, so these notes keep a copy of it under `Lectures/LoVe/`, together with its BSD 3-clause licence. The copy is verbatim except for the attribute `@[reducible]` on `Set.PartialOrder`, which the definition linter of Lean v4.32.0 requires and the original, written for Lean v4.24.0, does not carry.

{fnAnchor "goal"}[] A *goal* is what remains to be proved at a point in a proof. Lean displays it as the hypotheses in scope, one per line, followed by the symbol ⊢ and the proposition to prove. Every tactic either closes a goal or replaces it with simpler ones, and the proof ends when none remain. Proving `Q ∧ P` from a hypothesis `h : P ∧ Q`, for instance, starts from the goal

```
P Q : Prop
h : P ∧ Q
⊢ Q ∧ P
```

which the tactic `exact ⟨h.right, h.left⟩` closes. {secref}[tactics] returns to the subject in detail.

:::

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

Connectives build compound propositions from simpler ones, and {numref}[tbl-connectives] names the five.

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

{tabcap "tbl-connectives"}[The five connectives, with their symbols and readings.]

The truth value of a compound proposition depends only on the truth values of its parts. {numref}[tbl-truth-values] defines the five connectives, with T for true and F for false.

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

{tabcap "tbl-truth-values"}[The truth values of the five connectives.]

Two rows of the implication column deserve attention. When P is false, P → Q is true regardless of Q. An implication claims nothing about cases where its antecedent fails, so those cases cannot refute it.

The disjunction column deserves the same attention. Disjunction is *inclusive*, so P ∨ Q is true when both disjuncts are.

# Logical Equivalence

A *valuation* assigns a truth value to each propositional variable. A proposition is a *tautology* when it is true under every valuation. Two propositions A and B are *logically equivalent*, written A ≡ B, when they have the same truth value under every valuation, that is, when A ↔ B is a tautology.

The classical equivalences of {numref}[tbl-equivalences] appear constantly in proofs.

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

{tabcap "tbl-equivalences"}[The classical equivalences.]

A truth table verifies each equivalence. For the second De Morgan law, the columns for ¬(P ∨ Q) and ¬P ∧ ¬Q agree on all four valuations, as {numref}[tbl-demorgan-check] shows.

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

{tabcap "tbl-demorgan-check"}[Truth table for the second De Morgan law.]

## Examples

Each equivalence below is verified by a truth table. Two propositions are equivalent when their final columns agree in every row, and a tautology has a column that is true in every row.

{ex "ex-logical-equivalence-double-negation-returns-original"}[] Double negation returns the original proposition, verified in {numref}[tbl-double-negation].

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

{tabcap "tbl-double-negation"}[Truth table for ¬¬P ≡ P.]

{ex "ex-logical-equivalence-excluded-middle-p-p"}[] The excluded middle P ∨ ¬P is a tautology, verified in {numref}[tbl-excluded-middle].

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

{tabcap "tbl-excluded-middle"}[Truth table for P ∨ ¬P.]

{ex "ex-logical-equivalence-non-contradiction-p-p"}[] Non-contradiction ¬(P ∧ ¬P) is a tautology, verified in {numref}[tbl-non-contradiction].

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

{tabcap "tbl-non-contradiction"}[Truth table for ¬(P ∧ ¬P).]

{ex "ex-logical-equivalence-first-de-morgan-law"}[] The first De Morgan law, verified in {numref}[tbl-demorgan-first].

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

{tabcap "tbl-demorgan-first"}[Truth table for ¬(P ∧ Q) ≡ ¬P ∨ ¬Q.]

{ex "ex-logical-equivalence-disjunction-commutes-verified-numref"}[] Disjunction commutes, verified in {numref}[tbl-or-comm].

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

{tabcap "tbl-or-comm"}[Truth table for P ∨ Q ≡ Q ∨ P.]

{ex "ex-logical-equivalence-disjunction-idempotent-verified-numref"}[] Disjunction is idempotent, verified in {numref}[tbl-or-idem].

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

{tabcap "tbl-or-idem"}[Truth table for P ∨ P ≡ P.]

{ex "ex-logical-equivalence-contrapositive-verified-numref-tbl"}[] The contrapositive, verified in {numref}[tbl-contrapositive].

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

{tabcap "tbl-contrapositive"}[Truth table for P → Q ≡ ¬Q → ¬P.]

{ex "ex-logical-equivalence-material-implication-verified-numref"}[] Material implication, verified in {numref}[tbl-material-implication].

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

{tabcap "tbl-material-implication"}[Truth table for P → Q ≡ ¬P ∨ Q.]

{ex "ex-logical-equivalence-biconditional-conjunction-two-implications"}[] The biconditional is the conjunction of its two implications, verified in {numref}[tbl-iff-split].

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

{tabcap "tbl-iff-split"}[Truth table for P ↔ Q ≡ (P → Q) ∧ (Q → P).]

{ex "ex-logical-equivalence-negation-implication-verified-numref"}[] The negation of an implication, verified in {numref}[tbl-not-implication].

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

{tabcap "tbl-not-implication"}[Truth table for ¬(P → Q) ≡ P ∧ ¬Q.]

## Logical Calculi

Truth tables decide any propositional question, but their size grows exponentially in the number of variables, and they do not extend to the quantifiers of Lecture 2. A *calculus* answers the same questions by derivation rather than by computation.

A calculus fixes a set of *axioms*, which are propositions taken as given, and a set of *inference rules*, each of which produces a proposition from propositions already derived. A *derivation* is a finite sequence of rule applications, and a proposition that ends a derivation is a *theorem* of the calculus. Valuations play no part in this. A derivation rewrites symbols according to the rules alone, and that is what lets a machine check it.

Two properties tie a calculus to the semantics of the previous sections. A calculus is *sound* when every theorem is a tautology, and *complete* when every tautology is a theorem. Post proved both for the propositional calculus in 1921, in the paper that also introduced the truth-table method.{margin}[E. L. Post, *Introduction to a General Theory of Elementary Propositions*, American Journal of Mathematics 43, 1921, pp. 163–185.]

Propositional logic admits several calculi, and they differ in the shape of their rules rather than in the theorems they prove.

An *axiomatic* calculus, in the style of Hilbert and Ackermann,{margin}[D. Hilbert and W. Ackermann, *Grundzüge der theoretischen Logik*, Julius Springer, Berlin, 1928.] takes many axioms and one rule. The system of Łukasiewicz and Tarski needs three axiom schemes over → and ¬, with modus ponens as its only rule.{margin}[J. Łukasiewicz and A. Tarski, *Untersuchungen über den Aussagenkalkül*, Comptes Rendus des Séances de la Société des Sciences et des Lettres de Varsovie, Classe III, 23, 1930, pp. 30–50.]

```
  A → (B → A)
  (A → (B → C)) → ((A → B) → (A → C))
  (¬A → ¬B) → (B → A)
```

Each scheme stands for every proposition of its shape, so `P → (Q → P)` and `(P ∧ Q) → (R → (P ∧ Q))` are both instances of the first. Deriving a theorem as simple as P → P takes five steps here, and finding the steps is an art.

*Resolution* goes to the other extreme, with one rule on propositions written as clauses, which is what machine provers search with.{margin}[J. A. Robinson, *A Machine-Oriented Logic Based on the Resolution Principle*, Journal of the ACM 12(1), 1965, pp. 23–41.]

*Natural deduction* sits between the two. It has no axioms and two rules for each connective, one that introduces the connective and one that eliminates it, and its derivations may rest on assumptions that a later rule discharges. Gentzen designed it to follow the steps a mathematician actually takes.{margin}[G. Gentzen, *Untersuchungen über das logische Schließen. I*, Mathematische Zeitschrift 39, 1935, pp. 176–210.] The *sequent calculus*, from the same paper, carries the assumptions explicitly to the left of a turnstile ⊢ and serves proof-theoretic arguments.

## The Calculus of This Course

This course uses natural deduction. Its introduction and elimination rules are the ones Lean's tactics implement, and a Lean proof term corresponds to one of its derivations. The next section presents the rules, and the rest of the lecture develops the corresponding proofs in Lean.

# Natural Deduction

Natural deduction derives a proposition from assumptions by rules that mirror how mathematicians argue. Dag Prawitz gave the system its proof-theoretic study.{margin}[D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*, Almqvist & Wiksell, Stockholm, 1965.] Each rule has zero or more *premises* above a horizontal line and one *conclusion* below it, and it reads as follows. Given derivations of the premises, the line licenses the conclusion.

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

{ex "ex-natural-deduction-implication-reflexive"}[] Implication is reflexive.

```
   [P]¹
  ──────  →I,¹
   P → P
```

{ex "ex-natural-deduction-conjunction-entails-each-conjunct"}[] A conjunction entails each conjunct.

```
   [P ∧ Q]¹
  ──────────  ∧E₁
      P
  ────────────  →I,¹
   P ∧ Q → P
```

{ex "ex-natural-deduction-disjunct-entails-disjunction"}[] A disjunct entails the disjunction.

```
     [P]¹
   ────────  ∨I₁
    P ∨ Q
  ────────────  →I,¹
   P → P ∨ Q
```

{ex "ex-natural-deduction-anything-follows-absurdity-principle"}[] Anything follows from absurdity, the principle *ex falso quodlibet*.

```
   [⊥]¹
  ──────  ⊥E
    P
  ────────  →I,¹
   ⊥ → P
```

{ex "ex-natural-deduction-modus-ponens-packaged-single"}[] Modus ponens, packaged as a single implication.

```
   [(P→Q)∧P]¹            [(P→Q)∧P]¹
  ───────────── ∧E₁     ───────────── ∧E₂
      P → Q                   P
     ───────────────────────────── →E
                  Q
   ─────────────────────────────────── →I,¹
          (P → Q) ∧ P → Q
```

{ex "ex-natural-deduction-disjunction-commutes"}[] Disjunction commutes.

```
                [P]²           [Q]²
   [P ∨ Q]¹    ─────── ∨I₂    ─────── ∨I₁
               Q ∨ P          Q ∨ P
  ────────────────────────────────────── ∨E,²
              Q ∨ P
  ─────────────────────── →I,¹
   P ∨ Q → Q ∨ P
```

{ex "ex-natural-deduction-double-negation-introduction"}[] Double negation introduction.

```
    [¬P]²   [P]¹
   ────────────── ¬E
         ⊥
     ────────── ¬I,²
        ¬¬P
    ────────────── →I,¹
      P → ¬¬P
```

{ex "ex-natural-deduction-contraposition"}[] Contraposition.

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

{ex "ex-natural-deduction-double-negation-elimination-which"}[] Double negation elimination, which needs the classical rule.

```
    [¬P]²  [¬¬P]¹
   ──────────────── ¬E
          ⊥
     ─────────── RAA,²
          P
    ─────────────── →I,¹
     ¬¬P → P
```

{ex "ex-natural-deduction-currying-turns-conjunctive-hypothesis"}[] Currying turns a conjunctive hypothesis into nested implications.

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

# The Syntax of Lean

The sections that follow read and write Lean, so this one fixes the notation. It explains how a declaration is spelled, not what makes a proof correct, which is the subject of the sections after it.

A declaration names a statement and gives its proof. The keyword comes first, then the name, then the hypotheses in parentheses, then the statement after the colon, then the proof after `:=`.

```lean
theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩
```

Here `theorem` names the result `and_swap`. The binders `(P Q : Prop)` and `(h : P ∧ Q)` introduce two propositions and one hypothesis. The statement to prove is `Q ∧ P`, and the proof is the term after `:=`. The keyword `example` replaces `theorem` when the result needs no name.

{numref}[tbl-lean-syntax] lists the pieces of syntax that the following sections use.

:::table +header
*
  * Written
  * Read as
*
  * `example (h : P) : Q := e`
  * anonymous statement with hypothesis h, proved by e
*
  * `fun h => e`
  * the function that takes h to e
*
  * `f a`
  * f applied to a, written without parentheses
*
  * `⟨a, b⟩`
  * the anonymous constructor, here a pair
*
  * `h.left`, `h.right`
  * the two components of a conjunction
*
  * `by`
  * enter tactic mode, one tactic per line
*
  * `·`
  * focus the next goal inside a tactic block
*
  * `sorry`
  * placeholder for a missing proof
*
  * `-- text`
  * comment to the end of the line
:::

{tabcap "tbl-lean-syntax"}[The syntax of declarations, terms and tactic blocks.]

The logical symbols are unicode, and {numref}[tbl-lean-symbols] gives the abbreviation that types each one. Typing the backslash abbreviation and then space or tab inserts the character in VS Code.

:::table +header
*
  * Symbol
  * Meaning
  * Typed as
*
  * →
  * implication
  * `\to`
*
  * ∧
  * conjunction
  * `\and`
*
  * ∨
  * disjunction
  * `\or`
*
  * ¬
  * negation
  * `\not`
*
  * ↔
  * biconditional
  * `\iff`
*
  * ⊥
  * absurdity
  * `\bot`
*
  * ⟨ ⟩
  * anonymous constructor
  * `\langle`, `\rangle`
*
  * ·
  * goal focus
  * `\.`
:::

{tabcap "tbl-lean-symbols"}[The logical symbols and the abbreviations that type them.]

The same statement can be proved by a term or in tactic mode, and the two produce the same underlying proof. The sections that follow use both.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  exact ⟨h.right, h.left⟩
```

The commands that inspect a declaration begin with `#`. The command `#check` prints the type of a term, which for a proof is the proposition it proves.

```lean (name := checkAndSwap)
#check fun (P Q : Prop) (h : P ∧ Q) =>
  (⟨h.right, h.left⟩ : Q ∧ P)
```
```leanOutput checkAndSwap
fun P Q h => ⟨h.right, h.left⟩ : ∀ (P Q : Prop), P ∧ Q → Q ∧ P
```

# Natural Deduction in Lean

In Lean, we state a proposition and prove it in one declaration. The `example` keyword introduces an anonymous statement, and `theorem` introduces a named one. Hypotheses appear before the colon as named assumptions, and the proposition to prove, the *goal*, appears after it.

Lean encodes natural deduction directly. A proof of a proposition is a *term* whose type is that proposition, an open assumption is a variable of that type, and each deduction rule becomes a way to build or take apart such a term. The simplest proof uses an assumption directly, the assumption rule of natural deduction.

```lean
example (P : Prop) (h : P) : P := h
```

Here `h` names the assumption that P holds, and the proof is `h` itself. Lecture 3 develops this correspondence between propositions and types.{margin}[W. A. Howard, *The Formulae-as-Types Notion of Construction*, in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980.]

{numref}[tbl-rules-to-lean] maps each rule of the section on natural deduction to the Lean term that realizes it. An introduction rule builds a term, and an elimination rule takes one apart.

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

{tabcap "tbl-rules-to-lean"}[The natural deduction rules and the Lean terms that realize them.]

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

{ex "ex-natural-deduction-lean-implication-reflexive"}[] Implication is reflexive.

```lean
example (P : Prop) : P → P :=
  fun h => h
```

{ex "ex-natural-deduction-lean-conjunction-entails-each-conjunct"}[] A conjunction entails each conjunct.

```lean
example (P Q : Prop) : P ∧ Q → P :=
  fun h => h.left
```

{ex "ex-natural-deduction-lean-disjunct-entails-disjunction"}[] A disjunct entails the disjunction.

```lean
example (P Q : Prop) : P → P ∨ Q :=
  fun h => Or.inl h
```

{ex "ex-natural-deduction-lean-anything-follows-absurdity"}[] Anything follows from absurdity.

```lean
example (P : Prop) : False → P :=
  fun h => False.elim h
```

{ex "ex-natural-deduction-lean-modus-ponens-packaged-single"}[] Modus ponens, packaged as a single implication.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q :=
  fun h => h.left h.right
```

{ex "ex-natural-deduction-lean-disjunction-commutes"}[] Disjunction commutes.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim
    (fun hP => Or.inr hP)
    (fun hQ => Or.inl hQ)
```

{ex "ex-natural-deduction-lean-double-negation-introduction"}[] Double negation introduction.

```lean
example (P : Prop) : P → ¬¬P :=
  fun hP hnP => hnP hP
```

This example deserves the full unfolding, because its proof has two functions where the statement seems to have one implication. Since ¬A is A → False, the double negation unfolds twice, from the outside in. First ¬¬P is ¬P → False, then it is (P → False) → False, and the whole statement is P → ((P → False) → False). The parentheses around the inner negation are needed. The arrow associates to the right, so P → P → P → False is the proposition P → (P → (P → False)), which is a different one, and a false one.

The term therefore has one function per arrow, and `fun hP hnP => hnP hP` abbreviates `fun hP => fun hnP => hnP hP`. The first function is the →I that discharges P and returns a proof of ¬¬P. That proof is itself a function, and the second function is the ¬I that discharges ¬P. Its parameter has type ¬P, not P, which is the easy place to slip. The context then holds hP of type P and hnP of type P → False, and False remains to be proved. A negative hypothesis is a function into False, so applying it to what it denies is the ¬E, and `hnP hP` closes the proof. The other order does not typecheck, because hP is not a function.

```lean
example (P : Prop) : P → ¬¬P :=
  fun (hP : P) =>
    fun (hnP : ¬P) => hnP hP
```

{ex "ex-natural-deduction-lean-contraposition"}[] Contraposition.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  fun hPQ hnQ hP => hnQ (hPQ hP)
```

{ex "ex-natural-deduction-lean-double-negation-elimination-which"}[] Double negation elimination, which needs classical reasoning.

```lean
example (P : Prop) : ¬¬P → P :=
  fun h => Classical.byContradiction (fun hnP => h hnP)
```

{ex "ex-natural-deduction-lean-currying-turns-conjunctive-hypothesis"}[] Currying turns a conjunctive hypothesis into nested implications.

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → (Q → R)) :=
  fun h hP hQ => h ⟨hP, hQ⟩
```

# Proving with Tactics
%%%
tag := "tactics"
%%%

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

{ex "ex-proving-tactics-implication-reflexive"}[] Implication is reflexive.

```lean
example (P : Prop) : P → P := by
  intro h
  exact h
```

{ex "ex-proving-tactics-conjunction-entails-each-conjunct"}[] A conjunction entails each conjunct.

```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left
```

{ex "ex-proving-tactics-disjunct-entails-disjunction"}[] A disjunct entails the disjunction.

```lean
example (P Q : Prop) : P → P ∨ Q := by
  intro h
  exact Or.inl h
```

{ex "ex-proving-tactics-anything-follows-absurdity"}[] Anything follows from absurdity.

```lean
example (P : Prop) : False → P := by
  intro h
  exact False.elim h
```

{ex "ex-proving-tactics-modus-ponens-packaged-single"}[] Modus ponens, packaged as a single implication.

```lean
example (P Q : Prop) : (P → Q) ∧ P → Q := by
  intro h
  apply h.left
  exact h.right
```

{ex "ex-proving-tactics-disjunction-commutes"}[] Disjunction commutes.

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ
```

{ex "ex-proving-tactics-double-negation-introduction"}[] Double negation introduction.

```lean
example (P : Prop) : P → ¬¬P := by
  intro hP hnP
  exact hnP hP
```

{ex "ex-proving-tactics-contraposition"}[] Contraposition.

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hPQ hnQ hP
  exact hnQ (hPQ hP)
```

{ex "ex-proving-tactics-double-negation-elimination-which"}[] Double negation elimination, which needs classical reasoning.

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  apply Classical.byContradiction
  intro hnP
  exact h hnP
```

{ex "ex-proving-tactics-currying-turns-conjunctive-hypothesis"}[] Currying turns a conjunctive hypothesis into nested implications.

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

From a proof of the absurdity, ⊥ elimination proves any proposition.{fnref}[exfalso]

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

An implication and its antecedent, both projected from the conjunction, combine by →E to give the consequent.{fnref}[modusponens]

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

This direction requires classical reasoning. `Classical.byContradiction` discharges the assumption ¬P after deriving ⊥ from it together with ¬¬P.{fnref}[raa]

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

:::footnotes

{fnAnchor "exfalso"}[] *Ex falso quodlibet* is Latin for "from a falsehood, anything follows".

{fnAnchor "modusponens"}[] *Modus ponens* is Latin, short for *modus ponendo ponens*, "the mode that affirms by affirming".

{fnAnchor "raa"}[] The classical step marked RAA is *reductio ad absurdum*, Latin for "reduction to absurdity".

:::

# Exercises

Prove each statement in Lean, replacing `sorry` with a proof. Download the exercise file [`Lecture01.lean`](example-code/Lectures/En/Lecture01.lean) and open it in VS Code.

```savedComment
Exercises for Lecture 1: Motivation and Propositional Logic.
Replace each `sorry` with a proof.
```

{exercise "exr-implication-composes"}[] Implication composes.

```savedLean -keep
theorem exercise1 (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry
```

{exercise "exr-conjunction-distributes-over-disjunction"}[] Conjunction distributes over disjunction.

```savedLean -keep
theorem exercise2 (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

{exercise "exr-disjunction-associates"}[] Disjunction associates.

```savedLean -keep
theorem exercise3 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry
```

{exercise "exr-this-direction-first-de"}[] This direction of the first De Morgan law is constructive.

```savedLean -keep
theorem exercise4 (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry
```

{exercise "exr-peirce-s-law-margin"}[] Peirce's law.{margin}[C. S. Peirce, *On the Algebra of Logic: A Contribution to the Philosophy of Notation*, American Journal of Mathematics 7(2), 1885, pp. 180–196.] It requires classical reasoning; consider a case analysis on `Classical.em P`.

```savedLean -keep
theorem exercise5 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry
```

{exercise "exr-disjunction-distributes-over-conjunction"}[] Disjunction distributes over conjunction.

```savedLean -keep
theorem exercise6 (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry
```

{exercise "exr-implication-conjunction-splits-two"}[] An implication into a conjunction splits into two implications.

```savedLean -keep
theorem exercise7 (P Q R : Prop) :
    (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  sorry
```

{exercise "exr-disjunction-negation-one-disjunct"}[] From a disjunction and the negation of one disjunct, the other holds.

```savedLean -keep
theorem exercise8 (P Q : Prop) : (P ∨ Q) → ¬P → Q := by
  sorry
```

{exercise "exr-no-proposition-equivalent-own"}[] No proposition is equivalent to its own negation.

```savedLean -keep
theorem exercise9 (P : Prop) : ¬(P ↔ ¬P) := by
  sorry
```

{exercise "exr-any-two-propositions-one"}[] Of any two propositions, one implies the other. It requires classical reasoning; consider a case analysis on `Classical.em P`.

```savedLean -keep
theorem exercise10 (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  sorry
```

```lean -show
end Lecture1
```
