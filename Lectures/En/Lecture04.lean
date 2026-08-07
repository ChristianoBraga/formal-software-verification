import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers
import Lectures.En.Lecture03

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Lecture 4: Backward Proofs" =>

%%%
tag := "lecture-4"
%%%

This lecture supplies the proof method that Lecture 3 postponed, following chapter 3 of the *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 3.] It presents tactic mode, the basic tactics, the rules for the connectives, the quantifiers and equality, the rewriting tactics `rw` and `simp`, and proofs by mathematical induction, and it discharges the statements that Lecture 3 left with `sorry`.

*This lecture is also available as [presentation slides](../slides/lecture-4.en.html).*

# Backward Proofs

A *tactic* operates on a proof goal and either proves it or creates new subgoals. A *goal* consists of a *local context*, which lists variable declarations x : σ and hypotheses h : P, and a *target* proposition, and we write C ⊢ Q for the goal with context C and target Q.{margin}[J. Avigad, L. de Moura, S. Kong, S. Ullrich, *Theorem Proving in Lean 4*, chapter 5.]

Tactics are a *backward* proof mechanism. A backward proof starts at the goal and works towards the available hypotheses and theorems, and its telltale phrase is "it suffices to". A *forward* proof starts at the hypotheses and works towards the goal, and Lecture 5 develops it. Given hypotheses ha : a, hab : a → b, hbc : b → c and the target c, the two directions read as follows.

```
Backward, from the goal:
  to prove c, by hbc it suffices to prove b;
  to prove b, by hab it suffices to prove a;
  and ha proves a.

Forward, from the hypotheses:
  from ha and hab, we have b;
  from b and hbc, we have c.
```

A derivation in the natural deduction of Lecture 1 admits both readings, forward from the leaves down to the conclusion, and backward from the conclusion up to the leaves.{margin}[G. Gentzen, *Untersuchungen über das logische Schließen. I*, Mathematische Zeitschrift 39, 1935, pp. 176–210.]

The keyword `by` enters tactic mode, and each line after it is one tactic. The proof below introduces the universally quantified variables and the two hypotheses, and closes the goal. The `trace_state` lines print the goal between the steps, and the outputs follow the code.

```lean (name := fstOfTwo)
namespace Backward

theorem fst_of_two_props :
    ∀ a b : Prop, a → b → a := by
  intro a b
  trace_state
  intro ha hb
  trace_state
  apply ha

end Backward
```

After `intro a b` the two propositions have entered the context, and the target is the implication that remains.

```leanOutput fstOfTwo
a b : Prop
⊢ a → b → a
```

After `intro ha hb` the two hypotheses are available, and the target is a.

```leanOutput fstOfTwo
a b : Prop
ha : a
hb : b
⊢ a
```

The proof below chains two implications. Read it as three "it suffices to" steps: to prove c, by hbc it suffices to prove b; to prove b, by hab it suffices to prove a; and ha proves a.

```lean
namespace Backward

theorem prop_comp (a b c : Prop) (hab : a → b)
    (hbc : b → c) : a → c := by
  intro ha
  apply hbc
  apply hab
  apply ha

end Backward
```

# Basic Tactics

The tactic `intro` moves the leading ∀-bound variable, or the leading assumption of an implication, from the target into the local context, under a chosen name. Given a provable goal it always produces a provable goal.

The tactic `apply` matches the target with the conclusion of a theorem or hypothesis, up to computation, and adds the assumptions of the theorem as new goals. It can turn a provable goal into an unprovable one. The tactic `exact` closes the goal with a term that proves it. Where both work, `exact` states the intention more clearly. The tactic `assumption` searches the local context for a hypothesis that matches the target.

Parameters written to the left of the colon arrive in the context already, so the proofs below need no `intro`.

```lean
namespace Backward

theorem fst_of_two_props_params (a b : Prop)
    (ha : a) (hb : b) : a := by
  apply ha

theorem fst_of_two_props_exact (a b : Prop)
    (ha : a) (hb : b) : a := by
  exact ha

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) : a := by
  assumption

end Backward
```

The tactic `sorry` closes any goal without proving it, exactly as the term `sorry` did in Lecture 3, and Lean flags every use. The example below shows how `apply` turns a provable goal into an unprovable one. The target `a ∨ b` follows from the hypothesis `hb` by the rule `Or.inr`, but `apply Or.inl` commits to the left disjunct and leaves the goal `a`, which no hypothesis proves.

```lean (name := unsafeApply)
example (a b : Prop) (hb : b) : a ∨ b := by
  apply Or.inl
  trace_state
  sorry
```

```leanOutput unsafeApply
a b : Prop
hb : b
⊢ a
```

With the right rule the proof goes through.

```lean
example (a b : Prop) (hb : b) : a ∨ b := by
  apply Or.inr
  exact hb
```

Two tactics clean the local context. The tactic `clear` drops variables or hypotheses that the rest of the proof does not need, and `rename` renames a hypothesis, selected by its proposition.

```lean
namespace Backward

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
    (hab : a → b) (hbc : b → c) : c := by
  clear ha hab a
  apply hbc
  clear hbc c
  rename b => h
  exact h

end Backward
```

## Examples

The examples below exercise `intro`, `apply`, `exact`, `assumption`, `sorry`, `clear` and `rename`, and distinguish the tactics that preserve provability from those that can lose it.

{ex "ex-basic-tactics-intro-forall-goal-trace"}[] `intro` on a ∀-goal moves the bound variable into the context. The trace shows the goal before and after.

```lean (name := exIntroForall)
example : ∀ n : ℕ, add n 0 = n := by
  trace_state
  intro n
  trace_state
  exact rfl
```

```leanOutput exIntroForall
⊢ ∀ (n : ℕ), add n 0 = n
```

```leanOutput exIntroForall
n : ℕ
⊢ add n 0 = n
```

{ex "ex-basic-tactics-one-intro-several-names"}[] One `intro` with several names abbreviates several `intro`s. The two scripts prove the same theorem.

```lean
example : ∀ a b : Prop, a → a := by
  intro a b ha
  exact ha

example : ∀ a b : Prop, a → a := by
  intro a
  intro b
  intro ha
  exact ha
```

{ex "ex-basic-tactics-parameters-left-colon-context"}[] Parameters to the left of the colon need no `intro`, since they arrive in the context already.

```lean
example : ∀ a : Prop, a → a := by
  intro a ha
  exact ha

example (a : Prop) (ha : a) : a := by
  exact ha
```

{ex "ex-basic-tactics-exact-apply-same-goal"}[] `exact h` and `apply h` close the same goal, and `exact` says more.

```lean
example (a b : Prop) (hab : a → b) (ha : a) : b := by
  exact hab ha

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  apply hab ha
```

{ex "ex-basic-tactics-assumption-closes-without-naming"}[] `assumption` closes the goal without naming the hypothesis.

```lean
example (a b c : Prop) (ha : a) (hb : b) (hc : c) : b := by
  assumption
```

{ex "ex-basic-tactics-two-applys-walk-backwards"}[] Two `apply`s in sequence walk backwards through two implications.

```lean
example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  apply hbc
  apply hab
  exact ha
```

{ex "ex-basic-tactics-unsafe-apply-provable-unprovable"}[] `apply` can lose a provable goal. Choosing the wrong disjunct leaves a target no hypothesis proves, and only `sorry` closes it.

```lean
example (a b : Prop) (ha : a) : a ∨ b := by
  apply Or.inr
  sorry
```

{ex "ex-basic-tactics-sorry-closes-print-axioms"}[] `sorry` closes any goal, and `#print axioms` reports the debt as `sorryAx`, as in Lecture 3.

```lean (name := exSorryAxioms)
namespace Backward

theorem unproved (a : Prop) : a := by
  sorry

end Backward

#print axioms Backward.unproved
```

```leanOutput exSorryAxioms
'Backward.unproved' depends on axioms: [sorryAx]
```

{ex "ex-basic-tactics-clear-removes-unused"}[] `clear` removes a hypothesis and a variable the proof does not use.

```lean
example (a b : Prop) (ha : a) (hb : b) : b := by
  clear ha a
  exact hb
```

{ex "ex-basic-tactics-rename-by-proposition"}[] `rename` renames a hypothesis, selected by its proposition.

```lean
example (a b : Prop) (h : a ∧ b) : a ∧ b := by
  rename a ∧ b => hab
  exact hab
```

# Reasoning about Connectives and Quantifiers

Lecture 1 presented the rules of the connectives as inference figures. Each figure is an ordinary Lean theorem. An *introduction rule* has the connective as the outermost symbol of its conclusion and says how to prove it, and an *elimination rule* has the connective in an assumption and says how such a proof must have been built. The display below lists the rules for ∧, ∨ and ↔, with metavariables in the places the rules leave open.

```
And.intro : ?a → ?b → ?a ∧ ?b
And.left  : ?a ∧ ?b → ?a
And.right : ?a ∧ ?b → ?b
Or.inl    : ?a → ?a ∨ ?b
Or.inr    : ?b → ?a ∨ ?b
Or.elim   : ?a ∨ ?b → (?a → ?c) → (?b → ?c) → ?c
Iff.intro : (?a → ?b) → (?b → ?a) → (?a ↔ ?b)
Iff.mp    : (?a ↔ ?b) → ?a → ?b
Iff.mpr   : (?a ↔ ?b) → ?b → ?a
```

The quantifier rules, truth, falsehood and the classical principles complete the list. Negation needs no rules of its own, since ¬a is *defined* as a → False, so `intro` works on a negated target, as Lecture 1 showed. `True.intro` is the only rule for truth, `False.elim` is the only rule for falsehood, and Lean's logic is classical through `Classical.em` and `Classical.byContradiction`, both used since Lecture 1 and now applicable backwards.

```
Exists.intro : ∀ (w : ?α), ?p w → ∃ x, ?p x
Exists.elim  : (∃ x, ?p x) → (∀ (w : ?α), ?p w → ?b) → ?b
True.intro   : True
False.elim   : False → ?c
Classical.em : ∀ (p : Prop), p ∨ ¬p
Classical.byContradiction : (¬?a → False) → ?a
```

A *metavariable* ?a stands for a term still to be determined. When `apply` matches the target with the conclusion of a rule, *unification* determines some metavariables and leaves the others as new goals, and those usually disappear as the proof proceeds. The proof below applies the introduction rule of ∧ backwards and closes each subgoal with an elimination rule.

```lean
namespace Backward

theorem And_swap (a b : Prop) : a ∧ b → b ∧ a := by
  intro hab
  apply And.intro
  apply And.right
  exact hab
  apply And.left
  exact hab

end Backward
```

The `·` bullet, used since Lecture 1, focuses each subgoal, and *juxtaposition* instantiates a rule forwards, passing the hypothesis directly instead of waiting for it to appear as a subgoal. This is a small forward step inside a backward proof, and it avoids the metavariables that `apply` leaves behind.

```lean
namespace Backward

theorem And_swap_braces :
    ∀ a b : Prop, a ∧ b → b ∧ a := by
  intro a b hab
  apply And.intro
  · exact And.right hab
  · exact And.left hab

end Backward
```

Juxtaposition also instantiates a universal hypothesis, exactly as in Lecture 2.

```lean
namespace Backward

opaque f : ℕ → ℕ

theorem f5_if (h : ∀ n : ℕ, f n = n) : f 5 = 5 := by
  exact h 5

end Backward
```

The elimination rule of ∨ performs the case analysis that the tactic `cases` performed in Lecture 1, and `modus_ponens` and `Not_Not_intro` combine the rules seen so far.

```lean
namespace Backward

theorem Or_swap (a b : Prop) : a ∨ b → b ∨ a := by
  intro hab
  apply Or.elim hab
  · intro ha
    exact Or.inr ha
  · intro hb
    exact Or.inl hb

theorem modus_ponens (a b : Prop) : (a → b) → a → b := by
  intro hab ha
  apply hab
  exact ha

theorem Not_Not_intro (a : Prop) : a → ¬¬ a := by
  intro ha hna
  apply hna
  exact ha

end Backward
```

For proving statements of propositional logic, the guide offers the following strategies.

* Look at the target. If it is an implication or a negation, `intro` makes progress.
* Look at the hypotheses. A conjunction offers `And.left` and `And.right`, a disjunction offers `Or.elim`, and an equivalence offers `Iff.mp` and `Iff.mpr`.
* Match the target with the conclusion of an introduction rule and `apply` it.
* Prefer tactics that preserve provability while they make progress, and record the choice points where a tactic commits to a side.
* When a subgoal repeats a hypothesis, `exact` or `assumption` closes it.
* When nothing constructive applies, consider a case analysis on `Classical.em`.
* If the proof stalls, backtrack to the last choice point and try the other option.

## Examples

The examples below apply the rules backwards with `apply`, instantiate them forwards by juxtaposition, and watch the metavariables that appear along the way.

{ex "ex-connectives-quantifiers-and-intro-splits-goals"}[] `apply And.intro` splits the conjunction into two goals, and the trace shows both.

```lean (name := exAndIntroSplit)
example (a b : Prop) (hab : a ∧ b) : b ∧ a := by
  apply And.intro
  trace_state
  · exact And.right hab
  · exact And.left hab
```

```leanOutput exAndIntroSplit
case left
a b : Prop
hab : a ∧ b
⊢ b

case right
a b : Prop
hab : a ∧ b
⊢ a
```

{ex "ex-connectives-quantifiers-juxtaposition-closes-projection"}[] Juxtaposition closes a goal in one step, passing the hypothesis to the elimination rule.

```lean
example (a b : Prop) (hab : a ∧ b) : b := by
  exact And.right hab
```

{ex "ex-connectives-quantifiers-metavariable-appears-instantiated"}[] Applying the elimination rule backwards leaves a metavariable ?a in the target, and even a second goal asking for ?a itself. The final `exact` instantiates both at once.

```lean (name := exMetaRight)
example (a b : Prop) (hab : a ∧ b) : b := by
  apply And.right
  trace_state
  exact hab
```

```leanOutput exMetaRight
case self
a b : Prop
hab : a ∧ b
⊢ ?a ∧ b

case a
a b : Prop
hab : a ∧ b
⊢ Prop
```

{ex "ex-connectives-quantifiers-or-inl-chooses-side"}[] `apply Or.inl` chooses the left side and leaves its proof as the goal.

```lean
example (a b : Prop) (ha : a) : a ∨ b := by
  apply Or.inl
  exact ha
```

{ex "ex-connectives-quantifiers-or-elim-one-goal-per-disjunct"}[] `apply Or.elim h` produces one subgoal per disjunct, and a bullet closes each.

```lean
example (a b c : Prop) (h : a ∨ b) (hac : a → c)
    (hbc : b → c) : c := by
  apply Or.elim h
  · intro ha
    exact hac ha
  · intro hb
    exact hbc hb
```

{ex "ex-connectives-quantifiers-iff-intro-two-implications"}[] `apply Iff.intro` splits an equivalence into its two implications.

```lean
example (a : Prop) : a ∧ a ↔ a := by
  apply Iff.intro
  · intro haa
    exact And.left haa
  · intro ha
    exact And.intro ha ha
```

{ex "ex-connectives-quantifiers-iff-mp-mpr-directions"}[] `Iff.mp` and `Iff.mpr` extract the two directions of an equivalence hypothesis by juxtaposition.

```lean
example (a b : Prop) (hab : a ↔ b) (ha : a) : b := by
  exact Iff.mp hab ha

example (a b : Prop) (hab : a ↔ b) (hb : b) : a := by
  exact Iff.mpr hab hb
```

{ex "ex-connectives-quantifiers-exists-intro-witness"}[] `apply Exists.intro` supplies a witness, and the hypothesis at the witness closes what remains.

```lean
example (P : ℕ → Prop) (h : P 3) : ∃ n, P n := by
  apply Exists.intro 3
  exact h
```

{ex "ex-connectives-quantifiers-exists-elim-names-witness"}[] `apply Exists.elim h` consumes an existential hypothesis and names its witness.

```lean
example (α : Type) (P : α → Prop) (Q : Prop)
    (hex : ∃ x, P x) (h : ∀ x, P x → Q) : Q := by
  apply Exists.elim hex
  intro a hPa
  exact h a hPa
```

{ex "ex-connectives-quantifiers-negation-truth-falsehood"}[] Three one-line closings. `intro` works on a negated target, `True.intro` is the only rule for truth, and `apply False.elim` closes any goal from a proof of `False`, since falsehood has no introduction rule.

```lean
example : ¬False := by
  intro h
  exact h

example : True := by
  exact True.intro

example (a : Prop) (h : False) : a := by
  apply False.elim
  exact h
```

# Reasoning about Equality

The tactic `rfl` proves a target l = r when the two sides become syntactically identical under computation, and it succeeds exactly where a mathematician says "by definition". The term `rfl` of Lecture 3 is its term-level form. Computation here names six *conversions*.

:::table +header
*
  * Conversion
  * What it does
*
  * α
  * renames a bound variable
*
  * β
  * applies an anonymous function to its argument
*
  * δ
  * unfolds a definition
*
  * ζ
  * substitutes a `let`
*
  * η
  * identifies `fun x => f x` with f
*
  * ι
  * projects a constructor application
:::

Equality is also a set of rules. `Eq.refl` introduces it, `Eq.symm` and `Eq.trans` say that it is an equivalence relation, and `Eq.subst` replaces equals for equals in a context that a metavariable represents. A parsing note: `=` binds more tightly than the connectives, so `a = b ∧ c = d` reads `(a = b) ∧ (c = d)`.

```
Eq.refl  : ∀ (a : ?α), a = a
Eq.symm  : ?a = ?b → ?b = ?a
Eq.trans : ?a = ?b → ?b = ?c → ?a = ?c
Eq.subst : ?a = ?b → ?P ?a → ?P ?b
```

```lean
namespace Backward

theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c := by
  apply Eq.trans
  · exact hab
  · apply Eq.symm
    exact hcb

end Backward
```

The tactic `ac_rfl` extends `rfl` with associativity and commutativity for the operators registered as associative and commutative, and §4.6 registers our `add` among them.

## Examples

The examples below name the conversion that each `rfl` performs, then reason with the equality rules. The definition of `double` supports the δ-conversion.

```lean
namespace Backward

def double (n : ℕ) : ℕ := n + n

end Backward
```

{ex "ex-equality-alpha-conversion-renames-bound"}[] α-conversion renames the bound variable.

```lean
namespace Backward

theorem α_example {α β : Type} (f : α → β) :
    (fun x => f x) = (fun y => f y) := by
  rfl

end Backward
```

{ex "ex-equality-beta-conversion-applies-function"}[] β-conversion applies an anonymous function to its argument.

```lean
namespace Backward

theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x => f x) a = f a := by
  rfl

end Backward
```

{ex "ex-equality-delta-conversion-unfolds-definition"}[] δ-conversion unfolds the definition of `double`.

```lean
namespace Backward

theorem δ_example : double 5 = 5 + 5 := by
  rfl

end Backward
```

{ex "ex-equality-zeta-conversion-substitutes-let"}[] ζ-conversion substitutes the locally scoped `let`.

```lean
namespace Backward

theorem ζ_example :
    (let n : ℕ := 2
     n + n) = 4 := by
  rfl

end Backward
```

{ex "ex-equality-eta-conversion-identifies-fun"}[] η-conversion identifies `fun x => f x` with f itself.

```lean
namespace Backward

theorem η_example {α β : Type} (f : α → β) :
    (fun x => f x) = f := by
  rfl

end Backward
```

{ex "ex-equality-iota-conversion-projects-constructor"}[] ι-conversion projects a component out of a constructor application.

```lean
namespace Backward

theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a := by
  rfl

end Backward
```

{ex "ex-equality-rfl-depends-recursion-pattern"}[] `rfl` proves `add m 0 = m` and not `add 0 m = m`, since `add` recurses on its second argument, as the third worked example of Lecture 3 showed. The second statement waits for §4.6.

```lean
example (m : ℕ) : add m 0 = m := by
  rfl

example (m : ℕ) : add 0 m = m := by
  sorry
```

{ex "ex-equality-ac-rfl-addition"}[] `ac_rfl` proves an equation up to associativity and commutativity of `+`.

```lean
example (a b c : ℕ) : a + b + c = c + b + a := by
  ac_rfl
```

{ex "ex-equality-ac-rfl-multiplication"}[] The same shape holds for `*`, which is also registered as associative and commutative.

```lean
example (a b c : ℕ) : a * b * c = c * b * a := by
  ac_rfl
```

{ex "ex-equality-eq-subst-arbitrary-context"}[] `apply Eq.subst` replaces equals for equals under an arbitrary predicate, which unification recovers.

```lean
example (α : Type) (P : α → Prop) (a b : α)
    (hab : a = b) (hPa : P a) : P b := by
  apply Eq.subst hab
  exact hPa
```

# Rewriting Tactics

The tactic `rw` applies an equation as a left-to-right rewrite rule, once. It finds the first subterm that matches the left-hand side, instantiates the variables of the equation accordingly, replaces every occurrence of that instantiated subterm, and then tries `rfl`. A leading `←` uses the equation right to left, `at h` rewrites the hypothesis h instead of the target, and `at *` rewrites everywhere. Given a constant name instead of an equation, `rw` uses the defining equations of the constant, which is how `rw [Not]` expands a negation and `rw [add]` unfolds our `add`.

```lean
namespace Backward

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c := by
  rw [hab]
  rw [hcb]

theorem a_proof_of_negation (a : Prop) : a → ¬¬ a := by
  rw [Not]
  rw [Not]
  intro ha hna
  apply hna
  exact ha

end Backward
```

The tactic `simp` applies a standard set of rewrite rules, the *simp set*, exhaustively. The syntax `simp [t₁, …, tₙ]` adds theorems or constants for one invocation, `simp [-t]` removes one, `simp [*] at *` uses every hypothesis on every hypothesis and on the target, and the attribute `@[simp]` registers a theorem permanently.

```lean
namespace Backward

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
    (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 := by
  simp [hab, hcd]

end Backward
```

Rewriting is where proofs stop being predictable. The guide's advice is to try a tactic, study the subgoals that emerge, and adjust, rather than to plan every step in advance. In the guide's own words, DON'T PANIC.

## Examples

The examples below rewrite in the target and in the hypotheses, in both directions, and compare `rw` with `simp` on the same goal.

{ex "ex-rewriting-rw-left-to-right"}[] `rw [h]` rewrites the target left to right and closes it with the `rfl` it tries at the end.

```lean
example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) :
    f a = f b := by
  rw [h]
```

{ex "ex-rewriting-rw-right-to-left"}[] `rw [←h]` uses the same equation right to left.

```lean
example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) :
    f b = f a := by
  rw [←h]
```

{ex "ex-rewriting-rw-two-equations-in-turn"}[] `rw [h₁, h₂]` applies two equations in turn.

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  rw [h₁, h₂]
```

{ex "ex-rewriting-rw-at-hypothesis"}[] `rw [h₂] at h₁` rewrites the hypothesis, and the rewritten hypothesis closes the goal.

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  rw [h₂] at h₁
  exact h₁
```

{ex "ex-rewriting-rw-closes-by-rfl"}[] `rw` closes the goal on its own once the two sides coincide, because it tries `rfl` after rewriting.

```lean
example (a b : ℕ) (h : a = b) : a = b := by
  rw [h]
```

{ex "ex-rewriting-rw-constant-unfolds-equation"}[] `rw [add]` unfolds a defining equation of our `add`.

```lean
example (m n : ℕ) :
    add m (Nat.succ n) = Nat.succ (add m n) := by
  rw [add]
```

{ex "ex-rewriting-rw-not-expands-negation"}[] `rw [Not] at h` expands the negation in a hypothesis, which then applies as an implication.

```lean
example (a : Prop) (h : ¬a) : a → False := by
  rw [Not] at h
  exact h
```

{ex "ex-rewriting-simp-closes-arithmetic"}[] `simp` alone closes an arithmetic goal from the default simp set.

```lean
example (n : ℕ) : n + 0 + 0 = n := by
  simp
```

{ex "ex-rewriting-simp-every-occurrence-rw-first"}[] `simp [h]` rewrites every occurrence, where `rw [h]` rewrites only the occurrences of the first matching subterm. The first script needs two rewrites, one per instance of the pattern, and the second needs one `simp`.

```lean
example (f : ℕ → ℕ) (hf : ∀ x, f x = 0) :
    f 1 + f 2 = 0 := by
  rw [hf]
  rw [hf]

example (f : ℕ → ℕ) (hf : ∀ x, f x = 0) :
    f 1 + f 2 = 0 := by
  simp [hf]
```

{ex "ex-rewriting-simp-star-at-star"}[] `simp [*] at *` uses every hypothesis everywhere and closes a goal from two chained hypotheses.

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  simp [*] at *
```

# Proofs by Mathematical Induction

The tactic `induction` performs structural induction on a variable, producing one named subgoal per constructor of its type. For ℕ, built from `Nat.zero` and `Nat.succ`, structural induction is ordinary mathematical induction. The names after a constructor bind its arguments and the induction hypothesis, so the branch `| succ n' ih` provides the predecessor n' and the hypothesis ih about it. The general form for ℕ reads as follows.

```
induction n with
| zero       => (proof of the base case)
| succ n' ih => (proof of the step case)
```

The section recalls `add` and `mul` from Lecture 3 and proves the laws that computation left open there. The extracted exercise file repeats the definitions, so it stands alone.

```savedLean -keep
namespace Backward

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => 0
  | m, Nat.succ n => add m (mul m n)

end Backward
```

The first two theorems supply the recursive equations that `add` lacks, on its first argument. Each proof inducts on the variable the recursion consumes and closes the step case with `simp`, using the defining equations of `add` and the induction hypothesis.

```savedLean
namespace Backward

theorem add_zero (n : ℕ) : add 0 n = n := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

end Backward
```

Commutativity and associativity follow, with the two theorems above discharging the base and step cases of the first. These are `SorryTheorems.add_comm` and `SorryTheorems.add_assoc` of Lecture 3, now with real proofs.

```savedLean
namespace Backward

theorem add_comm (m n : ℕ) : add m n = add n m := by
  induction n with
  | zero       => simp [add, add_zero]
  | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

end Backward
```

The two instances below register `add` as associative and commutative, which is what `ac_rfl` consults. The `instance` command is the one Lecture 2 used for `Membership` and its companions, and chapter 5 of the guide explains the mechanism, in week 6 of the course.

```savedLean
namespace Backward

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

end Backward
```

Distributivity closes the section, with `ac_rfl` finishing what `simp` leaves.

```savedLean
namespace Backward

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) := by
  induction n with
  | zero       => rfl
  | succ n' ih =>
    simp [add, mul, ih]
    ac_rfl

end Backward
```

The guide offers two hints. Induct on the argument the recursion consumes, and read a difficult base case as a sign of the wrong induction variable or of a missing auxiliary theorem.[^addzero]

[^addzero]: The guide names `add 0 n = n` as `add_zero` even though `add` recurses on its second argument and the usual convention reads the zero from the statement, which would give `zero_add`. The third worked example of Lecture 3 called the same statement `zero_add`. These notes keep the guide's names.

## Examples

The examples below induct on ℕ and once on lists, watch the two subgoals, and check what the finished proofs rest on.

{ex "ex-induction-two-branches-trace"}[] `induction n with` produces one branch per constructor, and the trace shows the base and the step goals.

```lean (name := exInductionTrace)
example (n : ℕ) : add 0 n = n := by
  induction n with
  | zero =>
    trace_state
    rfl
  | succ n' ih =>
    trace_state
    simp [add, ih]
```

```leanOutput exInductionTrace
case zero
⊢ add 0 0 = 0
```

```leanOutput exInductionTrace
case succ
n' : ℕ
ih : add 0 n' = n'
⊢ add 0 (n' + 1) = n' + 1
```

{ex "ex-induction-base-case-rfl"}[] The base case alone. Zero on the right matches the first equation of `add`, so `rfl` closes it.

```lean
example : add 0 0 = 0 := by
  rfl
```

{ex "ex-induction-step-case-simp"}[] The step case alone, from its induction hypothesis.

```lean
example (n' : ℕ) (ih : add 0 n' = n') :
    add 0 (Nat.succ n') = Nat.succ n' := by
  simp [add, ih]
```

{ex "ex-induction-add-succ-two-variables"}[] `add_succ` follows the same pattern on a statement with two variables, inducting on the second, which the recursion consumes.

```lean
example (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]
```

{ex "ex-induction-add-assoc-last-variable"}[] Associativity, inducting on the last variable.

```lean
example (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]
```

{ex "ex-induction-wrong-variable-stalls"}[] The wrong induction variable stalls. Inducting on m leaves goals that neither `rfl` nor the induction hypothesis reaches, and the traces show why: the recursion of `add` consumes n, which both goals leave untouched.

```lean (name := exWrongVariable)
example (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  induction m with
  | zero =>
    trace_state
    sorry
  | succ m' ih =>
    trace_state
    sorry
```

```leanOutput exWrongVariable
case zero
n : ℕ
⊢ add (Nat.succ 0) n = (add 0 n).succ
```

```leanOutput exWrongVariable
case succ
n m' : ℕ
ih : add m'.succ n = (add m' n).succ
⊢ add (m' + 1).succ n = (add (m' + 1) n).succ
```

{ex "ex-induction-ac-rfl-registered-add"}[] With the two instances registered, `ac_rfl` reasons about `add` as it reasons about `+`.

```lean
example (a b c : ℕ) :
    add (add a b) c = add c (add b a) := by
  ac_rfl
```

{ex "ex-induction-mul-zero-first-argument"}[] The recursive equation of `mul` on its first argument, by induction on the second.

```lean
example (n : ℕ) : mul 0 n = 0 := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [mul, add, ih]
```

{ex "ex-induction-list-append-nil"}[] Induction on a list has one branch per constructor of `List`, with `nil` as the base and `cons` as the step. Weeks 6 and 7 treat structural induction on arbitrary inductive types.

```lean
namespace Backward

theorem append_nil {α : Type} (xs : List α) :
    appendPretty xs [] = xs := by
  induction xs with
  | nil          => rfl
  | cons x xs' ih => simp [appendPretty, ih]

end Backward
```

{ex "ex-induction-print-axioms-propext"}[] The finished proof rests on `propext`, which `simp` uses, and not on `sorryAx`, closing the loop with the third example of Lecture 3's theorem section.

```lean (name := exAxiomsAddComm)
#print axioms Backward.add_comm
```

```leanOutput exAxiomsAddComm
'Backward.add_comm' depends on axioms: [propext]
```

# Worked Examples

Each example below is carried out in full and verbalised, as the guide does. They are disjoint from the exercises, and Lean checks every line when the notes are built.

## Distributing a conjunction over a disjunction

The statement a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) uses only `intro`, `apply`, `exact` and bullets. The elimination rule of ∨ drives the proof, and juxtaposition instantiates it with the right conjunct of the hypothesis.

```lean
namespace Backward

theorem and_or_distrib (a b c : Prop) :
    a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) := by
  intro habc
  apply Or.elim (And.right habc)
  · intro hb
    apply Or.inl
    apply And.intro
    · exact And.left habc
    · exact hb
  · intro hc
    apply Or.inr
    apply And.intro
    · exact And.left habc
    · exact hc

end Backward
```

In words. Assume a ∧ (b ∨ c). Its right conjunct is a disjunction, and it suffices to prove the target from each disjunct. If b holds, it suffices to prove the left disjunct a ∧ b, whose parts are the left conjunct of the hypothesis and b itself. If c holds, the right disjunct a ∧ c follows the same way. Each bullet closes one branch, and the proof reads exactly like its pen-and-paper counterpart.

## A dead end and a backtrack

The statement a ∧ b → a ∨ c has two proofs of its disjunction to choose from, and only one works. `Or.inl` and `Or.inr` can turn a provable goal into an unprovable one. The first attempt commits to the right disjunct, and the trace shows a target c that no hypothesis proves, so only `sorry` closes the block.

```lean (name := deadEnd)
example (a b c : Prop) : a ∧ b → a ∨ c := by
  intro hab
  apply Or.inr
  trace_state
  sorry
```

```leanOutput deadEnd
a b c : Prop
hab : a ∧ b
⊢ c
```

The remedy is to remember the choice point and backtrack. The second attempt commits to the left disjunct, and the left conjunct of the hypothesis closes it.

```lean
namespace Backward

theorem and_imp_or (a b c : Prop) : a ∧ b → a ∨ c := by
  intro hab
  apply Or.inl
  exact And.left hab

end Backward
```

## `rw` versus `simp`

Given f and the equation hf : ∀ x, f x = x + 1, the target f (f 0) = 2 falls to either tactic, in different ways. `rw [hf]` rewrites the occurrences of the first matching subterm, here the outer application, and needs a second invocation for the inner one, after which the `rfl` it tries closes the goal. `simp [hf]` rewrites exhaustively and needs one invocation.

```lean
example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) :
    f (f 0) = 2 := by
  rw [hf, hf]

example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) :
    f (f 0) = 2 := by
  simp [hf]
```

The residual goal makes "first matching subterm" concrete. One `rw [hf]` rewrites the outer application and leaves the inner one in place.

```lean (name := rwResidual)
example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) :
    f (f 0) = 2 := by
  rw [hf]
  trace_state
  rw [hf]
```

```leanOutput rwResidual
f : ℕ → ℕ
hf : ∀ (x : ℕ), f x = x + 1
⊢ f 0 + 1 = 2
```

## Discharging `reverse_cons`

The final worked example of Lecture 3 stated `reverse (x :: xs) = snoc (reverse xs) x` and left it with `sorry`. Unfolding `reverse` turns the left side into `appendPretty (reverse xs) [x]`, so the statement mixes `appendPretty` and `snoc`, and the missing piece is the theorem that relates them. This is the guide's hint in action: a hard case usually signals a missing auxiliary theorem.

```lean
namespace Backward

theorem append_snoc {α : Type} (ys : List α) (x : α) :
    appendPretty ys [x] = snoc ys x := by
  induction ys with
  | nil           => rfl
  | cons y ys' ih => simp [appendPretty, snoc, ih]

theorem reverse_cons {α : Type} (x : α) (xs : List α) :
    reverse (x :: xs) = snoc (reverse xs) x := by
  simp [reverse, append_snoc]

end Backward
```

The auxiliary theorem inducts on the list that the recursion of `appendPretty` consumes, and the main theorem is then one `simp` away, using the defining equations of `reverse` and the auxiliary theorem as rewrite rules.

# Exercises

Prove each statement in Lean, replacing `sorry`. Download the exercise file [`Lecture04.lean`](example-code/Lectures/En/Lecture04.lean) and open it in VS Code. The file already contains the definitions of `add` and `mul` and the theorems of §4.6, so the induction exercises can build on them. Exercises 1 to 6 use only `intro`, `apply` and `exact`, following LoVe exercise sheet 3.

```savedImport
import Mathlib.Data.Nat.Notation
```

```savedComment
Exercises for Lecture 4: Backward Proofs.
Replace each `sorry` with a proof. Exercises 1 to 6 use only
`intro`, `apply`, and `exact`. Exercises 7 to 9 use
`induction`, `simp`, and `rw`. Exercise 10 is optional.
The definitions and theorems above come from the lecture.
```

{exercise "exr-two-basic-combinators"}[] Two basic combinators, the identity and the projection to the second argument.

```savedLean -keep
namespace Backward

theorem I (a : Prop) :
    a → a :=
  sorry

theorem K (a b : Prop) :
    a → b → b :=
  sorry

end Backward
```

{exercise "exr-permutation-arguments-implication"}[] Permutation of the two arguments of an implication.

```savedLean -keep
namespace Backward

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  sorry

end Backward
```

{exercise "exr-two-proofs-same-statement"}[] Two proofs of the same statement, differing in which hypothesis they use.

```savedLean -keep
namespace Backward

theorem proj_fst (a : Prop) :
    a → a → a :=
  sorry

-- Give a different answer than for `proj_fst`:
theorem proj_snd (a : Prop) :
    a → a → a :=
  sorry

end Backward
```

{exercise "exr-longer-chain-implications"}[] A longer chain of implications.

```savedLean -keep
namespace Backward

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  sorry

end Backward
```

{exercise "exr-contraposition-rule"}[] Contraposition. Recall that ¬a abbreviates a → False.

```savedLean -keep
namespace Backward

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  sorry

end Backward
```

{exercise "exr-distributivity-forall-and"}[] Distributivity of ∀ over ∧. The right-to-left direction needs a forward step by juxtaposition, as `And_swap_braces` does in the notes.

```savedLean -keep
namespace Backward

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  sorry

end Backward
```

{exercise "exr-recursive-equations-mul-first"}[] The recursive equations of `mul` on its first argument, mirroring `add_zero` and `add_succ` of §4.6.

```savedLean -keep
namespace Backward

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  sorry

theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  sorry

end Backward
```

{exercise "exr-mul-comm-assoc-induction"}[] Commutativity and associativity of `mul`, by induction. Choose the induction variable carefully.

```savedLean -keep
namespace Backward

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  sorry

end Backward
```

{exercise "exr-add-mul-symmetric-variant"}[] The symmetric variant of `mul_add`, using `rw`. To rewrite at one position only, instantiate the rule, as in `mul_comm _ l`.

```savedLean -keep
namespace Backward

theorem add_mul (l m n : ℕ) :
    add (mul n l) (mul n m) = mul (add l m) n :=
  sorry

end Backward
```

{exercise "exr-three-classical-axioms"}[] Optional. Three classical axioms and two implications between them. Avoid the theorems of the `Classical` namespace; `rw [ExcludedMiddle]` unfolds the definition, and `Or.elim` and `False.elim` do the rest.

```savedLean -keep
namespace Backward

def ExcludedMiddle : Prop :=
  ∀ a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀ a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀ a : Prop, (¬¬ a) → a

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
  sorry

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
  sorry

end Backward
```
