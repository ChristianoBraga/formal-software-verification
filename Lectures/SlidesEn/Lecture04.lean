/-
Slides for Lecture 4, generated from checked sources. Each
top-level section is one slide; the document title and the intro
paragraphs form the title slide. All Lean code is elaborated at
build time and is identical to the code in the lecture notes
(`Lectures/En/Lecture04.lean`) where the two overlap.

Only the ℕ and ℤ notations are imported from Mathlib, plus the
Lecture 3 deck for `add`, `mul`, `appendPretty`, `reverse` and
`snoc`. The full library would collide with the decks' own names
once all decks build together.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesEn.Lecture03

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Backward Proofs" =>

Tactic mode, basic tactics, rewriting, and induction in Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Open the lecture notes](../en/Lecture-4___-Backward-Proofs/)

Based on the [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), chapter 3.

# §4.1 Backward and forward

* A *tactic* operates on a goal and either proves it or creates subgoals. A goal is the sequent C ⊢ Q, with antecedent C, the local context, and consequent Q, the conclusion.

::::cols
:::col
{lbl}[Backward, from the goal]

```
to prove c,
  by hbc it suffices to prove b;
to prove b,
  by hab it suffices to prove a;
and ha proves a.
```
:::
:::col
{lbl}[Forward, from the hypotheses]

```
from ha and hab, we have b;
from b and hbc, we have c.
```
:::
::::

* The characteristic phrase of a backward proof is *"it suffices to prove"*. In a natural deduction derivation, the premises of each rule sit above the inference line and the conclusion below it. The forward reading goes from the assumptions, at the top, to the conclusion, and the backward reading goes from the conclusion to the assumptions.

# §4.1 Tactic mode

* The keyword `by` enters tactic mode, and each line after it is one tactic. `trace_state` prints the goal between the steps.

::::cols
:::col
```lean (name := fstOfTwo)
namespace Backward

theorem first_of_two :
    ∀ a b : Prop, a → b → a := by
  intro a b
  trace_state
  intro ha hb
  trace_state
  apply ha

end Backward
```
:::
:::col
{lbl}[After the first and the second intro]

```leanOutput fstOfTwo
a b : Prop
⊢ a → b → a
```

```leanOutput fstOfTwo
a b : Prop
ha : a
hb : b
⊢ a
```
:::
::::

# §4.2 The four basic tactics

* Basic tactics perform one elementary transformation of the proof state each, and none depends on a particular connective or theory.

* `intro` moves variables and assumptions into the context; `apply` matches the conclusion of the goal with that of a theorem and leaves the assumptions as goals; `exact` closes the goal with a term; `assumption` searches the context.

::::cols
:::col
```lean
namespace Backward

theorem first_of_two_params (a b : Prop)
    (ha : a) (hb : b) : a := by
  apply ha

theorem first_of_two_exact (a b : Prop)
    (ha : a) (hb : b) : a := by
  exact ha

end Backward
```
:::
:::col
```lean
namespace Backward

theorem first_of_two_assumption (a b : Prop)
    (ha : a) (hb : b) : a := by
  assumption

theorem imp_chain (a b c : Prop) (hab : a → b)
    (hbc : b → c) : a → c := by
  intro ha
  apply hbc
  apply hab
  apply ha

end Backward
```
:::
::::

* Lean inserts the parameters left of the colon into the local context of the initial goal, so these proofs need no `intro`.

# §4.2 Losing provability

::::cols
:::col
{lbl}[apply can lose a provable goal]

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

```lean
example (a b : Prop) (hb : b) : a ∨ b := by
  apply Or.inr
  exact hb
```
:::
:::col
{lbl}[sorry, clear, rename]

```lean
namespace Backward

theorem drop_unused (p q : Prop)
    (hp : p) (hq : q)
    (hpq : p → q) : q := by
  clear hp hpq p
  rename q => hgoal
  exact hgoal

end Backward
```
:::
::::

* A provable goal stays provable after `intro`. `apply` can turn a provable goal into an unprovable one. `sorry` closes anything and `#print axioms` reports it as `sorryAx`.

# §4.3 Rules as theorems

* Every inference figure of Lecture 1 is an ordinary theorem, applied backwards by `apply`.

::::cols
:::col
{lbl}[Introduction and elimination]

```
And.intro : ?a → ?b → ?a ∧ ?b
And.left  : ?a ∧ ?b → ?a
And.right : ?a ∧ ?b → ?b
Or.inl    : ?a → ?a ∨ ?b
Or.inr    : ?b → ?a ∨ ?b
Or.elim   : ?a ∨ ?b →
  (?a → ?c) → (?b → ?c) → ?c
Iff.intro : (?a → ?b) →
  (?b → ?a) → (?a ↔ ?b)
Iff.mp    : (?a ↔ ?b) → ?a → ?b
Iff.mpr   : (?a ↔ ?b) → ?b → ?a
```
:::
:::col
```lean
namespace Backward

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a := by
  intro hab
  apply And.intro
  apply And.right
  exact hab
  apply And.left
  exact hab

end Backward
```
:::
::::

# §4.3 Metavariables and bullets

* A *metavariable* ?a stands for a term still to be determined, and *unification* determines it. The `·` bullet focuses one subgoal; *juxtaposition* instantiates a rule forwards.

::::cols
:::col
```lean
namespace Backward

theorem and_swap_bullets :
    ∀ a b : Prop, a ∧ b → b ∧ a := by
  intro a b hab
  apply And.intro
  · exact And.right hab
  · exact And.left hab

end Backward
```
:::
:::col
```lean
namespace Backward

opaque fixedFun : ℕ → ℕ

theorem fixedFun_at_seven
    (h : ∀ n : ℕ, fixedFun n = 0) :
    fixedFun 7 = 0 := by
  exact h 7

end Backward
```
:::
::::

* Passing `hab` directly to `And.right` is a small forward step inside a backward proof, and it avoids the metavariables that `apply And.right` would leave.

# §4.3 Quantifiers, truth, falsehood, negation

```
Exists.intro : ∀ (w : ?α), ?p w → ∃ x, ?p x
Exists.elim  : (∃ x, ?p x) → (∀ (w : ?α), ?p w → ?b) → ?b
True.intro   : True
False.elim   : False → ?c
Classical.em : ∀ (p : Prop), p ∨ ¬p
Classical.byContradiction : (¬?a → False) → ?a
```

* Negation needs no rules: ¬a is *defined* as a → False, so `intro` applies to a negated conclusion.

* `True.intro` is the only rule for truth; falsehood has no introduction rule, and `False.elim` closes any goal from a proof of `False`.

```lean
namespace Backward

theorem Not_Not_intro (a : Prop) : a → ¬¬ a := by
  intro ha hna
  apply hna
  exact ha

end Backward
```

# §4.3 Strategies

The guide's strategies for propositional proofs.

* Look at the conclusion. An implication or a negation calls for `intro`.

* Look at the hypotheses. A conjunction offers `And.left` and `And.right`, a disjunction offers `Or.elim`, an equivalence offers `Iff.mp` and `Iff.mpr`.

* Match the conclusion of the goal with an introduction rule and `apply` it.

* Prefer tactics that preserve provability while they make progress, and record the choice points where a tactic commits to a side.

* When a subgoal repeats a hypothesis, `exact` or `assumption` closes it.

* When nothing constructive applies, consider a case analysis on `Classical.em`.

* If the proof makes no progress, backtrack to the last choice point and try the other option.

# §4.4 `rfl` and the conversions

* `rfl` proves l = r when the sides agree *up to computation*, and each computation step is a named conversion.

::::cols
:::col
```
α  renames a bound variable
β  applies an anonymous function
δ  unfolds a definition
ζ  substitutes a let
η  fun x => f x equals f
ι  projects a constructor
```

```lean
namespace Backward

def double (n : ℕ) : ℕ := n + n

end Backward
```
:::
:::col
```lean
namespace Backward

theorem β_example {α β : Type}
    (f : α → β) (a : α) :
    (fun x => f x) a = f a := by
  rfl

theorem δ_example :
    double 5 = 5 + 5 := by
  rfl

theorem ι_example {α β : Type}
    (a : α) (b : β) :
    Prod.fst (a, b) = a := by
  rfl

end Backward
```
:::
::::

* `ac_rfl` adds associativity and commutativity of the registered operators, as in `a + b + c = c + b + a`.

# §4.4 Equality as rules

::::cols
:::col
```
Eq.refl  : ∀ (a : ?α), a = a
Eq.symm  : ?a = ?b → ?b = ?a
Eq.trans : ?a = ?b → ?b = ?c →
           ?a = ?c
Eq.subst : ?a = ?b → ?P ?a → ?P ?b
```

* `=` binds more tightly than the connectives, so `a = b ∧ c = d` reads `(a = b) ∧ (c = d)`.
:::
:::col
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
:::
::::

# §4.5 `rw`

* `rw` applies an equation left to right, once: it finds the first matching subterm, replaces every occurrence of it, and then tries `rfl`. `←` reverses the equation, `at h` rewrites a hypothesis, and a constant name uses its defining equations.

::::cols
:::col
```lean
namespace Backward

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c := by
  rw [hab]
  rw [hcb]

end Backward
```
:::
:::col
```lean
namespace Backward

theorem not_intro_demo (a : Prop) :
    (a → False) → ¬ a := by
  rw [Not]
  intro h
  exact h

end Backward
```
:::
::::

# §4.5 `simp`

* `simp` rewrites with the *simp set* exhaustively. `simp [t]` adds a theorem or constant for one call, `simp [-t]` removes one, `simp [*] at *` uses everything everywhere, and `@[simp]` registers a theorem permanently.

```lean
namespace Backward

theorem simp_congruence {α : Type} (a b : α)
    (k : α → ℕ → ℕ) (hab : a = b) :
    k a (2 + 3) = k b 5 := by
  simp [hab]

end Backward
```

* Rewriting is where proofs stop being predictable. Try a tactic, study the subgoals that emerge, and adjust. In the guide's words, DON'T PANIC.

# §4.6 Induction

* `induction` produces one named subgoal per constructor, and the branch names bind the constructor arguments and the induction hypothesis.

::::cols
:::col
```
induction n with
| zero       => (base case)
| succ n' ih => (step case)
```

* Induct on the argument the recursion consumes.

* A difficult base case signals the wrong variable or a missing auxiliary theorem.
:::
:::col
```lean
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
:::
::::

# §4.6 Commutativity and `ac_rfl`

* These are the laws Lecture 3 stated with `sorry`, now proved, and the instances let `ac_rfl` treat `add` like `+`.

::::cols
:::col
```lean
namespace Backward

theorem add_comm (m n : ℕ) :
    add m n = add n m := by
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
:::
:::col
```lean
namespace Backward

instance Associative_add :
    Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add :
    Std.Commutative add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
    mul l (add m n) =
      add (mul l m) (mul l n) := by
  induction n with
  | zero       => rfl
  | succ n' ih =>
    simp [add, mul, ih]
    ac_rfl

end Backward
```
:::
::::

# §4.7 Worked example: discharging `reverse_cons`

* Lecture 3 stated `reverse (x :: xs) = snoc (reverse xs) x` with `sorry`. The statement mixes `appendPretty` and `snoc`, so the missing piece is the theorem that relates them.

::::cols
:::col
{lbl}[The auxiliary theorem]

```lean
namespace Backward

theorem append_snoc {α : Type}
    (ys : List α) (x : α) :
    appendPretty ys [x] = snoc ys x := by
  induction ys with
  | nil           => rfl
  | cons y ys' ih =>
    simp [appendPretty, snoc, ih]

end Backward
```
:::
:::col
{lbl}[The theorem, one simp away]

```lean
namespace Backward

theorem reverse_cons {α : Type}
    (x : α) (xs : List α) :
    reverse (x :: xs) =
      snoc (reverse xs) x := by
  simp [reverse, append_snoc]

end Backward
```

* A hard case usually signals a missing auxiliary theorem.
:::
::::

# Summary

* A tactic transforms the goal, and a backward proof reads as a chain of "it suffices to".

* `intro`, `apply`, `exact` and `assumption` prove the propositional theorems of this lecture, and among them only `intro` never loses a provable goal.

* Every rule of Lecture 1 is a theorem that `apply` consumes backwards and juxtaposition instantiates forwards.

* `rfl` decides equality up to computation, one named conversion at a time, and `ac_rfl` adds associativity and commutativity.

* `rw` rewrites once at the first match and then tries `rfl`; `simp` rewrites exhaustively with the simp set.

* `induction … with` proves the general laws that computation cannot reach, and it discharges Lecture 3's statements.

* Lecture 5 turns the same proofs around, into forward and structured proofs.

Exercises: see the [lecture notes](../en/Lecture-4___-Backward-Proofs/).
