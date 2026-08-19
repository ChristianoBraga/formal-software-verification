/-
Slides for Lecture 5, generated from checked sources. Each
top-level section is one slide; the document title and the intro
paragraphs form the title slide. All Lean code is elaborated at
build time and is identical to the code in the lecture notes
(`Lectures/En/Lecture05.lean`) where the two overlap.

The Lecture 4 deck supplies `add`, `mul`, `appendPretty`,
`reverse`, `snoc` and the `Backward` theorems. The `fix` and
`assume` term parsers, copied from LoVe's `LoVelib` (which the
slide build cannot import without a `Set` name clash), are
defined below. Everything new is declared inside
`namespace Forward`.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesEn.Lecture04

section StructuredParsers
open Lean Lean.Parser Lean.Parser.Term

@[term_parser] def slideFix :=
  leading_parser withPosition
    ("fix " >> many1 Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

@[term_parser] def slideAssume :=
  leading_parser withPosition
    ("assume " >> Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

macro_rules
| `(fix $x* : $ty; $y)    => `(fun $x* : $ty => $y)
| `(assume $h : $ty; $y)  => `(fun $h : $ty => $y)

end StructuredParsers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Forward Proofs" =>

Structured proofs, calculational proofs, and the PAT principle

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Open the lecture notes](../en/Lecture-5___-Forward-Proofs/)

Based on the [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), chapter 4.

# §5.1 Forward and backward, once more

* A *forward* proof starts at the hypotheses and derives new facts until it reaches the goal. Its phrase is *"from … we have …"*, the mirror of Lecture 4's *"it suffices to prove"*.

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

* A natural deduction derivation admits both readings; this lecture writes the forward one, as a structured term.

# §5.1 The PAT principle

* *Propositions as types, proofs as terms.* A proposition is a type, and a proof of it is a term of that type. An implication a → b is the type of functions from proofs of a to proofs of b, so a proof of an implication *is* a function, and ∀ x, P x is a dependent function type.

```lean (name := patCheck)
#check (fun (a : Prop) (h : a) => h)
#check (assume h : True; h)
```

```leanOutput patCheck
fun a h => h : ∀ (a : Prop), a → a
```

```leanOutput patCheck
fun h => h : True → True
```

* `fix` and `assume`, from LoVe's library, are the term parsers that expand to `fun`.

# §5.2 Structured constructs

* `fix x : α` discharges a ∀; `assume h : P` discharges a →; `have h : P := pf` names a forward fact; `show P from pf` restates the goal.

::::cols
:::col
```lean
namespace Forward

theorem fst_of_two_props :
    ∀ a b : Prop, a → b → a :=
  fix a b : Prop;
  assume ha : a;
  assume hb : b;
  show a from ha

end Forward
```
:::
:::col
{lbl}[The same term, three ways]

```lean
namespace Forward

example : ∀ a b : Prop, a → b → a :=
  fix a b : Prop;
  assume ha : a; assume hb : b; ha

example : ∀ a b : Prop, a → b → a :=
  fun a b ha hb => ha

end Forward
```
:::
::::

# §5.2 Structured versus tactic

* The composition of implications, forwards as two `have` steps and backwards as the Lecture 4 script.

::::cols
:::col
```lean
namespace Forward

theorem prop_comp (a b c : Prop)
    (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a;
  have hb : b := hab ha;
  show c from hbc hb

end Forward
```
:::
:::col
```lean
namespace Forward

example (a b c : Prop)
    (hab : a → b) (hbc : b → c) :
    a → c := by
  intro ha
  apply hbc
  apply hab
  exact ha

end Forward
```
:::
::::

* From ha and hab we have b; from b and hbc we have c.

# §5.3 Forward about conjunction and disjunction

* Elimination rules take a hypothesis apart; introduction rules and the anonymous constructor build the goal.

::::cols
:::col
```lean
namespace Forward

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  assume h : a ∧ b;
  have ha : a := And.left h;
  have hb : b := And.right h;
  show b ∧ a from
    And.intro hb ha

end Forward
```
:::
:::col
```lean
namespace Forward

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  assume h : a ∨ b;
  Or.elim h
    (fun ha => Or.inr ha)
    (fun hb => Or.inl hb)

end Forward
```
:::
::::

# §5.3 Forward about existential and biconditional

* `Exists.intro t pf` supplies a witness; `Exists.elim h f` names one; `Iff.mp` and `Iff.mpr` apply an equivalence each way.

::::cols
:::col
```lean
namespace Forward

example (P : ℕ → Prop) (h : P 3) :
    ∃ n, P n :=
  Exists.intro 3 h

example (α : Type) (P : α → Prop)
    (Q : Prop) (h : ∃ x, P x)
    (f : ∀ x, P x → Q) : Q :=
  Exists.elim h f

end Forward
```
:::
:::col
```lean
namespace Forward

example (a b : Prop)
    (h : a ↔ b) (ha : a) : b :=
  Iff.mp h ha

example (a b : Prop)
    (h : a ↔ b) (hb : b) : a :=
  Iff.mpr h hb

end Forward
```
:::
::::

# §5.3 One-point rules

* The payoff. A quantifier whose bound variable is pinned by an equation collapses to a single instance.

::::cols
:::col
```lean
namespace Forward

theorem Forall_one_point (α : Type)
    (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x;
     h t rfl)
    (assume hpt : P t;
     fix x : α;
     assume hxt : x = t;
     hxt ▸ hpt)

end Forward
```
:::
:::col
```lean
namespace Forward

theorem Exists_one_point (α : Type)
    (t : α) (P : α → Prop) :
    (∃ x, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume h : ∃ x, x = t ∧ P x;
     Exists.elim h
       (fun x hx => hx.1 ▸ hx.2))
    (assume hpt : P t;
     Exists.intro t
       (And.intro rfl hpt))

end Forward
```
:::
::::

# §5.4 `calc`

* A calculational proof lays a chain of equalities out for the reader, each step justified by a rewrite or a lemma, `calc` composing `Eq.trans`.

```lean
namespace Forward

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

end Forward
```

* Each step is the kind of equation `rw` consumes, and `ac_rfl` closes a rearrangement.

# §5.4 `calc` versus `simp` and `Eq.trans`

* One identity, three proofs. `calc` documents the chain, `Eq.trans` shows the transitivity, `ac_rfl` hides it all.

::::cols
:::col
```lean
namespace Forward

theorem two_mul_trans (m n : ℕ) :
    2 * m + n = m + n + m := by
  have h1 :
      2 * m + n = (m + m) + n := by
    rw [Nat.two_mul]
  have h2 :
      (m + m) + n = m + n + m := by
    ac_rfl
  exact Eq.trans h1 h2

end Forward
```
:::
:::col
```lean
namespace Forward

theorem two_mul_ac (m n : ℕ) :
    2 * m + n = m + n + m := by
  rw [Nat.two_mul]
  ac_rfl

end Forward
```

* The choice is about the reader, not the checker.
:::
::::

# §5.5 Forward steps in tactic mode

* `have h : P := pf` adds a proved fact; `let x := t` adds an abbreviation; `specialize` and `obtain` are forward steps too. Real proofs mix the two directions.

::::cols
:::col
```lean
namespace Forward

example (P : ℕ → Prop)
    (h : ∀ n, P n) : P 7 := by
  specialize h 7
  exact h

end Forward
```
:::
:::col
```lean
namespace Forward

example (α : Type) (P : α → Prop)
    (Q : Prop) (hex : ∃ x, P x)
    (h : ∀ x, P x → Q) : Q := by
  obtain ⟨a, ha⟩ := hex
  exact h a ha

end Forward
```
:::
::::

# §5.5 A mixed proof

* A forward `have` inside a backward proof, each direction marked.

::::cols
:::col
```lean
namespace Forward

theorem prop_comp_tactical
    (a b c : Prop)
    (hab : a → b) (hbc : b → c) :
    a → c := by
  intro ha
  have hb : b := hab ha
  exact hbc hb

end Forward
```
:::
:::col
* `intro ha` and `exact` work backwards from the goal.

* `have hb : b := hab ha` works forwards from the hypotheses.

* The mixed proof is often the shortest, taking each fact from wherever it is easiest to reach.
:::
::::

# §5.6 Proofs by recursion

* Under PAT, a recursive function returning a proof *is* a proof by induction, and the recursive call is the induction hypothesis.

```lean
namespace Forward

theorem append_nil {α : Type} :
    ∀ (xs : List α), appendPretty xs [] = xs
  | []      => rfl
  | x :: xs => congrArg (List.cons x) (append_nil xs)

theorem append_assoc {α : Type} :
    ∀ (xs ys zs : List α),
      appendPretty (appendPretty xs ys) zs
        = appendPretty xs (appendPretty ys zs)
  | [],      _, _ => rfl
  | x :: xs, ys, zs =>
      congrArg (List.cons x) (append_assoc xs ys zs)

end Forward
```

# §5.6 Recursion versus `induction`

* The recursive proof and the `induction` tactic are the same proof; the recursive call is the branch's `ih`.

::::cols
:::col
```lean
namespace Forward

theorem reverse_append {α : Type} :
    ∀ (xs ys : List α),
      reverse (appendPretty xs ys)
        = appendPretty (reverse ys)
            (reverse xs)
  | [],      ys => by
      simp [reverse, appendPretty,
            append_nil]
  | x :: xs, ys => by
      simp [reverse, appendPretty,
            reverse_append xs ys,
            append_assoc]

end Forward
```
:::
:::col
```lean
namespace Forward

theorem reverse_append_tac
    {α : Type} (xs ys : List α) :
    reverse (appendPretty xs ys)
      = appendPretty (reverse ys)
          (reverse xs) := by
  induction xs with
  | nil =>
    simp [reverse, appendPretty,
          append_nil]
  | cons x xs' ih =>
    simp [reverse, appendPretty,
          ih, append_assoc]

end Forward
```

* Weeks 6 and 7 give the general method.
:::
::::

# §5.7 Worked example: `Forall_one_point`

* A quantifier proof natural forwards and awkward backwards.

```lean
namespace Forward

theorem Forall_one_point_worked (α : Type)
    (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

end Forward
```

* Forwards, instantiate h at t and close t = t by `rfl`. Backwards, fix x, assume x = t, and rewrite with `▸`.

# §5.7 Worked example: the distributive law

* `a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c)`, the first worked example of Lecture 4, now as a structured term.

::::cols
:::col
```lean
namespace Forward

theorem and_or_distrib
    (a b c : Prop) :
    a ∧ (b ∨ c) →
      (a ∧ b) ∨ (a ∧ c) :=
  assume habc : a ∧ (b ∨ c);
  have ha : a := And.left habc;
  Or.elim (And.right habc)
    (fun hb =>
      Or.inl (And.intro ha hb))
    (fun hc =>
      Or.inr (And.intro ha hc))

end Forward
```
:::
:::col
* From habc we have a, named ha.

* Its right conjunct b ∨ c gives two cases.

* In each case we build the matching disjunct with the anonymous constructor.

* The backward script planned from the goal; the forward term builds from the hypotheses.
:::
::::

# Summary

* A forward proof reads *"from … we have …"*, the mirror of backward's *"it suffices to prove"*.

* A structured proof is a term shaped like its proposition, with `fix`, `assume`, `have`, `show`.

* Under PAT a proposition is a type and a proof is a term, so `assume` is `fun`.

* Forward reasoning uses the rule names by juxtaposition and the anonymous constructor.

* `calc` lays a chain of equalities out for the reader; `ac_rfl` and `simp` hide it.

* Real proofs mix directions, a forward `have` inside a backward `apply`.

* Structural recursion is a proof by induction, formalised in weeks 6 and 7.

Exercises: see the [lecture notes](../en/Lecture-5___-Forward-Proofs/).
