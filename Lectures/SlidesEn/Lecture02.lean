/-
Slides for Lecture 2, generated from checked sources. Each
top-level section is one slide; the document title and the intro
paragraphs form the title slide. All Lean code is elaborated at
build time and is identical to the code in the lecture notes
(`Lectures/En/Lecture02.lean`) where the two overlap.
-/

import VersoManual
import Lectures.Meta.SlideDeck

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Predicate Logic and Sets" =>

Quantifiers, negation laws, quantifier order, and sets as predicates in Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Open the lecture notes](../en/Lecture-2___-Predicate-Logic-and-Sets/)

Based on [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL), chapters [2](https://djvelleman.github.io/HTPIwL/Chap2.html) and [3](https://djvelleman.github.io/HTPIwL/Chap3.html).

# §2.1 Predicates and quantifiers

* A *predicate* on a type α assigns a proposition to each element, so in Lean it is a function `α → Prop`.

```lean (name := checkPred)
#check fun n : Nat => n > 3
```
```leanOutput checkPred
fun n => n > 3 : Nat → Prop
```

* Quantifiers *bind* the variable of a predicate and produce a proposition (Frege, 1879). The variable ranges over a type, inferred when the context determines it.

:::table +header
*
  * Symbol
  * Name
  * Reading
*
  * ∀ x, P x
  * universal quantifier
  * P x holds for every x
*
  * ∃ x, P x
  * existential quantifier
  * P x holds for some x
:::

```lean (name := checkQuant)
#check ∃ n : Nat, n > 3
#check ∀ n : Nat, n > 3
```
```leanOutput checkQuant
∃ n, n > 3 : Prop
```
```leanOutput checkQuant
∀ (n : Nat), n > 3 : Prop
```

A quantifier takes the predicate, of type `Nat → Prop`, to a proposition, of type `Prop`.

# §2.2 The universal quantifier

* *Introduce* ∀ x, P x by considering an arbitrary element: `intro`, the same tactic that introduces implications.

* *Eliminate* it by instantiation. A universal hypothesis is a *function*, so `h a` instantiates it at `a`; `specialize` does it in place.

::::cols
:::col
```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro a
  exact (h a).left
```
:::
:::col
```lean
example (α : Type) (P Q : α → Prop) (h : ∀ x, P x → Q x)
    (a : α) (hPa : P a) : Q a := by
  specialize h a
  exact h hPa
```
:::
::::

# §2.2 Distribution over conjunction

The universal quantifier distributes over conjunction. The proof combines the quantifier rules with the Lecture 1 rules for conjunction and the biconditional.

```lean
theorem forall_and_distrib (α : Type) (P Q : α → Prop) :
    (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro a
      exact (h a).left
    · intro a
      exact (h a).right
  · intro h a
    exact ⟨h.left a, h.right a⟩
```

# §2.3 The existential quantifier

* *Introduce* ∃ x, P x by exhibiting a *witness* with its proof: the anonymous constructor `⟨3, rfl⟩`, or the `exists` tactic.

* *Eliminate* it by naming a witness and its proof: `cases` (one case, constructor `intro`) or `obtain ⟨a, ha⟩ := h` in one step.

```lean
example : ∃ n : Nat, n * n = 9 := ⟨3, rfl⟩
```

::::cols
:::col
```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  cases h with
  | intro a ha => exact ⟨a, ha.left⟩
```
:::
:::col
```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.right⟩
```
:::
::::

# §2.3 A pointwise implication

The theorem below combines the two quantifiers. A pointwise implication carries existence from P to Q, and the witness does not change.

```lean
theorem exists_imp_exists (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, P x) → ∃ x, Q x := by
  intro hex
  obtain ⟨a, hPa⟩ := hex
  exact ⟨a, h a hPa⟩
```

# §2.4 Quantifier negation laws

:::table +header
*
  * Name
  * Equivalence
*
  * Negation of ∃
  * ¬(∃ x, P x) ≡ ∀ x, ¬P x
*
  * Negation of ∀
  * ¬(∀ x, P x) ≡ ∃ x, ¬P x
:::

* They exchange negation with the quantifiers, extending the *De Morgan laws* of Lecture 1.

* The first law is *constructive* in both directions.

* In the second, producing the witness needs *classical reasoning*, as the first De Morgan law did: two applications of `Classical.byContradiction`.

# §2.4 The two laws in Lean

::::cols
:::col
```lean
theorem not_exists_iff (α : Type) (P : α → Prop) :
    ¬(∃ x, P x) ↔ ∀ x, ¬P x := by
  constructor
  · intro h a hPa
    exact h ⟨a, hPa⟩
  · intro h hex
    obtain ⟨a, hPa⟩ := hex
    exact h a hPa
```
:::
:::col
```lean
theorem not_forall_exists (α : Type) (P : α → Prop)
    (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  apply Classical.byContradiction
  intro hne
  apply h
  intro a
  apply Classical.byContradiction
  intro hnPa
  exact hne ⟨a, hnPa⟩
```
:::
::::

# §2.4 Beyond intro, obtain, exact

* `intro` accepts the *anonymous constructor pattern*, introducing the existential and destructing it in one step.

* A negated goal is a *function into False*, so a proof term with a pattern-matching `fun` proves it, with no tactics.

::::cols
:::col
{lbl}[Pattern intro]

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨a, hPa⟩
  exact h a hPa
```
:::
:::col
{lbl}[Proof term]

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, P x) : ¬∃ x, ¬P x :=
  fun ⟨a, hnPa⟩ => hnPa (h a)
```
:::
::::

# §2.5 The order of quantifiers

* The order *determines what a statement asserts*.

* In ∀ y, ∃ x, R x y, the witness x may *depend on y*; in ∃ x, ∀ y, R x y, a single witness serves every y. The *uniform witness* is the stronger statement.

* Quantifiers of the *same kind* commute; the exchanges for ∀ and ∃ appeared as examples in §2.2 and §2.3.

* Quantifiers of *different kinds* do not commute. Only one direction holds: the stronger order implies the weaker one.

# §2.5 The swap and the counterexample

```lean
theorem exists_forall_swap (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha b⟩
```

The converse fails. Over ℕ take R x y as x ≥ y. Both claims of the counterexample hold in Lean.

::::cols
:::col
```lean
example : ∀ y : Nat, ∃ x : Nat, x ≥ y := by
  intro b
  exact ⟨b, Nat.le_refl b⟩
```
:::
:::col
```lean
example : ¬∃ x : Nat, ∀ y : Nat, x ≥ y := by
  intro ⟨a, ha⟩
  exact absurd (ha (a + 1)) (Nat.not_succ_le_self a)
```
:::
::::

# §2.6 Sets as predicates

* A set of elements of α is determined by *which elements belong to it*, so the membership predicate determines the set. We take this as the definition.

* A set given by a property *is* the predicate, and a membership proof is a proof of the property.

```lean
def Set (α : Type) : Type := α → Prop
```

```lean -show
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩
```

```lean
def Evens : Set Nat := fun n => ∃ k, n = 2 * k

example : (6 : Nat) ∈ Evens := ⟨3, rfl⟩
```

# §2.6 Type classes and instances

* Lean resolves notations such as `x ∈ s` through *type classes*. The class declares the notation; an `instance` provides its meaning at a particular type.

* `Set α` is a definition of this lecture, so no registered instance covers it. The instances below supply the meaning: `x ∈ s` unfolds to `s x`.

```lean
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩

instance : HasSubset (Set α) :=
  ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩

instance : Union (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩

instance : Inter (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩
```

{lbl}[Each notation unfolds to its definition]

```lean
example (α : Type) (s t : Set α) (h : s ⊆ t)
    (x : α) (hx : x ∈ s) : x ∈ t := h x hx

example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s) : x ∈ s ∪ t := Or.inl hx

example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s ∩ t) : x ∈ t := hx.right
```

# §2.6 Russell's paradox

* Naive set theory admits a set for *every property*. Take R to be the set of all sets that are not elements of themselves.

* Then *R ∈ R holds exactly when R ∉ R*, a contradiction, and the theory collapses.

* In Lean, s : Set α contains only elements of α, and s itself has type Set α, not α, so `s ∈ s` is *not well typed*. There is no way to state the property that defines R, and the paradox does not arise.

{cite}[B. Russell, letter to Frege, 16 June 1902.]

# §2.6 Inclusion, union, intersection

* The inclusion s ⊆ t is a *universally quantified implication*, so its proofs begin with `intro x hx`.

* Membership in ∩ is a *conjunction* and in ∪ a *disjunction*; the connective rules of Lecture 1 apply. Set identities are stated as *inclusions*, since equality needs extensionality.

::::cols
:::col
```lean
theorem inter_subset_left (α : Type) (s t : Set α) :
    s ∩ t ⊆ s := by
  intro x hx
  exact hx.left
```
:::
:::col
```lean
theorem union_subset_swap (α : Type) (s t : Set α) :
    s ∪ t ⊆ t ∪ s := by
  intro x hx
  cases hx with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
```
:::
::::

# Summary

* A *predicate* is a function `α → Prop`; quantifiers bind its variable and yield a proposition.

* ∀: introduce with `intro`; eliminate by instantiation, `h a` or `specialize`.

* ∃: introduce with a *witness*, `⟨3, rfl⟩` or `exists`; eliminate with `obtain ⟨a, ha⟩ := h`.

* The negation laws exchange ¬ with the quantifiers; ¬∃ is constructive in both directions, ¬∀ needs `Classical.byContradiction`.

* Quantifier order matters: the uniform witness ∃ x, ∀ y is stronger, and only (∃ x, ∀ y) → (∀ y, ∃ x) holds.

* A set is its membership predicate, `Set α := α → Prop`, with `Membership`, `HasSubset`, `Union`, `Inter` instances giving the notation.

* Inclusion proofs start with `intro x hx`; membership in ∩ is a conjunction and in ∪ a disjunction, pointwise.

Exercises: see the [lecture notes](../en/Lecture-2___-Predicate-Logic-and-Sets/).
