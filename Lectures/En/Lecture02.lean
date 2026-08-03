import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lecture 2: Predicate Logic and Sets" =>

%%%
tag := "lecture-2"
%%%

This lecture extends propositional logic with quantifiers and introduces sets, following chapters [2](https://djvelleman.github.io/HTPIwL/Chap2.html) and [3](https://djvelleman.github.io/HTPIwL/Chap3.html) of [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL). It presents the proof rules for the universal and existential quantifiers, the laws that relate them under negation, and sets as predicates in Lean.

*This lecture is also available as [presentation slides](../slides/lecture-2.en.html).*

# Predicates and Quantifiers

Lecture 1 excluded "x is even" from the propositions because its truth depends on the unbound variable x. A *predicate* makes this dependence explicit. A predicate on a type α assigns a proposition to each element of α, so in Lean a predicate is a function of type `α → Prop`.

```lean (name := checkPred)
#check fun n : Nat => n > 3
```
```leanOutput checkPred
fun n => n > 3 : Nat → Prop
```

Quantifiers bind the variable of a predicate and produce a proposition.{margin}[G. Frege, *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*, Verlag von Louis Nebert, Halle, 1879.] We write P x for the proposition that the predicate P yields at x.

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

The quantifier *binds* its variable, so ∀ x, P x depends on no free variable and is a proposition. The variable ranges over a type. For example, `∃ n : Nat, n * n = 9` states that some natural number squares to 9. When the context determines the type, Lean infers it and we omit the annotation.

# The Universal Quantifier

To prove ∀ x, P x, consider an arbitrary element and prove the proposition at it. The tactic `intro`, which introduced implications in Lecture 1, also introduces universal quantifiers.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro a
  exact (h a).left
```

The proof also uses the elimination rule. A hypothesis h : ∀ x, P x ∧ Q x is a function that returns a proof of P a ∧ Q a for each a, so the application `h a` *instantiates* it at a. This parallels Lecture 1, where a proof of an implication was a function on proofs. The tactic `specialize` instantiates a universal hypothesis in place.

```lean
example (α : Type) (P Q : α → Prop) (h : ∀ x, P x → Q x)
    (a : α) (hPa : P a) : Q a := by
  specialize h a
  exact h hPa
```

The universal quantifier distributes over conjunction. The proof combines the rules for the quantifier with the rules of Lecture 1 for conjunction and the biconditional.

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

## Examples

The examples below combine the two rules of this section with the connectives of Lecture 1.

Example 1. Implication is reflexive at each element.

```lean
example (α : Type) (P : α → Prop) : ∀ x, P x → P x := by
  intro a hPa
  exact hPa
```

Example 2. A universal hypothesis instantiates at any given element. The application `h a` is already the proof, so no tactics are needed.

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, P x) (a : α) : P a := h a
```

Example 3. Instantiating both variables of a binary predicate at the same element yields the diagonal. The tactic `apply` unifies the hypothesis with the goal and finds both instantiations.

```lean
example (α : Type) (R : α → α → Prop)
    (h : ∀ x, ∀ y, R x y) : ∀ x, R x x := by
  intro a
  apply h
```

Example 4. Consecutive universal quantifiers commute.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∀ x, ∀ y, R x y) : ∀ y, ∀ x, R x y := by
  intro b a
  exact h a b
```

Example 5. Conjunction commutes under the quantifier. The tactic `have` records the instantiated hypothesis, and `constructor` splits the goal into the two conjuncts.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∧ Q x) : ∀ x, Q x ∧ P x := by
  intro a
  have ha := h a
  constructor
  · exact ha.right
  · exact ha.left
```

Example 6. A disjunct entails the disjunction at each element. Applying `Or.inl` reduces the disjunction to its left side.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x) : ∀ x, P x ∨ Q x := by
  intro a
  apply Or.inl
  exact h a
```

Example 7. A pointwise disjunction whose left side fails everywhere yields its right side.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∨ Q x) (hn : ∀ x, ¬P x) : ∀ x, Q x := by
  intro a
  cases h a with
  | inl hPa => exact absurd hPa (hn a)
  | inr hQa => exact hQa
```

Example 8. Contraposition applies at each element. The proof reasons forward, deriving Q a with `have` before reaching the contradiction.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hn : ∀ x, ¬Q x) : ∀ x, ¬P x := by
  intro a hPa
  have hQa : Q a := h a hPa
  exact hn a hQa
```

Example 9. An antecedent that does not mention the quantified variable moves inside the quantifier.

```lean
example (α : Type) (P : Prop) (Q : α → Prop)
    (h : P → ∀ x, Q x) : ∀ x, P → Q x := by
  intro a hP
  exact h hP a
```

Example 10. When the type has an element, ∀ x, P x refutes ∀ x, ¬P x.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (h : ∀ x, P x) : ¬∀ x, ¬P x := by
  intro hn
  exact hn a (h a)
```

# The Existential Quantifier

To prove ∃ x, P x, exhibit a *witness* and prove the proposition at it. The anonymous constructor of Lecture 1 pairs the witness with the proof. The term `rfl` proves an equation whose two sides compute to the same value.

```lean
example : ∃ n : Nat, n * n = 9 := ⟨3, rfl⟩
```

The tactic `exists` provides the witness in tactic mode and closes the remaining goal when it holds by computation.

```lean
example : ∃ n : Nat, n * n = 9 := by
  exists 3
```

To use a hypothesis h : ∃ x, P x, name a witness and the proof that it satisfies P. The proposition ∃ x, P x has the single constructor `intro`, so the tactic `cases` treats it as it treated disjunction in Lecture 1, now with one case.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  cases h with
  | intro a ha => exact ⟨a, ha.left⟩
```

The tactic `obtain` destructures the hypothesis in one step, with a pattern that mirrors the anonymous constructor.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.right⟩
```

The theorem below combines the two quantifiers. A pointwise implication carries existence from P to Q, and the witness does not change.

```lean
theorem exists_imp_exists (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, P x) → ∃ x, Q x := by
  intro hex
  obtain ⟨a, hPa⟩ := hex
  exact ⟨a, h a hPa⟩
```

## Examples

The examples below combine the witness rule and existential elimination with the connectives of Lecture 1.

Example 1. The witness 7 proves a concrete existential by computation.

```lean
example : ∃ n : Nat, n + 5 = 12 := ⟨7, rfl⟩
```

Example 2. Both 0 and 1 satisfy `n * n = n`, and the proof picks the witness 1.

```lean
example : ∃ n : Nat, n * n = n := by
  exists 1
```

Example 3. An element together with a proof at it is the introduction rule packaged as a pair.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (hPa : P a) : ∃ x, P x := ⟨a, hPa⟩
```

Example 4. On an inhabited type, a universal statement yields an existential one. The tactic `specialize` instantiates the hypothesis, and `exists` finds it as an assumption.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (h : ∀ x, P x) : ∃ x, P x := by
  specialize h a
  exists a
```

Example 5. A proposition that does not mention the bound variable escapes the quantifier.

```lean
example (α : Type) (P : Prop) (h : ∃ _ : α, P) : P := by
  obtain ⟨_, hP⟩ := h
  exact hP
```

Example 6. Conjunction commutes under the quantifier.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro a ha => exact ⟨a, ha.right, ha.left⟩
```

Example 7. An existential of a conjunction splits, and the two parts share the witness. The pattern of `obtain` destructures the conjunction under the quantifier in one step.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : (∃ x, P x) ∧ (∃ x, Q x) := by
  obtain ⟨a, hPa, hQa⟩ := h
  constructor
  · exact ⟨a, hPa⟩
  · exact ⟨a, hQa⟩
```

Example 8. The witness for P x also witnesses Q x → P x.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x) : ∃ x, Q x → P x := by
  obtain ⟨a, hPa⟩ := h
  exists a
  intro _hQ
  exact hPa
```

Example 9. Consecutive existential quantifiers commute.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∃ y, R x y) : ∃ y, ∃ x, R x y := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨b, a, hab⟩
```

Example 10. An existential disjunction whose right side fails everywhere witnesses its left side.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∨ Q x) (hn : ∀ x, ¬Q x) : ∃ x, P x := by
  obtain ⟨a, ha⟩ := h
  cases ha with
  | inl hPa => exact ⟨a, hPa⟩
  | inr hQa => exact absurd hQa (hn a)
```

# Quantifier Negation Laws

The De Morgan laws of Lecture 1 exchange negation with conjunction and disjunction. The laws below exchange negation with the quantifiers.

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

The first law is constructive in both directions.

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

In the second law, the direction from ∃ x, ¬P x to ¬(∀ x, P x) is constructive, and the converse direction requires classical reasoning, as the first De Morgan law did in Lecture 1. Two applications of `Classical.byContradiction` produce the witness.

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

# The Order of Quantifiers

Consecutive quantifiers of the same kind commute, and quantifiers of different kinds do not. One direction of the exchange holds. A witness that satisfies R with every y in particular satisfies R with each given y.

```lean
theorem exists_forall_swap (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha b⟩
```

The converse fails. Over the natural numbers, take R x y to be x ≥ y. Then ∀ y, ∃ x, R x y holds, since each y satisfies y ≥ y, and ∃ x, ∀ y, R x y states that some natural number is greater than or equal to every natural number, which is false.

# Sets

[Chapter 3](https://djvelleman.github.io/HTPIwL/Chap3.html) of HTPIwL develops proofs about sets. A set of elements of a type α is determined by which elements belong to it, so the membership predicate determines the set. In Lean, we take this as the definition.

```savedLean
def Set (α : Type) : Type := α → Prop
```

Every element of a set comes from the fixed type α. In this typed setting, the collection of all sets that do not contain themselves cannot be written down, so Russell's paradox does not arise.{margin}[B. Russell, letter to Frege, 16 June 1902. In J. van Heijenoort, *From Frege to Gödel: A Source Book in Mathematical Logic, 1879–1931*, Harvard University Press, 1967, pp. 124–125.]

The instance below registers the notation x ∈ s, which unfolds by definition to the application s x. In this instance and the following ones, Lean binds the free type variable α automatically.

```savedLean
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩
```

A set given by a property is the predicate itself, and a membership proof is a proof of the property. Mathematical notation writes such a set in set-builder notation, as the set of all n such that `∃ k, n = 2 * k`. Lean core has no set-builder notation, so we write the predicate directly.

```lean
def Evens : Set Nat := fun n => ∃ k, n = 2 * k

example : (6 : Nat) ∈ Evens := ⟨3, rfl⟩
```

The inclusion s ⊆ t states that every element of s belongs to t.

```savedLean
instance : HasSubset (Set α) :=
  ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩
```

An inclusion is a universally quantified implication, so its proofs begin by considering an arbitrary element together with the assumption that it belongs to the left side. Union and intersection apply the connectives of Lecture 1 pointwise.

```savedLean
instance : Union (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩

instance : Inter (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩
```

Membership in an intersection is by definition a conjunction, so the projections of Lecture 1 apply to it.

```lean
theorem inter_subset_left (α : Type) (s t : Set α) :
    s ∩ t ⊆ s := by
  intro x hx
  exact hx.left
```

Membership in a union is a disjunction, so the tactic `cases` splits it.

```lean
theorem union_subset_swap (α : Type) (s t : Set α) :
    s ∪ t ⊆ t ∪ s := by
  intro x hx
  cases hx with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
```

Two sets with the same elements are equal. Proving such an equality requires extensionality principles beyond the logic presented so far, so we state set identities as inclusions.

# Exercises

Prove each statement in Lean, replacing `sorry` with a proof. Download the exercise file [`Lecture02.lean`](example-code/Lectures/En/Lecture02.lean) and open it in VS Code. The file already contains the definitions of `Set`, membership, inclusion, union, and intersection.

```savedComment
Exercises for Lecture 2: Predicate Logic and Sets.
Replace each `sorry` with a proof. The definitions above
come from the lecture.
```

Exercise 1. The universal quantifier distributes over implication.

```savedLean -keep
theorem exercise1 (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hP : ∀ x, P x) : ∀ x, Q x := by
  sorry
```

Exercise 2. The existential quantifier distributes over disjunction.

```savedLean -keep
theorem exercise2 (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry
```

Exercise 3. Eliminate the existential hypothesis, then instantiate the universal one at the witness.

```savedLean -keep
theorem exercise3 (α : Type) (P : α → Prop) (Q : Prop)
    (h : ∃ x, P x → Q) (hP : ∀ x, P x) : Q := by
  sorry
```

Exercise 4. Inclusion is transitive.

```savedLean -keep
theorem exercise4 (α : Type) (s t u : Set α)
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  sorry
```

Exercise 5. Intersection distributes over union.

```savedLean -keep
theorem exercise5 (α : Type) (s t u : Set α) :
    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  sorry
```
