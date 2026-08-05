import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lecture 2: Predicate Logic and Sets" =>

%%%
tag := "lecture-2"
%%%

```lean -show
namespace Lecture2
```

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

Quantifiers bind the variable of a predicate and produce a proposition, and {numref}[tbl-quantifiers] names the two.{margin}[G. Frege, *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*, Verlag von Louis Nebert, Halle, 1879.] We write P x for the proposition that the predicate P yields at x.

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

{tabcap "tbl-quantifiers"}[The two quantifiers, with their symbols and readings.]

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

{ex "ex-universal-quantifier-implication-reflexive-each-element"}[] Implication is reflexive at each element.

```lean
example (α : Type) (P : α → Prop) : ∀ x, P x → P x := by
  intro a hPa
  exact hPa
```

{ex "ex-universal-quantifier-universal-hypothesis-instantiates-any"}[] A universal hypothesis instantiates at any given element. The application `h a` is already the proof, so no tactics are needed.

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, P x) (a : α) : P a := h a
```

{ex "ex-universal-quantifier-instantiating-both-variables-binary"}[] Instantiating both variables of a binary predicate at the same element yields the diagonal. The tactic `apply` unifies the hypothesis with the goal and finds both instantiations.

```lean
example (α : Type) (R : α → α → Prop)
    (h : ∀ x, ∀ y, R x y) : ∀ x, R x x := by
  intro a
  apply h
```

{ex "ex-universal-quantifier-consecutive-universal-quantifiers-commute"}[] Consecutive universal quantifiers commute.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∀ x, ∀ y, R x y) : ∀ y, ∀ x, R x y := by
  intro b a
  exact h a b
```

{ex "ex-universal-quantifier-conjunction-commutes-under-quantifier"}[] Conjunction commutes under the quantifier. The tactic `have` records the instantiated hypothesis, and `constructor` splits the goal into the two conjuncts.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∧ Q x) : ∀ x, Q x ∧ P x := by
  intro a
  have ha := h a
  constructor
  · exact ha.right
  · exact ha.left
```

{ex "ex-universal-quantifier-disjunct-entails-disjunction-each"}[] A disjunct entails the disjunction at each element. Applying `Or.inl` reduces the disjunction to its left side.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x) : ∀ x, P x ∨ Q x := by
  intro a
  apply Or.inl
  exact h a
```

{ex "ex-universal-quantifier-pointwise-disjunction-whose-left"}[] A pointwise disjunction whose left side fails everywhere yields its right side.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x ∨ Q x) (hn : ∀ x, ¬P x) : ∀ x, Q x := by
  intro a
  cases h a with
  | inl hPa => exact absurd hPa (hn a)
  | inr hQa => exact hQa
```

{ex "ex-universal-quantifier-contraposition-applies-each-element"}[] Contraposition applies at each element. The proof reasons forward, deriving Q a with `have` before reaching the contradiction.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hn : ∀ x, ¬Q x) : ∀ x, ¬P x := by
  intro a hPa
  have hQa : Q a := h a hPa
  exact hn a hQa
```

{ex "ex-universal-quantifier-antecedent-does-not-mention"}[] An antecedent that does not mention the quantified variable moves inside the quantifier.

```lean
example (α : Type) (P : Prop) (Q : α → Prop)
    (h : P → ∀ x, Q x) : ∀ x, P → Q x := by
  intro a hP
  exact h hP a
```

{ex "ex-universal-quantifier-when-type-has-element"}[] When the type has an element, ∀ x, P x refutes ∀ x, ¬P x.

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

{ex "ex-existential-quantifier-witness-7-proves-concrete"}[] The witness 7 proves a concrete existential by computation.

```lean
example : ∃ n : Nat, n + 5 = 12 := ⟨7, rfl⟩
```

{ex "ex-existential-quantifier-both-0-1-satisfy"}[] Both 0 and 1 satisfy `n * n = n`, and the proof picks the witness 1.

```lean
example : ∃ n : Nat, n * n = n := by
  exists 1
```

{ex "ex-existential-quantifier-element-together-proof-introduction"}[] An element together with a proof at it is the introduction rule packaged as a pair.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (hPa : P a) : ∃ x, P x := ⟨a, hPa⟩
```

{ex "ex-existential-quantifier-inhabited-type-universal-statement"}[] On an inhabited type, a universal statement yields an existential one. The tactic `specialize` instantiates the hypothesis, and `exists` finds it as an assumption.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (h : ∀ x, P x) : ∃ x, P x := by
  specialize h a
  exists a
```

{ex "ex-existential-quantifier-proposition-does-not-mention"}[] A proposition that does not mention the bound variable escapes the quantifier.

```lean
example (α : Type) (P : Prop) (h : ∃ _ : α, P) : P := by
  obtain ⟨_, hP⟩ := h
  exact hP
```

{ex "ex-existential-quantifier-conjunction-commutes-under-quantifier"}[] Conjunction commutes under the quantifier.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  cases h with
  | intro a ha => exact ⟨a, ha.right, ha.left⟩
```

{ex "ex-existential-quantifier-existential-conjunction-splits-two"}[] An existential of a conjunction splits, and the two parts share the witness. The pattern of `obtain` destructures the conjunction under the quantifier in one step.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∧ Q x) : (∃ x, P x) ∧ (∃ x, Q x) := by
  obtain ⟨a, hPa, hQa⟩ := h
  constructor
  · exact ⟨a, hPa⟩
  · exact ⟨a, hQa⟩
```

{ex "ex-existential-quantifier-witness-p-x-also"}[] The witness for P x also witnesses Q x → P x.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x) : ∃ x, Q x → P x := by
  obtain ⟨a, hPa⟩ := h
  exists a
  intro _hQ
  exact hPa
```

{ex "ex-existential-quantifier-consecutive-existential-quantifiers-commute"}[] Consecutive existential quantifiers commute.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∃ y, R x y) : ∃ y, ∃ x, R x y := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨b, a, hab⟩
```

{ex "ex-existential-quantifier-existential-disjunction-whose-right"}[] An existential disjunction whose right side fails everywhere witnesses its left side.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x, P x ∨ Q x) (hn : ∀ x, ¬Q x) : ∃ x, P x := by
  obtain ⟨a, ha⟩ := h
  cases ha with
  | inl hPa => exact ⟨a, hPa⟩
  | inr hQa => exact absurd hQa (hn a)
```

# Quantifier Negation Laws

The De Morgan laws of Lecture 1 exchange negation with conjunction and disjunction. The laws of {numref}[tbl-quantifier-negation] exchange negation with the quantifiers.

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

{tabcap "tbl-quantifier-negation"}[The quantifier negation laws.]

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

## Examples

The examples below apply the two negation laws and combine them with the connectives of Lecture 1. Examples 6 and 10 reason classically.

{ex "ex-quantifier-negation-laws-property-fails-everywhere-admits"}[] A property that fails everywhere admits no witness. This is the constructive direction of the first law. The anonymous constructor pattern in `intro` introduces the existential and destructs it in one step, so no `obtain` is needed.

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨a, hPa⟩
  exact h a hPa
```

{ex "ex-quantifier-negation-laws-conversely-if-no-witness"}[] Conversely, if no witness exists, the property fails at each element.

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro a hPa
  exact h ⟨a, hPa⟩
```

{ex "ex-quantifier-negation-laws-witness-refutes-negation-existential"}[] A witness refutes the negation of the existential.

```lean
example (α : Type) (P : α → Prop)
    (a : α) (hPa : P a) : ¬¬∃ x, P x := by
  intro hn
  exact hn ⟨a, hPa⟩
```

{ex "ex-quantifier-negation-laws-property-holds-everywhere-excludes"}[] A property that holds everywhere excludes any counterexample. The proof is a proof term, as in Lecture 1. Since the negated goal is a function into `False`, a `fun` that matches the counterexample's witness proves it.

```lean
example (α : Type) (P : α → Prop)
    (h : ∀ x, P x) : ¬∃ x, ¬P x :=
  fun ⟨a, hnPa⟩ => hnPa (h a)
```

{ex "ex-quantifier-negation-laws-counterexample-refutes-universal-statement"}[] A counterexample refutes the universal statement. This is the constructive direction of the second law.

```lean
example (α : Type) (P : α → Prop)
    (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hall
  obtain ⟨a, hnPa⟩ := h
  exact hnPa (hall a)
```

{ex "ex-quantifier-negation-laws-converse-example-4-requires"}[] The converse of {numref}[ex-quantifier-negation-laws-property-holds-everywhere-excludes] requires classical reasoning. Given the absence of counterexamples, `Classical.byContradiction` proves the property at each element.

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∃ x, ¬P x) : ∀ x, P x := by
  intro a
  apply Classical.byContradiction
  intro hnPa
  exact h ⟨a, hnPa⟩
```

{ex "ex-quantifier-negation-laws-pointwise-implication-transports-absence"}[] A pointwise implication transports the absence of witnesses from the conclusion to the premise. The pattern in `intro` again destructs the existential at introduction.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hn : ¬∃ x, Q x) : ¬∃ x, P x := by
  intro ⟨a, hPa⟩
  exact hn ⟨a, h a hPa⟩
```

{ex "ex-quantifier-negation-laws-when-no-element-satisfies"}[] When no element satisfies both properties, each element that satisfies the first fails to satisfy the second.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ¬∃ x, P x ∧ Q x) : ∀ x, P x → ¬Q x := by
  intro a hPa hQa
  exact h ⟨a, hPa, hQa⟩
```

{ex "ex-quantifier-negation-laws-negating-existential-disjunction-yields"}[] Negating an existential disjunction yields, at each element, the conjunction of the negations, which combines the first law with a De Morgan law.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ¬∃ x, P x ∨ Q x) : ∀ x, ¬P x ∧ ¬Q x := by
  intro a
  constructor
  · intro hPa
    exact h ⟨a, Or.inl hPa⟩
  · intro hQa
    exact h ⟨a, Or.inr hQa⟩
```

{ex "ex-quantifier-negation-laws-theorem-this-section-extracts"}[] The theorem `not_forall_exists` of this section extracts a counterexample, and the pointwise implication converts it into a witness.

```lean
example (α : Type) (P Q : α → Prop) (h : ¬∀ x, P x)
    (hq : ∀ x, ¬P x → Q x) : ∃ x, Q x := by
  obtain ⟨a, hnPa⟩ := not_forall_exists α P h
  exact ⟨a, hq a hnPa⟩
```

# The Order of Quantifiers

The order of quantifiers determines what a statement asserts. In ∀ y, ∃ x, R x y, the witness x may depend on y, and different values of y may require different witnesses. In ∃ x, ∀ y, R x y, a single witness x satisfies R with every y at once. The second form asserts a uniform witness, so it is the stronger statement.

Quantifiers of the same kind commute, and the examples of the two previous sections proved the exchanges for ∀ and for ∃. Quantifiers of different kinds do not commute, and only one direction of the exchange holds. The stronger order implies the weaker one. A witness that satisfies R with every y in particular satisfies R with each given y.

```lean
theorem exists_forall_swap (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha b⟩
```

The converse fails. Over the natural numbers, take R x y to be x ≥ y. Then ∀ y, ∃ x, R x y holds, since each y satisfies y ≥ y, and ∃ x, ∀ y, R x y states that some natural number is greater than or equal to every natural number, which is false.

## Examples

The examples below move quantifiers across one another. The last two prove in Lean the two claims of the counterexample above.

{ex "ex-order-quantifiers-witness-relates-every-element"}[] A witness that relates to every element in particular relates to itself.

```lean
example (α : Type) (R : α → α → Prop)
    (h : ∃ x, ∀ y, R x y) : ∃ x, R x x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha a⟩
```

{ex "ex-order-quantifiers-existential-universal-statement-yields"}[] An existential-universal statement yields the doubly existential one when the inner type has an element.

```lean
example (α β : Type) (R : α → β → Prop) (b : β)
    (h : ∃ x, ∀ y, R x y) : ∃ x, ∃ y, R x y := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, b, ha b⟩
```

{ex "ex-order-quantifiers-doubly-universal-statement-yields"}[] A doubly universal statement yields the mixed order when the type of witnesses has an element.

```lean
example (α β : Type) (R : α → β → Prop) (a : α)
    (h : ∀ x, ∀ y, R x y) : ∀ y, ∃ x, R x y := by
  intro b
  exact ⟨a, h a b⟩
```

{ex "ex-order-quantifiers-theorem-function-applying-hypothesis"}[] The theorem `exists_forall_swap` is a function, and applying it to a hypothesis and an element gives the instantiated conclusion. The proof is the application itself.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ∃ x, ∀ y, R x y) (b : β) : ∃ x, R x b :=
  exists_forall_swap α β R h b
```

{ex "ex-order-quantifiers-conjunction-under-two-quantifiers"}[] A conjunction under the two quantifiers projects to its left conjunct, preserving the witness.

```lean
example (α β : Type) (R S : α → β → Prop)
    (h : ∃ x, ∀ y, R x y ∧ S x y) : ∃ x, ∀ y, R x y := by
  obtain ⟨a, ha⟩ := h
  exists a
  intro b
  exact (ha b).left
```

{ex "ex-order-quantifiers-two-existential-universal-hypotheses"}[] Two existential-universal hypotheses combine into a doubly existential conjunction, and each witness instantiates the universal of the other.

```lean
example (α β : Type) (R S : α → β → Prop)
    (h1 : ∃ x, ∀ y, R x y) (h2 : ∃ y, ∀ x, S x y) :
    ∃ x, ∃ y, R x y ∧ S x y := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a, b, ha b, hb a⟩
```

{ex "ex-order-quantifiers-three-quantifiers-existential-witness"}[] With three quantifiers, the existential witness serves for every z, so the outer universal moves to the front.

```lean
example (α β γ : Type) (T : α → β → γ → Prop)
    (h : ∃ x, ∀ y, ∀ z, T x y z) :
    ∀ z, ∃ x, ∀ y, T x y z := by
  intro c
  obtain ⟨a, ha⟩ := h
  exists a
  intro b
  exact ha b c
```

{ex "ex-order-quantifiers-contraposition-transports-negation-opposite"}[] Contraposition of `exists_forall_swap` transports the negation in the opposite direction.

```lean
example (α β : Type) (R : α → β → Prop)
    (h : ¬∀ y, ∃ x, R x y) : ¬∃ x, ∀ y, R x y := by
  intro hex
  exact h (exists_forall_swap α β R hex)
```

{ex "ex-order-quantifiers-first-claim-counterexample-above"}[] The first claim of the counterexample above. Each natural number is greater than or equal to itself.

```lean
example : ∀ y : Nat, ∃ x : Nat, x ≥ y := by
  intro b
  exact ⟨b, Nat.le_refl b⟩
```

{ex "ex-order-quantifiers-second-claim-no-natural"}[] The second claim. No natural number is greater than or equal to every natural number, since a + 1 exceeds a. The lemma `Nat.not_succ_le_self` refutes a ≥ a + 1.

```lean
example : ¬∃ x : Nat, ∀ y : Nat, x ≥ y := by
  intro ⟨a, ha⟩
  exact absurd (ha (a + 1)) (Nat.not_succ_le_self a)
```

# Sets

[Chapter 3](https://djvelleman.github.io/HTPIwL/Chap3.html) of HTPIwL develops proofs about sets. A set of elements of a type α is determined by which elements belong to it, so the membership predicate determines the set. In Lean, we take this as the definition.

```savedLean
def Set (α : Type) : Type := α → Prop
```

Every element of a set comes from the fixed type α, and this typing discipline blocks *Russell's paradox*.{margin}[B. Russell, letter to Frege, 16 June 1902. In J. van Heijenoort, *From Frege to Gödel: A Source Book in Mathematical Logic, 1879–1931*, Harvard University Press, 1967, pp. 124–125.] Naive set theory admits a set for every property. Take R to be the set of all sets that are not elements of themselves. Then R ∈ R holds exactly when R ∉ R, which is a contradiction, and the theory collapses. In Lean, a set s : Set α contains only elements of α, and s itself has type Set α, not α, so the expression s ∈ s is not well typed. There is no way to state the property that defines R or to form the collection, so the paradox does not arise.

Nothing so far gives the symbol ∈ a meaning at our sets, and Lean does not build one in. A *type class* declares an operation and leaves it without meaning, and an `instance` declaration supplies the meaning at one type. The notation x ∈ s reaches ours in three steps, and each step lives in a different place.

The symbol is ordinary notation, declared in the core module `Init.Notation`. It abbreviates an application and nothing more.

```
notation:50 a:50 " ∈ " b:50 => Membership.mem b a
```

The name `Membership.mem` on the right is the single field of a class declared in the core module `Init.Prelude`. The class fixes the shape of the operation, taking the type of the elements and the type of the container, and it gives no definition.

```
class Membership (α : outParam (Type u)) (γ : Type v) where
  mem : γ → α → Prop
```

The container comes first in `mem` and second in the notation, so x ∈ s abbreviates `Membership.mem s x`.

The third step is ours. When Lean elaborates x ∈ s, it searches the registered instances for one whose container type matches the type of s. `Set α` is a definition of this lecture, so that search finds nothing and the notation fails to elaborate. The instance below ends the search and gives `mem` its definition at `Set α`. In this instance and the following ones, Lean binds the free type variable α automatically.

```savedLean
instance : Membership α (Set α) :=
  ⟨fun s a => s a⟩
```

Printing a membership with the notation turned off shows the two steps at once, the expansion of the symbol and the instance that the elaborator found.

```lean (name := checkMem)
set_option pp.notation false in
#check fun (α : Type) (s : Set α) (x : α) => x ∈ s
```
```leanOutput checkMem
fun α s x => Membership.mem s x : (α : Type) → Set α → α → Prop
```

With the instance in scope, x ∈ s is the application s x by definition, so the two are interchangeable and `rfl` proves them equal.

```lean
example (α : Type) (s : Set α) (x : α) :
    (x ∈ s) = s x := rfl
```

The three steps split between two of the components of {numref}[fig-lean-components]. The macro expander performs the first, replacing the symbol by the application, and the elaborator performs the third, choosing the instance from the type of s.

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

The notation unfolds to its definition. A hypothesis h : s ⊆ t applies to an element and a membership proof.

```lean
example (α : Type) (s t : Set α) (h : s ⊆ t)
    (x : α) (hx : x ∈ s) : x ∈ t := h x hx
```

An inclusion is a universally quantified implication, so its proofs begin by considering an arbitrary element together with the assumption that it belongs to the left side. Union and intersection apply the connectives of Lecture 1 pointwise.

```savedLean
instance : Union (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩

instance : Inter (Set α) :=
  ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩
```

Both notations unfold likewise, so the proof terms of Lecture 1 build and use memberships directly.

```lean
example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s) : x ∈ s ∪ t := Or.inl hx

example (α : Type) (s t : Set α) (x : α)
    (hx : x ∈ s ∩ t) : x ∈ t := hx.right
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

## Examples

The examples below prove memberships and inclusions directly from the definitions. Each inclusion proof begins by introducing an element and its membership hypothesis, and the notations unfold to the connectives and quantifiers of the previous sections.

{ex "ex-sets-set-given-predicate-contains"}[] A set given by a predicate contains an element exactly when the predicate holds at it. The witness 3 proves that 9 is a square.

```lean
def Squares : Set Nat := fun n => ∃ k, n = k * k

example : (9 : Nat) ∈ Squares := ⟨3, rfl⟩
```

{ex "ex-sets-inclusion-reflexive-proof-introduces"}[] Inclusion is reflexive. The proof introduces an element and its membership hypothesis and returns the hypothesis unchanged.

```lean
example (α : Type) (s : Set α) : s ⊆ s := by
  intro x hx
  exact hx
```

{ex "ex-sets-union-contains-left-side"}[] The union contains its left side. Membership in the union is a disjunction, and `Or.inl` picks the left side.

```lean
example (α : Type) (s t : Set α) : s ⊆ s ∪ t := by
  intro x hx
  exact Or.inl hx
```

{ex "ex-sets-intersection-commutes-inclusion-membership"}[] Intersection commutes as an inclusion. Membership in the intersection is a conjunction, and the anonymous constructor swaps its parts.

```lean
example (α : Type) (s t : Set α) : s ∩ t ⊆ t ∩ s := by
  intro x hx
  exact ⟨hx.right, hx.left⟩
```

{ex "ex-sets-union-contains-intersection"}[] The union contains the intersection.

```lean
example (α : Type) (s t : Set α) : s ∩ t ⊆ s ∪ t := by
  intro x hx
  exact Or.inl hx.left
```

{ex "ex-sets-when-t-u-both"}[] When t and u both contain s, their intersection contains s.

```lean
example (α : Type) (s t u : Set α)
    (h1 : s ⊆ t) (h2 : s ⊆ u) : s ⊆ t ∩ u := by
  intro x hx
  exact ⟨h1 x hx, h2 x hx⟩
```

{ex "ex-sets-when-u-contains-both"}[] When u contains both sides of a union, u contains the union. The tactic `cases` splits the disjunction.

```lean
example (α : Type) (s t u : Set α)
    (h1 : s ⊆ u) (h2 : t ⊆ u) : s ∪ t ⊆ u := by
  intro x hx
  cases hx with
  | inl hs => exact h1 x hs
  | inr ht => exact h2 x ht
```

{ex "ex-sets-union-fixed-set-preserves"}[] Union with a fixed set preserves inclusion.

```lean
example (α : Type) (s t u : Set α)
    (h : s ⊆ t) : s ∪ u ⊆ t ∪ u := by
  intro x hx
  cases hx with
  | inl hs => exact Or.inl (h x hs)
  | inr hu => exact Or.inr hu
```

{ex "ex-sets-empty-set-whose-membership"}[] The empty set, whose membership predicate is `False` at every element, is a subset of every set. `False.elim` closes the goal.

```lean
def EmptySet (α : Type) : Set α := fun _ => False

example (α : Type) (s : Set α) : EmptySet α ⊆ s := by
  intro x hx
  exact False.elim hx
```

{ex "ex-sets-every-set-subset-universal"}[] Every set is a subset of the universal set, whose membership predicate is `True` at every element.

```lean
def UnivSet (α : Type) : Set α := fun _ => True

example (α : Type) (s : Set α) : s ⊆ UnivSet α := by
  intro x _hx
  exact True.intro
```

# Worked Examples

Each example below appears two ways, as a proof term and as a tactic proof. The two present the same proof, and Lean checks both scripts when the notes are built. The quantifier rules follow the same introduction and elimination discipline as the connectives of Lecture 1, so we omit the derivation trees and let the terms mirror them. These propositions are disjoint from the examples of the earlier sections and from the exercises.

## Contraposition under quantifiers

The witness of the failure of Q also witnesses the failure of P, since the implication at that element sends a proof of P a to a proof of Q a. The pattern in `intro` destructs the existential.

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, ¬Q x) → ∃ x, ¬P x :=
  fun ⟨a, hnQa⟩ => ⟨a, fun hPa => hnQa (h a hPa)⟩
```

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) : (∃ x, ¬Q x) → ∃ x, ¬P x := by
  intro ⟨a, hnQa⟩
  exists a
  intro hPa
  exact hnQa (h a hPa)
```

## A disjunction of universals

Whichever side holds, its instance at each element proves the pointwise disjunction. The term eliminates the disjunction with `.elim`, and the tactic proof with `cases`.

```lean
example (α : Type) (P Q : α → Prop) :
    (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x :=
  fun h a =>
    h.elim (fun hp => Or.inl (hp a))
      (fun hq => Or.inr (hq a))
```

```lean
example (α : Type) (P Q : α → Prop) :
    (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  intro h a
  cases h with
  | inl hp => exact Or.inl (hp a)
  | inr hq => exact Or.inr (hq a)
```

## Intersection preserves inclusion

The inclusion applies to the left part of the membership, and the right part passes through unchanged.

```lean
example (α : Type) (s t u : Set α)
    (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x hx => ⟨h x hx.left, hx.right⟩
```

```lean
example (α : Type) (s t u : Set α)
    (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x hx
  constructor
  · exact h x hx.left
  · exact hx.right
```

## Classical existence

The theorem `not_forall_exists` of the negation laws section produces a witness where ¬P fails, and `Classical.byContradiction` removes the double negation, as in Lecture 1.

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∀ x, ¬P x) : ∃ x, P x :=
  (not_forall_exists α (fun x => ¬P x) h).elim
    fun a hnnPa => ⟨a, Classical.byContradiction hnnPa⟩
```

```lean
example (α : Type) (P : α → Prop)
    (h : ¬∀ x, ¬P x) : ∃ x, P x := by
  obtain ⟨a, hnnPa⟩ := not_forall_exists α (fun x => ¬P x) h
  exact ⟨a, Classical.byContradiction hnnPa⟩
```

# Exercises

Prove each statement in Lean, replacing `sorry` with a proof. Download the exercise file [`Lecture02.lean`](example-code/Lectures/En/Lecture02.lean) and open it in VS Code. The file already contains the definitions of `Set`, membership, inclusion, union, and intersection.

```savedComment
Exercises for Lecture 2: Predicate Logic and Sets.
Replace each `sorry` with a proof. The definitions above
come from the lecture.
```

{exercise "exr-universal-quantifier-distributes-over"}[] The universal quantifier distributes over implication.

```savedLean -keep
theorem exercise1 (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hP : ∀ x, P x) : ∀ x, Q x := by
  sorry
```

{exercise "exr-existential-quantifier-distributes-over"}[] The existential quantifier distributes over disjunction.

```savedLean -keep
theorem exercise2 (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry
```

{exercise "exr-eliminate-existential-hypothesis-then"}[] Eliminate the existential hypothesis, then instantiate the universal one at the witness.

```savedLean -keep
theorem exercise3 (α : Type) (P : α → Prop) (Q : Prop)
    (h : ∃ x, P x → Q) (hP : ∀ x, P x) : Q := by
  sorry
```

{exercise "exr-inclusion-transitive"}[] Inclusion is transitive.

```savedLean -keep
theorem exercise4 (α : Type) (s t u : Set α)
    (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  sorry
```

{exercise "exr-intersection-distributes-over-union"}[] Intersection distributes over union.

```savedLean -keep
theorem exercise5 (α : Type) (s t u : Set α) :
    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  sorry
```

```lean -show
end Lecture2
```
