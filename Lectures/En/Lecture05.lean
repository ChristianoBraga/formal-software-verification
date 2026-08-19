import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers
import Lectures.En.Lecture04

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Lecture 5: Forward Proofs" =>

%%%
tag := "lecture-5"
%%%

Lecture 4 proved the theorems of logic backwards, starting at the goal and reducing it with tactics. This lecture turns the same statements around and proves them forwards, starting at the hypotheses and deriving new facts until it reaches the goal, following chapter 4 of the *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 4.] It writes proofs as *structured terms* whose shape mirrors the proposition, it introduces calculational proofs with `calc`, and it explains the Curry–Howard reading, the principle that a proof is a term and a proposition is a type. These are the two faces of one activity, and by the end the two lectures read as a single argument seen from both ends.

*This lecture is also available as [presentation slides](../slides/lecture-5.en.html).*

# Forward Proofs and the PAT Principle

A *forward* proof starts at the hypotheses and derives new facts until it reaches the goal. Its characteristic phrase is "from … we have …", the mirror of Lecture 4's "it suffices to prove". Given the hypotheses ha : a, hab : a → b, hbc : b → c and the goal c, the forward reading builds b from ha and hab, then c from b and hbc, exactly the direction that a natural deduction derivation admits when read downwards from its assumptions.

A *structured* proof is a term whose shape follows the proposition it proves. A proof of a universally quantified statement fixes an arbitrary variable; a proof of an implication assumes its antecedent; a proof of a conjunction or an existential is built with the anonymous constructor; and intermediate facts are named as the proof proceeds. Lean writes these four shapes as `fix`, `assume`, the anonymous constructor `⟨…, …⟩`, and `have`, with `show` to restate the current goal.

The reading that unifies term mode and tactic mode is the *PAT principle*, propositions as types and proofs as terms.{margin}[W. A. Howard, "The formulae-as-types notion of construction", in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980, pp. 479–490.] A proposition is a type, and a proof of it is a term of that type. Under this reading an implication a → b is at once a logical statement and the type of functions from proofs of a to proofs of b, so a proof of an implication *is* a function, as Lecture 1 already hinted. A universally quantified statement ∀ x, P x is a *dependent* function type, whose result type P x depends on the argument x, and the single arrow of dependent function types accounts for both → and ∀.{margin}[J. Avigad, L. de Moura, S. Kong, S. Ullrich, *Theorem Proving in Lean 4*, the chapter on propositions and proofs.]

The constructs `fix` and `assume` are not part of Lean's core. They come from the LoVe support library, `Lectures/LoVe/LoVelib.lean`, which the import chain of these notes makes available, and they are term parsers that expand `fix x : τ; e` and `assume h : P; e` to the anonymous functions `fun x : τ ↦ e` and `fun h : P ↦ e`. The proof of the three-argument projection below shows the structured shape. It fixes the two propositions, assumes the two hypotheses, and states the goal it returns.

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

Because `fix` and `assume` are literally `fun`, the same theorem written with `fun`, and the variant that drops the final `show`, elaborate to the identical term.

```lean
namespace Forward

theorem fst_of_two_props_no_show :
    ∀ a b : Prop, a → b → a :=
  fix a b : Prop;
  assume ha : a;
  assume hb : b;
  ha

theorem fst_of_two_props_fun :
    ∀ a b : Prop, a → b → a :=
  fun a b ha hb => ha

end Forward
```

That a proof is a function is not a metaphor but the literal state of affairs, and `#check` makes it visible. The identity proof of a → a is the identity function, and `assume` prints back as the `fun` it abbreviates.

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

# Structured Constructs

The four structured constructs are the term-mode counterparts of tactics from Lecture 4. `fix x : α` discharges a universally quantified goal by fixing an arbitrary x, as `intro` does for a ∀ in tactic mode. `assume h : P` discharges an implication by assuming its antecedent, as `intro` does for a →. `have h : P := pf; rest` names a proof pf of P as h for use in rest, the forward step that adds a fact to what is known. `show P from pf` restates the goal as P, definitionally, and supplies pf, which documents the proof and guides elaboration. A term-level `let x := t; rest` abbreviates a term, not a proof.

The composition of two implications, proved backwards in Lecture 4 as three "it suffices to" steps, reads forwards as two `have` steps that build the intermediate fact and then the conclusion.

```lean
namespace Forward

theorem prop_comp (a b c : Prop) (hab : a → b)
    (hbc : b → c) : a → c :=
  assume ha : a;
  have hb : b := hab ha;
  show c from hbc hb

end Forward
```

Read the proof as prose. Assume a. From ha and hab we have b, which we name hb. From hb and hbc we have c, which is the goal. Each `have` is one forward inference, and the proof term records the derivation top to bottom.

## Examples

The examples below use `fix`, `assume`, `have`, `show` and a term-level `let`, and each sits beside the tactic it mirrors.

{ex "ex-structured-fix-discharges-forall"}[] `fix` alone discharges a universally quantified goal, and the `fun` written the other way is the same term.

```lean
namespace Forward

example : ∀ n : ℕ, n = n :=
  fix n : ℕ; rfl

example : ∀ n : ℕ, n = n :=
  fun n => rfl

end Forward
```

{ex "ex-structured-assume-discharges-implication"}[] `assume` alone discharges an implication. The tactic proof uses `intro` for the same step.

```lean
namespace Forward

example (a : Prop) : a → a :=
  assume h : a; h

example (a : Prop) : a → a := by
  intro h
  exact h

end Forward
```

{ex "ex-structured-fix-assume-projection"}[] `fix` and `assume` together prove the projection forwards, and the Lecture 4 script with `intro` and `apply` sits beside it.

```lean
namespace Forward

example : ∀ a b : Prop, a → b → a :=
  fix a b : Prop; assume ha : a; assume hb : b; ha

example : ∀ a b : Prop, a → b → a := by
  intro a b ha hb
  apply ha

end Forward
```

{ex "ex-structured-have-forward-step"}[] `have` inserts a forward step, naming the derived fact. The same proof inlines the term instead.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b :=
  have hb : b := hab ha; hb

example (a b : Prop) (hab : a → b) (ha : a) : b :=
  hab ha

end Forward
```

{ex "ex-structured-show-documents-goal"}[] `show P from pf` documents the goal, where a bare term leaves it implicit. The two proofs are the same.

```lean
namespace Forward

example (a : Prop) (ha : a) : a :=
  show a from ha

example (a : Prop) (ha : a) : a :=
  ha

end Forward
```

{ex "ex-structured-prop-comp-two-haves"}[] The composition of implications by two `have` steps, then the same proof inlined into a single application.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a;
  have hb : b := hab ha;
  show c from hbc hb

example (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a; hbc (hab ha)

end Forward
```

{ex "ex-structured-let-abbreviation"}[] A term-level `let` abbreviates a value inside a proof. Here the two sides agree by computation once the `let` is unfolded.

```lean
namespace Forward

example : (2 : ℕ) + 2 = 4 :=
  let n : ℕ := 2;
  (rfl : n + n = 4)

end Forward
```

{ex "ex-structured-have-reuses-lemma"}[] A `have` names a fact that the rest of the proof uses more than once. Here the named implication is applied to two different hypotheses.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha ha' : a) :
    b ∧ b :=
  have f : a → b := hab;
  And.intro (f ha) (f ha')

end Forward
```

{ex "ex-structured-tactic-versus-term"}[] The same theorem in tactic mode and in structured term mode, so the correspondence is visible line by line.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  exact hab ha

example (a b : Prop) (hab : a → b) (ha : a) : b :=
  show b from hab ha

end Forward
```

{ex "ex-structured-show-changes-form"}[] `show` may restate the goal in a definitionally equal but syntactically different form, since ¬ a unfolds to a → False, and term mode accepts the change.

```lean
namespace Forward

example (a : Prop) (h : a → False) : ¬ a :=
  show a → False from h

end Forward
```

# Forward Reasoning about Connectives and Quantifiers

Lecture 4 applied the rules of the connectives backwards with `apply`. Forwards, the same rules are used by *juxtaposition*, supplying the hypothesis directly. An elimination rule takes a hypothesis apart, and an introduction rule builds the goal. Thus `And.left h` and `And.right h` extract the two conjuncts, `And.intro ha hb` and the anonymous constructor `⟨ha, hb⟩` build a conjunction, `Or.inl` and `Or.inr` build a disjunction, `Or.elim h f g` consumes one with two function branches, `Iff.mp` and `Iff.mpr` apply an equivalence in each direction, `Exists.intro t pf` supplies a witness, and `Exists.elim h f` names the witness of an existential hypothesis. Each is a forward step, and a structured proof strings them together with `have`.

The commutativity of conjunction, proved backwards in Lecture 4, reads forwards as three `have` steps.

```lean
namespace Forward

theorem And_swap (a b : Prop) : a ∧ b → b ∧ a :=
  assume h : a ∧ b;
  have ha : a := And.left h;
  have hb : b := And.right h;
  show b ∧ a from And.intro hb ha

end Forward
```

The commutativity of disjunction consumes the hypothesis with `Or.elim` and rebuilds it on the other side. `modus_ponens` and `Not_Not_intro` combine the steps seen so far, recalling that ¬ a is a → False.

```lean
namespace Forward

theorem Or_swap (a b : Prop) : a ∨ b → b ∨ a :=
  assume h : a ∨ b;
  Or.elim h
    (fun ha => Or.inr ha)
    (fun hb => Or.inl hb)

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  assume hab : a → b;
  assume ha : a;
  show b from hab ha

theorem Not_Not_intro (a : Prop) : a → ¬¬ a :=
  assume ha : a;
  assume hna : ¬ a;
  show False from hna ha

end Forward
```

The high point of the section is the pair of *one-point rules*, which collapse a quantifier whose bound variable is pinned to a fixed value by an equation. The rule for ∀ says that a universally quantified implication guarded by x = t is equivalent to its instance at t; the rule for ∃ is its existential mirror. Each proof is structured, and each is more natural forwards than backwards.

```lean
namespace Forward

theorem Forall_one_point (α : Type) (t : α)
    (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

theorem Exists_one_point (α : Type) (t : α)
    (P : α → Prop) :
    (∃ x, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume h : ∃ x, x = t ∧ P x;
     Exists.elim h (fun x hx => hx.1 ▸ hx.2))
    (assume hpt : P t;
     Exists.intro t (And.intro rfl hpt))

end Forward
```

In the forward direction of the ∀ rule, the hypothesis is instantiated at t and the guard t = t is discharged by `rfl`. In the backward direction, an arbitrary x is fixed, the guard x = t is assumed, and the equation rewrites P t into P x through the substitution operator `▸`. The ∃ rule supplies the witness t on one side and names the witness on the other.

## Examples

The examples below apply each rule forwards by juxtaposition, then prove the two one-point rules.

{ex "ex-forward-and-left-right"}[] `And.left` and `And.right` extract the two conjuncts forwards.

```lean
namespace Forward

example (a b : Prop) (h : a ∧ b) : a :=
  And.left h

example (a b : Prop) (h : a ∧ b) : b :=
  And.right h

end Forward
```

{ex "ex-forward-and-intro-anonymous"}[] `And.intro` and the anonymous constructor build a conjunction, and the two terms are the same.

```lean
namespace Forward

example (a b : Prop) (ha : a) (hb : b) : a ∧ b :=
  And.intro ha hb

example (a b : Prop) (ha : a) (hb : b) : a ∧ b :=
  ⟨ha, hb⟩

end Forward
```

{ex "ex-forward-and-swap-beside-backward"}[] The commutativity of conjunction forwards, beside its Lecture 4 backward script.

```lean
namespace Forward

example (a b : Prop) : a ∧ b → b ∧ a :=
  assume h : a ∧ b;
  And.intro (And.right h) (And.left h)

example (a b : Prop) : a ∧ b → b ∧ a := by
  intro h
  apply And.intro
  · exact And.right h
  · exact And.left h

end Forward
```

{ex "ex-forward-or-inl-inr"}[] `Or.inl` and `Or.inr` build a disjunction by choosing a side.

```lean
namespace Forward

example (a b : Prop) (ha : a) : a ∨ b :=
  Or.inl ha

example (a b : Prop) (hb : b) : a ∨ b :=
  Or.inr hb

end Forward
```

{ex "ex-forward-or-elim-two-branches"}[] `Or.elim h f g` consumes a disjunction with two function branches.

```lean
namespace Forward

example (a b c : Prop) (h : a ∨ b) (f : a → c)
    (g : b → c) : c :=
  Or.elim h f g

end Forward
```

{ex "ex-forward-iff-mp-mpr"}[] `Iff.mp` and `Iff.mpr` apply an equivalence in each direction by juxtaposition.

```lean
namespace Forward

example (a b : Prop) (h : a ↔ b) (ha : a) : b :=
  Iff.mp h ha

example (a b : Prop) (h : a ↔ b) (hb : b) : a :=
  Iff.mpr h hb

end Forward
```

{ex "ex-forward-exists-intro-witness"}[] `Exists.intro t pf` supplies a witness forwards, and the anonymous constructor is the same term.

```lean
namespace Forward

example (P : ℕ → Prop) (h : P 3) : ∃ n, P n :=
  Exists.intro 3 h

example (P : ℕ → Prop) (h : P 3) : ∃ n, P n :=
  ⟨3, h⟩

end Forward
```

{ex "ex-forward-exists-elim-names-witness"}[] `Exists.elim h f` names the witness of an existential hypothesis in a function branch.

```lean
namespace Forward

example (α : Type) (P : α → Prop) (Q : Prop)
    (h : ∃ x, P x) (f : ∀ x, P x → Q) : Q :=
  Exists.elim h f

end Forward
```

{ex "ex-forward-forall-one-point"}[] The one-point rule for ∀ forwards, instantiating at t on one side and rewriting with the guard on the other.

```lean
namespace Forward

example (α : Type) (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

end Forward
```

{ex "ex-forward-exists-one-point"}[] The one-point rule for ∃ forwards, contrasting the witness supplied on one side with the witness named on the other.

```lean
namespace Forward

example (α : Type) (t : α) (P : α → Prop) :
    (∃ x, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume h : ∃ x, x = t ∧ P x;
     Exists.elim h (fun x hx => hx.1 ▸ hx.2))
    (assume hpt : P t;
     Exists.intro t (And.intro rfl hpt))

end Forward
```

# Calculational Proofs

A *calculational* proof lays a chain of equalities out for the reader, one step per line, each step justified by a rewrite or a lemma. The keyword `calc` composes the steps into a single transitive derivation, playing the part of `Eq.trans` so the writer does not have to. Each step is exactly the kind of equation that `rw` consumes, and a step that holds only up to associativity and commutativity is closed by the `ac_rfl` of Lecture 4. The layout reads as a mathematician writes it, with the running term on the left and the justification on the right.

```lean
namespace Forward

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

end Forward
```

The same argument written with nested `have` steps and `Eq.trans` shows what `calc` abbreviates. The chain of two equalities becomes two named facts joined by transitivity.

```lean
namespace Forward

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m := by
  have h1 : 2 * m + n = (m + m) + n := by
    rw [Nat.two_mul]
  have h2 : (m + m) + n = m + n + m := by ac_rfl
  exact Eq.trans h1 h2

end Forward
```

`calc` also chains any transitive relation, not equality alone, and the examples include a chain over ↔ closed by `Iff.trans`.

## Examples

The examples below build calculational chains, justify their steps by rewrites and by lemmas, and compare `calc` with the alternatives it abbreviates.

{ex "ex-calc-two-steps-rfl"}[] A two-step chain on ℕ, each step closed by `rfl`.

```lean
namespace Forward

example : (1 : ℕ) + 1 + 1 = 3 := by
  calc (1 : ℕ) + 1 + 1 = 2 + 1 := rfl
    _ = 3 := rfl

end Forward
```

{ex "ex-calc-same-by-eq-trans"}[] The same identity by `Eq.trans`, which exposes what the chain abbreviates.

```lean
namespace Forward

example : (1 : ℕ) + 1 + 1 = 3 :=
  Eq.trans
    (rfl : (1 : ℕ) + 1 + 1 = 2 + 1)
    (rfl : (2 : ℕ) + 1 = 3)

end Forward
```

{ex "ex-calc-step-by-rw"}[] A single step justified by rewriting with commutativity.

```lean
namespace Forward

example (a b : ℕ) : a + b = b + a := by
  calc a + b = b + a := by rw [Nat.add_comm]

end Forward
```

{ex "ex-calc-step-by-lemma"}[] A step justified by a named lemma from Lecture 4, the associativity of our `add`.

```lean
namespace Forward

example (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  calc add (add l m) n
      = add l (add m n) := Backward.add_assoc l m n

end Forward
```

{ex "ex-calc-mixing-rw-and-ac-rfl"}[] A chain that mixes a `rw` step with an `ac_rfl` step, the full doubling identity.

```lean
namespace Forward

example (m n : ℕ) : 2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

end Forward
```

{ex "ex-calc-last-step-ac-rfl"}[] A chain whose last step is `ac_rfl` and whose first is a `rfl`.

```lean
namespace Forward

example (a b c : ℕ) : a + b + c = c + (a + b) := by
  calc a + b + c = (a + b) + c := rfl
    _ = c + (a + b) := by ac_rfl

end Forward
```

{ex "ex-calc-three-equalities"}[] A chain of three equalities built from two hypotheses.

```lean
namespace Forward

example (a b c d : ℕ) (h1 : a = b) (h2 : b = c)
    (h3 : c = d) : a = d := by
  calc a = b := h1
    _ = c := h2
    _ = d := h3

end Forward
```

{ex "ex-calc-over-iff"}[] `calc` chains two biconditionals with `Iff.trans` exactly as it chains equalities.

```lean
namespace Forward

example (a b c : Prop) (h1 : a ↔ b) (h2 : b ↔ c) :
    a ↔ c := by
  calc a ↔ b := h1
    _ ↔ c := h2

end Forward
```

{ex "ex-calc-versus-simp"}[] The same goal by an explicit chain and by a single `simp`, which shows when the chain earns its length.

```lean
namespace Forward

example (a b : ℕ) : (a + b) * 1 = a + b := by
  calc (a + b) * 1 = a + b := by rw [Nat.mul_one]

example (a b : ℕ) : (a + b) * 1 = a + b := by
  simp

end Forward
```

{ex "ex-calc-step-right-to-left"}[] A step that reads right to left, justified by a rewrite with a reversed equation.

```lean
namespace Forward

example (a b : ℕ) (h : a = b) : b = a := by
  calc b = a := by rw [← h]

end Forward
```

# Forward Reasoning with Tactics

Real proofs interleave the two directions. In tactic mode, `have h : P := pf` and `have h : P := by …` add a proved fact to the context, and `let x := t` adds an abbreviation, both working forwards while the surrounding proof works backwards. The `specialize` tactic of Lecture 2 and the elimination `obtain ⟨…⟩ := h` are further forward steps. The composition of implications, proved forwards as a term earlier in this lecture, reads in the mixed style as one forward `have` inside a backward proof.

```lean
namespace Forward

theorem prop_comp_tactical (a b c : Prop)
    (hab : a → b) (hbc : b → c) : a → c := by
  intro ha
  have hb : b := hab ha
  exact hbc hb

end Forward
```

The forward `have` builds b from ha and hab, and the backward `exact` closes the goal with hbc applied to it. The mixed proof is often the shortest, because it takes each fact from wherever it is easiest to reach.

## Examples

The examples below add facts with `have`, abbreviate with `let`, instantiate with `specialize`, eliminate with `obtain`, and mix the two directions.

{ex "ex-tactics-have-then-exact"}[] A forward `have` builds the intermediate fact, and a backward `exact` closes the goal.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  have hb : b := hab ha
  exact hbc hb

end Forward
```

{ex "ex-tactics-purely-backward"}[] The same theorem written purely backwards, for contrast.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  exact hbc (hab ha)

end Forward
```

{ex "ex-tactics-have-by-block"}[] `have … := by …` proves the intermediate fact by its own tactic block.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  have hb : b := by exact hab ha
  exact hb

end Forward
```

{ex "ex-tactics-let-abbreviation"}[] `let x := t` abbreviates a term, and `show` restates the goal in terms of the abbreviation.

```lean
namespace Forward

example (n : ℕ) : n + n = n + n := by
  let m := n + n
  show m = m
  rfl

end Forward
```

{ex "ex-tactics-specialize"}[] `specialize` instantiates a universal hypothesis forwards, recalling Lecture 2.

```lean
namespace Forward

example (P : ℕ → Prop) (h : ∀ n, P n) : P 7 := by
  specialize h 7
  exact h

end Forward
```

{ex "ex-tactics-have-enables-simp"}[] A forward `have` makes a subsequent `simp` succeed.

```lean
namespace Forward

example (f : ℕ → ℕ) (a : ℕ) (h : f a = 0) :
    f a + 1 = 1 := by
  have hf : f a = 0 := h
  simp [hf]

end Forward
```

{ex "ex-tactics-obtain-existential"}[] `obtain ⟨a, ha⟩ := h` eliminates an existential hypothesis forwards, naming its witness.

```lean
namespace Forward

example (α : Type) (P : α → Prop) (Q : Prop)
    (hex : ∃ x, P x) (h : ∀ x, P x → Q) : Q := by
  obtain ⟨a, ha⟩ := hex
  exact h a ha

end Forward
```

{ex "ex-tactics-two-haves-chained"}[] Two `have` steps chained, the second using the first.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  have hb : b := hab ha
  have hc : c := hbc hb
  exact hc

end Forward
```

{ex "ex-tactics-mixed-apply-have"}[] A proof mixing a backward `apply` with a forward `have`.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  apply hbc
  have hb : b := hab ha
  exact hb

end Forward
```

{ex "ex-tactics-mixed-is-shorter"}[] The same theorem backward-only and mixed, so the mixed one shows its economy.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  apply hab
  exact ha

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  exact hab ha

end Forward
```

# Proofs by Pattern Matching and Recursion

Under the PAT principle, a recursive function that returns a proof *is* a proof by induction, and the recursive call is the induction hypothesis. A definition by pattern matching on a list has one equation for the empty list and one for a cons, and the equation for `x :: xs` may call the function on the smaller list `xs`, which is the appeal to the induction hypothesis. The section shows two list identities proved this way and states plainly that the general theory of structural induction over arbitrary inductive types is the subject of weeks 6 and 7. Here recursion appears only as a forward proof device.

Two auxiliary identities come first. Appending the empty list on the right changes nothing, and appending is associative. Each is proved by recursion on the first list, and the recursive call carries the induction hypothesis; `congrArg (List.cons x)` rebuilds the cons around it.

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

Reversal distributes over append, in reversed order. The proof recurses on the first list, using the two auxiliaries and the recursive call, which `simp` consumes as rewrite rules.

```lean
namespace Forward

theorem reverse_append {α : Type} :
    ∀ (xs ys : List α),
      reverse (appendPretty xs ys)
        = appendPretty (reverse ys) (reverse xs)
  | [],      ys => by
      simp [reverse, appendPretty, append_nil]
  | x :: xs, ys => by
      simp [reverse, appendPretty,
            reverse_append xs ys, append_assoc]

end Forward
```

The same statement proved by the `induction` tactic of Lecture 4 is the same proof in a different dress. The base case is the `nil` branch, and the step case is the `cons` branch, whose induction hypothesis `ih` is exactly the recursive call above.

```lean
namespace Forward

theorem reverse_append_tactical {α : Type}
    (xs ys : List α) :
    reverse (appendPretty xs ys)
      = appendPretty (reverse ys) (reverse xs) := by
  induction xs with
  | nil           =>
    simp [reverse, appendPretty, append_nil]
  | cons x xs' ih =>
    simp [reverse, appendPretty, ih, append_assoc]

end Forward
```

## Examples

The examples below prove list and number identities by recursion, set the recursive proof beside the `induction` tactic, name the recursive call as the induction hypothesis, and mark the discipline that weeks 6 and 7 formalise.

{ex "ex-recursion-nat-pattern-match"}[] A proof by recursion on ℕ, its base case `0` and its step case `n + 1`, recasting the induction of Lecture 4 as pattern matching. The identity is `add 0 n = n` for the `add` of Lecture 3.

```lean
namespace Forward

theorem add_zero_rec :
    ∀ (n : ℕ), add 0 n = n
  | 0     => rfl
  | n + 1 => by simp [add, add_zero_rec n]

end Forward
```

{ex "ex-recursion-append-assoc-base"}[] The base case of associativity alone. The empty first list makes both sides reduce to the same term, so `rfl` closes it.

```lean
namespace Forward

example {α : Type} (ys zs : List α) :
    appendPretty (appendPretty [] ys) zs
      = appendPretty [] (appendPretty ys zs) :=
  rfl

end Forward
```

{ex "ex-recursion-call-is-hypothesis"}[] The step case makes the induction hypothesis explicit. The recursive call `ih` proves the associativity of the smaller lists, and `congrArg (List.cons x)` rebuilds the cons around it.

```lean
namespace Forward

example {α : Type} (x : α) (xs ys zs : List α)
    (ih : appendPretty (appendPretty xs ys) zs
            = appendPretty xs (appendPretty ys zs)) :
    appendPretty (appendPretty (x :: xs) ys) zs
      = appendPretty (x :: xs) (appendPretty ys zs) :=
  congrArg (List.cons x) ih

end Forward
```

{ex "ex-recursion-reverse-append-base"}[] The base case of `reverse_append`, where the reversal of the empty list and the right identity of append together close the goal.

```lean
namespace Forward

example {α : Type} (ys : List α) :
    reverse (appendPretty [] ys)
      = appendPretty (reverse ys)
          (reverse ([] : List α)) := by
  simp [reverse, appendPretty, append_nil]

end Forward
```

{ex "ex-recursion-reverse-append-step"}[] The step case of `reverse_append`, using the induction hypothesis `ih` and the associativity of append.

```lean
namespace Forward

example {α : Type} (x : α) (xs ys : List α)
    (ih : reverse (appendPretty xs ys)
            = appendPretty (reverse ys) (reverse xs)) :
    reverse (appendPretty (x :: xs) ys)
      = appendPretty (reverse ys)
          (reverse (x :: xs)) := by
  simp [reverse, appendPretty, ih, append_assoc]

end Forward
```

{ex "ex-recursion-append-nil-two-ways"}[] The right identity of append by the `induction` tactic. It is the same proof as the recursive `append_nil` above, in a different dress.

```lean
namespace Forward

example {α : Type} (xs : List α) :
    appendPretty xs [] = xs := by
  induction xs with
  | nil           => rfl
  | cons x xs' ih => simp [appendPretty, ih]

end Forward
```

{ex "ex-recursion-rests-on-structural"}[] The finished recursive proof rests on `propext`, which `simp` uses, and not on `sorryAx`, so the recursion is genuine.

```lean (name := recAxioms)
namespace Forward

#print axioms reverse_append

end Forward
```

```leanOutput recAxioms
'Forward.reverse_append' depends on axioms: [propext]
```

{ex "ex-recursion-rejected-non-structural"}[] Not every recursive definition is accepted. The definition below calls itself on the *same* list, so no argument grows smaller and the recursion never stops, and Lean rejects it with a termination error. The discipline that weeks 6 and 7 formalise is exactly what rules such definitions out.

```
def loopForever {α : Type} : List α → List α
  | []      => []
  | x :: xs => loopForever (x :: xs)
```

{ex "ex-recursion-same-identity-two-ways"}[] One identity, two proofs. The associativity of append by recursion and by the `induction` tactic prove the same proposition, and both rest only on structural recursion.

```lean
namespace Forward

example {α : Type} (xs ys zs : List α) :
    appendPretty (appendPretty xs ys) zs
      = appendPretty xs (appendPretty ys zs) := by
  induction xs with
  | nil           => rfl
  | cons x xs' ih => simp [appendPretty, ih]

end Forward
```

{ex "ex-recursion-general-form-pointer"}[] The general form. A structural recursion on an inductive type has one branch per constructor, and each recursive call, taken on a smaller value, is the induction hypothesis for that branch. Weeks 6 and 7 make this precise for arbitrary inductive types; the `reverse_reverse` of the worked examples is one more instance.

```lean
namespace Forward

example {α : Type} (xs : List α) :
    reverse (appendPretty xs []) = reverse xs := by
  rw [append_nil]

end Forward
```

# Worked Examples

Each example below turns a Lecture 4 artefact around into the forward, structured style, so the two lectures read as one argument seen from both ends. Lean checks every line when the notes are built.

## The distributive law, forwards

The statement a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) was the first worked example of Lecture 4, proved backwards. Forwards it reads as a structured term. From the hypothesis we have a and we have b ∨ c; from b ∨ c we get two cases; in each we build the matching disjunct with the anonymous constructor.

```lean
namespace Forward

theorem and_or_distrib (a b c : Prop) :
    a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) :=
  assume habc : a ∧ (b ∨ c);
  have ha : a := And.left habc;
  Or.elim (And.right habc)
    (fun hb => Or.inl (And.intro ha hb))
    (fun hc => Or.inr (And.intro ha hc))

end Forward
```

In words. Assume a ∧ (b ∨ c), and name its left conjunct ha. Its right conjunct is a disjunction, so we reason by cases. If b holds, the left disjunct a ∧ b follows from ha and b. If c holds, the right disjunct a ∧ c follows from ha and c. The backward proof of Lecture 4 applied `Or.elim` to split the goal and closed each branch with bullets; the forward proof consumes the same disjunction with `Or.elim` and returns the built disjunct directly. The trade-off is the usual one, the backward script planning from the goal and the forward term building from the hypotheses.

## `Forall_one_point` in full

The one-point rule (∀ x, x = t → P x) ↔ P t is the payoff of the connectives section, and it is a quantifier proof that is natural forwards and awkward backwards.

```lean
namespace Forward

theorem Forall_one_point_worked (α : Type) (t : α)
    (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

end Forward
```

The forward direction instantiates the hypothesis h at the fixed value t and discharges the guard t = t with `rfl`, so h t rfl proves P t. The backward direction fixes an arbitrary x, assumes the guard x = t, and rewrites P t into P x with the substitution `hxt ▸ hpt`, where hxt : x = t carries the equation. Backwards the same proof would leave a metavariable for the witness and an awkward equation to discharge; forwards the witness is simply t.

## A calculational proof

The identity `2 * m + n = m + n + m` has three proofs, and comparing them draws the moral of the calculational style.

```lean
namespace Forward

theorem two_mul_example_calc (m n : ℕ) :
    2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

theorem two_mul_example_trans (m n : ℕ) :
    2 * m + n = m + n + m := by
  have h1 : 2 * m + n = (m + m) + n := by
    rw [Nat.two_mul]
  have h2 : (m + m) + n = m + n + m := by ac_rfl
  exact Eq.trans h1 h2

theorem two_mul_example_ac (m n : ℕ) :
    2 * m + n = m + n + m := by
  rw [Nat.two_mul]
  ac_rfl

end Forward
```

The `calc` proof documents the chain that the reader follows. The `Eq.trans` proof shows the transitivity that `calc` hides. The `ac_rfl` proof hides the chain altogether and lets the checker rearrange the terms. All three are correct and rest on the same facts; the choice is about the reader, not the checker.

## `reverse_reverse` by recursion

Reversing a list twice returns the list, and the proof recurses on the list, using the `reverse_append` proved above as its auxiliary. This closes the loop with the fourth worked example of Lecture 4, which discharged `reverse_cons`.

```lean
namespace Forward

theorem reverse_reverse {α : Type} :
    ∀ (xs : List α), reverse (reverse xs) = xs
  | []      => rfl
  | x :: xs => by
      simp [reverse, reverse_append, appendPretty,
            reverse_reverse xs]

end Forward
```

The base case reverses the empty list twice and closes by `rfl`. In the step case, reversing `x :: xs` gives `appendPretty (reverse xs) [x]`, and reversing that, by `reverse_append`, brings the head back to the front and leaves `reverse (reverse xs)`, which the recursive call, the induction hypothesis, rewrites to xs. The `induction` tactic of Lecture 4 would prove the same statement with `ih` in place of the recursive call; the two are the same proof. Weeks 6 and 7 give the general method for arbitrary inductive types.

# Exercises

Prove each statement in Lean, replacing `sorry`. Download the exercise file [`Lecture05.lean`](example-code/Lectures/En/Lecture05.lean) and open it in VS Code. Every exercise asks for a structured proof. Exercises 1 to 6 use `fix`, `assume`, `have`, `show` and the rule names only, no tactics; exercises 7 and 8 use `calc`; exercises 9 and 10 are optional.

```savedImport
import Lectures.LoVe.LoVelib
```

```savedComment
Exercises for Lecture 5: Forward Proofs.
Give a structured proof of each statement, replacing `sorry`.
The import provides `fix` and `assume` and the arithmetic lemmas.
Exercises 1 to 6 use `fix`, `assume`, `have`, and `show` only.
Exercises 7 and 8 use `calc`. Exercises 9 and 10 are optional.
```

{exercise "exr-s-combinator"}[] The S combinator, distributing an argument through two functions.

```savedLean -keep
namespace Forward

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  sorry

end Forward
```

{exercise "exr-curry-iff"}[] Currying and uncurrying, the two directions as one biconditional.

```savedLean -keep
namespace Forward

theorem curry_iff (a b c : Prop) :
    (a ∧ b → c) ↔ (a → b → c) :=
  sorry

end Forward
```

{exercise "exr-iff-symm"}[] A biconditional is symmetric, built from its two directions.

```savedLean -keep
namespace Forward

theorem iff_symm (a b : Prop) :
    (a ↔ b) → (b ↔ a) :=
  sorry

end Forward
```

{exercise "exr-non-contradiction"}[] Non-contradiction, recalling that ¬ a abbreviates a → False.

```savedLean -keep
namespace Forward

theorem non_contradiction (a : Prop) :
    ¬ (a ∧ ¬ a) :=
  sorry

end Forward
```

{exercise "exr-or-imp"}[] An implication out of a disjunction splits into two.

```savedLean -keep
namespace Forward

theorem or_imp (a b c : Prop) :
    (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  sorry

end Forward
```

{exercise "exr-forall-eq-three"}[] A concrete one-point rule. Instantiating the guard at the fixed value collapses the quantifier.

```savedLean -keep
namespace Forward

theorem forall_eq_three (P : ℕ → Prop) :
    (∀ x, x = 3 → P x) ↔ P 3 :=
  sorry

end Forward
```

{exercise "exr-two-distrib"}[] Doubling a sum, by `calc`. Hint: `Nat.two_mul` opens the double and `ac_rfl` closes the rearrangement.

```savedLean -keep
namespace Forward

theorem two_distrib (a b : ℕ) :
    2 * (a + b) = a + a + (b + b) :=
  sorry

end Forward
```

{exercise "exr-calc-chain"}[] Right distributivity of multiplication over a sum, by `calc`.

```savedLean -keep
namespace Forward

theorem calc_chain (a b c : ℕ) :
    (a + b) * c = a * c + b * c :=
  sorry

end Forward
```

{exercise "exr-exists-eq-three"}[] Optional. The concrete one-point rule for ∃, its mirror on the existential side.

```savedLean -keep
namespace Forward

theorem exists_eq_three (P : ℕ → Prop) :
    (∃ x, x = 3 ∧ P x) ↔ P 3 :=
  sorry

end Forward
```

{exercise "exr-curry-three"}[] Optional. Currying a threefold conjunction, both directions.

```savedLean -keep
namespace Forward

theorem curry_three (a b c d : Prop) :
    (a ∧ b ∧ c → d) ↔ (a → b → c → d) :=
  sorry

end Forward
```
