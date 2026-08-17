# Plan for Lecture 5: Forward Proofs

Syllabus week 5, "Provas progressivas; provas estruturadas | LoVe04" (`ementas/Ementa-VerificacaoFormalSoftware.md`, line 61). Source material is chapter 4 of the *Hitchhiker's Guide to Logical Verification*, 2026 edition, "Forward Proofs", together with `lean/LoVe/LoVe04_ForwardProofs_Demo.lean` and `lean/LoVe/LoVe04_ForwardProofs_ExerciseSheet.lean` in [lean-forward/logical_verification_2026](https://github.com/lean-forward/logical_verification_2026). The demo and exercise sheet were read from the public repository; the PDF was not on disk at planning time, so every Lean snippet below must be compiled during writing before its `leanOutput` is trusted.

Lecture 4 (LoVe03) proved logic backwards with tactics. Lecture 5 turns the same statements around: it proves them forwards, in term mode, as *structured proofs*, and it introduces the Curry–Howard reading that makes a proof a term and a proposition a type. Lecture 6 (week 6, LoVe05) then leaves logic for functional programming and inductive types.

## Confirmed scope of LoVe04

The demo file imports `LoVe.LoVe02_ProgramsAndTheorems_Demo`, opens `namespace LoVe` and `namespace LoVe.ForwardProofs`, and is organised in six sections.

- **Structured Constructs.** `add_comm` restated with `sorry`; `add_comm_zero_left` and `add_comm_zero_left_by_exact` (term mode, `by exact`); `fst_of_two_props : ∀ a b : Prop, a → b → a` with `fix`, `assume`, `show`; `fst_of_two_props_show` and `fst_of_two_props_no_show`; `prop_comp` and `prop_comp_inline` with `assume`, `have`, `show`. Introduces `fix`, `assume`, `show`, `have` as term-level structured constructs.
- **Forward Reasoning about Connectives and Quantifiers.** `And_swap` with `assume`/`have` and `And.left`/`And.right`/`And.intro`; `Or_swap` with `Or.elim`/`Or.inl`/`Or.inr`; `double`; `Nat_exists_double_iden` and its `no_show` variant with `Exists.intro` and `by rfl`; `modus_ponens`; `not_not_intro`; `Forall.one_point (t : α) (P : α → Prop) : (∀ x, x = t → P x) ↔ P t`; `beast_666` applying it; `Exists.one_point (t : α) (P : α → Prop) : (∃ x, x = t ∧ P x) ↔ P t`.
- **Calculational Proofs.** `two_mul_example (m n : ℕ) : 2 * m + n = m + n + m` by `calc` with `by rw` and `by ac_rfl`; `two_mul_example_have`, the same argument with nested `have` and `Eq.trans`. Introduces `calc`.
- **Forward Reasoning with Tactics.** `prop_comp_tactical` in tactic mode with `intro`, `have`, `let`, `exact`. Introduces `let` in tactic mode and the `have h : P := …` forward step inside a backward proof.
- **Dependent Types.** Prose only. The PAT principle (propositions as types, proofs as terms), dependent function types, and the reading of `→` and `∀` as one dependent arrow.
- **Induction by Pattern Matching and Recursion.** `reverse_append`, `reverse_append_tactical`, `reverse_reverse`, proved by structural recursion on lists and, in the `_tactical` variant, by the `induction` tactic of Lecture 4.

The exercise sheet sets three questions. Q1 asks for **structured** proofs of `I`, `K` (which returns its *second* argument, `a → b → b`), `C`, `proj_fst`, `proj_snd`, `some_nonsense`, `contrapositive`, and `forall_and`, with an optional `forall_exists_of_exists_forall {α} (p : α → α → Prop) : (∃ x, ∀ y, p x y) → (∀ y, ∃ x, p x y)`. Q2 asks for a `calc` proof of `binomial_square (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b`, with an optional structured variant. Q3 (optional) asks the student to derive `False` from a deliberately wrong one-point rule stated as an axiom, once for `∀` and once for `∃`.

**The exercise sheet is used only to understand the chapter's scope, never as a source of exercises.** Q1 of this sheet is in fact identical to Q1 of the LoVe03 sheet, which Lecture 4 (before its rework) had copied. Lecture 5's exercises are wholly original, listed in the Exercises section below, and drawn neither from this sheet nor from HTPIwL nor from Lean's documentation. Canonical facts are used freely; copied problems are not.

What chapter 4 does **not** contain, and what this lecture must therefore not teach: `linarith`, `omega`, `decide`, `norm_num`, tactic combinators beyond `·` (Guide chapter 8), monads (LoVe07), and the general theory of structural induction over arbitrary inductive types (weeks 6–7, LoVe05). Pattern-matching recursion appears in the demo's last section on lists, so it is admissible here as a *forward* proof device, but the systematic treatment stays in weeks 6–7, and the text must say so.

## What the lecture may assume, and what it must not repeat

Lectures 1–4 use, as tactics, `intro`, `apply`, `exact`, `assumption`, `cases … with`, `constructor`, `show`, `have`, `left`, `right`, `specialize`, `exists`, `obtain`, `rfl`, `rw`, `simp`, `ac_rfl`, `induction … with`, `clear`, `rename`, the `·` bullet, and `sorry`. They use `fun`, the anonymous constructor `⟨…, …⟩`, and juxtaposition in term mode, and the rule names `And.intro`, `And.left`, `And.right`, `Or.inl`, `Or.inr`, `Or.elim`, `Iff.intro`, `Iff.mp`, `Iff.mpr`, `Exists.intro`, `Exists.elim`, `True.intro`, `False.elim`, `Eq.refl`, `Eq.symm`, `Eq.trans`, `Eq.subst`, `Classical.em`, `Classical.byContradiction`. Lecture 4 introduced the goal notation `C ⊢ Q`, metavariables and unification, and the six conversions α, β, δ, ζ, η, ι.

New in Lecture 5:

| New | Already known |
| --- | --- |
| the forward direction as the primary mode, "from … we have …" | the backward direction and "it suffices to" (Lecture 4) |
| structured term-mode proofs as the default shape | `have` and `show` as *tactics* (Lectures 1–2, 4) |
| `fix x : α` for ∀-introduction in term mode | `intro` for ∀ and → in tactic mode |
| `assume h : P` for →-introduction in term mode | `fun` and juxtaposition in term mode |
| `have h : P := …` and `show P from …` at term level | the rule names, used backwards by `apply` in Lecture 4 |
| `calc` and the calculational layout | `rw`, `ac_rfl`, `Eq.trans` (Lecture 4) |
| `let` inside tactic mode; the forward `have` step inside a backward proof | `intro`, `exact` (Lecture 4) |
| the PAT principle and dependent function types | `∀` and `→` as separate readings (Lectures 1–2) |
| structural recursion on lists as a proof, contrasted with `induction` | `induction … with` on ℕ and lists (Lecture 4) |
| the one-point rules for `∀` and `∃` | `Iff.intro`, `Exists.intro`, `Exists.elim` (Lectures 2, 4) |

`fix` and `assume` are not Lean core. They are defined in `Lectures/LoVe/LoVelib.lean`, lines 42–52, as term parsers that expand `fix x* : ty; y` to `fun x* : ty ↦ y` and `assume h : ty; y` to `fun h : ty ↦ y`. Lecture 5 reaches them through the import chain and must not redefine them.

Lecture 4 proved `fst_of_two_props`, `prop_comp`, `And_swap`, `Or_swap`, `modus_ponens`, `Not_Not_intro` backwards. Lecture 5 reproves the same statements forwards, side by side with a reminder of the tactic script, and this contrast is the pedagogical spine of §5.2 and §5.3. It does not re-teach what the rules mean; Lecture 1 gave the natural deduction rules and Lecture 4 showed they are theorems.

## Learning goals

After this lecture the student can

1. explain the PAT principle: a proposition is a type, a proof is a term of that type, and `→` and `∀` are the same dependent function arrow;
2. read and write a structured term proof with `fix`, `assume`, `have`, and `show`, and relate each construct to the natural deduction rule it realises;
3. take a tactic proof from Lecture 4 and rewrite it as a forward structured proof, and say when each style is clearer;
4. reason forwards about `∧`, `∨`, `↔`, `∃` with the rule names, building a proof term by `have` steps and the anonymous constructor;
5. write a calculational proof with `calc`, justify each step by a rewrite or a lemma, and close arithmetic steps with `ac_rfl`;
6. combine directions, inserting a forward `have` or `let` step into a backward tactic proof;
7. state and prove the one-point rules for `∀` and `∃`, and explain why the naïve variant is inconsistent;
8. read a proof by structural recursion on a list as a forward proof, and point to weeks 6–7 for the general method.

Place in the course. Lectures 1 and 2 proved logic without naming the method; Lecture 4 named it and did it backwards; Lecture 5 does it forwards and in structured term form, closing the logic block. The PAT principle introduced here is the bridge to weeks 6–7, where types carry data as well as propositions, and to the dependent-type machinery of the later Hoare-logic weeks.

## Module layout and naming

`Lectures/En/Lecture05.lean` **imports `Lectures.En.Lecture04`**. This gives `add`, `mul`, `reverse`, `snoc`, `appendPretty`, `double` and the `Backward` theorems without redefinition, and it lets §5.2 and §5.3 place a forward proof next to the backward proof of the same statement. The demo imports LoVe02, but our lecture chain is linear and importing Lecture04 keeps the contrast material in scope.

All new named declarations go inside `namespace Forward … end Forward`, reopened per code block, exactly as Lecture 4 used `namespace Backward`. `Forward.And_swap`, `Forward.prop_comp` and the rest then coexist with the `Backward` versions in the one environment that `Lectures/En.lean` builds, and with Mathlib's root names reached through `LoVelib`. Verify before writing that `Lectures/En.lean` and `SlidesEnMain.lean` still elaborate once Lecture 5 is added, since both import every lecture into a single environment and a duplicate root name fails the import (the error text, from the Lecture 4 work, is `import B failed, environment already contains 'x' from A`).

`Lectures/Pt/Lecture05.lean` imports `Lectures.Pt.Lecture04` and uses the same `Forward` namespace; the two language trees are separate executables and never share an environment.

## Section-by-section outline

Six sections, matching the shape of Lectures 3 and 4: one opening section without examples, then five sections each closing with `## Examples` containing exactly ten examples, for fifty examples in total.

### 5.1 Forward Proofs and the PAT Principle | Provas Progressivas e o Princípio PAT (no Examples subsection)

Teaches the vocabulary and the Curry–Howard reading. A *forward* proof starts at the hypotheses and derives new facts until it reaches the goal; its characteristic phrase is "from … we have …", the mirror of Lecture 4's "it suffices to prove". A *structured* proof is a term whose shape mirrors the proposition: `fix` for a `∀`, `assume` for a `→`, the anonymous constructor for a `∧` or a `∃`, and `have`/`show` to name intermediate facts and to state the goal. The PAT principle says a proposition is a type and a proof is a term of that type, so `a → b` is at once an implication and a function type, and `∀ x, P x` is a dependent function type. `fix`/`assume` are literally `fun`, which is why a proof of an implication *is* a function, as Lecture 1 already hinted.

Lean code shown. A plain block giving the informal three-line forward proof of `c` from `ha`, `hab`, `hbc` (the mirror of Lecture 4's opening), then `Forward.fst_of_two_props` in three styles: full structured with `fix a b; assume ha hb; show a from ha`, the `no_show` variant, and the bare `fun`, each elaborating to the same term (show this with `#print` or by stating that they are definitionally equal). Then `Forall.one_point` deferred to §5.3, mentioned here only as a slogan. A `#check (fun (h : a) => h : a → a)` to make the "proof is a function" point concrete.

Margin notes. The Guide, chapter 4. W. A. Howard, "The formulae-as-types notion of construction", 1980. Avigad, de Moura, Kong, Ullrich, *Theorem Proving in Lean 4*, chapter 3 (the propositions-as-types chapter; verify the number in the current edition).

### 5.2 Structured Constructs | Construções Estruturadas (10 examples)

Teaches `fix`, `assume`, `have`, `show`, and term-mode `let`. `fix x : α` discharges a `∀ x : α`; `assume h : P` discharges a `P → …`; `have h : P := pf; rest` names a proof of `P` for use in `rest`, the forward step; `show P from pf` restates the goal as `P` and supplies `pf`, aiding readability and elaboration; `let` abbreviates a term, not a proof. Each construct is the term-mode counterpart of a Lecture 4 tactic, and the section shows the two side by side.

Lean code shown. `Forward.fst_of_two_props`, `Forward.prop_comp` and `prop_comp_inline`, each with the Lecture 4 backward script quoted in a comment or an adjacent block for contrast.

The ten examples.

1. `fix` alone discharges a `∀`, `fun` written the other way; the two terms are equal.
2. `assume` alone discharges a `→`; contrast with `intro` in a quoted tactic block.
3. `fix`/`assume` combined prove `fst_of_two_props` forwards; the Lecture 4 `intro`/`apply` version sits beside it.
4. `have hb : b := hab ha; …` inserts a forward step; the same proof without the `have`, inlined.
5. `show a from ha` versus a bare `ha`; `show` documents the goal.
6. `prop_comp` forwards by two `have` steps, then the inline term.
7. A `let n := 2` abbreviation inside a term proof of a trivial arithmetic fact.
8. A structured proof whose `have` names a lemma applied twice, showing reuse.
9. The same theorem in tactic mode and in structured term mode, the two scripts labelled, so the student sees the correspondence line by line.
10. A `show` that changes the *syntactic* form of the goal to a definitionally equal one (for example `¬ a` shown as `a → False`), which term mode accepts.

### 5.3 Forward Reasoning about Connectives and Quantifiers | Raciocínio Progressivo sobre Conectivos e Quantificadores (10 examples)

Teaches forward use of the rule names. An elimination rule applied by juxtaposition takes apart a hypothesis; an introduction rule with the anonymous constructor or `Or.inl`/`Or.inr` builds the goal. `And.left h`, `And.right h`, `Or.elim h f g`, `Iff.mp`, `Iff.mpr`, `Exists.intro t pf`, `Exists.elim h f` are all forward steps. The section reproves Lecture 4's `And_swap`, `Or_swap`, `modus_ponens`, `Not_Not_intro` forwards, and then proves the two one-point rules, the section's high point.

Lean code shown. `Forward.And_swap` by `assume h; have ha := And.left h; have hb := And.right h; show b ∧ a from And.intro hb ha`; `Forward.Or_swap` by `assume h; Or.elim h (fun ha => Or.inr ha) (fun hb => Or.inl hb)`; `modus_ponens`; `Not_Not_intro`; `Forall.one_point` and `Exists.one_point`, each proved with `Iff.intro` and a `fix`/`assume`/`have` body, using `rw` where the demo uses it.

The ten examples.

1. `And.left h` and `And.right h` extract the two parts forwards.
2. `And.intro ha hb` and `⟨ha, hb⟩` build a conjunction; the two are the same.
3. `And_swap` forwards, beside its Lecture 4 backward script.
4. `Or.inl`/`Or.inr` build a disjunction; choosing the provable side.
5. `Or.elim h f g` consumes a disjunction with two function branches.
6. `Iff.mp` and `Iff.mpr` apply a biconditional in each direction by juxtaposition.
7. `Exists.intro t pf` supplies a witness forwards; `⟨t, pf⟩` as the same term.
8. `Exists.elim h f` names the witness of an existential hypothesis in a function branch.
9. `Forall.one_point` proved forwards, the `→` direction instantiating at `t`, the `←` direction by `fix`/`assume`/`rw`.
10. `Exists.one_point` proved forwards, contrasting the witness supplied on one side with the witness named on the other.

### 5.4 Calculational Proofs | Provas Calculacionais (10 examples)

Teaches `calc`. A calculational proof is a chain `calc a = b := pf₁ _ = c := pf₂ …`, each step justified by a rewrite or a lemma, the whole reading as a single transitive derivation. `calc` composes `Eq.trans` for the student and lays the reasoning out as a mathematician writes it. The section connects `calc` to Lecture 4's `rw` and `ac_rfl`: each step is exactly the kind of equation `rw` consumes, and a step that holds by associativity and commutativity is closed by `ac_rfl`. `calc` also works for `↔` and for any transitive relation, mentioned in one sentence with a forward pointer.

Lean code shown. `Forward.two_mul_example` by `calc`, with `by rw […]` and `by ac_rfl` steps; `two_mul_example_have`, the same by nested `have` and `Eq.trans`, to show what `calc` abbreviates.

The ten examples.

1. A two-step `calc` on ℕ closed by `rfl` steps.
2. The same identity by `Eq.trans`, to expose the abbreviation.
3. A step justified by `rw [add_comm]`.
4. A step justified by a named lemma from Lecture 4 (`Backward.add_assoc`).
5. `two_mul_example` in full, mixing `rw` and `ac_rfl` steps.
6. A `calc` whose last step is `ac_rfl`, the rest `rw`.
7. A `calc` chain of three equalities.
8. A `calc` over `↔` chaining two biconditionals with `Iff.trans`.
9. The same goal proved by `calc` and by a single `simp`, the two scripts labelled, showing when the explicit chain earns its length.
10. A `calc` step that reads right to left, justified by `rw [← …]`.

### 5.5 Forward Reasoning with Tactics | Raciocínio Progressivo com Táticas (10 examples)

Teaches the forward step inside a backward proof. In tactic mode, `have h : P := pf` and `have h : P := by …` add a proved fact to the context, and `let x := t` adds an abbreviation; both work forwards while the surrounding proof works backwards. This is the everyday mixed style, and the section states plainly that real proofs interleave the two directions. `specialize` (Lecture 2) and `apply … at` are named as further forward tactic steps.

Lean code shown. `Forward.prop_comp_tactical` with `intro`, `have`, `let`, `exact`; a proof that derives an intermediate fact by a nested `have … := by …` and then closes with `exact`.

The ten examples.

1. `have hb : b := hab ha` adds a fact, then `exact hbc hb`.
2. The same proof written purely backwards, for contrast.
3. `have … := by …` proves the intermediate fact by its own tactic block.
4. `let x := t` abbreviates a term used twice in the remaining goal.
5. `specialize h a` instantiates a universal hypothesis forwards (recalling Lecture 2).
6. A forward `have` that makes a subsequent `simp` or `rw` possible.
7. `obtain ⟨a, ha⟩ := hex` as a forward elimination step (recalling Lecture 2).
8. Two `have` steps chained, the second using the first.
9. A proof mixing a backward `apply` with a forward `have`, annotated to mark each direction.
10. The same theorem proved backward-only and mixed, the two scripts labelled, so the student sees the mixed one is shorter.

### 5.6 Proofs by Pattern Matching and Recursion | Provas por Casamento de Padrões e Recursão (10 examples)

Teaches structural recursion as a forward proof, lightly, with a firm forward pointer. Under PAT, a recursive function that returns a proof is a proof by induction: the recursive call is the induction hypothesis. The section shows `reverse_append` and `reverse_reverse` proved by recursion on the list, and the `_tactical` variant by the `induction` tactic of Lecture 4, and states that the general theory of structural induction over arbitrary inductive types is the subject of weeks 6–7. This section stays deliberately short on new theory and long on the correspondence with Lecture 4.

Lean code shown. `reverse_append` and `reverse_reverse` by pattern matching on `[]` and `x :: xs`, each with the recursive call named as the induction hypothesis; `reverse_append_tactical` by `induction … with`.

The ten examples.

1. A recursive proof of a list identity, the base case `[]` and the step `x :: xs`.
2. The same by `induction … with`, side by side, to show they are the same proof.
3. The recursive call is the induction hypothesis, made explicit by naming it.
4. `reverse_append` on `[]`, the base case alone.
5. `reverse_append` on `x :: xs`, the step case, using the recursive call.
6. `reverse_reverse` reducing to `reverse_append`, an auxiliary result feeding another.
7. A proof by recursion on ℕ (`Nat.zero`/`Nat.succ`) recast as pattern matching, tying back to Lecture 4's `add_zero`.
8. A pattern match that fails to be structurally recursive and is rejected, with the error shown, motivating the discipline weeks 6–7 formalise.
9. The `induction` tactic and the recursive definition producing definitionally equal terms, checked.
10. A closing example that states the general form of the correspondence and points to weeks 6–7.

## Worked Examples (4)

Each turns a Lecture 4 artefact around into the forward, structured style, so the two lectures read as one argument seen from both ends. All four must be compiled against `Lectures.En.Lecture04` before writing the prose.

### 1. The distributive law, forwards | A lei distributiva, progressivamente

`a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c)`, the statement of Lecture 4's worked example 1, now as a structured term proof with `assume`, `have`, `Or.elim`, `And.left`, and the anonymous constructor, narrated as "from `habc` we have `a` and we have `b ∨ c`; from `b ∨ c` we get two cases; in each we build the disjunct". The prose then sets this beside the Lecture 4 backward script and names the trade-off.

### 2. `Forall.one_point` in full | `Forall.one_point` por extenso

The one-point rule `(∀ x, x = t → P x) ↔ P t`, proved forwards. The `→` direction instantiates the hypothesis at `t` and discharges `t = t` by `rfl`; the `←` direction is `fix x; assume h : x = t; rw [h]; exact hPt`. The example is the section's payoff and shows a quantifier proof that is natural forwards and awkward backwards.

### 3. A calculational proof | Uma prova calculacional

`2 * m + n = m + n + m` by `calc`, then the same by nested `have`/`Eq.trans`, then by a single `ac_rfl`. Three proofs of one equation, the text drawing the moral that `calc` documents a chain that `ac_rfl` hides and `simp` automates, and that the choice is about the reader, not the checker.

### 4. `reverse_reverse` by recursion | `reverse_reverse` por recursão

`reverse (reverse xs) = xs`, proved by structural recursion on `xs`, using an auxiliary `reverse_append`. The proof is set beside Lecture 4's `induction` proof of a list identity, and the text names the recursive call as the induction hypothesis and points to weeks 6–7 for the general method. This closes the loop with Lecture 4's worked example 4, which discharged `reverse_cons`.

## Exercises (10)

Disjoint from the section examples, from the worked examples, from **Lecture 4's** exercises, and from the LoVe04 exercise sheet. The whole set is original. Canonical facts are used freely, but no statement is taken from LoVe, HTPIwL, or Lean's documentation, and none repeats an exercise of Lectures 1 to 4. Every exercise asks for a **structured** proof, and exercises 1 to 6 use `fix`, `assume`, `have`, `show` and the rule names only, no tactics.

The exercise file needs the notations and the arithmetic lemmas the `calc` questions build on. Those go in `savedLean` blocks without `-keep`, as in Lectures 3 and 4, inside `namespace Forward`. Every skeleton below must be wrapped in `namespace Forward … end Forward` in the lecture module, though shown bare here; the `-keep` rollback happens after elaboration, so a bare root name would still collide with Mathlib during elaboration.

```savedImport
import Mathlib.Data.Nat.Notation
```

```savedComment
Exercises for Lecture 5: Forward Proofs.
Give a structured proof of each statement, replacing `sorry`.
Questions 1 to 6 use `fix`, `assume`, `have`, and `show` only.
Questions 7 and 8 use `calc`. Questions 9 and 10 are optional.
```

Exercise 1. The `S` combinator, distributing an argument through two functions.

```savedLean -keep
theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  sorry
```

Exercise 2. Currying and uncurrying, the two directions as one biconditional.

```savedLean -keep
theorem curry_iff (a b c : Prop) :
    (a ∧ b → c) ↔ (a → b → c) :=
  sorry
```

Exercise 3. A biconditional is symmetric, built structurally from its two directions.

```savedLean -keep
theorem iff_symm (a b : Prop) :
    (a ↔ b) → (b ↔ a) :=
  sorry
```

Exercise 4. Non-contradiction, recalling that `¬ a` abbreviates `a → False`.

```savedLean -keep
theorem non_contradiction (a : Prop) :
    ¬ (a ∧ ¬ a) :=
  sorry
```

Exercise 5. An implication out of a disjunction splits into two.

```savedLean -keep
theorem or_imp (a b c : Prop) :
    (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  sorry
```

Exercise 6. A concrete one-point rule. Instantiating the guard at the fixed value collapses the quantifier.

```savedLean -keep
theorem forall_eq_three (P : ℕ → Prop) :
    (∀ x, x = 3 → P x) ↔ P 3 :=
  sorry
```

Exercise 7. Doubling a sum, by `calc`. Hint: `Nat.two_mul` opens the double and `ac_rfl` closes the rearrangement.

```savedLean -keep
theorem two_distrib (a b : ℕ) :
    2 * (a + b) = a + a + (b + b) :=
  sorry
```

Exercise 8. Right distributivity of multiplication over a sum, by `calc`.

```savedLean -keep
theorem calc_chain (a b c : ℕ) :
    (a + b) * c = a * c + b * c :=
  sorry
```

Exercise 9 (optional). The concrete one-point rule for `∃`, its mirror on the existential side.

```savedLean -keep
theorem exists_eq_three (P : ℕ → Prop) :
    (∃ x, x = 3 ∧ P x) ↔ P 3 :=
  sorry
```

Exercise 10 (optional). Currying a threefold conjunction, both directions.

```savedLean -keep
theorem curry_three (a b c d : Prop) :
    (a ∧ b ∧ c → d) ↔ (a → b → c → d) :=
  sorry
```

Every statement above must be verified provable during writing, exactly as the Lecture 4 exercise set was verified in a scratch file before shipping the `sorry` skeletons. Progression runs from structured propositional proofs (1 to 5), through a concrete one-point rule (6), to calculational arithmetic (7 and 8), ending with the optional pair (9 and 10). None repeats an exercise of Lectures 1 to 4, and none is taken from the LoVe04 sheet: Lecture 5 uses `S`, `curry_iff`, `iff_symm`, `non_contradiction`, `or_imp`, `forall_eq_three`, `two_distrib`, `calc_chain`, `exists_eq_three`, and `curry_three`.

## Slide deck outline

`Lectures/SlidesEn/Lecture05.lean` and `Lectures/SlidesPt/Lecture05.lean`, in the style of `SlidesEn/Lecture04.lean`, with `::::cols`/`:::col`, `{lbl}[…]`, and `lean`/`leanOutput`. Register the deck in `SlidesEnMain.lean` and `SlidesPtMain.lean` with `fileName := "lecture-5.en.html"`, `prevLink` to lecture 4, and update lecture 4's `nextLink`. Import `Lectures.SlidesEn.Lecture04` to reuse its `add`, `mul`, `reverse` and avoid redeclaration, and keep the deck's Mathlib imports to `Mathlib.Data.Nat.Notation` and `Mathlib.Data.Int.Notation` as Lectures 3 and 4 do.

Title slide. "Forward Proofs" / "Provas Progressivas", subtitle "Structured proofs, calculational proofs, and the PAT principle", the author line, the link back to the notes, and the LoVe chapter 4 attribution.

1. §5.1 Forward and backward, once more. The two informal proofs side by side, the "from … we have …" phrase, the mirror of Lecture 4's slide 1.
2. §5.1 The PAT principle. Proposition as type, proof as term, `→` and `∀` as one arrow; `fun` is `assume`.
3. §5.2 Structured constructs. `fix`, `assume`, `have`, `show` in one column, `fst_of_two_props` forwards in the other, the tactic version quoted.
4. §5.2 Structured versus tactic. `prop_comp` two ways, the two scripts aligned.
5. §5.3 Forward about ∧ and ∨. `And.left`/`And.right`/`And.intro`, `Or.elim`, `And_swap` and `Or_swap`.
6. §5.3 Forward about ∃ and ↔. `Exists.intro`/`Exists.elim`, `Iff.mp`/`Iff.mpr`, a worked `Exists` proof.
7. §5.3 One-point rules. `Forall.one_point` and `Exists.one_point`, the payoff slide.
8. §5.4 `calc`. The layout, a two-step chain, the `by rw`/`by ac_rfl` steps.
9. §5.4 `calc` versus `simp` and `Eq.trans`. `two_mul_example` three ways.
10. §5.5 Forward steps in tactic mode. `have`, `let`, `specialize`, the mixed style.
11. §5.5 A mixed proof. `prop_comp_tactical`, each direction annotated.
12. §5.6 Proofs by recursion. `reverse_append` by pattern matching, the recursive call as the induction hypothesis.
13. §5.6 Recursion versus `induction`. The `_tactical` variant beside it, the pointer to weeks 6–7.
14. Worked example. `Forall.one_point` in full, two columns.
15. Worked example. The distributive law forwards, beside the Lecture 4 backward script.

Summary slide. Seven bullets. A forward proof reads "from … we have …", the mirror of backward's "it suffices to". A structured proof is a term shaped like its proposition, with `fix`, `assume`, `have`, `show`. Under PAT a proposition is a type and a proof a term, so `assume` is `fun`. Forward reasoning uses the rule names by juxtaposition and the anonymous constructor. `calc` lays a chain of equalities out for the reader; `ac_rfl` and `simp` hide it. Real proofs mix directions, a forward `have` inside a backward `apply`. Structural recursion is a proof by induction, formalised in weeks 6–7. Closing line linking to the exercises in the notes.

## Risks and gotchas

**`fix`/`assume` availability.** Verified: `Lectures/LoVe/LoVelib.lean` lines 42–52 define both as term parsers expanding to `fun`. They are term-mode only. A `fix`/`assume` at the start of a tactic line is a parse error; inside `by` one uses `intro`. The slides and notes must keep them in term position.

**`calc` layout and Verso.** The `calc` block's alignment and the leading `_` on continuation lines must survive Verso's code rendering. Check early that a `calc` inside a `lean` block renders with its steps aligned and the `leanOutput`, if any, intact. If Verso mangles the alignment, fall back to `Eq.trans`/`have` chains for the displayed proofs and mention `calc` in prose.

**Same statements, two namespaces.** `Forward.And_swap` and `Backward.And_swap` must coexist. Keep every named declaration inside `namespace Forward`, and verify `Lectures/En.lean` and `SlidesEnMain.lean` still elaborate with Lecture 5 present, since both build one environment from all lectures.

**Exercise originality and disjointness.** No exercise is taken from the LoVe04 sheet, from HTPIwL, or from Lean's documentation, and none repeats an exercise of Lectures 1 to 4 or a section example. When writing, grep the exercise blocks of Lectures 1 to 4 for each proposed Lecture 5 name and statement to confirm no repeat, and verify each statement is provable in a scratch file before shipping the `sorry` skeleton.

**Concrete one-point exercises.** Exercises 6 and 9 fix the guard at `3`, so the `→` direction instantiates the hypothesis at `3` and closes `3 = 3` by `rfl`, and the `←` direction rewrites with the equality. Verify both are provable before shipping the skeleton, as with the whole set.

**Structural induction scope.** §5.6 shows recursion-as-proof but must not teach the general structural-induction principle, which is weeks 6–7. Keep the section short, frame every recursive proof as a preview, and state the deferral in the text, as the Lecture 4 plan deferred arbitrary-type induction.

**`leanOutput` byte for byte.** Every `#check`, `#print`, and `trace_state` output must be copied from the build. The PAT slides use `#check` on a `fun` term and on `∀`; the definitional-equality claims in §5.2 examples 1 and 9 should be checked with `#print` or an `example … := rfl`-style equality rather than asserted.

**Linter warnings.** `assume h : P` that goes unused, and `fix x` for a variable used only in the type, trigger `linter.unusedVariables`. Set `set_option linter.unusedVariables false` in the preambles as LoVe and Lecture 4 do, and add `linter.unnecessarySeqFocus` and `linter.tacticAnalysis.introMerge` if their warnings appear.

**Verso `*` traps.** A bare `*` in prose or a heading breaks the parse; the PAT and `calc` discussions are prose-heavy but light on `*`, so the risk is lower than in Lecture 4, but the rule stands.

**Bilingual delivery.** Write English first, then Portuguese with byte-identical code and translated prose. Portuguese: "progressiva" and "regressiva" for forward and backward, "prova estruturada", "prova calculacional", "casamento de padrões" for pattern matching, "recursão" for recursion, "termo" for term, "tipo" for type, "princípio PAT" glossed as "proposições como tipos, provas como termos", following Lectures 3 and 4. Translate "from … we have …" as "de … temos …".

## Verified references

- A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 4, "Forward Proofs". Structure and declarations taken from `lean/LoVe/LoVe04_ForwardProofs_Demo.lean` and `lean/LoVe/LoVe04_ForwardProofs_ExerciseSheet.lean` in the public repository; the PDF must be read in full during writing to confirm section prose and the exact one-point axioms.
- J. Blanchette et al., LoVe demo 4 and exercise sheet 4, in [lean-forward/logical_verification_2026](https://github.com/lean-forward/logical_verification_2026), read from the repository at planning time.
- J. Avigad, L. de Moura, S. Kong, S. Ullrich, *Theorem Proving in Lean 4*, the propositions-as-types chapter (verify the chapter number in the current edition before a margin note).
- W. A. Howard, "The formulae-as-types notion of construction", in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980, pp. 479–490. For the PAT principle.
- G. Gentzen, *Untersuchungen über das logische Schließen. I*, Mathematische Zeitschrift 39, 1935, pp. 176–210. Already cited in Lectures 1 and 4; reuse for the forward reading of a derivation.
```
