# Plan for Lecture 4: Backward Proofs

Syllabus week 4, "Provas regressivas; táticas básicas | LoVe03" (`ementas/Ementa-VerificacaoFormalSoftware.md`, line 60). Source material is chapter 3 of the *Hitchhiker's Guide to Logical Verification*, 2026 edition, "Backward Proofs", pp. 23–36, read in full from `hh2026.pdf`, together with `lean/LoVe/LoVe03_BackwardProofs_Demo.lean` and `lean/LoVe/LoVe03_BackwardProofs_ExerciseSheet.lean` in `lean-forward/logical_verification_2026`.

## Confirmed scope of LoVe03

Chapter 3 has eight numbered sections plus a summary. Its unnumbered opening defines a tactic as a procedure that operates on the goal, contrasts backward proofs ("to prove c, by b → c it suffices to prove b") with forward proofs ("from a and a → b, we have b"), and shows a natural deduction derivation read bottom to top. §3.1 introduces `by`, the goal `C ⊢ Q`, the local context, and the theorems `fst_of_two_props`, `fst_of_two_props_params`, `prop_comp`. §3.2 documents `intro`, `apply`, `exact`, `assumption`, `rfl`, `ac_rfl`, `sorry`, and the safe/unsafe distinction. §3.3 presents the introduction and elimination rules as ordinary theorems (`And.intro`, `And.left`, `And.right`, `Or.inl`, `Or.inr`, `Or.elim`, `Iff.intro`, `Iff.mp`, `Iff.mpr`, `Exists.intro`, `Exists.elim`, `True.intro`, `False.elim`, `Classical.em`, `Classical.byContradiction`), metavariables and unification, the `·` combinator, instantiation by juxtaposition, and a list of strategies for logic puzzles. §3.4 gives `Eq.refl`, `Eq.symm`, `Eq.trans`, `Eq.subst`, and the note that `=` binds more tightly than the connectives. §3.5 gives `rw` (with `←` and `at`) and `simp` (with a theorem list, `simp [*] at *`, `-` to remove, and the `@[simp]` attribute). §3.6 proves `add_zero`, `add_succ`, `add_comm`, `add_assoc`, `mul_add` by induction on ℕ, registers `Std.Associative` and `Std.Commutative` instances for `add`, and lists hints on choosing the induction variable. §3.7 gives the full syntax of `induction`. §3.8 gives `clear` and `rename`. §3.9 lists the newly introduced constructs, namely the attribute `@[simp]`, the proof command `by`, the tactics `ac_rfl`, `apply`, `assumption`, `clear`, `exact`, `induction`, `intro`, `rename`, `rfl`, `rw`, `simp`, `sorry`, and the tactic combinator `·`.

The demo file adds to the chapter the theorems `fst_of_two_props_exact`, `fst_of_two_props_assumption`, the six conversion examples `α_example` through `ι_example` on `def double (n : ℕ) : ℕ := n + n`, `Or_swap`, `modus_ponens`, `Not_Not_intro`, `a_proof_of_negation` (which uses `rw [Not]`), `cong_two_args_1p1` (which uses `simp [hab, hcd]`), `abc_Eq_cba` (which uses `ac_rfl`), `cleanup_example` (which uses `clear` and `rename`), and `opaque f : ℕ → ℕ` for `f5_if`. It works inside `namespace LoVe` and `namespace BackwardProofs`, and it reuses `add` and `mul` from the LoVe02 demo.

What chapter 3 does **not** contain, and what this lecture must therefore not teach: `linarith` (Guide §6.4), `norm_num`, `omega`, `decide`, `repeat`, `first`, `all_goals`, `<;>`, and user-defined tactic combinators (Guide chapter 8, "Metaprogramming"). `rcases` and `obtain` are Mathlib tactics absent from the chapter; Lecture 2 already uses `obtain`, so Lecture 4 neither extends nor explains it. Structural induction over arbitrary inductive types belongs to weeks 6–7 (LoVe05); chapter 3 covers induction on ℕ and mentions `List.cons` in the syntax of `induction`, so list induction is admissible here and the general treatment stays in weeks 6–7.

## What the lecture may assume, and what it must not repeat

Lectures 1 and 2 already use, as tactics, `intro`, `exact`, `apply`, `cases … with`, `constructor`, `show`, `have`, `left`, `right`, `specialize`, `exists`, `obtain`, the `·` bullet, and the anonymous constructor `⟨…, …⟩`. They also use `Classical.em`, `Classical.byContradiction` and `False.elim` as terms. Lecture 3 uses `rfl` and `sorry` as terms, never as tactics. A grep over `Lectures/En/Lecture01–03.lean` confirms that `assumption`, `rfl`, `simp`, `rw`, `ac_rfl`, `induction`, `clear` and `rename` never appear at the start of a tactic line in any of them.

New in Lecture 4, therefore:

| New | Already known |
| --- | --- |
| the backward/forward distinction and the phrase "it suffices to" | `intro`, `exact`, `apply` |
| the goal notation `C ⊢ Q` and the local context | `·` focusing |
| `assumption` | `constructor`, `cases … with`, `have`, `show` |
| safe versus unsafe tactics | `Classical.em`, `Classical.byContradiction` |
| metavariables and unification | `False.elim` |
| `rfl` as a tactic, and the conversions α, β, δ, ζ, η, ι | `rfl` as a term (Lecture 3) |
| `ac_rfl` | `sorry` as a term (Lecture 3) |
| `Eq.refl`, `Eq.symm`, `Eq.trans`, `Eq.subst` | |
| `rw`, with `←` and `at` | |
| `simp`, the simp set, `simp [*] at *`, `@[simp]` | |
| `induction … with` | |
| `clear`, `rename` | |
| `sorry` as a tactic | |
| the intro/elim rules applied by `apply` and instantiated by juxtaposition | |

Lecture 1 taught the intro/elim rules of natural deduction as inference figures and gave their term-level counterparts. Lecture 4 does not re-derive them. It shows that each figure is an ordinary Lean theorem that `apply` consumes backwards, which is the point chapter 3 makes and Lecture 1 did not.

## Learning goals

After this lecture the student can

1. read a proof state as a goal `C ⊢ Q` and explain what a tactic does to it;
2. distinguish a backward proof from a forward one, and verbalise a tactic script as a chain of "it suffices to" steps;
3. prove propositional and quantified statements with `intro`, `apply`, `exact` and `assumption` alone, and say which of the four are safe;
4. name the introduction and elimination rules of ∧, ∨, ↔, ∃, `True`, `False` and `=`, apply them backwards, and instantiate them forwards by juxtaposition;
5. recognise a metavariable in a goal and explain how unification instantiates it;
6. prove equations with `rfl`, name the conversion that each step performs, and use `ac_rfl` where associativity and commutativity suffice;
7. rewrite with `rw`, in the goal and in a hypothesis, in either direction, and simplify with `simp` and its variants, explaining how the two differ;
8. prove a statement about a recursive function on ℕ or on lists by `induction … with`, choose the induction variable, and discharge the `sorry` statements Lecture 3 left open;
9. clean a proof state with `clear` and `rename`.

Place in the course. Lectures 1 and 2 proved logic with tactics without naming the method. Lecture 3 defined programs and stated theorems about them without proving any. Lecture 4 supplies the proof method for those statements and closes the loop, and Lecture 5 (syllabus week 5, LoVe04) turns the same proofs around into forward and structured proofs. The `induction` tactic introduced here is applied to arbitrary inductive types in weeks 6–7.

## Module layout and naming

`Lectures/En/Lecture04.lean` **imports `Lectures.En.Lecture03`**, mirroring LoVe, whose chapter 3 demo imports its chapter 2 demo. This gives `add`, `mul`, `power`, `fib`, `appendPretty`, `reverse`, `snoc`, `AExp`, `eval` and the `SorryTheorems` statements without redefinition, and it lets §4.6 discharge exactly the theorems Lecture 3 left with `sorry`. Verified: a module importing `Lectures.En.Lecture03` sees `add : ℕ → ℕ → ℕ`, `mul`, `@reverse` and `SorryTheorems.add_comm`, and proves `add_zero`, `add_succ`, `add_comm` by induction over them.

All new named declarations go inside `namespace Backward … end Backward`, reopened in each code block as Lecture 3 reopens `MoreTheorems`. This is not cosmetic. `Lectures/En.lean` imports every English lecture into one environment, and Lean rejects the import of a second module that declares a name the first already declares. Verified with two one-line modules:

```
C.lean:1:0: error: import B failed, environment already contains 'addx' from A
```

Root-level `add_zero`, `add_succ`, `add_comm`, `add_assoc`, `mul_add`, `mul_comm`, `mul_assoc`, `double`, `f` would collide with Mathlib (reachable through Lecture 3's `LoVelib` import) or with Lecture 3's own root names. Inside `Backward` they do not. `example` blocks are anonymous and need no namespace, so most of the fifty section examples can stay outside it.

`Lectures/Pt/Lecture04.lean` imports `Lectures.Pt.Lecture03` and uses the same `Backward` namespace; the two language trees are built by separate executables (`lectures-en`, `lectures-pt`), so they never share an environment.

## Section-by-section outline

Six sections, matching Lecture 3's shape: one opening section without examples, then five sections each closing with `## Examples` containing exactly ten examples. The guide's §3.8 (cleanup tactics) folds into §4.2 rather than becoming a seventh section, since `clear` and `rename` support two examples, not ten. The guide's `rfl` and `ac_rfl`, listed under Basic Tactics in §3.2, move to §4.4 with the rest of equality, where the conversions belong.

### 4.1 Backward Proofs | Provas Regressivas (no Examples subsection)

Teaches the vocabulary. A tactic operates on the goal and either closes it or produces subgoals. A goal is a local context of variable declarations `x : σ` and hypotheses `h : P` together with a target, written `C ⊢ Q`. A backward proof starts at the goal and works towards proved theorems, and its telltale phrase is "it suffices to". A forward proof starts at the theorems and works towards the goal, and Lecture 5 develops it. The natural deduction derivation of Lecture 1 reads as a forward proof top to bottom and as a backward proof bottom to top.

Lean code shown. A plain (unelaborated) block with the guide's three-line informal backward proof of `c` from `a`, `a → b`, `b → c`, and its two-line forward counterpart, in the style of the plain block Lecture 3 uses for the step-by-step `eval` unfolding. Then `Backward.fst_of_two_props : ∀ a b : Prop, a → b → a` proved by `intro a b`, `intro ha hb`, `apply ha`, with `trace_state` after each `intro` and matching `leanOutput` blocks. Then `Backward.prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) : a → c` by `intro ha`, `apply hbc`, `apply hab`, `apply ha`, followed by its verbalisation as three "it suffices to" lines.

Margin notes. The Guide, chapter 3. Avigad, de Moura, Kong and Ullrich, *Theorem Proving in Lean 4*, chapter 5, which the guide cites for the tactics.

### 4.2 Basic Tactics | Táticas Básicas (10 examples)

Teaches `intro`, `apply`, `exact`, `assumption`, `sorry` as a tactic, and the cleanup pair `clear` and `rename`. `intro` moves the leading ∀-bound variable or the leading assumption into the local context and takes optional names; given a provable goal it always produces a provable goal, so it is safe. `apply` matches the target with the conclusion of a theorem or hypothesis, up to computation, and adds the assumptions as new goals; it can turn a provable goal into an unprovable one, so it is unsafe. `exact` matches the target exactly and states the intention more clearly than `apply`. `assumption` searches the context. `clear` drops a variable or hypothesis the rest of the proof does not need, and `rename` renames one by its type or proposition.

Lean code shown. `fst_of_two_props_params`, `fst_of_two_props_exact`, `fst_of_two_props_assumption`, the guide's unsafe-`apply` illustration built from `theorem falseImpTrue : False → True`, and `cleanup_example`. Verified: `clear ha hab a`, `apply hbc`, `clear hbc c`, `rename b => h`, `exact h` compiles; the unused-variable linter warns on `ha` and `hab`, so the file needs `set_option linter.unusedVariables false`, as LoVe sets.

The ten examples.

1. `intro` on a ∀-goal, with `trace_state` before and after.
2. One `intro` with three names against three separate `intro`s, same theorem, two scripts.
3. Parameters written to the left of the colon arrive in the context already, so no `intro` is needed.
4. `exact h` and `apply h` close the same goal; `exact` says more.
5. `assumption` closes the goal without naming the hypothesis.
6. Two `apply`s in sequence walk backwards through two implications.
7. `apply falseImpTrue` turns the provable `⊢ True` into the unprovable `⊢ False`, shown by `trace_state` and closed by `sorry`.
8. `sorry` closes any goal, and `#print axioms` reports `sorryAx`, as in Lecture 3.
9. `clear` removes a hypothesis and a variable the proof does not use.
10. `rename` renames a hypothesis by its proposition.

### 4.3 Reasoning about Connectives and Quantifiers | Raciocínio sobre Conectivos e Quantificadores (10 examples)

Teaches that each rule of Lecture 1 is a Lean theorem. An introduction rule has the connective as the outermost symbol of its conclusion and tells us how to prove; an elimination rule has it in an assumption and tells us how such a proof must have been built. `apply` consumes a rule backwards; juxtaposition instantiates it forwards, which is a forward step inside a backward proof and which avoids the metavariables that `apply` leaves behind. A metavariable `?a` stands for a term still to be determined, unification determines it, and the extra goals metavariables raise usually disappear on their own. Negation abbreviates `a → False`, so `intro` works on a negated goal. `True.intro` is the only rule for truth and `False.elim` the only one for falsehood. Lean's logic is classical through `Classical.em` and `Classical.byContradiction`, both already used in Lectures 1 and 2 and now applicable backwards. The section closes with the guide's seven strategies for logic puzzles, rendered as a Verso bulleted list.

Lean code shown. `And_swap` by `intro hab`, `apply And.intro`, `apply And.right`, `exact hab`, `apply And.left`, `exact hab`; `And_swap_braces` with `intro a b hab`, `apply And.intro`, and two `·` bullets using juxtaposition; `Or_swap` with `apply Or.elim hab`; `modus_ponens`; `Not_Not_intro`; `opaque f : ℕ → ℕ` with `f5_if (h : ∀ n : ℕ, f n = n) : f 5 = 5 := by exact h 5`. Two display blocks list the rules with their metavariables, one for ∧, ∨, ↔, one for ∃, `True`, `False`, `Classical`.

The ten examples.

1. `apply And.intro` splits `⊢ b ∧ a` into two goals, shown by `trace_state`.
2. `exact And.right hab` closes one of them by juxtaposition.
3. After `apply And.right` the target contains the metavariable `?left.a`, and `exact hab` instantiates it; `trace_state` shows both states.
4. `apply Or.inl` on `⊢ a ∨ b` leaves `⊢ a`, and choosing the wrong side leaves an unprovable goal.
5. `apply Or.elim hab` produces one subgoal per disjunct, closed by two bullets.
6. `apply Iff.intro` splits an equivalence into two implications.
7. `Iff.mp` and `Iff.mpr` extract the two directions of an equivalence hypothesis by juxtaposition.
8. `apply Exists.intro 0` supplies a witness, and `rfl` closes what remains.
9. `apply Exists.elim hex` consumes an existential hypothesis and names its witness.
10. Three one-line proofs in one block: `intro` on `⊢ ¬ a`, `exact False.intro`-free closure of any goal by `apply False.elim`, and `exact True.intro`.

### 4.4 Reasoning about Equality | Raciocínio sobre Igualdade (10 examples)

Teaches `rfl` as a tactic and the conversions it performs, then equality as a set of rules. `rfl` proves `⊢ l = r` when the two sides become syntactically identical under reduction, and it succeeds where a mathematician says "by definition". The six conversions are α (renaming a bound variable), β (applying an anonymous function), δ (unfolding a definition), ζ (substituting a `let`), η (`fun x => f x` equals `f`), ι (projecting a constructor). `ac_rfl` proves equations up to associativity and commutativity for operators registered as such. `Eq.refl`, `Eq.symm` and `Eq.trans` say that `=` is an equivalence relation, and `Eq.subst` replaces equals for equals in an arbitrary context represented by a metavariable `?P`. A parsing note closes the section: `=` binds more tightly than the connectives, so `a = b ∧ c = d` reads `(a = b) ∧ (c = d)`.

Lean code shown. `def double (n : ℕ) : ℕ := n + n` inside `Backward`, the six conversion theorems `α_example` … `ι_example` (all verified to compile with `by rfl`), the rule display block, and `Eq_trans_symm` by `apply Eq.trans`, `· exact hab`, `· apply Eq.symm`, `exact hcb`.

The ten examples.

1. α-conversion, `(fun x => f x) = (fun y => f y)`.
2. β-conversion, `(fun x => f x) a = f a`.
3. δ-conversion, `double 5 = 5 + 5`.
4. ζ-conversion, `(let n : ℕ := 2; n + n) = 4`.
5. η-conversion, `(fun x => f x) = f`.
6. ι-conversion, `Prod.fst (a, b) = a`.
7. `rfl` proves `add m 0 = m` but not `add 0 m = m`, recalling Lecture 3 and motivating §4.6; the second is closed by `sorry`.
8. `ac_rfl` proves `a + b + c = c + b + a` on ℕ (verified).
9. `ac_rfl` proves the same shape for `*`.
10. `apply Eq.subst hab` replaces `a` by `b` under an arbitrary predicate `P` (verified).

### 4.5 Rewriting Tactics | Táticas de Reescrita (10 examples)

Teaches `rw` and `simp`. Both use equations as left-to-right rewrite rules. `rw` finds the first subterm matching the left-hand side, replaces every occurrence of that subterm, instantiates the variables of the equation as needed, and then tries `rfl`. A leading `←` uses the equation in reverse. `at h₁ … hₙ` rewrites the named hypotheses and `at *` rewrites everything. Giving a constant name instead of a theorem uses the constant's defining equations, which is how `rw [Not]` expands negation and `rw [add]` unfolds our function. `simp` rewrites with the simp set exhaustively; `simp [t₁, …, tₙ]` adds theorems or constants temporarily, `simp [-t]` removes one, `simp [*] at *` uses every hypothesis on every hypothesis and on the target, and `@[simp]` registers a theorem permanently. The section repeats the guide's advice to try tactics and study the emerging subgoals rather than model them exactly, and ends on the guide's DON'T PANIC.

Lean code shown. `Eq_trans_symm_rw` by `rw [hab]`, `rw [hcb]`; `a_proof_of_negation` by `rw [Not]`, `rw [Not]`, `intro ha`, `intro hna`, `apply hna`, `exact ha`; `cong_two_args_1p1` by `simp [hab, hcd]`.

The ten examples.

1. `rw [h]` rewrites the target left to right.
2. `rw [←h]` rewrites it right to left.
3. `rw [h₁, h₂]` applies two equations in turn.
4. `rw [h₂] at h₁` rewrites a hypothesis, then `exact h₁` closes the goal (verified).
5. `rw` closes the goal on its own once the two sides coincide, because it tries `rfl`.
6. `rw [add]` unfolds a defining equation of our `add` (verified).
7. `rw [Not]` expands negation, and the resulting goal accepts `intro`.
8. `simp` alone closes an arithmetic goal from the default simp set.
9. `simp [h]` rewrites every occurrence, where `rw [h]` rewrites only the first matching subterm; the same goal, two scripts, one showing the residual subterm.
10. `simp [*] at *` closes a goal from two chained hypotheses (verified).

### 4.6 Proofs by Mathematical Induction | Provas por Indução Matemática (10 examples)

Teaches `induction`. Structural induction follows the structure of the inductive type, and for ℕ built from `Nat.zero` and `Nat.succ` it is ordinary mathematical induction. The syntax names one branch per constructor, `| zero => …` and `| succ n' ih => …`, and the names after a constructor bind its arguments and the induction hypothesis. The section gives the full syntax of the tactic, then the guide's hints. Induct on the argument the recursion consumes; a difficult base case usually means the wrong variable, or a missing auxiliary theorem.

This section discharges what Lecture 3 deferred. `SorryTheorems.add_comm` and `SorryTheorems.add_assoc` of Lecture 3 become `Backward.add_comm` and `Backward.add_assoc` with real proofs, and the text says so explicitly. The general treatment of structural induction over arbitrary inductive types stays in weeks 6–7, and the text says that too.

Lean code shown (all verified against `Lectures.En.Lecture03`). `add_zero (n : ℕ) : add 0 n = n` by `induction n with | zero => rfl | succ n' ih => simp [add, ih]`; `add_succ`; `add_comm` with `simp [add, add_zero]` and `simp [add, add_succ, ih]`; `add_assoc`; `instance Associative_add : Std.Associative add := { assoc := add_assoc }` and `instance Commutative_add : Std.Commutative add := { comm := add_comm }`, with one sentence saying that chapter 5 explains the mechanism; `mul_add` closing with `simp [add, mul, ih]` then `ac_rfl`.

A footnote at the end of the section records that the guide names `add 0 n = n` as `add_zero` even though `add` recurses on its second argument, and that Lecture 3's worked example called the same statement `zero_add`.

The ten examples.

1. `induction n with` on `add 0 n = n`, with `trace_state` in each branch showing `⊢ add 0 0 = 0` and `n' : ℕ, ih : add 0 n' = n' ⊢ add 0 (n' + 1) = n' + 1`.
2. The base case alone, closed by `rfl`.
3. The step case alone, closed by `simp [add, ih]`.
4. `add_succ` by the same pattern, on a statement with two variables.
5. `add_assoc`, inducting on the last variable.
6. The wrong induction variable stalls: `add_succ` attempted by induction on `m`, both branches left as `sorry`, with `trace_state` showing why (verified to elaborate with two `sorry`s).
7. `ac_rfl` on `add` after the two instances are registered.
8. `mul_zero : mul 0 n = 0` by `induction n with … simp [mul, add, ih]` (verified).
9. Induction on a list, `appendPretty xs [] = xs` by `| nil => rfl | cons x xs' ih => simp [appendPretty, ih]` (verified), with a forward pointer to weeks 6–7.
10. `#print axioms Backward.add_comm` reports `[propext]` and not `sorryAx` (verified output: `'Backward.add_comm' depends on axioms: [propext]`), closing the loop with Lecture 3's Example 3.

## Worked Examples (4)

All four are verified to compile against `Lectures.En.Lecture03`.

### 1. Distributing a conjunction over a disjunction | Distribuir uma conjunção sobre uma disjunção

`a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c)`, proved with `intro`, `apply`, `exact` and bullets only, and narrated line by line as "to prove …, it suffices to prove …". The script applies `Or.elim (And.right habc)`, then in each branch `Or.inl` or `Or.inr`, then `And.intro`, and closes the leaves with `And.left habc` and the branch hypothesis. The prose then writes the same proof as five sentences of pen-and-paper mathematics, matching the guide's habit of verbalising every script.

### 2. A dead end and a backtrack | Um beco sem saída e um retrocesso

`a ∧ b → a ∨ c`. The first attempt applies `Or.inr` and reaches `⊢ c`, which `trace_state` displays and which no hypothesis proves; the block ends in `sorry`. The second attempt applies `Or.inl` and closes with `exact And.left hab`. The lesson is the guide's own: `Or.inl` and `Or.inr` are unsafe, a provable theorem can produce an unprovable subgoal, and the remedy is to remember the choices made and backtrack.

### 3. `rw` against `simp` | `rw` contra `simp`

Given `f : ℕ → ℕ` and `hf : ∀ x, f x = x + 1`, prove `f (f 0) = 2` twice, once by `rw [hf, hf]` and once by `simp [hf]` (both verified). The text explains the difference. `rw [hf]` rewrites the first matching subterm and needs a second invocation, and it then closes the goal because it tries `rfl`; `simp [hf]` rewrites exhaustively and reaches the numeral in one step. A third variant shows `rw [hf]` alone and the residual goal, so the student sees what "first matching subterm" means.

### 4. Discharging `reverse_cons` | Descarregar `reverse_cons`

Lecture 3's final worked example stated `reverse (x :: xs) = snoc (reverse xs) x` and left it with `sorry`. This lecture proves it. The proof needs an auxiliary theorem first, `append_snoc (ys : List α) (x : α) : appendPretty ys [x] = snoc ys x`, by induction on `ys` with `| nil => rfl | cons y ys' ih => simp [appendPretty, snoc, ih]`. The theorem then follows by `simp [reverse, append_snoc]`. Both are verified. The text draws the guide's hint from this: a hard case usually signals a missing auxiliary theorem, and the auxiliary theorem here is the one that relates the two list functions the statement mixes.

## Exercises (10)

Statements and skeletons below, all disjoint from the section examples and the worked examples. Exercises 1–6 follow LoVe exercise sheet 3, question 1; exercises 7–9 follow question 2; exercise 10 follows the optional question 3. The propositional exercises use `intro`, `apply` and `exact` only, as the sheet requires.

The exercise file needs the definitions and the theorems the induction exercises build on. Those go in `savedLean` blocks without `-keep`, following the Lecture 3 precedent, namely `namespace Backward`, `add`, `mul`, `add_zero`, `add_succ`, `add_comm`, `add_assoc`, `mul_add` and the two `Std` instances. The extracted file imports only the notations, which is enough: verified that `add_zero`, `mul_comm` and `mul_zero` are undefined after `import Mathlib.Data.Nat.Notation`, so the student file has no collision with Mathlib.

```savedImport
import Mathlib.Data.Nat.Notation
```

```savedComment
Exercises for Lecture 4: Backward Proofs.
Replace each `sorry` with a proof. Questions 1 to 6 use only
`intro`, `apply`, and `exact`. Questions 7 to 9 use
`induction`, `simp`, and `rw`. Question 10 is optional.
```

Exercise 1. The identity and the constant combinators.

```savedLean -keep
theorem I (a : Prop) :
    a → a :=
  sorry

theorem K (a b : Prop) :
    a → b → b :=
  sorry
```

Exercise 2. Permutation of the two arguments of an implication.

```savedLean -keep
theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  sorry
```

Exercise 3. Two proofs of the same statement, differing in which hypothesis they use.

```savedLean -keep
theorem proj_fst (a : Prop) :
    a → a → a :=
  sorry

-- Give a different answer than for `proj_fst`:
theorem proj_snd (a : Prop) :
    a → a → a :=
  sorry
```

Exercise 4. A longer chain of implications.

```savedLean -keep
theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  sorry
```

Exercise 5. Contraposition. Recall that `¬ a` abbreviates `a → False`.

```savedLean -keep
theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  sorry
```

Exercise 6. Distributivity of ∀ over ∧. The right-to-left direction needs a forward step by juxtaposition, as `And_swap_braces` does in the notes.

```savedLean -keep
theorem forall_and {α : Type} (p q : α → Prop) :
    (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  sorry
```

Exercise 7. Recursive equations for `mul` on its first argument.

```savedLean -keep
theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  sorry

theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  sorry
```

Exercise 8. Commutativity and associativity of `mul`, by induction. Choose the induction variable carefully.

```savedLean -keep
theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  sorry
```

Exercise 9. The symmetric variant of `mul_add`, using `rw`. To rewrite at one position only, instantiate the rule, as in `mul_comm _ l`.

```savedLean -keep
theorem add_mul (l m n : ℕ) :
    add (mul n l) (mul n m) = mul (add l m) n :=
  sorry
```

Exercise 10 (optional). Three classical axioms and their relations. Avoid the theorems of the `Classical` namespace; `rw [ExcludedMiddle]` unfolds a definition, and `Or.elim` and `False.elim` do the rest.

```savedLean -keep
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
```

Progression runs from single-tactic propositional proofs (1–4), through negation and quantifiers (5–6), to induction on ℕ and rewriting (7–9), ending with the optional metatheoretic question (10). None repeats an example. The notes' examples use `And`, `Or`, `Iff`, `Exists`, `Eq`, `add`, `appendPretty` and `reverse`; the exercises use the combinators, `contrapositive`, `forall_and`, `mul`, and the three classical axioms.

## Slide deck outline

`Lectures/SlidesEn/Lecture04.lean` and `Lectures/SlidesPt/Lecture04.lean`, in the style of `SlidesEn/Lecture03.lean`, with `::::cols` / `:::col` two-column layouts, `{lbl}[…]` column labels, and `lean` plus `leanOutput` blocks. Register the deck in `SlidesEnMain.lean` and `SlidesPtMain.lean` with `fileName := "lecture-4.en.html"`, `prevLink` to lecture 3, and update lecture 3's `nextLink`.

Title slide. "Backward Proofs" / "Provas Regressivas", subtitle "Tactic mode, basic tactics, rewriting, and induction in Lean", the author line, the link back to the notes, and the LoVe chapter 3 attribution.

1. §4.1 Backward and forward. The two informal proofs side by side in `cols`, and the natural deduction derivation of Lecture 1 read in both directions.
2. §4.1 Tactic mode. `by`, the goal `C ⊢ Q`, `fst_of_two_props` with `trace_state` output.
3. §4.2 The four staples. `intro`, `apply`, `exact`, `assumption`, as four proofs of the same theorem in two columns.
4. §4.2 Safe and unsafe. `intro` always keeps a provable goal; `apply falseImpTrue` on `⊢ True` produces `⊢ False`. `sorry`, `clear` and `rename` in the second column.
5. §4.3 Rules as theorems. The ∧, ∨, ↔ rules in one column, `And_swap` in the other.
6. §4.3 Metavariables and bullets. `And_swap_braces`, the `?left.a` metavariable, `·`, and instantiation by juxtaposition with `f5_if`.
7. §4.3 Quantifiers, truth, falsehood, negation. `Exists.intro`, `Exists.elim`, `True.intro`, `False.elim`, `¬ a` as `a → False`, `Classical.em`.
8. §4.3 Strategies. The guide's list of strategies for logic puzzles, as bullets, one slide of prose with no code.
9. §4.4 `rfl` and the conversions. The six conversions in a table on the left, three of the `_example` theorems on the right, `ac_rfl` at the bottom.
10. §4.4 Equality as rules. `Eq.refl`, `Eq.symm`, `Eq.trans`, `Eq.subst`, and `Eq_trans_symm`.
11. §4.5 `rw`. Syntax, `←`, `at`, a constant name instead of a theorem, `Eq_trans_symm_rw` and `a_proof_of_negation`.
12. §4.5 `simp`. The simp set, `simp [t]`, `simp [*] at *`, `@[simp]`, `cong_two_args_1p1`, and DON'T PANIC.
13. §4.6 Induction. Syntax on the left, `add_zero` and `add_succ` on the right, with the two subgoals shown.
14. §4.6 Commutativity and `ac_rfl`. `add_comm`, `add_assoc`, the two `Std` instances, `mul_add` finishing with `ac_rfl`, and the note that these discharge Lecture 3's `sorry` statements.
15. Worked example. `reverse_cons` through the auxiliary theorem `append_snoc`, in two columns.

Summary slide. Seven bullets. A tactic transforms the goal, and a backward proof reads as a chain of "it suffices to". `intro`, `apply`, `exact` and `assumption` prove any propositional puzzle, and only `intro` is safe. Every rule of Lecture 1 is a theorem that `apply` consumes backwards and juxtaposition instantiates forwards. `rfl` decides equality up to computation and names its conversions; `ac_rfl` adds associativity and commutativity. `rw` rewrites once at the first match, `simp` rewrites exhaustively with the simp set. `induction … with` proves the general laws that computation cannot reach, and it discharges Lecture 3's statements. Lecture 5 turns the same proofs into forward and structured proofs. Closing line with the link to the exercises in the notes.

## Risks and gotchas

**Duplicate root names across modules.** Verified error text: `import B failed, environment already contains 'addx' from A`. `Lectures/En.lean` imports every English lecture, and `SlidesEnMain.lean` imports every English deck, so a root name declared in Lecture 4 must not appear in Lectures 1–3, in the reachable part of Mathlib, or in LoVelib. `namespace Backward` around every named declaration removes the risk. Check the deck separately from the notes, since they are different environments with different names in them.

**Mathlib imports for the notes.** `Lectures/En/Lecture04.lean` imports `Lectures.En.Lecture03`, which imports `Lectures.LoVe.LoVelib`, which imports Aesop, several Mathlib algebra and data modules, `Mathlib.Tactic.Linarith` and `Mathlib.Tactic.Ring`. Nothing further is needed. The lecture uses no Mathlib tactic beyond `simp`, `rw`, `rfl` and `ac_rfl`, all of which are core Lean.

**Mathlib imports for the deck.** The Lecture 3 deck imports only `Mathlib.Data.Nat.Notation` and `Mathlib.Data.Int.Notation`, because full Mathlib brings a `Set` that collides with the `Set` defined in the Lecture 2 deck. The Lecture 4 deck must keep the same discipline, and it can. Verified: `induction … with`, `simp [add, ih]`, `ac_rfl`, the `Std.Associative` and `Std.Commutative` instances for a user-defined `add`, `rw [Not]`, `clear`, `rename` and all six conversion examples compile under those two imports alone. The deck should also `import Lectures.SlidesEn.Lecture03` to reuse that deck's `add`, `mul` and `reverse` rather than redeclaring them, which would collide.

**Linter warnings.** `cleanup_example` triggers `linter.unusedVariables` on `ha` and `hab`. Set `set_option linter.unusedVariables false` in the lecture and deck preambles, as LoVe does, or the warnings appear in the rendered output. LoVe also sets `linter.unnecessarySeqFocus` and `linter.tacticAnalysis.introMerge`; add them if the corresponding warnings appear during the build.

**`trace_state` and `leanOutput`.** `trace_state` prints the goal in exactly the guide's format, verified output for one goal being the four lines `a b : Prop`, `ha : a`, `hb : b`, `⊢ a`. This device carries much of the lecture, since a backward-proof lecture that never shows a proof state teaches little. Verify at the start of writing that Verso's `leanOutput` captures the info message a `trace_state` inside a `lean` block produces, exactly as it captures `#check` output. If it does not, fall back to plain unelaborated blocks holding the state, at the cost of losing the guarantee that the displayed state is the real one.

**`leanOutput` matches byte for byte.** Every expected output must be copied from the build, not typed from memory. Two outputs already collected: `'Backward.add_comm' depends on axioms: [propext]` and `'Backward.add_zero' depends on axioms: [propext]`. The `propext` comes from `simp`, so `#print axioms` on these theorems does not report "does not depend on any axioms", unlike Lecture 3's `rfl` proofs. Example 10 of §4.6 must say `propext` and not claim the proof is axiom-free.

**Verso parsing traps.** A bare `*` in prose or in a heading breaks the parse; write it inside backticks, as in `` `simp [*] at *` ``. This lecture mentions `simp [*] at *`, `at *` and `@[simp]` repeatedly, so the risk is higher here than in Lectures 1–3. In prose, `*…*` renders bold and `_…_` italic. Bulleted lists use `*` at the start of a line, which is list syntax and safe; the guide's seven strategies and the induction hints render as such lists.

**`sorry` in displayed proofs.** Four blocks display `sorry` deliberately (the unsafe `apply`, the wrong induction variable, the dead end of worked example 2, and the `rfl` that fails in §4.4). Each produces a `declaration uses 'sorry'` warning. Lecture 3 already displays `sorry` in `lean` blocks and builds, so this is expected rather than a risk, but the count is higher here.

**Naming mismatch with the guide.** The guide's `add_zero` states `add 0 n = n`, which the usual convention would call `zero_add`, and Lecture 3's worked example did call it `zero_add`. Keep the guide's names for fidelity and record the mismatch in a footnote at the end of §4.6, not in a margin note; margin notes carry bibliographic references only.

**Instances before chapter 5.** `instance Associative_add : Std.Associative add` appears in §3.6 of the guide, ahead of its explanation in chapter 5. Introduce it in one sentence as the registration that lets `ac_rfl` know about `add`, and point forward to weeks 6–7. Lecture 2 already showed `instance` declarations for `Membership`, `HasSubset`, `Union` and `Inter`, so the syntax is not new.

**Section count and example count.** Five example-bearing sections at ten examples each gives fifty examples, matching Lecture 3. Sections 4.4 and 4.5 are the ones most likely to run thin; the conversion examples fill 4.4 and the `rw`/`simp` contrasts fill 4.5, and both lists above are complete rather than indicative.

**Bilingual delivery.** Write `Lectures/En/Lecture04.lean` first, then `Lectures/Pt/Lecture04.lean` with byte-identical code blocks and translated prose, then the two decks. Portuguese uses "verificar" and not "checar", "objetivo" and not "meta" for the goal, "tática" for tactic, "regressiva" and "progressiva" for backward and forward, "reescrita" for rewriting, "espaço de nomes" for namespace, and "casamento de padrões" for pattern matching, all following Lecture 3. Avoid the demonstrative "tal" and avoid cacófatos. Translate the guide's "it suffices to" as "basta provar".

## Verified references

- A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 3, "Backward Proofs", pp. 23–36. Read in full from `hh2026.pdf`, sections 3.1 through 3.9 and the unnumbered opening.
- J. Blanchette et al., LoVe demo 3, `lean/LoVe/LoVe03_BackwardProofs_Demo.lean`, and exercise sheet 3, `lean/LoVe/LoVe03_BackwardProofs_ExerciseSheet.lean`, in [lean-forward/logical_verification_2026](https://github.com/lean-forward/logical_verification_2026). The exercise sheet was read in full; the demo was enumerated declaration by declaration.
- J. Avigad, L. de Moura, S. Kong, S. Ullrich, *Theorem Proving in Lean 4*. The guide cites its chapter 5 for the tactics of this chapter; verify the chapter number in the current edition before printing it in a margin note.
- G. Gentzen, *Untersuchungen über das logische Schließen. I*, Mathematische Zeitschrift 39, 1935, pp. 176–210. Already cited in `Lecture01.lean` line 536; reuse it in §4.1 for the derivation read in both directions.
