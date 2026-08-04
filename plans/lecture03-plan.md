# Plan for Lecture 3: Programs and Theorems; Definitions, Computation

Syllabus week 3, "Programas e teoremas; definições, computação | LoVe02" (`ementas/Ementa-VerificacaoFormalSoftware.md`, line 59). Source material is `lean/LoVe/LoVe02_ProgramsAndTheorems_Demo.lean` in `lean-forward/logical_verification_2026`, read in full together with its exercise sheet. The demo corresponds to chapter 2 of the Hitchhiker's Guide 2026 ("Programs and Theorems", §2.1 Type Definitions, §2.2 Function Definitions, §2.3 Theorem Statements, §2.4 Summary, pp. 11–20).

## Confirmed scope of LoVe02

The demo defines, in namespace `LoVe`, the inductive types `MyNat.Nat` (`zero`, `succ`), `AExp` (`num : ℤ → AExp`, `var : String → AExp`, `add`, `sub`, `mul`, `div`), and `MyList.List` (`nil`, `cons`); the functions `fib`, `add`, `mul`, `power`, `powerParam`, `iter`, `powerIter`, `append` (explicit type argument), `appendImplicit`, `appendPretty`, `reverse`, and `eval : (String → ℤ) → AExp → ℤ`; the commands `#check`, `#print`, `#eval`, `#reduce`; and, in namespace `SorryTheorems`, the statements `add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `mul_add`, `reverse_reverse`, all proved by `sorry`, followed by `opaque a b : ℤ` and `axiom a_less_b : a < b`.

The demo's own header states the boundary. It reviews programs and theorem statements "without carrying out any proofs yet". No induction (structural induction is LoVe05, weeks 6–7 of the syllabus; the induction tactic is Guide §3.6–3.7), no `Option`, no binary trees, no structures or type classes (all LoVe05), no tactic proofs. The only proof device this lecture can honestly add is `rfl` on ground equations, which the students already used blindly in Lecture 2 (`⟨3, rfl⟩`); explaining it here as computation is a small, well-motivated extension beyond LoVe02.

## Learning goals

After this lecture the student can

1. define an inductive type by listing its constructors, and read `#check` and `#print` output for types and constructors;
2. define functions by pattern matching and structural recursion, on one or several arguments;
3. use polymorphic definitions with explicit and implicit type arguments, `@`, and the list notation `[]`, `::`, `[a, b, c]`;
4. evaluate terms with `#eval` and `#reduce` and explain the difference;
5. prove concrete evaluation facts with `rfl`, understanding it as definitional computation, which retroactively explains the `rfl` of Lecture 2;
6. state a theorem about a program, distinguish the statement from its proof, use `sorry` as a placeholder, and explain why the general laws (`add_comm`, `reverse_reverse`) must wait for structural induction in weeks 6–7;
7. see the Curry–Howard correspondence promised in Lecture 1 (Howard 1980 margin note, `Lecture01.lean` line 715) concretely, since `def` and `theorem` share one syntax, `fun` builds both programs and proofs of implications, and pattern matching in definitions parallels the `cases` tactic on hypotheses.

Connections back. Lectures 1–2 taught `intro`, `exact`, `apply`, `cases`, `constructor`, `have`, `obtain`, `specialize`, `exists`, pattern `intro`, and proof terms; Lecture 2 introduced type classes informally through the `Membership`/`HasSubset`/`Union`/`Inter` instances for `Set`. Lecture 3 introduces no new proof tactic. Its new commands are all definitional (`inductive`, `def` by equations, `#print`, `#eval`, `#reduce`, `theorem` with `sorry`, `axiom`, `opaque`).

## Section-by-section outline

Follows the Lecture 2 pattern, an opening section without examples plus example-bearing sections, each closing with `## Examples` containing 10 worked examples. Per section: key material, new constructs, and 2–3 concrete example candidates; the remaining examples get drafted in the same style during writing.

**3.1 From Proofs to Programs** (no Examples subsection). Bridge section. A proof is a term whose type is the proposition (Lecture 1); now types classify data and terms are programs. `#check` on `fun n : Nat => n + 1` beside `#check` on a proof term. Announce the LoVe02 contract, definitions and statements now, proofs from Lecture 4 on. Margin citations for the Guide chapter 2 and Howard 1980. Optional figure `fig-aexp-tree` (new SVG, existing `figureAnchor`/`figref` machinery from `Lectures/Meta/Figure.lean`) showing the abstract syntax tree of (x + 3) * y, referenced again in 3.2 and 3.5.

**3.2 Inductive Types.** `MyNat.Nat` with `zero` and `succ` inside `namespace MyNat`, exactly as LoVe does; the namespace is load-bearing in Verso, since a top-level `inductive Nat` would shadow core `Nat` for the rest of the document. An inductive type contains exactly the values built by finitely many constructor applications. `#check`/`#print` on the type and constructors; core `Nat` versus `MyNat.Nat`. Then `AExp` (with `Int` for LoVe's ℤ) and `MyList.List` in `namespace MyList`. New constructs `inductive … where`, `namespace`/`end`, `#print`. Example candidates: (a) build the numeral three as `MyNat.Nat.succ (MyNat.Nat.succ (MyNat.Nat.succ MyNat.Nat.zero))` and `#check` it; (b) a small enumeration type (e.g. `inductive Answer where | yes | no | maybe`) showing constructors with no arguments; (c) build the `AExp` value for (x + 3) * y and connect it to the figure.

**3.3 Functions by Pattern Matching and Recursion.** `add`, `mul`, `power` on core `Nat`, pattern matching on `Nat.zero`/`Nat.succ`, multiple arguments separated by commas; `fib` with the `n + 2` pattern; `powerParam` moving a non-matched argument left of the colon; termination, Lean accepts structurally recursive definitions, which peel off one constructor per call. New construct `def` by equations. Candidates: (a) `add` with the observation that `add` recurses on its second argument; (b) `fib` with `#eval fib 10`; (c) `power` versus `powerParam`.

**3.4 Polymorphism and Implicit Arguments.** `iter` and `powerIter`; `append` with explicit `(α : Type)` and calls `append Nat` / `append _`; `appendImplicit` with `{α : Type}`; `@appendImplicit`; the aliases `[]`, `x :: xs`, `[x₁, …, xₙ]`; `appendPretty`; `reverse`. New constructs `{ }` binders, `@`, `_`, list notation. Candidates: (a) the three call forms of append, explicit, `_`, implicit; (b) `reverse` with an `#eval`; (c) `powerIter` as an instance of the generic `iter`.

**3.5 Evaluation.** `#eval` (compiled evaluation) versus `#reduce` (kernel reduction), demonstrated on `add 2 7` as in the demo; `eval` for `AExp` under an environment `String → Int`; the demo's division-by-zero evaluation, `eval (fun _ => 7) (AExp.div (AExp.var "y") (AExp.num 0))`, with the observation that integer division in Lean is total with x / 0 = 0 (verify the exact output at build time); the exercise sheet's warning that the command `#eval` and our function `eval` are unrelated. Then `rfl`, an equation whose two sides compute to the same value holds by `rfl`, e.g. `example : add 2 7 = 9 := rfl`, which explains Lecture 2's `⟨3, rfl⟩`. Candidates: (a) `#eval`/`#reduce` pair on `add 2 7` with `leanOutput`; (b) evaluation of a nested `AExp` under a concrete environment; (c) a `rfl` proof of a ground evaluation fact.

**3.6 Theorem Statements.** `theorem` is `def` whose result is a proposition; the six `SorryTheorems` statements (`add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `mul_add`, `reverse_reverse`) stated with `sorry`; the `sorry` warning; the contrast, `rfl` proves `add 2 7 = add 7 2` but not `add m n = add n m`, because variables block computation, and the general law needs structural induction (forward pointer to weeks 6–7, LoVe05). Close with `axiom` and `opaque` following the demo (`opaque a b : Int`, `axiom a_less_b : a < b`) and the caution that axioms carry no proof. New constructs `theorem` with `sorry`, `axiom`, `opaque`. Candidates: (a) `add_comm` stated with `sorry` next to its `rfl`-provable ground instance; (b) `reverse_reverse` as a specification of `reverse`; (c) the `opaque`/`axiom` pair.

## Adaptation from LoVe conventions to course conventions

> **Addendum (2026-08-04).** Direction changed after this plan was written: the project is adopting Mathlib (tag `v4.32.0`, matching the Verso toolchain, binary cache via `lake exe cache get`) plus a vendored `LoVelib.lean` (compiles verbatim on our pins) for the LoVe-based lectures, precisely to avoid divergence from the LoVe material. Under that decision, the first bullet below is superseded: Lecture 3 keeps LoVe's ℕ/ℤ/↦ notation and imports the vendored LoVelib instead of translating to core spellings. Lectures 1–2 remain Mathlib-free. Spike evidence on branch `mathlib-spike`.

- ~~Core Lean only. Replace ℕ/ℤ notation with `Nat`/`Int`, `↦` with `=>`, and drop LoVe's `set_option` lines and `import LoVe.LoVelib`.~~ Superseded; see addendum.
- Keep LoVe's declaration names (`add`, `mul`, `power`, `fib`, `append`, `reverse`, `eval`, `AExp`, …). None clashes with a core top-level name or with Lectures 1–2 (`Set` and instances). `MyNat`/`MyList` namespaces prevent shadowing core `Nat`/`List`.
- Wrap all code at 60 columns; the `AExp` and `eval` lines from LoVe already fit.
- Bilingual delivery as before, write `Lectures/En/Lecture03.lean` first, then `Lectures/Pt/Lecture03.lean` with byte-identical code blocks and translated prose; add the slides line and build `lecture-3.en.html`/`.pt.html` slides as for Lectures 1–2.

## Exercises (10, statements only, disjoint from the worked examples)

Definitions needed by the extracted exercise file (`AExp`, `eval`, `append`/`appendPretty`, `reverse`) go in `savedLean` blocks without `-keep`, following the Lecture 2 precedent with `Set`; exercise blocks use ```savedLean -keep``` with `sorry`. This lecture's exercises mix `def … := sorry` and statement-writing, matching the LoVe02 exercise sheet's character.

1. (Warm-up) Define `pred : Nat → Nat` returning the predecessor, with `pred 0 = 0`; check with the `#eval` lines provided. (LoVe Q1.)
2. Define `double : Nat → Nat` by recursion on the argument, without using `*`, and prove `double 5 = 10` by `rfl`.
3. Define `someEnv : String → Int` mapping "x" to 3, "y" to 17, and every other name to 201, by pattern matching on strings; prove two given ground facts about `eval someEnv` by `rfl`, one exercising `AExp.sub` and one `AExp.div` with a zero divisor.
4. Define truncated subtraction `sub : Nat → Nat → Nat` by pattern matching on both arguments, so that `sub 3 5 = 0`.
5. Define `length : List α → Nat` with an implicit type argument, and prove `length [1, 2, 3] = 3` by `rfl`.
6. Define `map : (α → β) → List α → List β`. (LoVe Q3.1.)
7. Define `snoc : List α → α → List α`, which appends one element at the end, then state, with `sorry`, the theorem `reverse_cons` relating `reverse (x :: xs)` to `snoc (reverse xs) x`.
8. Complete the given `simplify : AExp → AExp` with the cases for `sub`, `mul`, and `div` (simplifying e − 0, 1 * e, e * 1, e / 1, and the analogues of the given `add` cases). (LoVe Q2.2.)
9. State, with `sorry`, the correctness of `simplify`, the simplified expression evaluates to the same value as the original under every environment. (LoVe Q2.3; the point is writing the statement.)
10. State, with `sorry` and at full generality in the types, the functorial laws of `map`, identity and composition. (LoVe Q3.2.)

Progression runs from single-type recursive definitions (1–4), through polymorphism (5–7), to the statement-writing skill that is the heart of the lecture (7–10). None repeats a worked example; the lecture's examples use `fib`, `add`, `mul`, `power`, `append`, `reverse`, `eval`, and the `SorryTheorems` statements, while the exercises use `pred`, `double`, `sub`, `length`, `map`, `snoc`, `simplify`, and the map laws.

## New Verso/meta machinery

None required. Existing machinery covers everything: `lean` blocks with `(name := …)` plus `leanOutput` for `#check`/`#eval`/`#reduce`/`#print` output, `savedLean`/`savedLean -keep`/`savedComment` for the exercise file, `figureAnchor`/`figref` for the optional AST figure (one new SVG asset only), margin-note citations. Two items to verify during writing rather than build now. First, that `#print` output renders through `leanOutput` as `#check` does. Second, whether the doc should show a rejected non-structurally-recursive definition; if so, Verso's InlineLean expected-error block support needs checking, and the fallback is prose plus a code listing without elaboration. Also verify that a `sorry`-carrying `theorem` inside a plain `lean` block builds without failing the book (the warning is expected; Lecture 3 is the first to display `sorry` in the prose, not only in extracted exercises).

## Verified references

- J. Blanchette et al., LoVe demo 2, `lean/LoVe/LoVe02_ProgramsAndTheorems_Demo.lean`, and exercise sheet 2, `lean/LoVe/LoVe02_ProgramsAndTheorems_ExerciseSheet.lean`, in [lean-forward/logical_verification_2026](https://github.com/lean-forward/logical_verification_2026). Both read in full.
- A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, 2026 edition, chapter 2, "Programs and Theorems", pp. 11–20 (`hitchhikers_guide_2026_desktop.pdf` in the same repository; table of contents verified).
- W. A. Howard, *The Formulae-as-Types Notion of Construction*, in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980. Already cited in `Lecture01.lean` line 715; reuse the margin note in 3.1.
- *The Lean Language Reference* (already in the syllabus bibliography) for `#eval`/`#reduce` and integer division semantics; verify the specific division claim at build time before citing a chapter.
