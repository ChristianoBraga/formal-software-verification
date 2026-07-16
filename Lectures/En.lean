import VersoManual
import Lectures.Meta.Lean
import Lectures.Papers
import Lectures.En.Lecture01

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Formal Software Verification" =>

%%%
authors := ["Christiano Braga"]
%%%

These are the lecture notes for the course *Formal Software Verification*, offered in the Master's program in Systems and Computing at the Military Institute of Engineering (IME), Rio de Janeiro.

The course presents the foundations and the corresponding infrastructure in Lean needed to prove properties of imperative programs by means of Hoare logic. It covers classical first-order logic with structured proofs, dependent type theory, interactive proving with forward and backward reasoning, functional programming and inductive types, structural induction, inductive predicates and rule induction, programming with effects and monads, big-step operational semantics of an imperative language, Hoare logic, and practical verification with the `mvcgen` tactic.

The main references are [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL), [*The Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), and [*The Lean Language Reference*](https://lean-lang.org/doc/reference/latest/).

{include 0 Lectures.En.Lecture01}
