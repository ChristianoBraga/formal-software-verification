import VersoManual
import Lectures.Meta.Lean
import Lectures.Papers
import Lectures.Pt.Lecture01

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Verificação Formal de Software" =>

%%%
authors := ["Christiano Braga"]
%%%

Estas são as notas de aula da disciplina *Verificação Formal de Software*, oferecida no Mestrado em Sistemas e Computação do Instituto Militar de Engenharia (IME), Rio de Janeiro.

A disciplina apresenta os fundamentos e a infraestrutura correspondente em Lean necessários para provar propriedades de programas imperativos por meio da lógica de Hoare. O conteúdo cobre lógica clássica de primeira ordem com provas estruturadas, teoria de tipos dependentes, prova interativa com raciocínio regressivo e progressivo, programação funcional e tipos indutivos, indução estrutural, predicados indutivos e indução por regras, programação com efeitos e mônadas, semântica operacional big-step de uma linguagem imperativa, lógica de Hoare e verificação prática com a tática `mvcgen`.

As referências principais são [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) (HTPIwL), [*The Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe) e [*The Lean Language Reference*](https://lean-lang.org/doc/reference/latest/).

{include 0 Lectures.Pt.Lecture01}
