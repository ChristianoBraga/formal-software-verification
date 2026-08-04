/-
Entry point for the Portuguese slide-deck build.
Run with: lake exe slides-pt --output _out/slides-pt
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesPt.Lecture01

open Verso Doc
open Verso.Genre Manual

open Lectures

def aula1Deck : SlideDeck where
  fileName := "lecture-1.pt.html"
  pageTitle := "Aula 1: Motivação e Lógica Proposicional · Slides"
  htmlLang := "pt"
  kicker := "Aula 1 · Verificação Formal de Software"
  label := "Aula 1 · Motivação e Lógica Proposicional"
  notesLink := some ("../pt/Aula-1___-Motiva______o-e-L___gica-Proposicional/", "↩ Notas")
  nextLink := some ("lecture-2.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesPt.Lecture01), aula1Deck)])
