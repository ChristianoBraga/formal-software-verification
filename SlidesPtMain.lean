/-
Entry point for the Portuguese slide-deck build.
Run with: lake exe slides-pt --output _out/slides-pt
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesPt.Lecture01
import Lectures.SlidesPt.Lecture02
import Lectures.SlidesPt.Lecture03

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

def aula2Deck : SlideDeck where
  fileName := "lecture-2.pt.html"
  pageTitle := "Aula 2: Lógica de Predicados e Conjuntos · Slides"
  htmlLang := "pt"
  kicker := "Aula 2 · Verificação Formal de Software"
  label := "Aula 2 · Lógica de Predicados e Conjuntos"
  notesLink := some ("../pt/Aula-2___-L___gica-de-Predicados-e-Conjuntos/", "↩ Notas")
  prevLink := some ("lecture-1.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-3.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula3Deck : SlideDeck where
  fileName := "lecture-3.pt.html"
  pageTitle := "Aula 3: Programas e Teoremas · Slides"
  htmlLang := "pt"
  kicker := "Aula 3 · Verificação Formal de Software"
  label := "Aula 3 · Programas e Teoremas"
  notesLink := some ("../pt/Aula-3___-Programas-e-Teoremas/", "↩ Notas")
  prevLink := some ("lecture-2.pt.html", "‹ Aula anterior")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesPt.Lecture01), aula1Deck),
   ((%doc Lectures.SlidesPt.Lecture02), aula2Deck),
   ((%doc Lectures.SlidesPt.Lecture03), aula3Deck)])
