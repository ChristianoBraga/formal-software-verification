/-
Entry point for the English slide-deck build. Emits every English
deck into one directory.
Run with: lake exe slides-en --output _out/slides-en
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesEn.Lecture01
import Lectures.SlidesEn.Lecture02
import Lectures.SlidesEn.Lecture03
import Lectures.SlidesEn.Lecture04
import Lectures.SlidesEn.Lecture05
import Lectures.SlidesEn.Lecture06

open Verso Doc
open Verso.Genre Manual

open Lectures

def lecture1Deck : SlideDeck where
  fileName := "lecture-1.en.html"
  pageTitle := "Lecture 1: Motivation and Propositional Logic · Slides"
  kicker := "Lecture 1 · Formal Software Verification"
  label := "Lecture 1 · Motivation and Propositional Logic"
  notesLink := some ("../en/Lecture-1___-Motivation-and-Propositional-Logic/", "↩ Notes")
  nextLink := some ("lecture-2.en.html", "Next lecture ›")

def lecture2Deck : SlideDeck where
  fileName := "lecture-2.en.html"
  pageTitle := "Lecture 2: Predicate Logic and Sets · Slides"
  kicker := "Lecture 2 · Formal Software Verification"
  label := "Lecture 2 · Predicate Logic and Sets"
  notesLink := some ("../en/Lecture-2___-Predicate-Logic-and-Sets/", "↩ Notes")
  prevLink := some ("lecture-1.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-3.en.html", "Next lecture ›")

def lecture3Deck : SlideDeck where
  fileName := "lecture-3.en.html"
  pageTitle := "Lecture 3: Programs and Theorems · Slides"
  kicker := "Lecture 3 · Formal Software Verification"
  label := "Lecture 3 · Programs and Theorems"
  notesLink := some ("../en/Lecture-3___-Programs-and-Theorems/", "↩ Notes")
  prevLink := some ("lecture-2.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-4.en.html", "Next lecture ›")

def lecture4Deck : SlideDeck where
  fileName := "lecture-4.en.html"
  pageTitle := "Lecture 4: Backward Proofs · Slides"
  kicker := "Lecture 4 · Formal Software Verification"
  label := "Lecture 4 · Backward Proofs"
  notesLink := some ("../en/Lecture-4___-Backward-Proofs/", "↩ Notes")
  prevLink := some ("lecture-3.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-5.en.html", "Next lecture ›")

def lecture5Deck : SlideDeck where
  fileName := "lecture-5.en.html"
  pageTitle := "Lecture 5: Forward Proofs · Slides"
  kicker := "Lecture 5 · Formal Software Verification"
  label := "Lecture 5 · Forward Proofs"
  notesLink := some ("../en/Lecture-5___-Forward-Proofs/", "↩ Notes")
  prevLink := some ("lecture-4.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-6.en.html", "Next lecture ›")

def lecture6Deck : SlideDeck where
  fileName := "lecture-6.en.html"
  pageTitle := "Lecture 6: Functional Programming · Slides"
  kicker := "Lecture 6 · Formal Software Verification"
  label := "Lecture 6 · Functional Programming"
  notesLink := some ("../en/Lecture-6___-Functional-Programming/", "↩ Notes")
  prevLink := some ("lecture-5.en.html", "‹ Previous lecture")

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesEn.Lecture01), lecture1Deck),
   ((%doc Lectures.SlidesEn.Lecture02), lecture2Deck),
   ((%doc Lectures.SlidesEn.Lecture03), lecture3Deck),
   ((%doc Lectures.SlidesEn.Lecture04), lecture4Deck),
   ((%doc Lectures.SlidesEn.Lecture05), lecture5Deck),
   ((%doc Lectures.SlidesEn.Lecture06), lecture6Deck)])
