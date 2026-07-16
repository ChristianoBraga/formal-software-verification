/-
Bibliography for the Formal Software Verification lecture notes.
References that Verso's citation types can express live here; online books
(HTPIwL, LoVe, the Lean Language Reference) are cited with hyperlinks in
the text.
-/
import VersoManual
open Verso.Genre.Manual

def kahn1987 : InProceedings where
  title := inlines!"Natural Semantics"
  authors := #[inlines!"Gilles Kahn"]
  year := 1987
  booktitle := inlines!"STACS 87"
  series := some <| inlines!"Lecture Notes in Computer Science, vol. 247, pp. 22–39, Springer"
  url := some "https://inria.hal.science/inria-00075953"
