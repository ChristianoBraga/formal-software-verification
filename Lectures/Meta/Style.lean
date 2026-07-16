/-
Syntax-highlighting colors for Lean code blocks, injected into every page's
`head` via the `extraHead` field of the render configuration. Verso exposes
CSS custom properties for keyword, constant, and variable tokens; the other
token kinds get direct rules with higher specificity than the defaults.
Palette follows the One Light theme.
-/

import VersoManual

open Verso.Output Html

namespace Lectures

def codeHighlightCss : String := "
.hl.lean {
  --verso-code-keyword-color: #a626a4;
  --verso-code-const-color: #4078f2;
}
.hl.lean .sort.token { color: #c18401; }
.hl.lean .literal.token, .hl.lean .number.token { color: #986801; }
.hl.lean .string.token, .hl.lean .char.token { color: #50a14f; }
.hl.lean .comment { color: #a0a1a7; font-style: italic; }
"

def codeHighlightHead : Array Verso.Output.Html :=
  #[{{<style>{{Verso.Output.Html.text false codeHighlightCss}}</style>}}]
