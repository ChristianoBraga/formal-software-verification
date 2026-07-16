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

/--
Site theme matching the landing page in `site/index.html`. Palette is
indigo `#1e3a8a` to teal `#0d9488` on slate, with the header carrying the
landing gradient.
-/
def themeCss : String := "
:root {
  --verso-text-color: #0f172a;
  --verso-structure-color: #0f172a;
  --verso-code-color: #0f172a;
  --verso-toc-background-color: #f8fafc;
  --verso-burger-toc-hidden-color: #ffffff;
}
header {
  background: linear-gradient(135deg, #1e3a8a 0%, #0d9488 100%);
  box-shadow: 0 1px 6px rgba(15, 23, 42, 0.35);
}
.header-title h1 { color: #ffffff; }
#logo img { padding: 0.4rem 0 0.4rem 0.6rem; box-sizing: border-box; }
main section a { color: #1e3a8a; }
main section a:hover { color: #0d9488; }
#toc a:hover { color: #0d9488; }
"

def codeHighlightHead : Array Verso.Output.Html :=
  #[{{<style>{{Verso.Output.Html.text false codeHighlightCss}}</style>}},
    {{<style>{{Verso.Output.Html.text false themeCss}}</style>}}]
