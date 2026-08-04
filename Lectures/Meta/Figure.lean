/-
Figure anchors and cross-references. Usage:

  {figureAnchor "fig-key"}[![alt text](image.svg)]  -- marks the figure
  {figref "fig-key"}[Figura 1.1]                    -- links to it

The anchor registers the figure in a document domain at traversal time, so a
`figref` resolves to a working link from any page of the book.
-/

import VersoManual

open Lean Elab
open Verso Doc Elab Html
open Verso.Output Html
open Verso.Genre Manual
open Verso.ArgParse

namespace Lectures

def figureDomain : Name := `Lectures.figure

def figureCss : String := r#"
.figure-anchor:target {
  background-color: var(--verso-selected-color);
  outline: auto;
}
"#

inline_extension figureAnchor (key : String) where
  data := .str key
  traverse id data _ := do
    match data with
    | .str key =>
      let path ← (·.path) <$> read
      let _ ← Verso.Genre.Manual.externalTag id path s!"--figure-{key}"
      modify (·.saveDomainObject figureDomain key id)
      pure none
    | _ => pure none
  toTeX := none
  extraCss := [figureCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI id _ content => do
      let some link := (← Verso.Doc.Html.HtmlT.state).externalTags[id]?
        | reportError s!"figureAnchor: no external tag for figure"
          content.mapM goI
      pure {{<span class="figure-anchor" id={{link.htmlId.toString}}>{{← content.mapM goI}}</span>}}

inline_extension figref (key : String) where
  data := .str key
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ data content => do
      match data with
      | .str key =>
        let st ← Verso.Doc.Html.HtmlT.state
        if let some obj := st.getDomainObject? figureDomain key then
          let ids := obj.ids.toArray
          if h : ids.size = 1 then
            if let some link := st.resolveId ids[0] then
              return {{<a class="figure-ref" href={{link.relativeLink}}>{{← content.mapM goI}}</a>}}
          reportError s!"figref: ambiguous or unresolved figure '{key}'"
          content.mapM goI
        else
          reportError s!"figref: no figure with key '{key}'"
          content.mapM goI
      | _ =>
        reportError s!"figref: failed to deserialize key: {data}"
        content.mapM goI

section
variable {m} [Monad m] [MonadError m]

structure FigureConfig where
  key : String

instance : FromArgs FigureConfig m where
  fromArgs := FigureConfig.mk <$> .positional `key (ValDesc.string.as "figure key (string literal)")
end

@[role figureAnchor]
def figureAnchorExpander : RoleExpanderOf FigureConfig
  | {key}, content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (figureAnchor $(quote key)) #[$content,*])

@[role figref]
def figrefExpander : RoleExpanderOf FigureConfig
  | {key}, content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (figref $(quote key)) #[$content,*])
