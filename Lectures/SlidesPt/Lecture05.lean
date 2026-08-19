/-
Slides da Aula 5, gerados a partir de fontes verificadas. Cada
seção de nível superior é um slide; o título do documento e os
parágrafos de introdução formam o slide de título. Todo o código
Lean é elaborado no momento da compilação e é idêntico ao código
das notas de aula (`Lectures/Pt/Lecture05.lean`) onde os dois se
sobrepõem.

O deck da Aula 4 fornece `add`, `mul`, `appendPretty`, `reverse`,
`snoc` e os teoremas `Backward`. Os analisadores de termos `fix` e
`assume`, copiados do `LoVelib` da LoVe (que a compilação de
slides não pode importar sem um conflito de nome com `Set`), são
definidos abaixo. Tudo o que é novo é declarado dentro de
`namespace Forward`.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesPt.Lecture04

section StructuredParsers
open Lean Lean.Parser Lean.Parser.Term

@[term_parser] def slideFix :=
  leading_parser withPosition
    ("fix " >> many1 Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

@[term_parser] def slideAssume :=
  leading_parser withPosition
    ("assume " >> Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

macro_rules
| `(fix $x* : $ty; $y)    => `(fun $x* : $ty => $y)
| `(assume $h : $ty; $y)  => `(fun $h : $ty => $y)

end StructuredParsers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Provas Progressivas" =>

Provas estruturadas, provas calculacionais e o princípio PAT

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-5___-Provas-Progressivas/)

Baseado no [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), capítulo 4.

# §5.1 Progressiva e regressiva, mais uma vez

* Uma prova *progressiva* parte das hipóteses e deriva novos fatos até alcançar o objetivo. A sua frase é *"de … temos …"*, o espelho do *"basta provar"* da Aula 4.

::::cols
:::col
{lbl}[Regressiva, a partir do objetivo]

```
para provar c,
  por hbc basta provar b;
para provar b,
  por hab basta provar a;
e ha prova a.
```
:::
:::col
{lbl}[Progressiva, a partir das hipóteses]

```
de ha e hab, temos b;
de b e hbc, temos c.
```
:::
::::

* Uma derivação em dedução natural admite as duas leituras; esta aula escreve a progressiva, como um termo estruturado.

# §5.1 O princípio PAT

* *Proposições como tipos, provas como termos.* Uma proposição é um tipo, e uma prova dela é um termo desse tipo. Uma implicação a → b é o tipo das funções de provas de a em provas de b, então a prova de uma implicação *é* uma função, e ∀ x, P x é um tipo de função dependente.

```lean (name := patCheck)
#check (fun (a : Prop) (h : a) => h)
#check (assume h : True; h)
```

```leanOutput patCheck
fun a h => h : ∀ (a : Prop), a → a
```

```leanOutput patCheck
fun h => h : True → True
```

* `fix` e `assume`, da biblioteca da LoVe, são os analisadores de termos que expandem para `fun`.

# §5.2 Construções estruturadas

* `fix x : α` descarrega um ∀; `assume h : P` descarrega uma →; `have h : P := pf` nomeia um fato progressivo; `show P from pf` reafirma o objetivo.

::::cols
:::col
```lean
namespace Forward

theorem fst_of_two_props :
    ∀ a b : Prop, a → b → a :=
  fix a b : Prop;
  assume ha : a;
  assume hb : b;
  show a from ha

end Forward
```
:::
:::col
{lbl}[O mesmo termo, de três modos]

```lean
namespace Forward

example : ∀ a b : Prop, a → b → a :=
  fix a b : Prop;
  assume ha : a; assume hb : b; ha

example : ∀ a b : Prop, a → b → a :=
  fun a b ha hb => ha

end Forward
```
:::
::::

# §5.2 Estruturada versus tática

* A composição de implicações, progressiva como dois passos `have` e regressiva como o roteiro da Aula 4.

::::cols
:::col
```lean
namespace Forward

theorem prop_comp (a b c : Prop)
    (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a;
  have hb : b := hab ha;
  show c from hbc hb

end Forward
```
:::
:::col
```lean
namespace Forward

example (a b c : Prop)
    (hab : a → b) (hbc : b → c) :
    a → c := by
  intro ha
  apply hbc
  apply hab
  exact ha

end Forward
```
:::
::::

* De ha e hab temos b; de b e hbc temos c.

# §5.3 Progressivo sobre conjunção e disjunção

* Regras de eliminação desmontam uma hipótese; regras de introdução e o construtor anônimo constroem o objetivo.

::::cols
:::col
```lean
namespace Forward

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  assume h : a ∧ b;
  have ha : a := And.left h;
  have hb : b := And.right h;
  show b ∧ a from
    And.intro hb ha

end Forward
```
:::
:::col
```lean
namespace Forward

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  assume h : a ∨ b;
  Or.elim h
    (fun ha => Or.inr ha)
    (fun hb => Or.inl hb)

end Forward
```
:::
::::

# §5.3 Progressivo sobre existencial e bicondicional

* `Exists.intro t pf` fornece uma testemunha; `Exists.elim h f` nomeia uma; `Iff.mp` e `Iff.mpr` aplicam uma equivalência em cada direção.

::::cols
:::col
```lean
namespace Forward

example (P : ℕ → Prop) (h : P 3) :
    ∃ n, P n :=
  Exists.intro 3 h

example (α : Type) (P : α → Prop)
    (Q : Prop) (h : ∃ x, P x)
    (f : ∀ x, P x → Q) : Q :=
  Exists.elim h f

end Forward
```
:::
:::col
```lean
namespace Forward

example (a b : Prop)
    (h : a ↔ b) (ha : a) : b :=
  Iff.mp h ha

example (a b : Prop)
    (h : a ↔ b) (hb : b) : a :=
  Iff.mpr h hb

end Forward
```
:::
::::

# §5.3 Regras do ponto único

* O ápice. Um quantificador cuja variável ligada é presa por uma igualdade colapsa a uma única instância.

::::cols
:::col
```lean
namespace Forward

theorem Forall_one_point (α : Type)
    (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x;
     h t rfl)
    (assume hpt : P t;
     fix x : α;
     assume hxt : x = t;
     hxt ▸ hpt)

end Forward
```
:::
:::col
```lean
namespace Forward

theorem Exists_one_point (α : Type)
    (t : α) (P : α → Prop) :
    (∃ x, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume h : ∃ x, x = t ∧ P x;
     Exists.elim h
       (fun x hx => hx.1 ▸ hx.2))
    (assume hpt : P t;
     Exists.intro t
       (And.intro rfl hpt))

end Forward
```
:::
::::

# §5.4 `calc`

* Uma prova calculacional dispõe uma cadeia de igualdades para o leitor, cada passo justificado por uma reescrita ou por um lema, com `calc` compondo `Eq.trans`.

```lean
namespace Forward

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

end Forward
```

* Cada passo é o tipo de igualdade que `rw` consome, e `ac_rfl` fecha um rearranjo.

# §5.4 `calc` versus `simp` e `Eq.trans`

* Uma identidade, três provas. `calc` documenta a cadeia, `Eq.trans` mostra a transitividade, `ac_rfl` esconde tudo.

::::cols
:::col
```lean
namespace Forward

theorem two_mul_trans (m n : ℕ) :
    2 * m + n = m + n + m := by
  have h1 :
      2 * m + n = (m + m) + n := by
    rw [Nat.two_mul]
  have h2 :
      (m + m) + n = m + n + m := by
    ac_rfl
  exact Eq.trans h1 h2

end Forward
```
:::
:::col
```lean
namespace Forward

theorem two_mul_ac (m n : ℕ) :
    2 * m + n = m + n + m := by
  rw [Nat.two_mul]
  ac_rfl

end Forward
```

* A escolha é sobre o leitor, não sobre o verificador.
:::
::::

# §5.5 Passos progressivos no modo de táticas

* `have h : P := pf` acrescenta um fato provado; `let x := t` acrescenta uma abreviação; `specialize` e `obtain` também são passos progressivos. As provas reais misturam as duas direções.

::::cols
:::col
```lean
namespace Forward

example (P : ℕ → Prop)
    (h : ∀ n, P n) : P 7 := by
  specialize h 7
  exact h

end Forward
```
:::
:::col
```lean
namespace Forward

example (α : Type) (P : α → Prop)
    (Q : Prop) (hex : ∃ x, P x)
    (h : ∀ x, P x → Q) : Q := by
  obtain ⟨a, ha⟩ := hex
  exact h a ha

end Forward
```
:::
::::

# §5.5 Uma prova mista

* Um `have` progressivo dentro de uma prova regressiva, cada direção marcada.

::::cols
:::col
```lean
namespace Forward

theorem prop_comp_tactical
    (a b c : Prop)
    (hab : a → b) (hbc : b → c) :
    a → c := by
  intro ha
  have hb : b := hab ha
  exact hbc hb

end Forward
```
:::
:::col
* `intro ha` e `exact` trabalham de forma regressiva a partir do objetivo.

* `have hb : b := hab ha` trabalha de forma progressiva a partir das hipóteses.

* A prova mista costuma ser a mais curta, tomando cada fato de onde é mais fácil alcançá-lo.
:::
::::

# §5.6 Provas por recursão

* Sob PAT, uma função recursiva que devolve uma prova *é* uma prova por indução, e a chamada recursiva é a hipótese de indução.

```lean
namespace Forward

theorem append_nil {α : Type} :
    ∀ (xs : List α), appendPretty xs [] = xs
  | []      => rfl
  | x :: xs => congrArg (List.cons x) (append_nil xs)

theorem append_assoc {α : Type} :
    ∀ (xs ys zs : List α),
      appendPretty (appendPretty xs ys) zs
        = appendPretty xs (appendPretty ys zs)
  | [],      _, _ => rfl
  | x :: xs, ys, zs =>
      congrArg (List.cons x) (append_assoc xs ys zs)

end Forward
```

# §5.6 Recursão versus `induction`

* A prova recursiva e a tática `induction` são a mesma prova; a chamada recursiva é o `ih` do ramo.

::::cols
:::col
```lean
namespace Forward

theorem reverse_append {α : Type} :
    ∀ (xs ys : List α),
      reverse (appendPretty xs ys)
        = appendPretty (reverse ys)
            (reverse xs)
  | [],      ys => by
      simp [reverse, appendPretty,
            append_nil]
  | x :: xs, ys => by
      simp [reverse, appendPretty,
            reverse_append xs ys,
            append_assoc]

end Forward
```
:::
:::col
```lean
namespace Forward

theorem reverse_append_tac
    {α : Type} (xs ys : List α) :
    reverse (appendPretty xs ys)
      = appendPretty (reverse ys)
          (reverse xs) := by
  induction xs with
  | nil =>
    simp [reverse, appendPretty,
          append_nil]
  | cons x xs' ih =>
    simp [reverse, appendPretty,
          ih, append_assoc]

end Forward
```

* As semanas 6 e 7 dão o método geral.
:::
::::

# §5.7 Exemplo resolvido: `Forall_one_point`

* Uma prova de quantificador natural de forma progressiva e desajeitada de forma regressiva.

```lean
namespace Forward

theorem Forall_one_point_worked (α : Type)
    (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

end Forward
```

* De forma progressiva, instancie h em t e feche t = t por `rfl`. De forma regressiva, fixe x, suponha x = t, e reescreva com `▸`.

# §5.7 Exemplo resolvido: a lei distributiva

* `a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c)`, o primeiro exemplo resolvido da Aula 4, agora como um termo estruturado.

::::cols
:::col
```lean
namespace Forward

theorem and_or_distrib
    (a b c : Prop) :
    a ∧ (b ∨ c) →
      (a ∧ b) ∨ (a ∧ c) :=
  assume habc : a ∧ (b ∨ c);
  have ha : a := And.left habc;
  Or.elim (And.right habc)
    (fun hb =>
      Or.inl (And.intro ha hb))
    (fun hc =>
      Or.inr (And.intro ha hc))

end Forward
```
:::
:::col
* De habc temos a, nomeado ha.

* A sua conjunção direita b ∨ c dá dois casos.

* Em cada caso construímos a disjunção correspondente com o construtor anônimo.

* O roteiro regressivo planejou a partir do objetivo; o termo progressivo constrói a partir das hipóteses.
:::
::::

# Resumo

* Uma prova progressiva se lê *"de … temos …"*, o espelho do *"basta provar"* regressivo.

* Uma prova estruturada é um termo com a forma da sua proposição, com `fix`, `assume`, `have`, `show`.

* Sob PAT uma proposição é um tipo e uma prova é um termo, então `assume` é `fun`.

* O raciocínio progressivo usa os nomes das regras por justaposição e o construtor anônimo.

* `calc` dispõe uma cadeia de igualdades para o leitor; `ac_rfl` e `simp` a escondem.

* As provas reais misturam direções, um `have` progressivo dentro de um `apply` regressivo.

* A recursão estrutural é uma prova por indução, formalizada nas semanas 6 e 7.

Exercícios: veja as [notas de aula](../pt/Aula-5___-Provas-Progressivas/).
