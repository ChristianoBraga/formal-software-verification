import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Papers
import Lectures.Pt.Lecture04

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Aula 5: Provas Progressivas" =>

%%%
tag := "aula-5"
%%%

A Aula 4 provou os teoremas da lógica de forma regressiva, partindo do objetivo e reduzindo-o com táticas. Esta aula inverte os mesmos enunciados e os prova de forma progressiva, partindo das hipóteses e derivando novos fatos até alcançar o objetivo, seguindo o capítulo 4 do *Hitchhiker's Guide to Logical Verification*.{margin}[A. Baanen, A. Bentkamp, J. Blanchette, J. Hölzl, J. Limperg, *The Hitchhiker's Guide to Logical Verification*, edição de 2026, capítulo 4.] Ela escreve provas como *termos estruturados* cuja forma espelha a proposição, introduz provas calculacionais com `calc` e explica a leitura de Curry–Howard, o princípio de que uma prova é um termo e uma proposição é um tipo. São as duas faces de uma mesma atividade, e ao final as duas aulas se leem como um único argumento visto de ambos os extremos.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-5.pt.html).*

# Provas Progressivas e o Princípio PAT

Uma prova *progressiva* parte das hipóteses e deriva novos fatos até alcançar o objetivo. A sua frase característica é "de … temos …", o espelho do "basta provar" da Aula 4. Dadas as hipóteses ha : a, hab : a → b, hbc : b → c e o objetivo c, a leitura progressiva constrói b a partir de ha e hab, depois c a partir de b e hbc, exatamente a direção que uma derivação em dedução natural admite quando lida de cima para baixo, a partir das suas suposições.

Uma prova *estruturada* é um termo cuja forma segue a proposição que ela prova. A prova de um enunciado universalmente quantificado fixa uma variável arbitrária; a prova de uma implicação supõe o seu antecedente; a prova de uma conjunção ou de um existencial se constrói com o construtor anônimo; e os fatos intermediários são nomeados à medida que a prova avança. Lean escreve essas quatro formas como `fix`, `assume`, o construtor anônimo `⟨…, …⟩` e `have`, com `show` para reafirmar o objetivo atual.

A leitura que unifica o modo de termos e o modo de táticas é o *princípio PAT*, proposições como tipos e provas como termos.{margin}[W. A. Howard, "The formulae-as-types notion of construction", in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980, pp. 479–490.] Uma proposição é um tipo, e uma prova dela é um termo desse tipo. Sob essa leitura, uma implicação a → b é ao mesmo tempo um enunciado lógico e o tipo das funções que levam provas de a em provas de b, de modo que a prova de uma implicação *é* uma função, como a Aula 1 já sugeria. Um enunciado universalmente quantificado ∀ x, P x é um tipo de função *dependente*, cujo tipo de resultado P x depende do argumento x, e a única seta dos tipos de função dependente dá conta tanto de → quanto de ∀.{margin}[J. Avigad, L. de Moura, S. Kong, S. Ullrich, *Theorem Proving in Lean 4*, o capítulo sobre proposições e provas.]

Os construtos `fix` e `assume` não fazem parte do núcleo de Lean. Eles vêm da biblioteca de apoio LoVe, `Lectures/LoVe/LoVelib.lean`, que a cadeia de importações destas notas torna disponível, e são analisadores de termos que expandem `fix x : τ; e` e `assume h : P; e` nas funções anônimas `fun x : τ ↦ e` e `fun h : P ↦ e`. A prova da projeção de três argumentos abaixo mostra a forma estruturada. Ela fixa as duas proposições, supõe as duas hipóteses e afirma o objetivo que devolve.

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

Como `fix` e `assume` são literalmente `fun`, o mesmo teorema escrito com `fun`, e a variante que descarta o `show` final, elaboram para o termo idêntico.

```lean
namespace Forward

theorem fst_of_two_props_no_show :
    ∀ a b : Prop, a → b → a :=
  fix a b : Prop;
  assume ha : a;
  assume hb : b;
  ha

theorem fst_of_two_props_fun :
    ∀ a b : Prop, a → b → a :=
  fun a b ha hb => ha

end Forward
```

Que uma prova é uma função não é uma metáfora, e sim o estado de coisas literal, e `#check` o torna visível. A prova identidade de a → a é a função identidade, e `assume` se imprime de volta como o `fun` que abrevia.

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

# Construções Estruturadas

Os quatro construtos estruturados são as contrapartes, no modo de termos, de táticas da Aula 4. `fix x : α` descarrega um objetivo universalmente quantificado fixando um x arbitrário, como `intro` faz para um ∀ no modo de táticas. `assume h : P` descarrega uma implicação supondo o seu antecedente, como `intro` faz para uma →. `have h : P := pf; resto` nomeia como h uma prova pf de P para uso em resto, o passo progressivo que acrescenta um fato ao que já se sabe. `show P from pf` reafirma o objetivo como P, por definição, e fornece pf, o que documenta a prova e guia a elaboração. Um `let x := t; resto` no nível de termos abrevia um termo, não uma prova.

A composição de duas implicações, provada de forma regressiva na Aula 4 como três passos de "basta provar", se lê de forma progressiva como dois passos `have` que constroem o fato intermediário e depois a conclusão.

```lean
namespace Forward

theorem prop_comp (a b c : Prop) (hab : a → b)
    (hbc : b → c) : a → c :=
  assume ha : a;
  have hb : b := hab ha;
  show c from hbc hb

end Forward
```

Leia a prova como texto corrido. Suponha a. De ha e hab temos b, que nomeamos hb. De hb e hbc temos c, que é o objetivo. Cada `have` é uma inferência progressiva, e o termo de prova registra a derivação de cima para baixo.

## Exemplos

Os exemplos abaixo usam `fix`, `assume`, `have`, `show` e um `let` no nível de termos, e cada um fica ao lado da tática que espelha.

{ex "ex-structured-fix-discharges-forall"}[] `fix` sozinho descarrega um objetivo universalmente quantificado, e o `fun` escrito da outra maneira é o mesmo termo.

```lean
namespace Forward

example : ∀ n : ℕ, n = n :=
  fix n : ℕ; rfl

example : ∀ n : ℕ, n = n :=
  fun n => rfl

end Forward
```

{ex "ex-structured-assume-discharges-implication"}[] `assume` sozinho descarrega uma implicação. A prova por táticas usa `intro` para o mesmo passo.

```lean
namespace Forward

example (a : Prop) : a → a :=
  assume h : a; h

example (a : Prop) : a → a := by
  intro h
  exact h

end Forward
```

{ex "ex-structured-fix-assume-projection"}[] `fix` e `assume` juntos provam a projeção de forma progressiva, e o roteiro da Aula 4 com `intro` e `apply` fica ao lado.

```lean
namespace Forward

example : ∀ a b : Prop, a → b → a :=
  fix a b : Prop; assume ha : a; assume hb : b; ha

example : ∀ a b : Prop, a → b → a := by
  intro a b ha hb
  apply ha

end Forward
```

{ex "ex-structured-have-forward-step"}[] `have` insere um passo progressivo, nomeando o fato derivado. A mesma prova insere o termo diretamente.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b :=
  have hb : b := hab ha; hb

example (a b : Prop) (hab : a → b) (ha : a) : b :=
  hab ha

end Forward
```

{ex "ex-structured-show-documents-goal"}[] `show P from pf` documenta o objetivo, onde um termo simples o deixa implícito. As duas provas são a mesma.

```lean
namespace Forward

example (a : Prop) (ha : a) : a :=
  show a from ha

example (a : Prop) (ha : a) : a :=
  ha

end Forward
```

{ex "ex-structured-prop-comp-two-haves"}[] A composição de implicações por dois passos `have`, depois a mesma prova reduzida a uma única aplicação.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a;
  have hb : b := hab ha;
  show c from hbc hb

example (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a; hbc (hab ha)

end Forward
```

{ex "ex-structured-let-abbreviation"}[] Um `let` no nível de termos abrevia um valor dentro de uma prova. Aqui os dois lados coincidem por computação, uma vez desdobrado o `let`.

```lean
namespace Forward

example : (2 : ℕ) + 2 = 4 :=
  let n : ℕ := 2;
  (rfl : n + n = 4)

end Forward
```

{ex "ex-structured-have-reuses-lemma"}[] Um `have` nomeia um fato que o resto da prova usa mais de uma vez. Aqui a implicação nomeada é aplicada a duas hipóteses diferentes.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha ha' : a) :
    b ∧ b :=
  have f : a → b := hab;
  And.intro (f ha) (f ha')

end Forward
```

{ex "ex-structured-tactic-versus-term"}[] O mesmo teorema no modo de táticas e no modo de termos estruturado, para que a correspondência seja visível linha a linha.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  exact hab ha

example (a b : Prop) (hab : a → b) (ha : a) : b :=
  show b from hab ha

end Forward
```

{ex "ex-structured-show-changes-form"}[] `show` pode reafirmar o objetivo em uma forma definicionalmente igual, mas sintaticamente diferente, já que ¬ a se desdobra em a → False, e o modo de termos aceita a mudança.

```lean
namespace Forward

example (a : Prop) (h : a → False) : ¬ a :=
  show a → False from h

end Forward
```

# Raciocínio Progressivo sobre Conectivos e Quantificadores

A Aula 4 aplicou as regras dos conectivos de forma regressiva com `apply`. De forma progressiva, as mesmas regras se usam por *justaposição*, fornecendo a hipótese diretamente. Uma regra de eliminação desmonta uma hipótese, e uma regra de introdução constrói o objetivo. Assim, `And.left h` e `And.right h` extraem as duas conjunções, `And.intro ha hb` e o construtor anônimo `⟨ha, hb⟩` constroem uma conjunção, `Or.inl` e `Or.inr` constroem uma disjunção, `Or.elim h f g` a consome com dois ramos funcionais, `Iff.mp` e `Iff.mpr` aplicam uma equivalência em cada direção, `Exists.intro t pf` fornece uma testemunha, e `Exists.elim h f` nomeia a testemunha de uma hipótese existencial. Cada um é um passo progressivo, e uma prova estruturada os encadeia com `have`.

A comutatividade da conjunção, provada de forma regressiva na Aula 4, se lê de forma progressiva como três passos `have`.

```lean
namespace Forward

theorem And_swap (a b : Prop) : a ∧ b → b ∧ a :=
  assume h : a ∧ b;
  have ha : a := And.left h;
  have hb : b := And.right h;
  show b ∧ a from And.intro hb ha

end Forward
```

A comutatividade da disjunção consome a hipótese com `Or.elim` e a reconstrói do outro lado. `modus_ponens` e `Not_Not_intro` combinam os passos vistos até aqui, lembrando que ¬ a é a → False.

```lean
namespace Forward

theorem Or_swap (a b : Prop) : a ∨ b → b ∨ a :=
  assume h : a ∨ b;
  Or.elim h
    (fun ha => Or.inr ha)
    (fun hb => Or.inl hb)

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  assume hab : a → b;
  assume ha : a;
  show b from hab ha

theorem Not_Not_intro (a : Prop) : a → ¬¬ a :=
  assume ha : a;
  assume hna : ¬ a;
  show False from hna ha

end Forward
```

O ponto alto da seção é o par de *regras do ponto único*, que colapsam um quantificador cuja variável ligada é presa a um valor fixo por uma igualdade. A regra para ∀ diz que uma implicação universalmente quantificada guardada por x = t é equivalente à sua instância em t; a regra para ∃ é o seu espelho existencial. Cada prova é estruturada, e cada uma é mais natural de forma progressiva do que regressiva.

```lean
namespace Forward

theorem Forall_one_point (α : Type) (t : α)
    (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

theorem Exists_one_point (α : Type) (t : α)
    (P : α → Prop) :
    (∃ x, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume h : ∃ x, x = t ∧ P x;
     Exists.elim h (fun x hx => hx.1 ▸ hx.2))
    (assume hpt : P t;
     Exists.intro t (And.intro rfl hpt))

end Forward
```

Na direção progressiva da regra para ∀, a hipótese é instanciada em t e a guarda t = t é descarregada por `rfl`. Na direção regressiva, um x arbitrário é fixado, a guarda x = t é suposta, e a igualdade reescreve P t em P x pelo operador de substituição `▸`. A regra para ∃ fornece a testemunha t de um lado e nomeia a testemunha do outro.

## Exemplos

Os exemplos abaixo aplicam cada regra de forma progressiva por justaposição, depois provam as duas regras do ponto único.

{ex "ex-forward-and-left-right"}[] `And.left` e `And.right` extraem as duas conjunções de forma progressiva.

```lean
namespace Forward

example (a b : Prop) (h : a ∧ b) : a :=
  And.left h

example (a b : Prop) (h : a ∧ b) : b :=
  And.right h

end Forward
```

{ex "ex-forward-and-intro-anonymous"}[] `And.intro` e o construtor anônimo constroem uma conjunção, e os dois termos são o mesmo.

```lean
namespace Forward

example (a b : Prop) (ha : a) (hb : b) : a ∧ b :=
  And.intro ha hb

example (a b : Prop) (ha : a) (hb : b) : a ∧ b :=
  ⟨ha, hb⟩

end Forward
```

{ex "ex-forward-and-swap-beside-backward"}[] A comutatividade da conjunção de forma progressiva, ao lado do seu roteiro regressivo da Aula 4.

```lean
namespace Forward

example (a b : Prop) : a ∧ b → b ∧ a :=
  assume h : a ∧ b;
  And.intro (And.right h) (And.left h)

example (a b : Prop) : a ∧ b → b ∧ a := by
  intro h
  apply And.intro
  · exact And.right h
  · exact And.left h

end Forward
```

{ex "ex-forward-or-inl-inr"}[] `Or.inl` e `Or.inr` constroem uma disjunção escolhendo um lado.

```lean
namespace Forward

example (a b : Prop) (ha : a) : a ∨ b :=
  Or.inl ha

example (a b : Prop) (hb : b) : a ∨ b :=
  Or.inr hb

end Forward
```

{ex "ex-forward-or-elim-two-branches"}[] `Or.elim h f g` consome uma disjunção com dois ramos funcionais.

```lean
namespace Forward

example (a b c : Prop) (h : a ∨ b) (f : a → c)
    (g : b → c) : c :=
  Or.elim h f g

end Forward
```

{ex "ex-forward-iff-mp-mpr"}[] `Iff.mp` e `Iff.mpr` aplicam uma equivalência em cada direção por justaposição.

```lean
namespace Forward

example (a b : Prop) (h : a ↔ b) (ha : a) : b :=
  Iff.mp h ha

example (a b : Prop) (h : a ↔ b) (hb : b) : a :=
  Iff.mpr h hb

end Forward
```

{ex "ex-forward-exists-intro-witness"}[] `Exists.intro t pf` fornece uma testemunha de forma progressiva, e o construtor anônimo é o mesmo termo.

```lean
namespace Forward

example (P : ℕ → Prop) (h : P 3) : ∃ n, P n :=
  Exists.intro 3 h

example (P : ℕ → Prop) (h : P 3) : ∃ n, P n :=
  ⟨3, h⟩

end Forward
```

{ex "ex-forward-exists-elim-names-witness"}[] `Exists.elim h f` nomeia a testemunha de uma hipótese existencial em um ramo funcional.

```lean
namespace Forward

example (α : Type) (P : α → Prop) (Q : Prop)
    (h : ∃ x, P x) (f : ∀ x, P x → Q) : Q :=
  Exists.elim h f

end Forward
```

{ex "ex-forward-forall-one-point"}[] A regra do ponto único para ∀ de forma progressiva, instanciando em t de um lado e reescrevendo com a guarda do outro.

```lean
namespace Forward

example (α : Type) (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

end Forward
```

{ex "ex-forward-exists-one-point"}[] A regra do ponto único para ∃ de forma progressiva, contrastando a testemunha fornecida de um lado com a testemunha nomeada do outro.

```lean
namespace Forward

example (α : Type) (t : α) (P : α → Prop) :
    (∃ x, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume h : ∃ x, x = t ∧ P x;
     Exists.elim h (fun x hx => hx.1 ▸ hx.2))
    (assume hpt : P t;
     Exists.intro t (And.intro rfl hpt))

end Forward
```

# Provas Calculacionais

Uma prova *calculacional* dispõe uma cadeia de igualdades para o leitor, um passo por linha, cada passo justificado por uma reescrita ou por um lema. A palavra-chave `calc` compõe os passos em uma única derivação transitiva, fazendo o papel de `Eq.trans` para que quem escreve não precise fazê-lo. Cada passo é exatamente o tipo de igualdade que `rw` consome, e um passo que vale apenas a menos de associatividade e comutatividade é fechado pelo `ac_rfl` da Aula 4. A disposição se lê como um matemático escreve, com o termo corrente à esquerda e a justificativa à direita.

```lean
namespace Forward

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

end Forward
```

O mesmo argumento escrito com passos `have` aninhados e `Eq.trans` mostra o que `calc` abrevia. A cadeia de duas igualdades vira dois fatos nomeados unidos por transitividade.

```lean
namespace Forward

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m := by
  have h1 : 2 * m + n = (m + m) + n := by
    rw [Nat.two_mul]
  have h2 : (m + m) + n = m + n + m := by ac_rfl
  exact Eq.trans h1 h2

end Forward
```

`calc` também encadeia qualquer relação transitiva, não só a igualdade, e os exemplos incluem uma cadeia sobre ↔ fechada por `Iff.trans`.

## Exemplos

Os exemplos abaixo constroem cadeias calculacionais, justificam os seus passos por reescritas e por lemas, e comparam `calc` com as alternativas que ele abrevia.

{ex "ex-calc-two-steps-rfl"}[] Uma cadeia de dois passos sobre ℕ, cada passo fechado por `rfl`.

```lean
namespace Forward

example : (1 : ℕ) + 1 + 1 = 3 := by
  calc (1 : ℕ) + 1 + 1 = 2 + 1 := rfl
    _ = 3 := rfl

end Forward
```

{ex "ex-calc-same-by-eq-trans"}[] A mesma identidade por `Eq.trans`, que expõe o que a cadeia abrevia.

```lean
namespace Forward

example : (1 : ℕ) + 1 + 1 = 3 :=
  Eq.trans
    (rfl : (1 : ℕ) + 1 + 1 = 2 + 1)
    (rfl : (2 : ℕ) + 1 = 3)

end Forward
```

{ex "ex-calc-step-by-rw"}[] Um único passo justificado por reescrita com a comutatividade.

```lean
namespace Forward

example (a b : ℕ) : a + b = b + a := by
  calc a + b = b + a := by rw [Nat.add_comm]

end Forward
```

{ex "ex-calc-step-by-lemma"}[] Um passo justificado por um lema nomeado da Aula 4, a associatividade do nosso `add`.

```lean
namespace Forward

example (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  calc add (add l m) n
      = add l (add m n) := Backward.add_assoc l m n

end Forward
```

{ex "ex-calc-mixing-rw-and-ac-rfl"}[] Uma cadeia que mistura um passo `rw` com um passo `ac_rfl`, a identidade completa da duplicação.

```lean
namespace Forward

example (m n : ℕ) : 2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

end Forward
```

{ex "ex-calc-last-step-ac-rfl"}[] Uma cadeia cujo último passo é `ac_rfl` e cujo primeiro é um `rfl`.

```lean
namespace Forward

example (a b c : ℕ) : a + b + c = c + (a + b) := by
  calc a + b + c = (a + b) + c := rfl
    _ = c + (a + b) := by ac_rfl

end Forward
```

{ex "ex-calc-three-equalities"}[] Uma cadeia de três igualdades construída a partir de duas hipóteses.

```lean
namespace Forward

example (a b c d : ℕ) (h1 : a = b) (h2 : b = c)
    (h3 : c = d) : a = d := by
  calc a = b := h1
    _ = c := h2
    _ = d := h3

end Forward
```

{ex "ex-calc-over-iff"}[] `calc` encadeia dois bicondicionais com `Iff.trans` exatamente como encadeia igualdades.

```lean
namespace Forward

example (a b c : Prop) (h1 : a ↔ b) (h2 : b ↔ c) :
    a ↔ c := by
  calc a ↔ b := h1
    _ ↔ c := h2

end Forward
```

{ex "ex-calc-versus-simp"}[] O mesmo objetivo por uma cadeia explícita e por um único `simp`, o que mostra quando a cadeia justifica o seu comprimento.

```lean
namespace Forward

example (a b : ℕ) : (a + b) * 1 = a + b := by
  calc (a + b) * 1 = a + b := by rw [Nat.mul_one]

example (a b : ℕ) : (a + b) * 1 = a + b := by
  simp

end Forward
```

{ex "ex-calc-step-right-to-left"}[] Um passo que se lê da direita para a esquerda, justificado por uma reescrita com a igualdade invertida.

```lean
namespace Forward

example (a b : ℕ) (h : a = b) : b = a := by
  calc b = a := by rw [← h]

end Forward
```

# Raciocínio Progressivo com Táticas

As provas reais entrelaçam as duas direções. No modo de táticas, `have h : P := pf` e `have h : P := by …` acrescentam um fato provado ao contexto, e `let x := t` acrescenta uma abreviação, ambos trabalhando de forma progressiva enquanto a prova ao redor trabalha de forma regressiva. A tática `specialize` da Aula 2 e a eliminação `obtain ⟨…⟩ := h` são outros passos progressivos. A composição de implicações, provada de forma progressiva como termo mais cedo nesta aula, se lê no estilo misto como um único `have` progressivo dentro de uma prova regressiva.

```lean
namespace Forward

theorem prop_comp_tactical (a b c : Prop)
    (hab : a → b) (hbc : b → c) : a → c := by
  intro ha
  have hb : b := hab ha
  exact hbc hb

end Forward
```

O `have` progressivo constrói b a partir de ha e hab, e o `exact` regressivo fecha o objetivo com hbc aplicado a ele. A prova mista costuma ser a mais curta, porque toma cada fato de onde é mais fácil alcançá-lo.

## Exemplos

Os exemplos abaixo acrescentam fatos com `have`, abreviam com `let`, instanciam com `specialize`, eliminam com `obtain` e misturam as duas direções.

{ex "ex-tactics-have-then-exact"}[] Um `have` progressivo constrói o fato intermediário, e um `exact` regressivo fecha o objetivo.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  have hb : b := hab ha
  exact hbc hb

end Forward
```

{ex "ex-tactics-purely-backward"}[] O mesmo teorema escrito de forma puramente regressiva, para contraste.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  exact hbc (hab ha)

end Forward
```

{ex "ex-tactics-have-by-block"}[] `have … := by …` prova o fato intermediário por um bloco de táticas próprio.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  have hb : b := by exact hab ha
  exact hb

end Forward
```

{ex "ex-tactics-let-abbreviation"}[] `let x := t` abrevia um termo, e `show` reafirma o objetivo em termos da abreviação.

```lean
namespace Forward

example (n : ℕ) : n + n = n + n := by
  let m := n + n
  show m = m
  rfl

end Forward
```

{ex "ex-tactics-specialize"}[] `specialize` instancia uma hipótese universal de forma progressiva, recordando a Aula 2.

```lean
namespace Forward

example (P : ℕ → Prop) (h : ∀ n, P n) : P 7 := by
  specialize h 7
  exact h

end Forward
```

{ex "ex-tactics-have-enables-simp"}[] Um `have` progressivo faz um `simp` posterior ter sucesso.

```lean
namespace Forward

example (f : ℕ → ℕ) (a : ℕ) (h : f a = 0) :
    f a + 1 = 1 := by
  have hf : f a = 0 := h
  simp [hf]

end Forward
```

{ex "ex-tactics-obtain-existential"}[] `obtain ⟨a, ha⟩ := h` elimina uma hipótese existencial de forma progressiva, nomeando a sua testemunha.

```lean
namespace Forward

example (α : Type) (P : α → Prop) (Q : Prop)
    (hex : ∃ x, P x) (h : ∀ x, P x → Q) : Q := by
  obtain ⟨a, ha⟩ := hex
  exact h a ha

end Forward
```

{ex "ex-tactics-two-haves-chained"}[] Dois passos `have` encadeados, o segundo usando o primeiro.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  have hb : b := hab ha
  have hc : c := hbc hb
  exact hc

end Forward
```

{ex "ex-tactics-mixed-apply-have"}[] Uma prova que mistura um `apply` regressivo com um `have` progressivo.

```lean
namespace Forward

example (a b c : Prop) (hab : a → b) (hbc : b → c)
    (ha : a) : c := by
  apply hbc
  have hb : b := hab ha
  exact hb

end Forward
```

{ex "ex-tactics-mixed-is-shorter"}[] O mesmo teorema apenas regressivo e misto, para que o misto mostre a sua economia.

```lean
namespace Forward

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  apply hab
  exact ha

example (a b : Prop) (hab : a → b) (ha : a) : b := by
  exact hab ha

end Forward
```

# Provas por Casamento de Padrões e Recursão

Sob o princípio PAT, uma função recursiva que devolve uma prova *é* uma prova por indução, e a chamada recursiva é a hipótese de indução. Uma definição por casamento de padrões sobre uma lista tem uma equação para a lista vazia e uma para um cons, e a equação para `x :: xs` pode chamar a função na lista menor `xs`, que é o apelo à hipótese de indução. A seção mostra duas identidades de listas provadas desse modo e afirma claramente que a teoria geral da indução estrutural sobre tipos indutivos arbitrários é o tema das semanas 6 e 7. Aqui a recursão aparece apenas como um dispositivo de prova progressiva.

Duas identidades auxiliares vêm primeiro. Anexar a lista vazia à direita nada muda, e a anexação é associativa. Cada uma é provada por recursão sobre a primeira lista, e a chamada recursiva carrega a hipótese de indução; `congrArg (List.cons x)` reconstrói o cons ao redor dela.

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

A reversão se distribui sobre a anexação, em ordem invertida. A prova recorre sobre a primeira lista, usando as duas auxiliares e a chamada recursiva, que `simp` consome como regras de reescrita.

```lean
namespace Forward

theorem reverse_append {α : Type} :
    ∀ (xs ys : List α),
      reverse (appendPretty xs ys)
        = appendPretty (reverse ys) (reverse xs)
  | [],      ys => by
      simp [reverse, appendPretty, append_nil]
  | x :: xs, ys => by
      simp [reverse, appendPretty,
            reverse_append xs ys, append_assoc]

end Forward
```

O mesmo enunciado provado pela tática `induction` da Aula 4 é a mesma prova em outra roupagem. O caso base é o ramo `nil`, e o caso do passo é o ramo `cons`, cuja hipótese de indução `ih` é exatamente a chamada recursiva acima.

```lean
namespace Forward

theorem reverse_append_tactical {α : Type}
    (xs ys : List α) :
    reverse (appendPretty xs ys)
      = appendPretty (reverse ys) (reverse xs) := by
  induction xs with
  | nil           =>
    simp [reverse, appendPretty, append_nil]
  | cons x xs' ih =>
    simp [reverse, appendPretty, ih, append_assoc]

end Forward
```

## Exemplos

Os exemplos abaixo provam identidades de listas e de números por recursão, colocam a prova recursiva ao lado da tática `induction`, nomeiam a chamada recursiva como a hipótese de indução e marcam a disciplina que as semanas 6 e 7 formalizam.

{ex "ex-recursion-nat-pattern-match"}[] Uma prova por recursão sobre ℕ, o seu caso base `0` e o seu caso do passo `n + 1`, reescrevendo a indução da Aula 4 como casamento de padrões. A identidade é `add 0 n = n` para o `add` da Aula 3.

```lean
namespace Forward

theorem add_zero_rec :
    ∀ (n : ℕ), add 0 n = n
  | 0     => rfl
  | n + 1 => by simp [add, add_zero_rec n]

end Forward
```

{ex "ex-recursion-append-assoc-base"}[] O caso base da associatividade sozinho. A primeira lista vazia faz os dois lados se reduzirem ao mesmo termo, de modo que `rfl` o fecha.

```lean
namespace Forward

example {α : Type} (ys zs : List α) :
    appendPretty (appendPretty [] ys) zs
      = appendPretty [] (appendPretty ys zs) :=
  rfl

end Forward
```

{ex "ex-recursion-call-is-hypothesis"}[] O caso do passo torna explícita a hipótese de indução. A chamada recursiva `ih` prova a associatividade das listas menores, e `congrArg (List.cons x)` reconstrói o cons ao redor dela.

```lean
namespace Forward

example {α : Type} (x : α) (xs ys zs : List α)
    (ih : appendPretty (appendPretty xs ys) zs
            = appendPretty xs (appendPretty ys zs)) :
    appendPretty (appendPretty (x :: xs) ys) zs
      = appendPretty (x :: xs) (appendPretty ys zs) :=
  congrArg (List.cons x) ih

end Forward
```

{ex "ex-recursion-reverse-append-base"}[] O caso base de `reverse_append`, onde a reversão da lista vazia e a identidade à direita da anexação juntas fecham o objetivo.

```lean
namespace Forward

example {α : Type} (ys : List α) :
    reverse (appendPretty [] ys)
      = appendPretty (reverse ys)
          (reverse ([] : List α)) := by
  simp [reverse, appendPretty, append_nil]

end Forward
```

{ex "ex-recursion-reverse-append-step"}[] O caso do passo de `reverse_append`, usando a hipótese de indução `ih` e a associatividade da anexação.

```lean
namespace Forward

example {α : Type} (x : α) (xs ys : List α)
    (ih : reverse (appendPretty xs ys)
            = appendPretty (reverse ys) (reverse xs)) :
    reverse (appendPretty (x :: xs) ys)
      = appendPretty (reverse ys)
          (reverse (x :: xs)) := by
  simp [reverse, appendPretty, ih, append_assoc]

end Forward
```

{ex "ex-recursion-append-nil-two-ways"}[] A identidade à direita da anexação pela tática `induction`. É a mesma prova que o `append_nil` recursivo acima, em outra roupagem.

```lean
namespace Forward

example {α : Type} (xs : List α) :
    appendPretty xs [] = xs := by
  induction xs with
  | nil           => rfl
  | cons x xs' ih => simp [appendPretty, ih]

end Forward
```

{ex "ex-recursion-rests-on-structural"}[] A prova recursiva concluída se apoia em `propext`, que `simp` usa, e não em `sorryAx`, de modo que a recursão é genuína.

```lean (name := recAxioms)
namespace Forward

#print axioms reverse_append

end Forward
```

```leanOutput recAxioms
'Forward.reverse_append' depends on axioms: [propext]
```

{ex "ex-recursion-rejected-non-structural"}[] Nem toda definição recursiva é aceita. A definição abaixo chama a si mesma na *mesma* lista, de modo que nenhum argumento diminui e a recursão nunca termina, e Lean a rejeita com um erro de terminação. A disciplina que as semanas 6 e 7 formalizam é exatamente o que exclui definições como essa.

```
def loopForever {α : Type} : List α → List α
  | []      => []
  | x :: xs => loopForever (x :: xs)
```

{ex "ex-recursion-same-identity-two-ways"}[] Uma identidade, duas provas. A associatividade da anexação por recursão e pela tática `induction` provam a mesma proposição, e ambas se apoiam apenas na recursão estrutural.

```lean
namespace Forward

example {α : Type} (xs ys zs : List α) :
    appendPretty (appendPretty xs ys) zs
      = appendPretty xs (appendPretty ys zs) := by
  induction xs with
  | nil           => rfl
  | cons x xs' ih => simp [appendPretty, ih]

end Forward
```

{ex "ex-recursion-general-form-pointer"}[] A forma geral. Uma recursão estrutural sobre um tipo indutivo tem um ramo por construtor, e cada chamada recursiva, tomada sobre um valor menor, é a hipótese de indução para aquele ramo. As semanas 6 e 7 tornam isso preciso para tipos indutivos arbitrários; o `reverse_reverse` dos exemplos resolvidos é mais uma instância.

```lean
namespace Forward

example {α : Type} (xs : List α) :
    reverse (appendPretty xs []) = reverse xs := by
  rw [append_nil]

end Forward
```

# Exemplos Resolvidos

Cada exemplo abaixo inverte um artefato da Aula 4 para o estilo progressivo e estruturado, de modo que as duas aulas se leiam como um único argumento visto de ambos os extremos. Lean verifica cada linha quando as notas são compiladas.

## A lei distributiva, progressivamente

O enunciado a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) foi o primeiro exemplo resolvido da Aula 4, provado de forma regressiva. De forma progressiva ele se lê como um termo estruturado. Da hipótese temos a e temos b ∨ c; de b ∨ c obtemos dois casos; em cada um construímos a disjunção correspondente com o construtor anônimo.

```lean
namespace Forward

theorem and_or_distrib (a b c : Prop) :
    a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) :=
  assume habc : a ∧ (b ∨ c);
  have ha : a := And.left habc;
  Or.elim (And.right habc)
    (fun hb => Or.inl (And.intro ha hb))
    (fun hc => Or.inr (And.intro ha hc))

end Forward
```

Em palavras. Suponha a ∧ (b ∨ c), e nomeie a sua conjunção esquerda ha. A sua conjunção direita é uma disjunção, então raciocinamos por casos. Se b vale, a disjunção esquerda a ∧ b segue de ha e b. Se c vale, a disjunção direita a ∧ c segue de ha e c. A prova regressiva da Aula 4 aplicou `Or.elim` para dividir o objetivo e fechou cada ramo com marcadores; a prova progressiva consome a mesma disjunção com `Or.elim` e devolve a disjunção construída diretamente. O compromisso é o de sempre, o roteiro regressivo planejando a partir do objetivo e o termo progressivo construindo a partir das hipóteses.

## `Forall_one_point` por extenso

A regra do ponto único (∀ x, x = t → P x) ↔ P t é o ápice da seção de conectivos, e é uma prova de quantificador que é natural de forma progressiva e desajeitada de forma regressiva.

```lean
namespace Forward

theorem Forall_one_point_worked (α : Type) (t : α)
    (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume h : ∀ x, x = t → P x; h t rfl)
    (assume hpt : P t;
     fix x : α; assume hxt : x = t; hxt ▸ hpt)

end Forward
```

A direção progressiva instancia a hipótese h no valor fixo t e descarrega a guarda t = t com `rfl`, de modo que h t rfl prova P t. A direção regressiva fixa um x arbitrário, supõe a guarda x = t, e reescreve P t em P x com a substituição `hxt ▸ hpt`, onde hxt : x = t carrega a igualdade. De forma regressiva a mesma prova deixaria uma metavariável para a testemunha e uma igualdade desajeitada por descarregar; de forma progressiva a testemunha é simplesmente t.

## Uma prova calculacional

A identidade `2 * m + n = m + n + m` tem três provas, e compará-las revela a moral do estilo calculacional.

```lean
namespace Forward

theorem two_mul_example_calc (m n : ℕ) :
    2 * m + n = m + n + m := by
  calc 2 * m + n = (m + m) + n := by rw [Nat.two_mul]
    _ = m + n + m := by ac_rfl

theorem two_mul_example_trans (m n : ℕ) :
    2 * m + n = m + n + m := by
  have h1 : 2 * m + n = (m + m) + n := by
    rw [Nat.two_mul]
  have h2 : (m + m) + n = m + n + m := by ac_rfl
  exact Eq.trans h1 h2

theorem two_mul_example_ac (m n : ℕ) :
    2 * m + n = m + n + m := by
  rw [Nat.two_mul]
  ac_rfl

end Forward
```

A prova por `calc` documenta a cadeia que o leitor segue. A prova por `Eq.trans` mostra a transitividade que `calc` esconde. A prova por `ac_rfl` esconde a cadeia por completo e deixa o verificador rearranjar os termos. As três estão corretas e se apoiam nos mesmos fatos; a escolha é sobre o leitor, não sobre o verificador.

## `reverse_reverse` por recursão

Reverter uma lista duas vezes devolve a lista, e a prova recorre sobre a lista, usando o `reverse_append` provado acima como sua auxiliar. Isto fecha o ciclo com o quarto exemplo resolvido da Aula 4, que descarregou `reverse_cons`.

```lean
namespace Forward

theorem reverse_reverse {α : Type} :
    ∀ (xs : List α), reverse (reverse xs) = xs
  | []      => rfl
  | x :: xs => by
      simp [reverse, reverse_append, appendPretty,
            reverse_reverse xs]

end Forward
```

O caso base reverte a lista vazia duas vezes e fecha por `rfl`. No caso do passo, reverter `x :: xs` dá `appendPretty (reverse xs) [x]`, e reverter isso, por `reverse_append`, traz a cabeça de volta à frente e deixa `reverse (reverse xs)`, que a chamada recursiva, a hipótese de indução, reescreve para xs. A tática `induction` da Aula 4 provaria o mesmo enunciado com `ih` no lugar da chamada recursiva; as duas são a mesma prova. As semanas 6 e 7 dão o método geral para tipos indutivos arbitrários.

# Exercícios

Prove cada enunciado em Lean, substituindo `sorry`. Baixe o arquivo de exercícios [`Lecture05.lean`](example-code/Lectures/Pt/Lecture05.lean) e o abra no VS Code. Cada exercício pede uma prova estruturada. Os exercícios 1 a 6 usam `fix`, `assume`, `have`, `show` e os nomes das regras apenas, sem táticas; os exercícios 7 e 8 usam `calc`; os exercícios 9 e 10 são opcionais.

```savedImport
import Lectures.LoVe.LoVelib
```

```savedComment
Exercícios da Aula 5: Provas Progressivas.
Dê uma prova estruturada de cada enunciado, substituindo `sorry`.
A importação fornece `fix` e `assume` e os lemas aritméticos.
Os exercícios 1 a 6 usam `fix`, `assume`, `have` e `show` apenas.
Os exercícios 7 e 8 usam `calc`. Os exercícios 9 e 10 são opcionais.
```

{exercise "exr-s-combinator"}[] O combinador S, distribuindo um argumento por duas funções.

```savedLean -keep
namespace Forward

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  sorry

end Forward
```

{exercise "exr-curry-iff"}[] Currificação e descurrificação, as duas direções como um bicondicional.

```savedLean -keep
namespace Forward

theorem curry_iff (a b c : Prop) :
    (a ∧ b → c) ↔ (a → b → c) :=
  sorry

end Forward
```

{exercise "exr-iff-symm"}[] Um bicondicional é simétrico, construído a partir das suas duas direções.

```savedLean -keep
namespace Forward

theorem iff_symm (a b : Prop) :
    (a ↔ b) → (b ↔ a) :=
  sorry

end Forward
```

{exercise "exr-non-contradiction"}[] A não contradição, lembrando que ¬ a abrevia a → False.

```savedLean -keep
namespace Forward

theorem non_contradiction (a : Prop) :
    ¬ (a ∧ ¬ a) :=
  sorry

end Forward
```

{exercise "exr-or-imp"}[] Uma implicação a partir de uma disjunção se divide em duas.

```savedLean -keep
namespace Forward

theorem or_imp (a b c : Prop) :
    (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  sorry

end Forward
```

{exercise "exr-forall-eq-three"}[] Uma regra do ponto único concreta. Instanciar a guarda no valor fixo colapsa o quantificador.

```savedLean -keep
namespace Forward

theorem forall_eq_three (P : ℕ → Prop) :
    (∀ x, x = 3 → P x) ↔ P 3 :=
  sorry

end Forward
```

{exercise "exr-two-distrib"}[] Duplicar uma soma, por `calc`. Dica: `Nat.two_mul` abre a duplicação e `ac_rfl` fecha o rearranjo.

```savedLean -keep
namespace Forward

theorem two_distrib (a b : ℕ) :
    2 * (a + b) = a + a + (b + b) :=
  sorry

end Forward
```

{exercise "exr-calc-chain"}[] Distributividade à direita da multiplicação sobre uma soma, por `calc`.

```savedLean -keep
namespace Forward

theorem calc_chain (a b c : ℕ) :
    (a + b) * c = a * c + b * c :=
  sorry

end Forward
```

{exercise "exr-exists-eq-three"}[] Opcional. A regra do ponto único concreta para ∃, o seu espelho no lado existencial.

```savedLean -keep
namespace Forward

theorem exists_eq_three (P : ℕ → Prop) :
    (∃ x, x = 3 ∧ P x) ↔ P 3 :=
  sorry

end Forward
```

{exercise "exr-curry-three"}[] Opcional. Currificar uma conjunção tripla, ambas as direções.

```savedLean -keep
namespace Forward

theorem curry_three (a b c d : Prop) :
    (a ∧ b ∧ c → d) ↔ (a → b → c → d) :=
  sorry

end Forward
```
