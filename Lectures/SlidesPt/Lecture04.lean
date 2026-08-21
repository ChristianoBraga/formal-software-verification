/-
Slides da Aula 4, gerados de fontes verificadas. Cada seção de
nível superior é um slide; o título do documento e os parágrafos
iniciais formam o slide de título. Todo o código Lean é elaborado
na construção e é idêntico ao código das notas de aula
(`Lectures/Pt/Lecture04.lean`) onde os dois se sobrepõem.

Somente as notações ℕ e ℤ vêm de Mathlib, além do deck da Aula 3
para `add`, `mul`, `appendPretty`, `reverse` e `snoc`. A
biblioteca completa colidiria com os nomes dos próprios decks
quando todos são construídos juntos.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesPt.Lecture03

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.introMerge false

#doc (Manual) "Provas Regressivas" =>

Modo de táticas, táticas básicas, reescrita e indução em Lean

Christiano Braga · Mestrado em Sistemas e Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-4___-Provas-Regressivas/)

Baseada no [*Hitchhiker's Guide to Logical Verification*](https://github.com/lean-forward/logical_verification_2026) (LoVe), capítulo 3.

# §4.1 Regressivo e progressivo

* Uma *tática* opera sobre um objetivo e o prova ou cria subobjetivos. Um objetivo é o sequente C ⊢ Q, com antecedente C, o contexto local, e consequente Q, a conclusão.

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

* A frase característica de uma prova regressiva é *"basta provar"*. Em uma derivação de dedução natural, as premissas de cada regra ficam acima do traço de inferência e a conclusão abaixo dele. A leitura progressiva vai das suposições, no topo, para a conclusão, e a regressiva vai da conclusão para as suposições.

# §4.1 Modo de táticas

* A palavra-chave `by` entra no modo de táticas, e cada linha depois dela é uma tática. `trace_state` imprime o objetivo entre os passos.

::::cols
:::col
```lean (name := fstOfTwo)
namespace Backward

theorem fst_of_two_props :
    ∀ a b : Prop, a → b → a := by
  intro a b
  trace_state
  intro ha hb
  trace_state
  apply ha

end Backward
```
:::
:::col
{lbl}[Depois do primeiro e do segundo intro]

```leanOutput fstOfTwo
a b : Prop
⊢ a → b → a
```

```leanOutput fstOfTwo
a b : Prop
ha : a
hb : b
⊢ a
```
:::
::::

# §4.2 As quatro táticas básicas

* Táticas básicas realizam uma transformação elementar do estado da prova cada uma, e nenhuma depende de um conectivo ou de uma teoria em particular.

* `intro` move variáveis e suposições para o contexto; `apply` casa a conclusão do objetivo com a de um teorema e deixa os seus argumentos e premissas não resolvidos como objetivos; `exact` fecha o objetivo com um termo; `assumption` procura no contexto.

::::cols
:::col
```lean
namespace Backward

theorem fst_of_two_props_params (a b : Prop)
    (ha : a) (hb : b) : a := by
  apply ha

theorem fst_of_two_props_exact (a b : Prop)
    (ha : a) (hb : b) : a := by
  exact ha

end Backward
```
:::
:::col
```lean
namespace Backward

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) : a := by
  assumption

theorem prop_comp (a b c : Prop) (hab : a → b)
    (hbc : b → c) : a → c := by
  intro ha
  apply hbc
  apply hab
  apply ha

end Backward
```
:::
::::

* Lean insere os parâmetros à esquerda dos dois-pontos no contexto local do objetivo inicial, então estas provas dispensam `intro`.

# §4.2 Perder a demonstrabilidade

::::cols
:::col
{lbl}[apply pode perder um objetivo demonstrável]

```lean (name := unsafeApply)
example (a b : Prop) (hb : b) : a ∨ b := by
  apply Or.inl
  trace_state
  sorry
```

```leanOutput unsafeApply
a b : Prop
hb : b
⊢ a
```

```lean
example (a b : Prop) (hb : b) : a ∨ b := by
  apply Or.inr
  exact hb
```
:::
:::col
{lbl}[sorry, clear, rename]

```lean
namespace Backward

theorem cleanup_example (a b c : Prop)
    (ha : a) (hb : b)
    (hab : a → b) (hbc : b → c) : c := by
  clear ha hab a
  apply hbc
  clear hbc c
  rename b => h
  exact h

end Backward
```
:::
::::

* Um objetivo demonstrável continua demonstrável após `intro`. `apply` e `clear` podem transformar um objetivo demonstrável em um indemonstrável. `sorry` fecha qualquer coisa e `#print axioms` o relata como `sorryAx`.

# §4.3 Regras como teoremas

* Cada figura de inferência da Aula 1 é um teorema ordinário, aplicado regressivamente por `apply`.

::::cols
:::col
{lbl}[Introdução e eliminação]

```
And.intro : ?a → ?b → ?a ∧ ?b
And.left  : ?a ∧ ?b → ?a
And.right : ?a ∧ ?b → ?b
Or.inl    : ?a → ?a ∨ ?b
Or.inr    : ?b → ?a ∨ ?b
Or.elim   : ?a ∨ ?b →
  (?a → ?c) → (?b → ?c) → ?c
Iff.intro : (?a → ?b) →
  (?b → ?a) → (?a ↔ ?b)
Iff.mp    : (?a ↔ ?b) → ?a → ?b
Iff.mpr   : (?a ↔ ?b) → ?b → ?a
```
:::
:::col
```lean
namespace Backward

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a := by
  intro hab
  apply And.intro
  apply And.right
  exact hab
  apply And.left
  exact hab

end Backward
```
:::
::::

# §4.3 Metavariáveis e marcadores

* Uma *metavariável* ?a representa um termo por determinar, e a *unificação* o determina. O marcador `·` foca um subobjetivo; a *justaposição* instancia uma regra progressivamente.

::::cols
:::col
```lean
namespace Backward

theorem And_swap_braces :
    ∀ a b : Prop, a ∧ b → b ∧ a := by
  intro a b hab
  apply And.intro
  · exact And.right hab
  · exact And.left hab

end Backward
```
:::
:::col
```lean
namespace Backward

opaque f : ℕ → ℕ

theorem f5_if (h : ∀ n : ℕ, f n = n) :
    f 5 = 5 := by
  exact h 5

end Backward
```
:::
::::

* Passar `hab` diretamente a `And.right` é um pequeno passo progressivo dentro de uma prova regressiva, e evita as metavariáveis que `apply And.right` deixaria.

# §4.3 Quantificadores, verdade, falsidade, negação

```
Exists.intro : ∀ (w : ?α), ?p w → ∃ x, ?p x
Exists.elim  : (∃ x, ?p x) → (∀ (w : ?α), ?p w → ?b) → ?b
True.intro   : True
False.elim   : False → ?c
Classical.em : ∀ (p : Prop), p ∨ ¬p
Classical.byContradiction : (¬?a → False) → ?a
```

* A negação dispensa regras: ¬a é *definida* como a → False, então `intro` se aplica a uma conclusão negada.

* `True.intro` é a única regra da verdade; a falsidade não tem regra de introdução, e `False.elim` fecha qualquer objetivo a partir de uma prova de `False`.

```lean
namespace Backward

theorem Not_Not_intro (a : Prop) : a → ¬¬ a := by
  intro ha hna
  apply hna
  exact ha

end Backward
```

# §4.3 Estratégias

As estratégias do guia para provas proposicionais.

* Olhe a conclusão. Uma implicação ou uma negação pede `intro`.

* Olhe as hipóteses. Uma conjunção oferece `And.left` e `And.right`, uma disjunção oferece `Or.elim`, uma equivalência oferece `Iff.mp` e `Iff.mpr`.

* Case a conclusão do objetivo com uma regra de introdução e a aplique com `apply`.

* Prefira táticas que preservam a demonstrabilidade enquanto fizerem progresso, e registre os pontos de escolha em que uma tática se compromete com um lado.

* Quando um subobjetivo repete uma hipótese, `exact` ou `assumption` o fecha.

* Quando nada construtivo se aplica, considere uma análise de casos sobre `Classical.em`.

* Se a prova não progride, retroceda até o último ponto de escolha e tente a outra opção.

# §4.4 `rfl` e as conversões

* `rfl` prova l = r quando os lados coincidem *a menos de computação*, e cada passo de computação é uma conversão nomeada.

::::cols
:::col
```
α  renomeia uma variável ligada
β  aplica uma função anônima
δ  desdobra uma definição
ζ  substitui um let
η  fun x => f x é igual a f
ι  projeta um construtor
```

```lean
namespace Backward

def double (n : ℕ) : ℕ := n + n

end Backward
```
:::
:::col
```lean
namespace Backward

theorem β_example {α β : Type}
    (f : α → β) (a : α) :
    (fun x => f x) a = f a := by
  rfl

theorem δ_example :
    double 5 = 5 + 5 := by
  rfl

theorem ι_example {α β : Type}
    (a : α) (b : β) :
    Prod.fst (a, b) = a := by
  rfl

end Backward
```
:::
::::

* `ac_rfl` adiciona associatividade e comutatividade dos operadores registrados, como em `a + b + c = c + b + a`.

# §4.4 A igualdade como regras

::::cols
:::col
```
Eq.refl  : ∀ (a : ?α), a = a
Eq.symm  : ?a = ?b → ?b = ?a
Eq.trans : ?a = ?b → ?b = ?c →
           ?a = ?c
Eq.subst : ?a = ?b → ?P ?a → ?P ?b
```

* `=` liga mais forte que os conectivos, então `a = b ∧ c = d` se lê `(a = b) ∧ (c = d)`.
:::
:::col
```lean
namespace Backward

theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c := by
  apply Eq.trans
  · exact hab
  · apply Eq.symm
    exact hcb

end Backward
```
:::
::::

# §4.5 `rw`

* `rw` aplica uma equação da esquerda para a direita, uma vez: encontra o primeiro subtermo que casa, substitui toda ocorrência dele e então tenta `rfl`. `←` inverte a equação, `at h` mira uma hipótese, e o nome de uma constante usa as equações que a definem.

::::cols
:::col
```lean
namespace Backward

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) : a = c := by
  rw [hab]
  rw [hcb]

end Backward
```
:::
:::col
```lean
namespace Backward

theorem a_proof_of_negation (a : Prop) :
    a → ¬¬ a := by
  rw [Not]
  rw [Not]
  intro ha hna
  apply hna
  exact ha

end Backward
```
:::
::::

# §4.5 `simp`

* `simp` reescreve com o *conjunto simp* exaustivamente. `simp [t]` adiciona um teorema ou constante por chamada, `simp [-t]` remove um, `simp [*] at *` usa tudo em toda parte, e `@[simp]` registra um teorema permanentemente.

```lean
namespace Backward

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
    (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 := by
  simp [hab, hcd]

end Backward
```

* A reescrita é onde as provas deixam de ser previsíveis. Tente uma tática, estude os subobjetivos que surgem e ajuste. Nas palavras do guia, NÃO ENTRE EM PÂNICO.

# §4.6 Indução

* `induction` produz um subobjetivo nomeado por construtor, e os nomes do ramo ligam os argumentos do construtor e a hipótese de indução.

::::cols
:::col
```
induction n with
| zero       => (caso base)
| succ n' ih => (caso do passo)
```

* Induza sobre o argumento que a recursão consome.

* Um caso base difícil sinaliza a variável errada ou um teorema auxiliar que falta.
:::
:::col
```lean
namespace Backward

theorem add_zero (n : ℕ) : add 0 n = n := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

end Backward
```
:::
::::

# §4.6 Comutatividade e `ac_rfl`

* Estas reprovam leis que a Aula 3 enunciou com `sorry`, agora como teoremas próprios, e as instâncias deixam `ac_rfl` tratar `add` como `+`.

::::cols
:::col
```lean
namespace Backward

theorem add_comm (m n : ℕ) :
    add m n = add n m := by
  induction n with
  | zero       => simp [add, add_zero]
  | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => simp [add, ih]

end Backward
```
:::
:::col
```lean
namespace Backward

instance Associative_add :
    Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add :
    Std.Commutative add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
    mul l (add m n) =
      add (mul l m) (mul l n) := by
  induction n with
  | zero       => rfl
  | succ n' ih =>
    simp [add, mul, ih]
    ac_rfl

end Backward
```
:::
::::

# §4.7 Exemplo trabalhado: descarregar `reverse_cons`

* A Aula 3 enunciou `reverse (x :: xs) = snoc (reverse xs) x` com `sorry`. O enunciado mistura `appendPretty` e `snoc`, então a peça que falta é o teorema que os relaciona.

::::cols
:::col
{lbl}[O teorema auxiliar]

```lean
namespace Backward

theorem append_snoc {α : Type}
    (ys : List α) (x : α) :
    appendPretty ys [x] = snoc ys x := by
  induction ys with
  | nil           => rfl
  | cons y ys' ih =>
    simp [appendPretty, snoc, ih]

end Backward
```
:::
:::col
{lbl}[O teorema, a um simp de distância]

```lean
namespace Backward

theorem reverse_cons {α : Type}
    (x : α) (xs : List α) :
    reverse (x :: xs) =
      snoc (reverse xs) x := by
  simp [reverse, append_snoc]

end Backward
```

* Um caso difícil costuma sinalizar um teorema auxiliar que falta.
:::
::::

# Resumo

* Uma tática transforma o objetivo, e uma prova regressiva se lê como uma cadeia de "basta provar".

* `intro`, `apply`, `exact` e `assumption` provam os teoremas proposicionais desta aula, e entre elas só `intro` nunca perde um objetivo demonstrável.

* Cada regra da Aula 1 é um teorema que `apply` consome regressivamente e a justaposição instancia progressivamente.

* `rfl` decide a igualdade a menos de computação, uma conversão nomeada por vez, e `ac_rfl` adiciona associatividade e comutatividade.

* `rw` reescreve uma vez no primeiro casamento e então tenta `rfl`; `simp` reescreve exaustivamente com o conjunto simp.

* `induction … with` prova as leis gerais que a computação não alcança, e reprova vários dos enunciados da Aula 3 como teoremas próprios.

* A Aula 5 vira as mesmas provas do avesso, em provas progressivas e estruturadas.

Exercícios: veja as [notas de aula](../pt/Aula-4___-Provas-Regressivas/).
