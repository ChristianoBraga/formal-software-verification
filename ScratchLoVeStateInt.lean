/- LoVe 2026 LoVelib "## States" section with ℕ replaced by ℤ
   (the lecture-relevant variant). Only the import and the value
   type differ from the verbatim extraction. -/
import Mathlib.Data.Int.Notation

set_option autoImplicit false

namespace LoVe

def State : Type :=
  String → ℤ

def State.update (name : String) (val : ℤ) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

notation s "[" name " ↦ " val "]" =>
  State.update name val s

@[simp] theorem update_apply (name : String) (val : ℤ) (s : State) :
    (s[name ↦ val]) name = val :=
  by
    apply if_pos
    rfl

@[simp] theorem update_apply_neq (name name' : String) (val : ℤ) (s : State)
      (hneq : name' ≠ name) :
    (s[name ↦ val]) name' = s name' :=
  by
    apply if_neg
    assumption

@[simp] theorem update_override (name : String) (val₁ val₂ : ℤ) (s : State) :
    s[name ↦ val₂][name ↦ val₁] = s[name ↦ val₁] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h => simp [h]
    | inr h => simp [h]

theorem update_swap (name₁ name₂ : String) (val₁ val₂ : ℤ) (s : State)
      (hneq : name₁ ≠ name₂ := by decide) :
    s[name₂ ↦ val₂][name₁ ↦ val₁] = s[name₁ ↦ val₁][name₂ ↦ val₂] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name₁) with
    | inl h => simp [*]
    | inr h =>
      cases Classical.em (name' = name₁) with
      | inl h => simp [*]
      | inr h => simp [State.update, *]

@[simp] theorem update_id (name : String) (s : State) :
    s[name ↦ s name] = s :=
  by
    apply funext
    intro name'
    simp [State.update]
    intro heq
    simp [*]

@[simp] theorem update_same_const (name : String) (val : ℤ) :
    (fun _ ↦ val)[name ↦ val] = (fun _ ↦ val) :=
  by
    apply funext
    simp [State.update]

example (s : State) :
    s["a" ↦ 0]["a" ↦ 2] = s["a" ↦ 2] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]) "b" = s "b" :=
  by simp

example (s : State) :
    s["a" ↦ 0]["b" ↦ 2] = s["b" ↦ 2]["a" ↦ 0] :=
  by simp [update_swap]

example (s : State) :
    s["a" ↦ s "a"]["b" ↦ 0] = s["b" ↦ 0] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]["b" ↦ 0]) "c" = s "c" :=
  by simp (config := {decide := true})

end LoVe
