/-!
Exercícios da Aula 1: Motivação e Lógica Proposicional.
Substitua cada `sorry` por uma prova.
-/
theorem exercise1 (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry

theorem exercise2 (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

theorem exercise3 (P Q R : Prop) :
    (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  sorry

theorem exercise4 (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry

theorem exercise5 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry

theorem exercise6 (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

theorem exercise7 (P Q R : Prop) :
    (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  sorry

theorem exercise8 (P Q : Prop) : (P ∨ Q) → ¬P → Q := by
  sorry

theorem exercise9 (P : Prop) : ¬(P ↔ ¬P) := by
  sorry

theorem exercise10 (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  sorry

