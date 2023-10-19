import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- Problem 4a
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro h1
    obtain ⟨t, ht⟩ := h1
    rw [h] at ht
    use t
    apply ht
  . intro h1 
    obtain ⟨t, ht⟩ := h1
    rw [← h] at ht
    use t
    apply ht

-- Problem 4b
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h
    obtain ⟨t, ht⟩ := h
    obtain ⟨t1, ht1⟩ := ht
    use t1
    use t
    apply ht1
  . intro h
    obtain ⟨t, ht⟩ := h
    obtain ⟨t1, ht1⟩ := ht
    use t1
    use t
    apply ht1

-- Problem 4c
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro h
    intro y
    intro x
    apply h
  . intro h
    intro y
    intro x
    apply h

-- Problem 4d
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro h
    obtain ⟨hl, hr⟩ := h
    obtain ⟨t, ht⟩ := hl
    use t
    apply And.intro ht hr
  . intro h
    obtain ⟨t, ht⟩ := h
    obtain ⟨hl, hr⟩ := ht
    constructor
    . use t; apply hl
    . apply hr


def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

-- Problem 5a

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h: Tribalanced 1
  . use 1
    constructor
    . apply h
    . ring
      intro h
      dsimp [Tribalanced] at h
      specialize h 2
      numbers at h
  . use 0
    constructor
    . intro n
      simp
      numbers
    . ring; apply h

-- Problem 5b
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . apply superpowered_one
  . ring
    intro h
    dsimp [Superpowered] at h
    specialize h 5
    numbers at h
    have h1 : ¬ Prime 4294967297 := by
      apply not_prime 641 6700417
      . numbers
      . numbers
      . ring 
    contradiction

