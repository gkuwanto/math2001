import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


-- Problem 5 c
theorem de_morgan_2 {p q : Prop} : (¬p∧ ¬q)  → ¬(p ∨ q) := by
  intro h
  obtain ⟨hnp, hnq⟩ := h
  intro h1
  cases h1 with
  | inl hp => exact hnp hp
  | inr hq => exact hnq hq
  
-- Problem 5 d
theorem de_morgan_3 {p q : Prop} : (¬p ∨ ¬q ) → ¬(p ∧ q) := by
  intro h
  cases h with
  | inl hnp => intro h1; exact hnp h1.1
  | inr hnq => intro h1; exact hnq h1.2
  

theorem problem6a {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ = -1 := by numbers

theorem problem6b {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + (a + 2 * b)) / 2:= by ring
    _ ≥  (a + 4) / 2 := by rel [h2]
    _ ≥ (3 + 4) / 2 := by rel [h1]
    _ ≥ 3 := by numbers

theorem problem6c {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x
      = x * ((x - 4)^2 - 14) := by ring
    _ ≥ 9 * ((9 - 4)^2 - 14) := by rel [hx]
    _ ≥ 3 := by numbers
