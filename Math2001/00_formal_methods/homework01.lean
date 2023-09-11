import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p
/- 3a -/
theorem problem3a {p q r : Prop} (h1: p ∧ q → r) : p → (q → r) := by
  intro hp
  intro hq
  have hpq: p ∧ q := by apply And.intro hp hq
  exact h1 hpq

/- 3b -/
theorem problem3b {p q r : Prop} (h1: p → ( q → r )) : ( p → q ) → ( p → r ) := by
  intro hpq
  intro hp 
  have hq: q := by apply hpq hp
  apply h1 hp hq

/- 3c -/
theorem problem3c {p q r : Prop} (h1: (p∧¬q)→ r) (h2: ¬r) (h3: p) : q := by
  have nnq: ¬¬q := by 
    intro hq
    have hpq : p ∧ ¬q := by apply And.intro h3 hq
    have r := by apply h1 hpq
    contradiction
  apply notnotE nnq

/- 4a -/
theorem problem4a {a b : ℤ } (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc
    a = a := by ring
    _ = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring
  
/- 4b -/
theorem problem4b {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

/- 4c -/
theorem problem4c {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * (b + 2 - 2) := by ring
    _ = 4 + 5 * (3 - 2) := by rw [h1, h2]
    _ = 9 := by ring
