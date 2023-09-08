import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

/- 3a -/
example {p q r : Prop} (h1: p ∧ q → r) : p → (q → r) := by
  intro hp
  intro hq
  have hpq: p ∧ q := by apply And.intro hp hq
  exact h1 hpq

/- 3b -/
example {p q r : Prop} (h1: p → ( q → r )) : ( p → q ) → ( p → r ) := by
  intro hpq
  intro hp 
  have hq: q := by apply hpq hp
  apply h1 hp hq

/- 3c -/
example {p q r : Prop} (h1: (p∧¬q)→ r) (h2: ¬r) (h3: p) : ¬ (¬ q) := by
  intro hq
  have hr: r := by apply h1 (And.intro h3 hq)
  contradiction

/- 4a -/
example {a b : ℤ } (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc
    a = a := by ring
    _ = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring
  
/- 4b -/
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

/- 4c -/
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  calc
    w = (3 * w + 1 - 1)/3 := by ring
    _ = (4 - 1) / 3 := by rw [h1]
    _ = 1 := by ring
