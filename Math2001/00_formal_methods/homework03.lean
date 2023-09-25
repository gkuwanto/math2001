import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

-- Problem 4a
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : x * -t > 0 := by calc
      x * -t = (-x) * t := by ring
      _ > 0:= by addarith [hxt]
    have hx' : 0 < x := by addarith [hx]
    cancel x at hxt'
    apply ne_of_lt
    have k : t<0 := by addarith [hxt']
    apply k

-- Problem 4b
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring



-- Problem 4c
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  . calc
    p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  . calc
    (p + q) / 2 < (q + q) / 2 := by rel [h]
    _ = q := by ring



-- Problem 5a
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt 0 x
  obtain hx | hx := H
  . use x+1
    calc
      (x+1)^2 = x^2 + 2*x + 1 := by ring
      _ = x * x + 2 * x +1 := by ring
      _ ≥ 0 * x + 2 * x + 1 := by rel [hx]
      _ = 2 * x + 1 := by ring
      _ > 2 * x := by extra
      _ = x + x := by ring
      _ ≥  0 + x := by rel[hx]
      _ = x := by ring
  . have h_neg_x : -x > 0 := by addarith [hx]
    use x-1
    calc
      (x-1)^2 = x^2 - 2*x + 1 := by ring
      _ =  -x * -x - 2 * x + 1  := by ring
      _ ≥ 0 * -x - 2 * x + 1 := by rel [h_neg_x]
      _ = -2 * x + 1 := by ring
      _ > -2*x := by extra
      _ = -x + -x := by ring
      _ ≥ 0 + 0 := by rel [h_neg_x]
      _ = 0 := by ring
      _ > x := by addarith [hx]

-- Problem 5b
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  intro ht
  rw [ht] at hxt
  apply ne_of_lt hxt
  ring

-- Problem 5c
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hxm⟩ := h
  intro hm
  rw [hm] at hxm
  obtain h1 | h1 := le_or_gt x 2
  . have := calc
      5 = 2 * x := by rw[hxm]
      _ ≤ 2 * 2 := by rel [h1]
      _ = 4 := by ring
    contradiction
  . have hr : x ≥ 3 := by addarith [h1]
    have := calc
      5 = 2 * x := by rw[hxm]
      _ ≥ 2 * 3 := by rel [hr]
      _ = 6 := by ring
    contradiction
