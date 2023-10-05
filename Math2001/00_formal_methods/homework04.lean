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
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- Problem 4a
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k,hk⟩ := hn
  use 7*k+1
  calc
    7*n-4 = 7*(2*k+1)-4 := by rw[hk]
    _ = 14*k+2 +  1 := by ring
    _ = 2 * (7*k+1) + 1 := by ring


-- Problem 4b
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨k1,hk1⟩ := hx
  obtain ⟨k2,hk2⟩ := hy
  use (2 * k1*k2 + k1 + 3*k2 + 1)
  calc
    x * y + 2 * y 
        = (2 * k1 + 1) * (2 * k2 + 1) + 2 * (2 * k2 + 1) := by rw [hk1,hk2]
      _ = 4*k1*k2 + 2*k1 + 2*k2 + 1 + 4 * k2 + 2 := by ring
      _ = 2 * (2 * k1*k2 + k1 + 3*k2 + 1) + 1 := by ring

-- Problem 4c
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨k,hk⟩ := hn
  use 2*k^2 + 2*k - 3
  calc
    n^2 + 2*n - 5 
      = (k+k)^2 + 2*(k+k) - 5 := by rw [hk]
    _ = 2 * (2*k^2 + 2*k - 3) + 1 := by ring
    


-- Problem 4d
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  dsimp [Even, Odd] at *
  obtain ha | ha := Int.even_or_odd a
  obtain hb | hb := Int.even_or_odd b
  . left
    obtain ⟨k1,hk1⟩ := ha
    obtain ⟨k2,hk2⟩ := hb
    use k1 - k2
    simp [hk1,hk2]
    ring
  . obtain hc | hc := Int.even_or_odd c
    . right
      left
      obtain ⟨k1,hk1⟩ := ha
      obtain ⟨k2,hk2⟩ := hc
      use k1 + k2
      simp [hk1,hk2]
      ring
    . right
      right
      obtain ⟨k1,hk1⟩ := hb
      obtain ⟨k2,hk2⟩ := hc
      use k1 - k2
      simp [hk1,hk2]
      ring
  . obtain hb | hb := Int.even_or_odd b
    . obtain hc | hc := Int.even_or_odd c
      . right
        right
        obtain ⟨k1,hk1⟩ := hb
        obtain ⟨k2,hk2⟩ := hc
        use k1 - k2
        simp [hk1,hk2]
        ring
      . right
        left
        obtain ⟨k1,hk1⟩ := ha
        obtain ⟨k2,hk2⟩ := hc
        use k1 + k2 + 1
        simp [hk1,hk2]
        ring
    . left
      obtain ⟨k1,hk1⟩ := ha
      obtain ⟨k2,hk2⟩ := hb
      use k1 - k2
      simp [hk1,hk2]
      ring

-- Problem 5a
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain hl | hr := h ((a + b)/2)
  . calc
    b = 2 * ((a + b)/2) - a := by ring
    _ ≥ 2 * a - a := by rel [hl]
    _ = a := by ring
  . calc
    a = 2 * ((a + b)/2) - b := by ring
    _ ≤ 2 * b - b := by rel [hr]
    _ = b := by ring

-- Problem 5b
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y
  intro h
  have h1 := calc
    (x+y)^2 ≤ (x+y)^2 + (x-y)^2 := by extra
    _ = 2 * (x^2 + y^2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ (3)^2 := by numbers
  have h2 : (0:ℝ) ≤ 3 := by numbers
  exact And.left (abs_le_of_sq_le_sq' h1 h2)

    

-- Problem 5c
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  obtain ⟨x, hx⟩ := hn 3 (by numbers) (by numbers)
  obtain ⟨y, hy⟩ := hn 5 (by numbers) (by numbers)
  use 2*x - 3*y
  calc
    n = 10*n - 9*n := by ring
    _ = 10*(3*x) - 9*(5*y) :=  by nth_rw 1 [hx]; rw[hy]
    _ = 15*(2*x - 3*y) := by ring


-- Problem 5d
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 10
  intro x hx
  calc
    x^3 + 3*x 
      = x * x^2 + 3*x := by ring
    _ ≥ 10 * x^2 + 3 * 10 := by rel[hx]
    _ = 7 * x^2 + 12 + (3*x^2 + 18):= by ring
    _ ≥ 7 * x^2 + 12 := by extra


-- Problem 6a
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have h1 := calc
      (x+3)*(x-2) =  x ^ 2 + x - 6 := by ring
      _ = 0 := by rw[h]
    rw [mul_eq_zero] at h1
    obtain h2 | h2 := h1
    . left
      addarith [h2]
    . right
      addarith [h2]
  . intro h
    obtain h1 | h1 := h
    . rw [h1] 
      ring
    . rw [h1]
      ring

-- Problem 6b
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h
    have h1 := calc 
      (2*a-5)^2 = 4*(a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 *-1 + 5 := by rel[h]
      _ = 1^2 := by ring
    have h2 : (0:ℤ) ≤1 := by numbers
    obtain ⟨h3, h4⟩ := abs_le_of_sq_le_sq' h1 h2
    have h3 : 2*2 ≤ 2*a := by addarith[h3]
    cancel 2 at h3
    have h4 : 2*a ≤ 2*3 := by addarith[h4]
    cancel 2 at h4
    interval_cases a
    · left; numbers
    · right; numbers
  . intro h
    obtain h1 | h1 := h
    . rw [h1]
      numbers
    . rw [h1]
      numbers