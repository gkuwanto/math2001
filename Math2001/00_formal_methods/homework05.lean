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
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  dsimp [(· ∣ ·)] at *
  constructor
  . intro h
    obtain ⟨k, hk⟩ := h
    constructor
    .use 9*k; rw [hk]; ring
    .use 7*k; rw [hk]; ring
  . intro h
    obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := h
    use 4*l - 3*k
    have := calc
      63 * (4*l - 3*k) 
        = 252*l - 189*k := by ring
      _ = 28*(9*l) - 27*(7*k) := by ring
      _ = 28*(9*l) - 27*n := by rw [hk]
      _ = 28*n - 27*n := by rw [hl]
      _ = n := by ring
    rw [this]
    
-- Problem 4b
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    have := calc
      k*k = k^2 := by ring
      _ ≤ 6 := by rel [h]
      _ <  9 := by numbers
      _ = 3*3 := by ring 
    rw [← Nat.mul_self_lt_mul_self_iff] at this
    interval_cases k
    . left; ring
    . right; left; ring
    . right; right; ring
  . intro h
    obtain h | h |h := h
    repeat {rw[h]; numbers}

-- Problem 5a
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  . intro a
    intro ha1
    intro ha3
    have h_neg := calc
      a - 2 ≥ 1 - 2 := by addarith[ha1]
      _ = -1 := by ring
    have h_pos := calc
      a - 2 ≤ 3 - 2 := by addarith[ha3]
      _ = 1 := by ring
    have h_sq := sq_le_sq' h_neg h_pos
    calc
      (a-2)^2 ≤ 1^2 := by rel[h_sq]
      _ = 1 := by ring
  . intro y
    intro h
    have ha1 := h 1 (by numbers) (by numbers)
    have ha3 := h 3 (by numbers) (by numbers)
    have h_le := calc
      (y-2)^2 = ((1-y)^2 + (3-y)^2 - 2)/2 := by ring
      _ ≤ (1 + 1 - 2)/2 := by rel[ha1, ha3]
      _ = 0 := by ring
    have h_ge := sq_nonneg (y-2)
    have h_eq := le_antisymm' h_le h_ge
    have h_mul := calc
      (y-2) * (y-2) = (y-2)^2 := by ring
      _ = 0 := by rel[h_eq]
      _ = 0 := by ring
    rw [mul_eq_zero] at h_mul
    obtain h|h := h_mul
    repeat{rw[sub_eq_zero] at h; exact h}

-- Problem 5b
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  . numbers
  . intro y hy
    calc
      y = ((4*y - 3) + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw[hy]
      _ = 3 := by ring

-- Problem 5c
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  . exact Nat.zero_le
  . intro y hy
    obtain h | h := Nat.eq_zero_or_pos y
    . exact h
    . specialize hy 0
      simp at hy
      exact hy  
    
-- Problem 6a

example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  . have hmp' : m ≤ p := (Nat.le_of_dvd hp' hmp)
    obtain h | h := Nat.eq_or_lt_of_le hmp'
    . right; exact h
    . have h1 := H m hm_left h
      contradiction
  
-- Problem 6b
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
    obtain h | h := lt_or_ge a 3
    . have h: a ≤ 2 := by addarith[h]
      obtain hb1 | hb1 := lt_or_ge b 2
      . have hb1: b ≤ 1 := by addarith[hb1]
        have hcsq := calc
          c*c = c^2 := by ring
          _ = a^2 + b^2 := by rw[h_pyth]
          _ ≤ 2^2 + 1^2 := by rel[h, hb1]
          _ = 5 := by ring
          _ < 3*3 := by numbers
        rw [← Nat.mul_self_lt_mul_self_iff] at hcsq
        interval_cases c 
        repeat{interval_cases a;repeat{interval_cases b; repeat{contradiction}}}
      . have hbc := calc
          b*b = b^2 := by ring
          _ < a^2+b^2 := by extra
          _ = c^2 := by rw[h_pyth]
          _ = c*c := by ring
        rw [← Nat.mul_self_lt_mul_self_iff] at hbc
        have hbc: b+1 ≤ c := by addarith[hbc]
        have hcb := calc
          c*c = c^2 := by ring
          _ = a^2 + b^2 := by rw[h_pyth]
          _ ≤ 2^2 + b^2 := by rel[h] 
          _ = b^2 + 2*2 := by ring
          _ ≤ b^2 + 2*b := by rel[hb1]
          _ < b^2 + 2*b +1 := by extra
          _ = (b+1)*(b+1) := by ring
        rw [← Nat.mul_self_lt_mul_self_iff] at hcb
        have hb1:= calc
          b+1 ≤ c := by rel[hbc]
          _ < b+1 := by rel[hcb]
        have h_cont: 1<1 := by addarith[hb1]
        contradiction
    . exact h
    
-- Problem 6c
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

-- Problem 6d
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, hdiv⟩ := h
  obtain h | h := lt_or_eq_of_le hp
  · right
    have h_not_even : ¬Nat.Even p := by
      intro h_even 
      obtain ⟨k, hk⟩ := h_even
      have h2 : 2∣p := by 
        use k
        rw [hk]
      obtain h_cont|h_cont := hdiv 2 h2
      . contradiction
      . rw [h_cont] at h
        have h_cont': 0 < 0 := by addarith[h]
        contradiction
    obtain h_is_even | h_p_is_odd := Nat.even_or_odd p
    . contradiction
    . apply h_p_is_odd
  · left
    rw[h]
