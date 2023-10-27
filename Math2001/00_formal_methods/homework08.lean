import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option linter.unusedVariables false

namespace Nat

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- Problemn 4a
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k hk
  . use 0
    simp
  . obtain ⟨x, hx⟩ := hk
    obtain ⟨y, hy⟩ := h
    use (a*x + b^k*y)
    calc
    a^(k+1)-b^(k+1)
      = a*(a^k-b^k) + b^k*(a-b) := by ring
    _ = a*(d*x) + b^k*(d*y) := by rw [hx, hy]
    _ = d*(a*x + b^k*y) := by ring

-- Problem 4a
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
    2^(k+1)
      = 2*2^k := by ring
    _ ≥ 2*k^2 := by rel [IH]
    _ = k^2 + k * k := by ring
    _ ≥ k^2 + 4*k := by rel [hk]
    _ = k^2 + 2*k + 2*k := by ring
    _ ≥ k^2 + 2*k + 2* 4 := by rel [hk]
    _ = (k+1)^2 + 7 := by ring
    _ ≥ (k+1)^2 := by extra

-- Problem 4c
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k hk
  . simp
  . have ha : 0 ≤ 1+a := by addarith [ha]
    calc
      (1 + a)^(k+1)
        = (1 + a) * ((1 + a)^k) := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [hk]
      _ = 1 + (k+1) * a + k * a^2 := by ring
      _ ≥ 1 + (k+1) * a := by extra

-- Problem 4d
example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . -- base case
    numbers
  . -- inductive step
    calc
      (3:ℤ) ^ (k + 1) = 3 ^ k * 2 + 3^k  := by ring
      _ ≥ 3^k*2 := by extra
      _ ≥ (2 ^ k + 100)*2 := by rel[IH]
      _ = 2^(k+1) + 100 + 100 := by ring
      _ ≥ 2^(k+1) + 100 := by extra

-- Problem 5
def sum_odd : ℕ → ℕ
  | 0 => 0
  | (n + 1) => (2*n + 1) + sum_odd n
theorem sum_of_odd_is_perfect_square (n : ℕ) : ∃j : ℕ, sum_odd n = j^2 := by
  use n
  simple_induction n with k hk
  . simp
  . simp [sum_odd]
    rw [hk]
    ring
