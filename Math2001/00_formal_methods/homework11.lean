import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Function


/- 2 points -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use fun x => x
  simp [Surjective]
  use 1
  intro x_odd
  intro h
  obtain h1 | h1 := le_or_gt x_odd 0
  . have := calc
      1 = 2 * x_odd := by rw[h]
      _ ≤ 2 * 0 := by rel [h1]
      _ = 0 := by ring
    contradiction
  . have hr : x_odd ≥ 1 := by addarith [h1]
    have := calc
      1 = 2 * x_odd := by rw[h]
      _ ≥ 2 * 1 := by rel [hr]
      _ = 2 := by ring
    contradiction

/- 2 points -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  simp
  dsimp [Surjective]
  push_neg
  use 1
  numbers
  simp

/- 3 points -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intro x y h
  have h1 : ¬ x ≠ y := by
    intro h_neg
    obtain h1 | h1 := lt_or_gt_of_ne h_neg
    . have := hf x y h1
      rw[h] at this
      linarith
    . have := hf y x h1
      rw[h] at this
      linarith
  push_neg at h1
  apply h1

/- 3 points -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro n
  simple_induction n with n hn
  . use x0
    rw[h0]
  . obtain ⟨x, hx⟩ := hn
    use i x
    rw[hi, hx]

/- 2 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  dsimp[Bijective]
  constructor
  . dsimp[Injective]
    intro x y h_injective
    simp at h_injective
    apply h_injective
  . dsimp[Surjective]
    intro y
    use (4 - y) / 3
    ring

/- 2 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use 0
  use -2
  simp
  ring

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x-1)/5

/- 3 points -/
theorem problem5c : Inverse u v := by
  dsimp [Inverse]
  constructor
  . dsimp [Function.comp]
    funext x
    simp [u, v]
    ring
  . dsimp [Function.comp]
    funext x
    simp [u, v]
    ring

/- 3 points -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective]
  intro x y h
  have h1 : f x = f y := by
    apply hg
    rw[h]
  apply hf
  apply h1
