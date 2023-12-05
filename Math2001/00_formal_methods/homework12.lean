import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Theory.InjectiveSurjective
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
import Library.Tactic.Product

set_option push_neg.use_distrib true
open Function

/- 3 points -/
theorem problem4a {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
    dsimp [Surjective]
    intro b
    specialize hg b
    obtain ⟨ga, hga⟩ := hg
    specialize hf ga
    obtain ⟨xa, hxa⟩ := hf
    use xa
    rw [←hga, ←hxa]

/- 2 points -/
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Function.comp]
  dsimp [Surjective] at hf
  choose g hf using hf
  use g
  ext x
  specialize hf x
  apply hf

/- 2 points -/
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  constructor
  . apply h.right
  . apply h.left

/- 3 points -/
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  have h_not : ¬ g1 ≠ g2 := by
    intro h_ne
    dsimp [Inverse] at *
    have h_left : g1 ∘ f = g2 ∘ f := by
      ext x
      rw [h1.left, h2.left]
    have h_right : f ∘ g1 = f ∘ g2 := by
      ext x
      rw [h1.right, h2.right]
    have h_eq : g1 = g2 := by
      ext x
      have ha : (g1 ∘ (f ∘ g1)) x = (g1 ∘ (f ∘ g2)) x:= by
        rw [h_right]
      rw [h1.right] at ha
      simp at ha
      calc
        g1 x = ((g1 ∘ f) ∘ g2) x:= by apply ha
        _ = (id ∘ g2) x := by rw [h1.left]
        _ = g2 x:= by extra
    apply h_ne h_eq
  push_neg at h_not
  apply h_not

/- 1 points -/
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (4, 2)
  use (2, 1)
  simp

/- 1 points -/
theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intro b
  use (b + 1, 0)
  simp

/- 2 points -/

theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro a
  apply ne_of_gt
  have : a.fst^2 + a.snd^2 ≥ 0 :=
    calc
      a.fst^2 + a.snd^2 ≥  a.snd^2 := by extra
      _ ≥ 0 := by extra
  have : a.fst^2 + a.snd^2 > -1 :=
    calc
      a.fst^2 + a.snd^2 ≥ 0 := this
      _ > -1 := by numbers
  apply this


/- 3 points -/
theorem problem5c : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp [Injective]
  push_neg
  use (7,4,2)
  use (6,6,1)
  numbers
  simp

/- 3 points -/
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  dsimp [Injective]
  intro a1 a2
  intro h_eq

  obtain ⟨h, h', hy⟩ := h_eq
  have hsnd : a1.snd = a2.snd := by calc
    a1.snd = a1.fst + 2*a1.snd - (a1.fst + a1.snd):= by ring
    _ = (a2.fst + 2 * a2.snd)  - (a1.fst + a1.snd) := by rw [h']
    _ = (a2.fst + 2 * a2.snd) - (a2.fst + a2.snd) := by rw [h]
    _ = a2.snd := by ring
  have hfst : a1.fst = a2.fst := calc
    a1.fst = a1.fst + a1.snd - a1.snd := by ring
    _ = a2.fst + a2.snd - a1.snd := by rw [h]
    _ = a2.fst + a2.snd - a2.snd := by rw [hsnd]
    _ = a2.fst := by ring
  constructor
  . apply hfst
  . apply hsnd
