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
  dsimp [Surjective] at *
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [hx, hy]

/- 2 points -/
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
/-based on usage of choose in example 8.3.7-/
  dsimp [Surjective] at *
  choose g hg using hf
  use g
  ext x
  rel [hg, x]


/- 2 points -/
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  obtain ⟨h1, h2⟩ := h
  use h2
  apply h1

/- 3 points -/
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp [Inverse] at *
  obtain ⟨hg1f, hfg1⟩ := h1
  obtain ⟨hg2f, hfg2⟩ := h2
  dsimp [id] at *
  funext x
  have heq : (f ∘ g1) x = (f ∘ g2) x := by rw [hfg1, hfg2]
  have hg1x : (f ∘ g1) x = x := by rw [hfg1]
  have hg2x : (f ∘ g2) x = x := by rw [hfg2]
  have heq' : g1 ((f ∘ g1) x) = g1 ((f ∘ g2) x) := by rw [heq]

  have hidk : g1 ((f ∘ g1) x) = (g1 x) := by rw [hg1x]
  have hwe : g1 x = g2 x := by
    calc
      g1 x = g1 ((f ∘ g1) x) := by rw [hidk]
      _ = g1 ((f ∘ g2) x) := by rw [heq']
      _ = (g1 ∘ f ∘ g2) x := by rfl
      _ = (g1 ∘ f) (g2 x) := by rfl
      _ = g2 x := by rw [hg1f]
  rw [hwe]


/- 1 points -/
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective] at *
  push_neg
  use (5, 1)
  use (7, 2)
  simp

/- 1 points -/
theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective] at *
  intro z
  use (z + 1, 0)
  simp

/- 2 points -/
theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp [Surjective] at *
  push_neg
  use -1
  intro h
  have h1: h.fst ^ 2 + h.snd ^ 2 > -1 := by
    calc
      h.fst ^ 2 + h.snd ^ 2 = h.fst ^ 2 + h.snd ^ 2 := by ring
      _ ≥ 0 := by extra
      _ > -1 := by numbers
  apply ne_of_gt h1

/- 3 points -/
theorem problem5c : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp [Injective] at *
  push_neg
  use (0,1,0), (1,-1,1)
  numbers
  simp

/- 3 points -/
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  dsimp [Injective] at *
  intro w z h
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : (w.fst + w.snd) + w.snd = (z.fst + z.snd) + z.snd := by
    calc
      (w.fst + w.snd) + w.snd = w.fst + 2 * w.snd := by ring
      _ = (z.fst + 2 * z.snd) := by rw [h2]
      _ = (z.fst + z.snd) + z.snd := by ring
  rw [h1] at h2'
  simp at h2'
  have h3 : w.fst = z.fst := by
    calc
      w.fst = z.fst + z.snd - w.snd := by addarith [h1]
      _ = z.fst + z.snd - z.snd := by rw [h2']
      _ = z.fst := by ring
  constructor
  exact h3
  exact h2'
