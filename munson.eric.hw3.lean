import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

--4a
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
    have h_t : t < 0 := by addarith [hxt']
    apply h_t

--4b
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1
  use a
  ring

--4c
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  have h2 : p < (p + q) / 2 := by linarith
  have h3 : (p + q) / 2 < q := by linarith
  exact ⟨h2, h3⟩

--5a
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1
  have h : x < x + 1 := by linarith
  have h4 : x < (x + 1) ^ 2 := by nlinarith
  exact h4

--5b
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  intro ht
  rw [ht] at hxt
  apply ne_of_lt hxt
  ring

--5c
example {m a : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hxm⟩ := h
  intro hm
  rw [hm] at hxm
  obtain hle | hgt := le_or_gt x 2
  . have := calc
      5 = 2 * x := by rw[hxm]
      _ ≤ 2 * 2 := by rel [hle]
      _ = 4 := by ring
    contradiction
  . have hr : x ≥ 3 := by addarith [hgt]
    have := calc
      5 = 2 * x := by rw[hxm]
      _ ≥ 2 * 3 := by rel [hr]
      _ = 6 := by ring
    contradiction