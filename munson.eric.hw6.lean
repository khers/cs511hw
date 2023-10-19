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
import Library.Tactic.Us

-- 4a
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    use x
    have hpq : P x ↔ Q x := h x
    rw [hpq] at hx
    exact hx
  · intro h
    obtain ⟨x, hx⟩ := h
    use x
    have hpq : Q x ↔ P x := by rw [h x]
    rw [hpq] at hx
    exact hx

-- 4b
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := h
    use y
    use x
    exact hxy
  · intro h
    obtain ⟨y, x, hxy⟩ := h
    use x
    use y
    exact hxy

-- 4c
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h
    intro y
    intro x
    exact h x y
  · intro h
    intro x
    intro y
    exact h y x

-- 4d
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.left
    use x
    constructor
    · exact hx
    · exact h.right
  · intro h
    obtain ⟨x, hx, hq⟩ := h
    constructor
    · use x
      exact hx
    · exact hq

-- 5a
example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by 
  by_cases h : Tribalanced 1
  · use 1
    constructor
    · exact h
    · intro h1
      dsimp [Tribalanced] at h1
      specialize h1 1
      simp at h1
      numbers at h1
  · use 0
    constructor
    · dsimp [Tribalanced]
      simp
      numbers
    · intro h0
      simp at h0
      exact h h0

-- 5b
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  · exact superpowered_one
  · intro h1
    dsimp [Superpowered] at h1
    specialize h1 5
    numbers at h1
    have : ¬ Prime 4294967297 := by
      apply not_prime 641 6700417
      · numbers
      · numbers
      · numbers
    contradiction