import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- 3a

example {p q r : Prop} (h: (p ∧ q) → r) : p → (q → r) := by
  intros h_p h_q
  apply h
  exact ⟨h_p, h_q⟩

-- 3b P → (Q → R) ⊢ (P → Q) → (P → R)

example {p q r : Prop} (h: p → (q → r)) : (p → q) → (p → r) := by
  intros h_pq h_p
  apply h
  exact h_p
  apply h_pq
  exact h_p

-- 3c (P ∧ ¬ Q) → R, ¬R, P ⊢ Q

example {p q r : Prop} (h1: (p ∧ ¬q) → r) (h2: ¬r) (h3: p) : q := by
  by_cases h_q : q
  exact h_q
  have h_pnq : p ∧¬q := And.intro h3 h_q
  have h_r : r := by apply h1 h_pnq
  contradiction

-- 4a

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc
    a = 2 * b + 5 := by exact h1
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

-- 4b

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

-- 4c

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  calc
    a = (a - 5 * b) + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = -6 + 5 * (b + 2) := by ring
    _ = -6 + 5 * 3 := by rw [h2]
    _ = 9 := by ring