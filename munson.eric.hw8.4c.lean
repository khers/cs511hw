import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simp
  simple_induction n with k IH
  · -- base case
    have h0 : 1 + 0 * a ≤ (1 + a) ^ 0 := by
      calc
        1 + 0 * a = 1 := by ring
        _ ≤ 1 := by numbers
    apply h0
  · -- inductive step
    have ha : 1 + a ≥ 0 := by addarith[ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
      _ ≥ (1 + k * a) * (1 + a) := by rel[IH]
      _ = 1 + a + k * a + k * a ^ 2:= by ring
      _ = 1 + (k + 1) * a + k * a ^ 2:= by ring
      _ ≥ 1 + (k + 1) * a := by extra

