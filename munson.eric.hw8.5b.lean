import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def recursive_sum : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>  2 * n + 1 + (recursive_sum n)

theorem problem5b (n : ℕ) (hn : 1 ≤ n): ∃ j : ℕ, recursive_sum n = j ^ 2 := by
  use n
  induction_from_starting_point n, hn with k hk IH
  · dsimp[recursive_sum]
    numbers
  · dsimp[recursive_sum]
    ring
    rw[IH]
