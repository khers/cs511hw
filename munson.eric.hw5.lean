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

namespace Nat

-- 4a
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    constructor
    · use 9 * k
      calc
        n = 63 * k := by apply hk
        _ = 7 * (9 * k) := by ring
    · use 7 * k
      calc
        n = 63 * k := by apply hk
        _ = 9 * (7 * k) := by ring
  · intro h
    dsimp [(.∣.)] at *
    obtain ⟨h1,h2⟩ := h
    obtain ⟨k1,hk1⟩ := h1
    obtain ⟨k2,hk2⟩ := h2
    use 4 * k2 - 3 * k1
    calc
      n = 28 * n - 27 * n := by ring
      _ = 4 * 7 * n - 3 * 9 * n := by ring
      _ = 4 * 7 * n - 3 * 9 * (7 * k1) := by rw [hk1]
      _ = 4 * 7 * (9 * k2) - 3 * 9 * (7 * k1) := by rw [hk2]
      _ = 63 * (4 * k2 - 3 * k1) := by ring


-- 4b
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    have h1 := le_or_gt k 0
    obtain l | r := h1
    · left
      simp at l
      apply l
    · right
      have h2 := le_or_gt k 1
      obtain l | r2 := h2
      · left
        have h3 : k ≥ 1 := by addarith [r]
        apply le_antisymm l h3
      · right
        have h3 : k ≥ 2 := by addarith [r2]
        have h4 : ¬(k ≥ 3) := by
          intro h5
          have h6 : 3 * 2 ≥ 3 * k :=
          calc
            3 * 2 = 6 := by ring
            _ ≥ k ^ 2 := by rel[h]
            _ = k * k := by ring
            _ ≥ 3 * k := by rel [h5]
          cancel 3 at h6
          have h7 : k = 2 := le_antisymm h6 h3
          addarith [h5,h7]
        simp at h4
        addarith [h3,h4]
  · intro h
    obtain h1 | h2 | h3 := h
    · rw [h1]
      numbers
    · rw [h2]
      numbers
    · rw [h3]
      numbers


-- 5a
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intros a h1 h2
    have h1m2 : -1 ≤ a - 2 := by addarith [h1]
    have h2m2 : a - 2 ≤ 1 := by addarith [h2]
    have sq : (a - 2) ^ 2 ≤ 1 ^ 2 := by apply sq_le_sq' h1m2 h2m2
    numbers at sq
    exact sq
  · intros i h
    have i1 := h 1
    have i3 := h 3
    have fi1 := by
      apply i1
      numbers
      numbers
    have fi3 := by
      apply i3
      numbers
      numbers
    have le0 : (i - 2) ^ 2 ≤ 0 := by
      calc
        (i - 2) ^ 2 = ((1 - i) ^ 2 + (3 - i) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + (3 - i) ^ 2 - 2) / 2 := by rel [fi1]
        _ ≤ (1 + 1 - 2) / 2 := by rel [fi3]
        _ = 0:= by numbers
    have ge0 : (i - 2) ^ 2 ≥ 0 := by extra
    have eq0 : (i - 2) ^ 2 = 0 := by apply le_antisymm le0 ge0
    have factor : (i - 2) * (i - 2) = 0 := by
      calc
        (i - 2) * (i - 2) = (i - 2) ^ 2 := by ring
        _ = 0 := by rw [eq0]
    have h := eq_zero_or_eq_zero_of_mul_eq_zero factor
    cases h with
    | inl l => addarith [l]
    | inr r => addarith [r]

-- 5b
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  simp
  constructor
  · numbers
  · intros y hy
    have h : 4 * y = 4 * 3 :=
      calc
        4 * y = 4 * y - 3 + 3 := by ring
        _ = 9 + 3 := by rw [hy]
        _ = 4 * 3 := by numbers
    cancel 4 at h


-- 5c
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · simp
  · simp
    intros x hx
    have ge0 : x ≥ 0 := by extra
    have le0 := by apply hx 0
    apply le_antisymm le0 ge0

-- 6a
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
  · have mlep : m ≤ p := by apply Nat.le_of_dvd hp' hmp
    have mlp_or_mep : m = p ∨ m < p := eq_or_lt_of_le mlep
    cases mlp_or_mep with
    | inl l =>
      right
      apply l
    | inr r =>
      have premise := H m
      have contra : ¬m ∣ p := by
        apply premise
        apply hm_left
        apply r
      contradiction

-- 6b



-- 6c
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  cancel n at h

-- 6d
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at *
  obtain ⟨leq2, mdivp1⟩ := h
  obtain le2 | ge3 := le_or_succ_le p 2
  · left
    apply le_antisymm le2 leq2
  · right
    have evenOrOddp := even_or_odd p
    dsimp [Even] at evenOrOddp
    cases evenOrOddp with
    | inr pOdd =>
      apply pOdd
    | inl pEven =>
      have h2_div_p : 2 ∣ p := by apply pEven
      have notmdivp1 := mdivp1 2
      have contra : 2 = p := by
        simp at notmdivp1
        apply notmdivp1
        apply h2_div_p
      have plt3 : p < 3 := by
        calc
          p = 2 := by rw [contra]
          _ < 3 := by numbers
      have contra2 : ¬p < 3 := by apply not_lt_of_ge ge3
      contradiction