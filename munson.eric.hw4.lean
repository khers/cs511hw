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

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- 4a
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

-- 4b
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + 3 * b + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 4 * a * b + 2 * a + 6 * b + 3 := by ring
    _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

-- 4c
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨r, hr⟩ := hn
  use 2 * r ^ 2 + 2 * r - 3
  calc
    n ^ 2 + 2 * n - 5 = (r + r)^2 + 2 * (r + r) - 5 := by rw [hr]
    _ = 2 * (2 * r ^ 2 + 2 * r - 3) + 1 := by ring

-- 4d
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  dsimp [Even, Odd] at *
  obtain ha | ha := Int.even_or_odd a
  obtain hb | hb := Int.even_or_odd b
  . left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x - y
    simp [hx, hy]
    ring
  . obtain hc | hc := Int.even_or_odd c
    . right
      left
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hc
      use x + y
      simp [hx, hy]
      ring
    . right
      right
      obtain ⟨x, hx⟩ := hb
      obtain ⟨y, hy⟩ := hc
      use x - y
      simp [hx, hy]
      ring
  . obtain hb | hb := Int.even_or_odd b
    . obtain hc | hc := Int.even_or_odd c
      . right
        right
        obtain ⟨x, hx⟩ := hb
        obtain ⟨y, hy⟩ := hc
        use x - y
        simp [hx, hy]
        ring
      . right
        left
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hc
        use x + y + 1
        simp [hx, hy]
        ring
    . left
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      use x - y
      simp [hx, hy]
      ring

-- 5a
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain hl | hr := h ((a + b) / 2)
  · calc
    b = 2 * ((a + b) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [hl]
    _ = a := by ring
  . calc
    a = 2 * ((a + b) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [hr]
    _ = b := by ring

-- 5b
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y
  intro h
  have h1 := calc
    (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by extra
    _ = 2 * (x^2 + y^2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ (3)^2 := by numbers
  have h2 : (0:ℝ) ≤ 3 := by numbers
  exact And.left (abs_le_of_sq_le_sq' h1 h2)

-- 5c
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  obtain ⟨x, hx⟩ := hn 3 (by numbers) (by numbers)
  obtain ⟨y, hy⟩ := hn 5 (by numbers) (by numbers)
  use 2 * x - 3 * y
  calc
    n = 10 * n - 9 * n := by ring
    _ = 10 * (3 * x) - 9 * (5 * y) :=  by nth_rw 1 [hx]; rw[hy]
    _ = 15 * (2 * x - 3 * y) := by ring

-- 5d



-- 6a
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have h1 := calc
      (x + 3) * (x - 2) =  x ^ 2 + x - 6 := by ring
      _ = 0 := by rw[h]
    rw [mul_eq_zero] at h1
    obtain h2 | h2 := h1
    . left
      addarith [h2]
    . right
      addarith [h2]
  . intro h3
    obtain h4 | h4 := h3
    . rw [h4]
      ring
    . rw [h4]
      ring

-- 6b


