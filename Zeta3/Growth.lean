import Mathlib

/-!
# The growth step (Lemma 8 of the report)

If a nonnegative, nondecreasing real sequence `u` satisfies Apéry's recurrence (A)

  `(n+1)³ u (n+1) - (34n³+51n²+27n+5) u n + n³ u (n-1) = 0`   (n ≥ 1),

then `u (n+1) ≥ 30 u n` for every `n ≥ 15`, and hence `u n ≥ 30^(n-15) u 15` for `n ≥ 15`.

Proof: `(n+1)³ u (n+1) = bₙ u n - n³ u (n-1) ≥ (bₙ - n³) u n`, and
`33n³+51n²+27n+5 - 30(n+1)³ = 3n³ - 39n² - 63n - 25 ≥ 0` for `n ≥ 15`
(with `n = 15 + y` it is `3y³ + 96y² + 792y + 380`).
-/

namespace Zeta3

/-- Lemma 8, the growth step: a nonnegative nondecreasing solution of Apéry's recurrence (A)
satisfies `u (n+1) ≥ 30 u n` for `n ≥ 15`. -/
theorem growth_step (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 3 * u (n + 1)
        - (34 * (n : ℝ) ^ 3 + 51 * (n : ℝ) ^ 2 + 27 * (n : ℝ) + 5) * u n
        + (n : ℝ) ^ 3 * u (n - 1) = 0)
    (hpos : ∀ n, 0 ≤ u n) (hmono : ∀ n : ℕ, 1 ≤ n → u (n - 1) ≤ u n)
    (n : ℕ) (hn : 15 ≤ n) : 30 * u n ≤ u (n + 1) := by
  have h := hu n (by omega)
  have hm := hmono n (by omega)
  have hx : (15 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := (n : ℝ) with hxdef
  have hy : 0 ≤ x - 15 := by linarith
  have hp : 0 ≤ 3 * x ^ 3 - 39 * x ^ 2 - 63 * x - 25 := by
    have e : 3 * x ^ 3 - 39 * x ^ 2 - 63 * x - 25
        = 3 * (x - 15) ^ 3 + 96 * (x - 15) ^ 2 + 792 * (x - 15) + 380 := by ring
    rw [e]
    positivity
  have key : 0 ≤ (x + 1) ^ 3 * (u (n + 1) - 30 * u n) := by
    have e : (x + 1) ^ 3 * (u (n + 1) - 30 * u n)
        = x ^ 3 * (u n - u (n - 1)) + (3 * x ^ 3 - 39 * x ^ 2 - 63 * x - 25) * u n := by
      linear_combination h
    rw [e]
    have hx0 : 0 ≤ x := by linarith
    exact add_nonneg (mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.2 hm))
      (mul_nonneg hp (hpos n))
  have hc : 0 < (x + 1) ^ 3 := by positivity
  have := (mul_nonneg_iff_of_pos_left hc).1 key
  linarith

/-- Iterating the growth step: `u n ≥ 30^(n-15) u 15` for `n ≥ 15`. -/
theorem growth_pow (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 3 * u (n + 1)
        - (34 * (n : ℝ) ^ 3 + 51 * (n : ℝ) ^ 2 + 27 * (n : ℝ) + 5) * u n
        + (n : ℝ) ^ 3 * u (n - 1) = 0)
    (hpos : ∀ n, 0 ≤ u n) (hmono : ∀ n : ℕ, 1 ≤ n → u (n - 1) ≤ u n)
    (n : ℕ) (hn : 15 ≤ n) : (30 : ℝ) ^ (n - 15) * u 15 ≤ u n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hs := growth_step u hu hpos hmono m hm
    have e : m + 1 - 15 = (m - 15) + 1 := by omega
    rw [e, pow_succ]
    nlinarith
