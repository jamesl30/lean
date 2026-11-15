import Mathlib

/-!
# The irrationality criterion (Lemma 1 of the report)

If `ξ = a / b` is rational with `b ≥ 1`, and `p`, `q` are integers with `q * ξ - p > 0`,
then `q * ξ - p ≥ 1 / b`. So integers `p_n`, `q_n` with `0 < q_n ξ - p_n → 0` cannot exist for a
rational `ξ`.
-/

namespace Zeta3

/-- Lemma 1: a positive value of an integer linear form in `1` and `a / b` is at least `1 / b`. -/
theorem criterion (a p q : ℤ) (b : ℕ) (hb : 1 ≤ b)
    (hpos : 0 < (q : ℝ) * ((a : ℝ) / b) - p) :
    (1 : ℝ) / b ≤ (q : ℝ) * ((a : ℝ) / b) - p := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have key : (q : ℝ) * ((a : ℝ) / b) - p = ((q * a - p * b : ℤ) : ℝ) / b := by
    push_cast
    field_simp
  rw [key] at hpos ⊢
  have hnum : (0 : ℝ) < ((q * a - p * b : ℤ) : ℝ) := by
    by_contra h
    push_neg at h
    exact absurd hpos (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg h hb'.le))
  have hint : (1 : ℤ) ≤ q * a - p * b := by
    have : (0 : ℤ) < q * a - p * b := by exact_mod_cast hnum
    omega
  have hreal : (1 : ℝ) ≤ ((q * a - p * b : ℤ) : ℝ) := by exact_mod_cast hint
  exact div_le_div_of_nonneg_right hreal hb'.le

end Zeta3
