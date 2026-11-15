import Mathlib

/-!
# The coefficients of Ball's rational function

Ball's rational function at level `n` is
`T_n(t) = n!² (2t+n) ∏_{r=1}^{n} (t−r)(t+n+r) / ∏_{h=0}^{n} (t+h)⁴
        = ∑_{j=0}^{n} ∑_{s=1}^{4} A_{s,j} / (t+j)^s`.
For `0 ≤ j ≤ n` the coefficient `A_{s,j}` is the coefficient of `x^{4−s}` in the Taylor expansion
at `x = 0` of `x⁴ T_n(−j + x)`, i.e.
`n!² (n − 2j + 2x) ∏_{r=1}^{n} (x − j − r)(x − j + n + r) ∏_{0 ≤ h ≤ n, h ≠ j} (x + h − j)^{−4}`.
We define this product as a formal power series over `ℚ` (`ballSeries`), with the inverses taken
in `PowerSeries ℚ` (each constant term `h − j` is nonzero), and then `ballA`, `ballU`, `ballV`.

Proved here: all `A_{s,j}` for `n = 1, 2, 3`, `ballU 1 = 10`, `ballV 1 = 12`,
`ballU 2 = 146`, `ballV 2 = 351/2`, `ballU 3 = 2890`, `ballV 3 = 62531/18` (so `U_n = 2u_n`,
`V_n = 2v_n` for `n ≤ 3`), the closed product for the top coefficient `A_{4,j}` (`ballA_four`),
and the symmetry `A_{s,n−j} = (−1)^{s+1} A_{s,j}` (`ballA_symm`, from `ballSeries_symm`).

Not formalised here: that these Taylor coefficients are the partial-fraction coefficients of
`T_n` (a standard fact), and anything about the series `F_n`.

How to compute: `c4 f` is the tuple of the first four coefficients of `f`; it is multiplicative
for the truncated product `m4` (`c4_mul`), and `c4` of every factor is explicit (`c4_C`, `c4_lin`,
`c4_inv_lin`; the last holds for every `a`, also `a = 0`, because `X⁻¹ = 0` and `0⁻¹ = 0`).
-/

-- CLAIMED: Zeta3.BallSer.ballA_one, Zeta3.BallSer.ballU_one, Zeta3.BallSer.ballV_one, Zeta3.BallSer.ballA_two, Zeta3.BallSer.ballU_two, Zeta3.BallSer.ballV_two, Zeta3.BallSer.ballU_three, Zeta3.BallSer.ballV_three, Zeta3.BallSer.ballA_four, Zeta3.BallSer.ballSeries_symm, Zeta3.BallSer.ballA_symm, Zeta3.BallSer.isDInt_mul, Zeta3.BallSer.isDInt_pow, Zeta3.BallSer.isDInt_prod, Zeta3.BallSer.isDInt_C, Zeta3.BallSer.isDInt_lin2, Zeta3.BallSer.isDInt_C_mul_inv_lin

set_option autoImplicit false

namespace Zeta3.BallSer
open Finset PowerSeries

/-- The linear power series `a + x`. -/
noncomputable def lin (a : ℚ) : PowerSeries ℚ := C a + X

/-- `x⁴ T_n(−j + x)` as a formal power series in `x`:
`n!² (n − 2j + 2x) ∏_{r=1}^{n} (x − j − r)(x − j + n + r) ∏_{0 ≤ h ≤ n, h ≠ j} (x + h − j)^{−4}`. -/
noncomputable def ballSeries (n j : ℕ) : PowerSeries ℚ :=
  C ((n.factorial : ℚ) ^ 2) * (C ((n : ℚ) - 2 * j) + C 2 * X) *
    (∏ r ∈ range n, lin (-(j : ℚ) - (r + 1)) * lin ((n : ℚ) - j + (r + 1))) *
    ∏ h ∈ (range (n + 1)).erase j, ((lin ((h : ℚ) - j))⁻¹) ^ 4

/-- `A_{s,j}`: the coefficient of `x^{4−s}` in `x⁴ T_n(−j + x)` (meant for `1 ≤ s ≤ 4`, `j ≤ n`). -/
noncomputable def ballA (n s j : ℕ) : ℚ := coeff (4 - s) (ballSeries n j)

/-- The harmonic number `H_j^{(s)} = ∑_{k=1}^{j} 1/k^s`. -/
def harm (s j : ℕ) : ℚ := ∑ k ∈ Icc 1 j, 1 / (k : ℚ) ^ s

/-- `U_n = ∑_j A_{3,j}`. -/
noncomputable def ballU (n : ℕ) : ℚ := ∑ j ∈ range (n + 1), ballA n 3 j

/-- `V_n = ∑_j ∑_s A_{s,j} H_j^{(s)}`. -/
noncomputable def ballV (n : ℕ) : ℚ :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, ballA n s j * harm s j

example : harm 3 0 = 0 := by simp [harm]
example : harm 3 2 = 9 / 8 := by
  rw [harm, show Icc 1 2 = {1, 2} by decide]; norm_num

/-! ### Computing the first four coefficients -/

/-- The first four coefficients. -/
noncomputable def c4 (f : PowerSeries ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (coeff 0 f, coeff 1 f, coeff 2 f, coeff 3 f)

/-- The product truncated after `x³`. -/
def m4 (a b : ℚ × ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (a.1 * b.1, a.1 * b.2.1 + a.2.1 * b.1, a.1 * b.2.2.1 + a.2.1 * b.2.1 + a.2.2.1 * b.1,
    a.1 * b.2.2.2 + a.2.1 * b.2.2.1 + a.2.2.1 * b.2.1 + a.2.2.2 * b.1)

theorem c4_mul (f g : PowerSeries ℚ) : c4 (f * g) = m4 (c4 f) (c4 g) := by
  simp only [c4, m4, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem c4_C (a : ℚ) : c4 (C a) = (a, 0, 0, 0) := by
  simp [c4, coeff_C]

theorem c4_lin (a : ℚ) : c4 (lin a) = (a, 1, 0, 0) := by
  simp [c4, lin, coeff_X]

theorem c4_lin2 (a b : ℚ) : c4 (C a + C b * X) = (a, b, 0, 0) := by
  simp [c4, coeff_C]

theorem c4_one : c4 (1 : PowerSeries ℚ) = (1, 0, 0, 0) := by
  simp [c4, coeff_one]

/-- The inverse of `a + x` is `∑ (−1)^i x^i / a^{i+1}` (for `a ≠ 0`). -/
theorem lin_mul_geom (a : ℚ) (ha : a ≠ 0) :
    lin a * mk (fun i => (-1) ^ i / a ^ (i + 1)) = 1 := by
  ext i
  rcases i with _ | k
  · simp [lin, add_mul, ha]
  · simp only [lin, add_mul, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_one]
    simp only [Nat.succ_ne_zero, ite_false]
    field_simp
    ring

theorem inv_lin (a : ℚ) (ha : a ≠ 0) :
    (lin a)⁻¹ = mk (fun i => (-1) ^ i / a ^ (i + 1)) := by
  have h : constantCoeff (lin a) ≠ 0 := by simp [lin, ha]
  have h1 := lin_mul_geom a ha
  calc (lin a)⁻¹ = (lin a)⁻¹ * (lin a * mk (fun i => (-1) ^ i / a ^ (i + 1))) := by
        rw [h1, mul_one]
    _ = mk (fun i => (-1) ^ i / a ^ (i + 1)) := by
        rw [← mul_assoc, PowerSeries.inv_mul_cancel _ h, one_mul]

theorem c4_inv_lin (a : ℚ) : c4 (lin a)⁻¹ = (a⁻¹, -(a ^ 2)⁻¹, (a ^ 3)⁻¹, -(a ^ 4)⁻¹) := by
  by_cases ha : a = 0
  · subst ha
    have : (lin 0)⁻¹ = 0 := by
      rw [PowerSeries.inv_eq_zero]; simp [lin]
    simp [this, c4]
  · rw [inv_lin a ha]
    simp only [c4, coeff_mk]
    simp only [Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring, by ring⟩

theorem c4_pow_four (f : PowerSeries ℚ) : c4 (f ^ 4) = m4 (m4 (m4 (c4 f) (c4 f)) (c4 f)) (c4 f) := by
  simp only [pow_succ, pow_zero, one_mul, c4_mul]

theorem ballA_four_eq (n j : ℕ) : ballA n 4 j = (c4 (ballSeries n j)).1 := rfl
theorem ballA_three_eq (n j : ℕ) : ballA n 3 j = (c4 (ballSeries n j)).2.1 := rfl
theorem ballA_two_eq (n j : ℕ) : ballA n 2 j = (c4 (ballSeries n j)).2.2.1 := rfl
theorem ballA_one_eq (n j : ℕ) : ballA n 1 j = (c4 (ballSeries n j)).2.2.2 := rfl

/-! ### Small values -/

theorem c4_ball_1_0 : c4 (ballSeries 1 0) = (-2, 5, -5, 0) := by
  rw [ballSeries, show (range 2).erase 0 = {1} by decide]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.prod_singleton, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4]

theorem c4_ball_1_1 : c4 (ballSeries 1 1) = (2, 5, 5, 0) := by
  rw [ballSeries, show (range 2).erase 1 = {0} by decide]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.prod_singleton, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4]

theorem c4_ball_2_0 : c4 (ballSeries 2 0) = (12, -71, 451 / 2, -524) := by
  rw [ballSeries, show (range 3).erase 0 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4]

theorem c4_ball_2_1 : c4 (ballSeries 2 1) = (0, 288, 0, 1048) := by
  rw [ballSeries, show (range 3).erase 1 = {0, 2} by decide, Finset.prod_pair (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4]

theorem c4_ball_2_2 : c4 (ballSeries 2 2) = (-12, -71, -451 / 2, -524) := by
  rw [ballSeries, show (range 3).erase 2 = {0, 1} by decide, Finset.prod_pair (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4]

/-- All eight coefficients for `n = 1`: `T_1(t) = (−2/t⁴ + 5/t³ − 5/t²) + (2/(t+1)⁴ + 5/(t+1)³ + 5/(t+1)²)`. -/
theorem ballA_one :
    ballA 1 4 0 = -2 ∧ ballA 1 3 0 = 5 ∧ ballA 1 2 0 = -5 ∧ ballA 1 1 0 = 0 ∧
    ballA 1 4 1 = 2 ∧ ballA 1 3 1 = 5 ∧ ballA 1 2 1 = 5 ∧ ballA 1 1 1 = 0 := by
  simp only [ballA_four_eq, ballA_three_eq, ballA_two_eq, ballA_one_eq, c4_ball_1_0, c4_ball_1_1]
  norm_num

/-- All twelve coefficients for `n = 2`. -/
theorem ballA_two :
    ballA 2 4 0 = 12 ∧ ballA 2 3 0 = -71 ∧ ballA 2 2 0 = 451 / 2 ∧ ballA 2 1 0 = -524 ∧
    ballA 2 4 1 = 0 ∧ ballA 2 3 1 = 288 ∧ ballA 2 2 1 = 0 ∧ ballA 2 1 1 = 1048 ∧
    ballA 2 4 2 = -12 ∧ ballA 2 3 2 = -71 ∧ ballA 2 2 2 = -451 / 2 ∧ ballA 2 1 2 = -524 := by
  simp only [ballA_four_eq, ballA_three_eq, ballA_two_eq, ballA_one_eq, c4_ball_2_0, c4_ball_2_1,
    c4_ball_2_2]
  norm_num

theorem harm_zero (s : ℕ) : harm s 0 = 0 := by simp [harm]
theorem harm_one (s : ℕ) : harm s 1 = 1 := by simp [harm]
theorem harm_two (s : ℕ) : harm s 2 = 1 + 1 / 2 ^ s := by
  rw [harm, show Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]; norm_num

theorem sum_Icc_one_four (f : ℕ → ℚ) : ∑ s ∈ Icc 1 4, f s = f 1 + f 2 + f 3 + f 4 := by
  rw [show Icc 1 4 = {1, 2, 3, 4} by decide]
  simp [Finset.sum_insert]
  ring

theorem ballU_one : ballU 1 = 10 := by
  simp only [ballU, Finset.sum_range_succ, Finset.sum_range_zero, ballA_three_eq, c4_ball_1_0,
    c4_ball_1_1]
  norm_num

theorem ballV_one : ballV 1 = 12 := by
  simp only [ballV, Finset.sum_range_succ, Finset.sum_range_zero, sum_Icc_one_four,
    ballA_four_eq, ballA_three_eq, ballA_two_eq, ballA_one_eq, c4_ball_1_0, c4_ball_1_1,
    harm_zero, harm_one]
  norm_num

theorem ballU_two : ballU 2 = 146 := by
  simp only [ballU, Finset.sum_range_succ, Finset.sum_range_zero, ballA_three_eq, c4_ball_2_0,
    c4_ball_2_1, c4_ball_2_2]
  norm_num

theorem ballV_two : ballV 2 = 351 / 2 := by
  simp only [ballV, Finset.sum_range_succ, Finset.sum_range_zero, sum_Icc_one_four,
    ballA_four_eq, ballA_three_eq, ballA_two_eq, ballA_one_eq, c4_ball_2_0, c4_ball_2_1,
    c4_ball_2_2, harm_zero, harm_one, harm_two]
  norm_num

theorem c4_ball_3_0 : c4 (ballSeries 3 0) = (-60, 473, -5909 / 3, 23355 / 4) := by
  rw [ballSeries, show (range 4).erase 0 = {1, 2, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4, Nat.factorial]

theorem c4_ball_3_1 : c4 (ballSeries 3 1) = (-3240, 972, -14427 / 2, -23355 / 4) := by
  rw [ballSeries, show (range 4).erase 1 = {0, 2, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4, Nat.factorial]

theorem c4_ball_3_2 : c4 (ballSeries 3 2) = (3240, 972, 14427 / 2, -23355 / 4) := by
  rw [ballSeries, show (range 4).erase 2 = {0, 1, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4, Nat.factorial]

theorem c4_ball_3_3 : c4 (ballSeries 3 3) = (60, 473, 5909 / 3, 23355 / 4) := by
  rw [ballSeries, show (range 4).erase 3 = {0, 1, 2} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, c4_mul,
    c4_C, c4_lin, c4_lin2, c4_inv_lin, c4_pow_four, c4_one]
  norm_num [m4, Nat.factorial]

/-- `U_3 = 2 u_3 = 2 · 1445`. -/
theorem ballU_three : ballU 3 = 2890 := by
  simp only [ballU, Finset.sum_range_succ, Finset.sum_range_zero, ballA_three_eq, c4_ball_3_0,
    c4_ball_3_1, c4_ball_3_2, c4_ball_3_3]
  norm_num

theorem harm_three (s : ℕ) : harm s 3 = 1 + 1 / 2 ^ s + 1 / 3 ^ s := by
  rw [harm, show Icc 1 3 = {1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num)]; norm_num; ring

/-- `V_3 = 2 v_3 = 2 · 62531/36`. -/
theorem ballV_three : ballV 3 = 62531 / 18 := by
  simp only [ballV, Finset.sum_range_succ, Finset.sum_range_zero, sum_Icc_one_four,
    ballA_four_eq, ballA_three_eq, ballA_two_eq, ballA_one_eq, c4_ball_3_0, c4_ball_3_1,
    c4_ball_3_2, c4_ball_3_3, harm_zero, harm_one, harm_two, harm_three]
  norm_num

/-! ### The top coefficient -/

/-- `A_{4,j}` is the value at `t = −j` of `(t+j)⁴ T_n(t)`:
`(n−2j) n!² ∏_{r=1}^{n} (−j−r)(n−j+r) / ∏_{0 ≤ h ≤ n, h ≠ j} (h−j)⁴`
(the same expression as `ballTopProd n j` of `BallTop.lean`). -/
theorem ballA_four (n j : ℕ) :
    ballA n 4 j = ((n : ℚ) - 2 * j) * (n.factorial : ℚ) ^ 2 *
      (∏ r ∈ Icc 1 n, ((-(j : ℚ) - r) * ((n : ℚ) - j + r))) /
      ∏ h ∈ (range (n + 1)).erase j, ((h : ℚ) - j) ^ 4 := by
  have hI : ∏ r ∈ Icc 1 n, ((-(j : ℚ) - r) * ((n : ℚ) - j + r)) =
      ∏ r ∈ range n, ((-(j : ℚ) - (r + 1)) * ((n : ℚ) - j + (r + 1))) := by
    rw [show Icc 1 n = Ico 1 (n + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
      Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun r _ => ?_
    push_cast; ring
  rw [hI, ballA, show 4 - 4 = 0 from rfl, coeff_zero_eq_constantCoeff_apply, ballSeries]
  simp only [map_mul, map_prod, map_pow, PowerSeries.constantCoeff_inv, lin, map_add,
    constantCoeff_C, constantCoeff_X, add_zero, mul_zero]
  rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  simp only [inv_pow]
  ring

/-! ### The symmetry `j ↦ n − j` -/

theorem rescale_C' (a : ℚ) : rescale (-1) (C a) = C a := by
  ext k
  rcases k with _ | k <;> simp [coeff_rescale, coeff_C]

theorem rescale_lin (a : ℚ) : rescale (-1) (lin a) = -lin (-a) := by
  ext k
  rcases k with _ | _ | k <;> simp [lin, rescale_C', coeff_rescale, coeff_X]

theorem rescale_lin2 (a b : ℚ) : rescale (-1) (C a + C b * X) = C a + C (-b) * X := by
  ext k
  rcases k with _ | _ | k <;> simp [rescale_C', coeff_rescale, coeff_C, coeff_X, coeff_C_mul]


theorem rescale_inv_lin (a : ℚ) : rescale (-1) (lin a)⁻¹ = -(lin (-a))⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    have : (lin 0)⁻¹ = 0 := by
      rw [PowerSeries.inv_eq_zero]; simp [lin]
    simp [this]
  · rw [inv_lin a ha, inv_lin (-a) (neg_ne_zero.mpr ha)]
    ext k
    simp only [coeff_rescale, coeff_mk, map_neg]
    rw [neg_pow a, pow_succ (-1 : ℚ) k]
    field_simp
    ring_nf
    simp [pow_mul']

/-- `x⁴ T_n(−(n−j) + x) = −(x⁴ T_n(−j − x))`, from `T_n(−n−t) = −T_n(t)`. -/
theorem ballSeries_symm (n j : ℕ) (hj : j ≤ n) :
    ballSeries n (n - j) = -rescale (-1) (ballSeries n j) := by
  have hP : ∏ r ∈ range n, lin (-((n - j : ℕ) : ℚ) - (r + 1)) * lin ((n : ℚ) - (n - j : ℕ) + (r + 1))
      = rescale (-1) (∏ r ∈ range n, lin (-(j : ℚ) - (r + 1)) * lin ((n : ℚ) - j + (r + 1))) := by
    rw [map_prod]
    refine prod_congr rfl fun r _ => ?_
    rw [map_mul, rescale_lin, rescale_lin]
    have e1 : -((n - j : ℕ) : ℚ) - (r + 1) = -((n : ℚ) - j + (r + 1)) := by
      push_cast [hj]; ring
    have e2 : (n : ℚ) - ((n - j : ℕ) : ℚ) + (r + 1) = -(-(j : ℚ) - (r + 1)) := by
      push_cast [hj]; ring
    rw [e1, e2]; ring
  have hQ : rescale (-1) (∏ h ∈ (range (n + 1)).erase j, (lin ((h : ℚ) - j))⁻¹ ^ 4) =
      ∏ h ∈ (range (n + 1)).erase (n - j), (lin ((h : ℚ) - ((n - j : ℕ) : ℚ)))⁻¹ ^ 4 := by
    rw [map_prod]
    refine Finset.prod_nbij' (fun h => n - h) (fun h => n - h) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp at ha ⊢; omega
    · intro a ha; simp at ha ⊢; omega
    · intro a ha; simp at ha ⊢; omega
    · intro a ha; simp at ha ⊢; omega
    · intro a ha
      simp only [mem_erase, mem_range] at ha
      rw [map_pow, rescale_inv_lin]
      have e : ((n - a : ℕ) : ℚ) - ((n - j : ℕ) : ℚ) = -((a : ℚ) - j) := by
        rw [Nat.cast_sub (by omega : a ≤ n), Nat.cast_sub hj]; ring
      rw [e]; ring
  rw [ballSeries, ballSeries, hP, ← hQ, map_mul, map_mul, map_mul, rescale_C', rescale_lin2,
    show ((n : ℚ) - 2 * ((n - j : ℕ) : ℚ)) = -((n : ℚ) - 2 * j) by push_cast [hj]; ring]
  simp only [map_neg]
  ring

/-- The symmetry `A_{s,n−j} = (−1)^{s+1} A_{s,j}` (for `j ≤ n`, `s ≤ 4`). -/
theorem ballA_symm (n s j : ℕ) (hj : j ≤ n) (hs : s ≤ 4) :
    ballA n s (n - j) = (-1) ^ (s + 1) * ballA n s j := by
  rw [ballA, ballA, ballSeries_symm n j hj, map_neg, coeff_rescale]
  interval_cases s <;> norm_num


/-! ### Towards the crude bound: power series with `D`-integral coefficients

`IsDInt D f` says that `D^k · [x^k] f` is an integer for every `k`. This class is closed under
products (coefficient `k` of `f g` is `∑_{i+i'=k}`, and `D^k = D^i D^{i'}`), contains the constants
and the linear series with integer coefficients, and contains `c · (c + x)⁻¹ = ∑ (−x/c)^i` when
`c` is a nonzero integer dividing `D`. -/

/-- All coefficients of `f` are `D`-integral: `D^k · [x^k] f ∈ ℤ`. -/
def IsDInt (D : ℕ) (f : PowerSeries ℚ) : Prop := ∀ k, ∃ z : ℤ, (D : ℚ) ^ k * coeff k f = z

theorem isDInt_mul {D : ℕ} {f g : PowerSeries ℚ} (hf : IsDInt D f) (hg : IsDInt D g) :
    IsDInt D (f * g) := by
  intro k
  choose a ha using hf
  choose b hb using hg
  refine ⟨∑ p ∈ antidiagonal k, a p.1 * b p.2, ?_⟩
  rw [coeff_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← ha p.1, ← hb p.2, ← hp, pow_add]
  ring

theorem isDInt_C (D : ℕ) (z : ℤ) : IsDInt D (C (z : ℚ)) := by
  intro k
  rcases k with _ | k
  · exact ⟨z, by simp⟩
  · exact ⟨0, by rw [coeff_C, if_neg (Nat.succ_ne_zero k)]; simp⟩

theorem isDInt_one (D : ℕ) : IsDInt D 1 := by
  have h := isDInt_C D 1
  simpa using h

theorem isDInt_pow {D : ℕ} {f : PowerSeries ℚ} (hf : IsDInt D f) (m : ℕ) :
    IsDInt D (f ^ m) := by
  induction m with
  | zero => simpa using isDInt_one D
  | succ m ih => rw [pow_succ]; exact isDInt_mul ih hf

theorem isDInt_prod {D : ℕ} {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ)
    (hf : ∀ i ∈ s, IsDInt D (f i)) : IsDInt D (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsDInt D) (fun _ _ => isDInt_mul) (isDInt_one D) hf

theorem isDInt_lin2 (D : ℕ) (z w : ℤ) : IsDInt D (C (z : ℚ) + C (w : ℚ) * X) := by
  intro k
  rcases k with _ | _ | k
  · exact ⟨z, by simp⟩
  · exact ⟨D * w, by rw [map_add, coeff_C_mul, coeff_C, coeff_X]; simp⟩
  · exact ⟨0, by rw [map_add, coeff_C_mul, coeff_C, coeff_X]; simp⟩

/-- `c · (c + x)⁻¹ = ∑ (−1)^i x^i / c^i` is `D`-integral when the nonzero integer `c` divides `D`. -/
theorem isDInt_C_mul_inv_lin (D : ℕ) (c : ℤ) (hc : c ≠ 0) (hcD : c ∣ (D : ℤ)) :
    IsDInt D (C (c : ℚ) * (lin c)⁻¹) := by
  obtain ⟨m, hm⟩ := hcD
  have hmQ : (D : ℚ) = c * m := by exact_mod_cast hm
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  intro k
  refine ⟨(-1) ^ k * m ^ k, ?_⟩
  rw [inv_lin _ hcQ, coeff_C_mul, coeff_mk, hmQ]
  push_cast
  field_simp
  ring

end Zeta3.BallSer