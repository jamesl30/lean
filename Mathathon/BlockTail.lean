import Mathlib
open Finset

namespace Mathathon.BlockTail

/-- generalised binomial coefficient binom(a, j) -/
noncomputable def gb (a : ℝ) (j : ℕ) : ℝ := (∏ i ∈ Finset.range j, (a - i)) / (j.factorial : ℝ)

lemma gb_succ (a : ℝ) (j : ℕ) : gb a (j + 1) = gb a j * ((a - j) / (j + 1)) := by
  unfold gb
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have h1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem gb_third_le (j : ℕ) (hj : 1 ≤ j) : |gb (1/3 : ℝ) j| ≤ 1/3 := by
  induction j, hj using Nat.le_induction with
  | base => norm_num [gb]
  | succ n hn ih =>
    rw [gb_succ, abs_mul]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < n + 1 := by linarith
    have hf : |(1/3 - (n:ℝ)) / (n + 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_of_nonpos (by linarith)]
      linarith
    calc |gb (1/3) n| * |(1/3 - (n:ℝ)) / (n + 1)| ≤ 1/3 * 1 :=
          mul_le_mul ih hf (abs_nonneg _) (by norm_num)
      _ = 1/3 := by norm_num

theorem tail_le (P r : ℝ) (hP : 0 ≤ P) (hr : 0 ≤ r) (hr4 : 2 * r ≤ 1/4) (J : ℕ) :
    |∑ j ∈ Finset.Icc 4 J, 3 * P * gb (1/3) j * (2 * r) ^ j| ≤ (64/3) * P * r ^ 4 := by
  set q := 2 * r with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by linarith
  calc |∑ j ∈ Finset.Icc 4 J, 3 * P * gb (1/3) j * q ^ j|
      ≤ ∑ j ∈ Finset.Icc 4 J, |3 * P * gb (1/3) j * q ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 4 J, P * q ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        have hj1 : 1 ≤ j := by simp at hj; omega
        have hg := gb_third_le j hj1
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ q ^ j),
          abs_of_nonneg hP, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
        have : 3 * P * |gb (1/3) j| ≤ P := by nlinarith [abs_nonneg (gb (1/3) j)]
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = P * ∑ j ∈ Finset.Ico 4 (J + 1), q ^ j := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ P * (q ^ 4 / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) hP
    _ ≤ (64/3) * P * r ^ 4 := by
        have h1q : 0 < 1 - q := by linarith
        have : q ^ 4 / (1 - q) ≤ (4/3) * q ^ 4 := by
          rw [div_le_iff₀ h1q]
          have : 0 ≤ q ^ 4 := by positivity
          nlinarith
        rw [hq] at this
        nlinarith [mul_le_mul_of_nonneg_left this hP]

theorem d3_cube_twist (k : ℕ) :
    ((k + 1) * (k + 2) / 2 : ℤ) - (if 3 ≤ k then ((k - 2) * (k - 1) / 2 : ℤ) else 0)
      = if k = 0 then 1 else 3 * k := by
  have hA : (2 : ℤ) ∣ ((k : ℤ) + 1) * ((k : ℤ) + 2) := by
    have := Int.even_mul_succ_self ((k : ℤ) + 1)
    rw [even_iff_two_dvd] at this
    convert this using 1; ring
  have hB : (2 : ℤ) ∣ ((k : ℤ) - 2) * ((k : ℤ) - 1) := by
    have := Int.even_mul_succ_self ((k : ℤ) - 2)
    rw [even_iff_two_dvd] at this
    convert this using 1; ring
  have eA := Int.ediv_mul_cancel hA
  have eB := Int.ediv_mul_cancel hB
  split_ifs with h1 h2 h2
  · omega
  · push_cast; linarith
  · subst h2; norm_num
  · interval_cases k <;> omega

end Mathathon.BlockTail
