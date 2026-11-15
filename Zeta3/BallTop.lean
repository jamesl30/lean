import Mathlib

/-!
# The top coefficients of Ball's rational function

Ball's rational function at level `b` is
`T_b(t) = b!² (2t+b) ∏_{r=1}^{b} (t−r)(t+b+r) / ∏_{r=0}^{b} (t+r)⁴`.
Its coefficient of `(t+d)^{-4}` (`0 ≤ d ≤ b`) is the value at `t = −d` of `(t+d)⁴ T_b(t)`,
written out here as `ballTopProd b d`. We prove that it equals
`ballTop b d = (−1)^b (b−2d) C(b,d)⁴ C(b+d,b) C(2b−d,b)` (`ballTopProd_eq`), that `ballTop` is
antisymmetric under `d ↦ b−d` (`ballTop_antisymm`) and that its sum over `0 ≤ d ≤ b` is zero
(`ballTop_sum`).
-/

-- CLAIMED: Zeta3.BallTop.ballTop_antisymm, Zeta3.BallTop.ballTop_sum, Zeta3.BallTop.ballTopProd_eq

set_option autoImplicit false

namespace Zeta3.BallTop
open Finset

/-- `(−1)^b (b−2d) C(b,d)⁴ C(b+d,b) C(2b−d,b)`; for `d ≤ b` the subtraction `2*b-d` in `ℕ` is exact. -/
def ballTop (b d : ℕ) : ℤ :=
  (-1) ^ b * ((b : ℤ) - 2 * d) * (b.choose d : ℤ) ^ 4 * ((b + d).choose b : ℤ) *
    ((2 * b - d).choose b : ℤ)

example : ballTop 0 0 = 0 := by decide
example : ballTop 1 0 = -2 := by decide
example : ballTop 1 1 = 2 := by decide
example : ballTop 2 0 = 12 := by decide
example : ballTop 2 1 = 0 := by decide
example : ballTop 2 2 = -12 := by decide
example : ballTop 3 0 = -60 := by decide
example : ballTop 3 1 = -3240 := by decide
example : ballTop 3 2 = 3240 := by decide
example : ballTop 3 3 = 60 := by decide

/-- The value at `t = −d` of `(t+d)⁴ T_b(t)`:
`(b−2d) (b!)² ∏_{r=1}^{b} (−d−r)(b−d+r) / ∏_{0 ≤ r ≤ b, r ≠ d} (r−d)⁴`. -/
def ballTopProd (b d : ℕ) : ℚ :=
  ((b : ℚ) - 2 * d) * (b.factorial : ℚ) ^ 2 *
      (∏ r ∈ Icc 1 b, ((-(d : ℚ) - r) * ((b : ℚ) - d + r))) /
    ∏ r ∈ (range (b + 1)).erase d, ((r : ℚ) - d) ^ 4

example : ballTopProd 1 0 = -2 := by
  rw [ballTopProd, show (range 2).erase 0 = {1} by decide, show Icc 1 1 = {1} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 2 0 = 12 := by
  rw [ballTopProd, show (range 3).erase 0 = {1, 2} by decide, show Icc 1 2 = {1, 2} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 3 1 = -3240 := by
  rw [ballTopProd, show (range 4).erase 1 = {0, 2, 3} by decide,
    show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 3 3 = 60 := by
  rw [ballTopProd, show (range 4).erase 3 = {0, 1, 2} by decide,
    show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 0 0 = 0 := by
  rw [ballTopProd, show (range 1).erase 0 = ∅ by decide]
  norm_num [Nat.factorial]

example : ballTopProd 1 1 = 2 := by
  rw [ballTopProd, show (range 2).erase 1 = {0} by decide,
    show Icc 1 1 = {1} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 2 1 = 0 := by
  rw [ballTopProd, show (range 3).erase 1 = {0, 2} by decide,
    show Icc 1 2 = {1, 2} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 2 2 = -12 := by
  rw [ballTopProd, show (range 3).erase 2 = {0, 1} by decide,
    show Icc 1 2 = {1, 2} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 3 0 = -60 := by
  rw [ballTopProd, show (range 4).erase 0 = {1, 2, 3} by decide,
    show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [Nat.factorial]

example : ballTopProd 3 2 = 3240 := by
  rw [ballTopProd, show (range 4).erase 2 = {0, 1, 3} by decide,
    show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [Nat.factorial]

theorem ballTop_antisymm : ∀ b d : ℕ, d ≤ b → ballTop b (b - d) = -ballTop b d := by
  intro b d h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : d + e - d = e := by omega
  have h2 : 2 * (d + e) - e = 2 * d + e := by omega
  have h3 : 2 * (d + e) - d = d + 2 * e := by omega
  have h4 : d + e + e = d + 2 * e := by omega
  have h5 : d + e + d = 2 * d + e := by omega
  simp only [ballTop, h1, h2, h3, h4, h5]
  rw [Nat.choose_symm_add]
  push_cast
  ring

theorem ballTop_sum : ∀ b : ℕ, ∑ d ∈ range (b + 1), ballTop b d = 0 := by
  intro b
  have h := Finset.sum_range_reflect (fun d => ballTop b d) (b + 1)
  have h' : ∑ j ∈ range (b + 1), ballTop b (b + 1 - 1 - j) =
      ∑ j ∈ range (b + 1), -ballTop b j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [show b + 1 - 1 - j = b - j by omega, ballTop_antisymm b j (by omega)]
  rw [h', Finset.sum_neg_distrib] at h
  linarith

/-- `m! ∏_{r=1}^{n} (m+r) = (m+n)!`. -/
lemma factorial_mul_prod_Icc (m n : ℕ) :
    (m.factorial : ℚ) * ∏ r ∈ Icc 1 n, ((m : ℚ) + r) = ((m + n).factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc, ih, ← Nat.add_assoc,
      Nat.factorial_succ]
    push_cast
    ring

/-- `∏_{0 ≤ r ≤ d+e, r ≠ d} (r−d) = (−1)^d d! e!`. -/
lemma prod_erase_sub (d e : ℕ) :
    ∏ r ∈ (range (d + e + 1)).erase d, ((r : ℚ) - d) =
      (-1) ^ d * (d.factorial : ℚ) * (e.factorial : ℚ) := by
  have hsplit : (range (d + e + 1)).erase d = range d ∪ Ico (d + 1) (d + e + 1) := by
    ext r; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range d) (Ico (d + 1) (d + e + 1)) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    simp only [mem_range] at h1; simp only [mem_Ico] at h2; omega
  rw [hsplit, Finset.prod_union hdisj]
  have hA : ∏ r ∈ range d, ((r : ℚ) - d) = (-1) ^ d * (d.factorial : ℚ) := by
    rw [← Finset.prod_range_reflect]
    have : ∀ j ∈ range d, (((d - 1 - j : ℕ) : ℚ) - d) = -((j : ℚ) + 1) := by
      intro j hj; rw [mem_range] at hj
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [Finset.prod_congr rfl this, Finset.prod_neg, card_range,
      ← Finset.prod_range_add_one_eq_factorial]
    push_cast; ring
  have hB : ∏ r ∈ Ico (d + 1) (d + e + 1), ((r : ℚ) - d) = (e.factorial : ℚ) := by
    rw [Finset.prod_Ico_eq_prod_range, show d + e + 1 - (d + 1) = e by omega,
      ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    apply Finset.prod_congr rfl
    intro j _; ring
  rw [hA, hB]

theorem ballTopProd_eq (b d : ℕ) (h : d ≤ b) : ballTopProd b d = (ballTop b d : ℚ) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  have hden : ∏ r ∈ (range (d + e + 1)).erase d, ((r : ℚ) - d) ^ 4 =
      ((d.factorial : ℚ) * (e.factorial : ℚ)) ^ 4 := by
    rw [Finset.prod_pow, prod_erase_sub]
    rw [mul_assoc, mul_pow, ← pow_mul, show d * 4 = 2 * (2 * d) by ring, pow_mul]
    norm_num
  have hnum : ∏ r ∈ Icc 1 (d + e), ((-(d : ℚ) - r) * (((d + e : ℕ) : ℚ) - d + r)) =
      (-1) ^ (d + e) * (∏ r ∈ Icc 1 (d + e), ((d : ℚ) + r)) *
        ∏ r ∈ Icc 1 (d + e), ((e : ℚ) + r) := by
    rw [Finset.prod_mul_distrib]
    have h1 : ∏ r ∈ Icc 1 (d + e), (-(d : ℚ) - r) =
        ∏ r ∈ Icc 1 (d + e), -((d : ℚ) + r) := by
      apply Finset.prod_congr rfl; intro r _; ring
    have h2 : ∏ r ∈ Icc 1 (d + e), (((d + e : ℕ) : ℚ) - d + r) =
        ∏ r ∈ Icc 1 (d + e), ((e : ℚ) + r) := by
      apply Finset.prod_congr rfl; intro r _; push_cast; ring
    rw [h1, h2, Finset.prod_neg, Nat.card_Icc, show d + e + 1 - 1 = d + e by omega]
  have hP1 := factorial_mul_prod_Icc d (d + e)
  have hP2 := factorial_mul_prod_Icc e (d + e)
  have hd : (d.factorial : ℚ) ≠ 0 := by positivity
  have he : (e.factorial : ℚ) ≠ 0 := by positivity
  have hb : ((d + e).factorial : ℚ) ≠ 0 := by positivity
  have hP1' : ∏ r ∈ Icc 1 (d + e), ((d : ℚ) + r) = ((d + (d + e)).factorial : ℚ) / d.factorial := by
    rw [eq_div_iff hd, mul_comm, hP1]
  have hP2' : ∏ r ∈ Icc 1 (d + e), ((e : ℚ) + r) = ((e + (d + e)).factorial : ℚ) / e.factorial := by
    rw [eq_div_iff he, mul_comm, hP2]
  have c1 : ((d + e).choose d : ℚ) = (d + e).factorial / (d.factorial * e.factorial) := by
    rw [Nat.cast_choose ℚ (by omega : d ≤ d + e), show d + e - d = e by omega]
  have c2 : ((d + e + d).choose (d + e) : ℚ) =
      (d + (d + e)).factorial / ((d + e).factorial * d.factorial) := by
    rw [Nat.cast_choose ℚ (by omega : d + e ≤ d + e + d), show d + e + d - (d + e) = d by omega,
      show d + e + d = d + (d + e) by omega]
  have c3 : ((2 * (d + e) - d).choose (d + e) : ℚ) =
      (e + (d + e)).factorial / ((d + e).factorial * e.factorial) := by
    rw [Nat.cast_choose ℚ (by omega : d + e ≤ 2 * (d + e) - d),
      show 2 * (d + e) - d - (d + e) = e by omega, show 2 * (d + e) - d = e + (d + e) by omega]
  rw [ballTopProd, hden, hnum, hP1', hP2', ballTop]
  push_cast
  rw [c1, c2, c3]
  field_simp

end Zeta3.BallTop