import Mathlib
import Zeta3.Apery
import Zeta3.AperyRec
import Zeta3.TableU
import Zeta3.GrowthRate

/-!
# More on the table U(n,m) (report §11.4, Proposition 12, §11.6 "Third change, for log 2")

Uses `tableU n m = Σ_{k ≤ min n m} aₖ(n)aₖ(m)` from `Zeta3.TableU`, `aₖ(n) = C(n,k)C(n+k,k)`.

1. **Half-steps (Proposition 12), hypothesis-free.** With `u_{n+1/2} = U(n+1,n)`:
   `u_{n+1/2}/u_n → 3 + 2√2` and `u_{n+1}/u_{n+1/2} → 3 + 2√2` (`tableU_halfstep_tendsto_left`,
   `tableU_halfstep_tendsto_right`), from (MIX) and `aperyU_halfstep_tendsto`.
2. **(SQ) for the integers**: `(n+1)³U(n+1,n) + n³U(n,n−1) = (2n+1)(3n²+3n+1)U(n,n)` for `n ≥ 1`
   (`tableU_sq`), the case `m = n` of (R), with symmetry; over ℕ.
3. **Small facts of §11.4**: `U(n,0) = 1` ("row 0", the integer part only), `U(0,m) = 1`,
   `U(1,m) = 1 + 2m(m+1)` ("the case n = 0": `U(1,m) = (1+2M)U(0,m)`).
4. **(COL) for the integers**: `(l+1)³U(n,l+1) = (n+1)³U(n+1,l) + r·U(n,l)` with
   `r = (l−n)((n+1)² − (n+1)(l+1) + (l+1)²)`, for all `n, l ≥ 0`, over ℚ (`tableU_col`).
   Proof by the telescoping certificate `c(k) = 2(b−a)(a+k)(b+k)·aₖ(n)aₖ(l)`, `a = n+1`, `b = l+1`
   (found numerically; it is the double-pole coefficient of the text's `C(t)` at `t = −k`, up to
   the factor `2(a−b)` and sign).
5. **log 2**: `D(n) = Σₖ aₖ(n)` (`delannoyD`; 1, 3, 13, 63) satisfies
   `(n+1)D(n+1) + nD(n−1) = 3(2n+1)D(n)` for `n ≥ 1` (`delannoyD_rec`, over ℕ), by the certificate
   `c(k) = −2(2n+1)·aₖ(n)`; and `D 0 = 1`, `D 1 = 3`, `D 2 = 13`.

Differences from the text: the text obtains (SQ), (COL) and the log 2 recurrence from rational
function identities read "at the poles"; here only the integer (`Pol`) sides are formalised, as
finite binomial-sum identities proved by telescoping certificates in `k`. The `Val` sides
(`Z(n,m)`, `Z(n,0) = ζ(3) − H_n^{(3)}`, the boundary term `−1`, the numbers `log 2`, `3 log 2 − 2`)
are not covered. `n − 1` is natural subtraction, with `n ≥ 1` where it matters.
-/

set_option autoImplicit false

open Filter Topology

namespace Zeta3

/-! ## 1. The half-steps -/

/-- (MIX) for Apéry's numbers, with the half-step `U(n+1,n)`, over ℝ. -/
theorem aperyU_mix_real (n : ℕ) :
    (aperyU (n + 1) : ℝ) + (aperyU n : ℝ) = 6 * (tableU (n + 1) n : ℝ) := by
  have h := tableU_mix n
  rw [tableU_diag, tableU_diag] at h
  have h' : aperyU (n + 1) + aperyU n = 6 * tableU (n + 1) n := by exact_mod_cast h
  exact_mod_cast h'

/-- **Proposition 12, half-steps (first)**: `u_{n+1/2}/u_n → 3 + 2√2`, `u_{n+1/2} = U(n+1,n)`. -/
theorem tableU_halfstep_tendsto_left :
    Tendsto (fun n => (tableU (n + 1) n : ℝ) / (aperyU n : ℝ)) atTop
      (𝓝 (3 + 2 * Real.sqrt 2)) :=
  (aperyU_halfstep_tendsto (fun n => (tableU (n + 1) n : ℝ)) aperyU_mix_real).1

/-- **Proposition 12, half-steps (second)**: `u_{n+1}/u_{n+1/2} → 3 + 2√2`. -/
theorem tableU_halfstep_tendsto_right :
    Tendsto (fun n => (aperyU (n + 1) : ℝ) / (tableU (n + 1) n : ℝ)) atTop
      (𝓝 (3 + 2 * Real.sqrt 2)) :=
  (aperyU_halfstep_tendsto (fun n => (tableU (n + 1) n : ℝ)) aperyU_mix_real).2

/-! ## 2. (SQ) -/

/-- **(SQ)** for the integers: `(n+1)³U(n+1,n) + n³U(n,n−1) = (2n+1)(3n²+3n+1)U(n,n)`, `n ≥ 1`. -/
theorem tableU_sq (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) ^ 3 * tableU (n + 1) n + n ^ 3 * tableU n (n - 1)
      = (2 * n + 1) * (3 * n ^ 2 + 3 * n + 1) * tableU n n := by
  have h := tableU_row n n hn
  rw [tableU_symm (n - 1) n] at h
  have hq : ((n : ℚ) + 1) ^ 3 * (tableU (n + 1) n : ℚ) + (n : ℚ) ^ 3 * (tableU n (n - 1) : ℚ)
      = (2 * (n : ℚ) + 1) * (3 * (n : ℚ) ^ 2 + 3 * (n : ℚ) + 1) * (tableU n n : ℚ) := by
    rw [h]; ring
  exact_mod_cast hq

/-! ## 3. Small facts -/

/-- Row 0 of the integer table: `U(n,0) = 1`. -/
theorem tableU_zero_right (n : ℕ) : tableU n 0 = 1 := by
  simp [tableU, aCoeff]

/-- `U(0,m) = 1`. -/
theorem tableU_zero_left (m : ℕ) : tableU 0 m = 1 := by
  rw [tableU_symm]; exact tableU_zero_right m

/-- The case `n = 0` of the row relation, integer side: `U(1,m) = 1 + 2m(m+1)`. -/
theorem tableU_one_left (m : ℕ) : tableU 1 m = 1 + 2 * m * (m + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [tableU, aCoeff]
  · have hmin : min 1 m = 1 := min_eq_left hm
    simp only [tableU, hmin, Finset.sum_range_succ, Finset.sum_range_zero, aCoeff]
    simp only [Nat.choose_zero_right, add_zero, Nat.choose_one_right, zero_add, mul_one,
      Nat.choose_self]
    ring

/-! ## 4. (COL) -/

/-- k-th term of (COL): `b³aₖ(n)aₖ(l+1) − a³aₖ(n+1)aₖ(l) − r·aₖ(n)aₖ(l)`. -/
def colTerm (n l k : ℕ) : ℚ :=
  ((l : ℚ) + 1) ^ 3 * (aCoeff n k : ℚ) * (aCoeff (l + 1) k : ℚ)
    - ((n : ℚ) + 1) ^ 3 * (aCoeff (n + 1) k : ℚ) * (aCoeff l k : ℚ)
    - ((l : ℚ) - n) * (((n : ℚ) + 1) ^ 2 - ((n : ℚ) + 1) * ((l : ℚ) + 1) + ((l : ℚ) + 1) ^ 2)
        * (aCoeff n k : ℚ) * (aCoeff l k : ℚ)

/-- Certificate for (COL): `c(k) = 2(b−a)(a+k)(b+k)·aₖ(n)aₖ(l)`. -/
def colCert (n l k : ℕ) : ℚ :=
  2 * ((l : ℚ) - n) * ((n : ℚ) + 1 + k) * ((l : ℚ) + 1 + k) * (aCoeff n k : ℚ) * (aCoeff l k : ℚ)

theorem colTerm_zero (n l : ℕ) : colTerm n l 0 = colCert n l 0 := by
  simp only [colTerm, colCert, aCoeff, Nat.choose_zero_right, add_zero]
  push_cast
  ring

theorem colTerm_succ (n l k : ℕ) :
    colTerm n l (k + 1) = colCert n l (k + 1) - colCert n l k := by
  have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have h1 := aCoeff_succ_succ n k
  have h2 := aCoeff_succ_right n k
  have h3 := aCoeff_succ_succ l k
  have h4 := aCoeff_succ_right l k
  have e1 : (aCoeff (n + 1) (k + 1) : ℚ)
      = (aCoeff n k : ℚ) * ((n : ℚ) + k + 2) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h1
  have e2 : (aCoeff n (k + 1) : ℚ)
      = (aCoeff n k : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h2
  have e3 : (aCoeff (l + 1) (k + 1) : ℚ)
      = (aCoeff l k : ℚ) * ((l : ℚ) + k + 2) * ((l : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h3
  have e4 : (aCoeff l (k + 1) : ℚ)
      = (aCoeff l k : ℚ) * ((l : ℚ) - k) * ((l : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h4
  unfold colTerm colCert
  rw [e1, e2, e3, e4]
  push_cast
  field_simp
  ring

theorem sum_colTerm (n l K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), colTerm n l j = colCert n l K := by
  induction K with
  | zero => simp [colTerm_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, colTerm_succ]; ring

/-- **(COL)** for the integer table, all `n, l ≥ 0`, over ℚ:
`(l+1)³U(n,l+1) = (n+1)³U(n+1,l) + r·U(n,l)`, `r = (l−n)((n+1)² − (n+1)(l+1) + (l+1)²)`. -/
theorem tableU_col (n l : ℕ) :
    ((l : ℚ) + 1) ^ 3 * (tableU n (l + 1) : ℚ)
      = ((n : ℚ) + 1) ^ 3 * (tableU (n + 1) l : ℚ)
        + ((l : ℚ) - n) * (((n : ℚ) + 1) ^ 2 - ((n : ℚ) + 1) * ((l : ℚ) + 1) + ((l : ℚ) + 1) ^ 2)
          * (tableU n l : ℚ) := by
  have hs := sum_colTerm n l (n + l + 1)
  have hc : colCert n l (n + l + 1) = 0 := by
    simp [colCert, aCoeff_eq_zero (show n < n + l + 1 by omega)]
  rw [hc] at hs
  rw [tableU_cast_eq n (l + 1) (n + l + 1 + 1) (by omega),
    tableU_cast_eq (n + 1) l (n + l + 1 + 1) (by omega),
    tableU_cast_eq n l (n + l + 1 + 1) (by omega)]
  unfold colTerm at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hs
  simp only [mul_assoc] at hs
  simp only [← Finset.mul_sum] at hs
  linear_combination hs

/-! ## 5. log 2: the central Delannoy numbers -/

/-- `D(n) = Σₖ aₖ(n) = Σₖ C(n,k)C(n+k,k)` (1, 3, 13, 63, …). -/
def delannoyD (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), aCoeff n k

theorem delannoyD_zero : delannoyD 0 = 1 := by decide

theorem delannoyD_one : delannoyD 1 = 3 := by decide

theorem delannoyD_two : delannoyD 2 = 13 := by decide

theorem delannoyD_cast_eq (n N : ℕ) (h : n + 1 ≤ N) :
    (delannoyD n : ℚ) = ∑ k ∈ Finset.range N, (aCoeff n k : ℚ) := by
  unfold delannoyD
  push_cast
  apply Finset.sum_subset (Finset.range_subset_range.2 h)
  intro k _ hk
  have hk' : n < k := by rw [Finset.mem_range] at hk; omega
  simp [aCoeff_eq_zero hk']

/-- k-th term of the log 2 recurrence at n = p + 1. -/
def delTerm (p k : ℕ) : ℚ :=
  ((p : ℚ) + 2) * (aCoeff (p + 2) k : ℚ) - 3 * (2 * ((p : ℚ) + 1) + 1) * (aCoeff (p + 1) k : ℚ)
    + ((p : ℚ) + 1) * (aCoeff p k : ℚ)

/-- Certificate: `c(k) = −2(2n+1)·aₖ(n)`, n = p + 1. -/
def delCert (p k : ℕ) : ℚ := -2 * (2 * ((p : ℚ) + 1) + 1) * (aCoeff (p + 1) k : ℚ)

theorem delTerm_zero (p : ℕ) : delTerm p 0 = delCert p 0 := by
  simp only [delTerm, delCert, aCoeff, Nat.choose_zero_right, add_zero]
  push_cast
  ring

theorem delTerm_succ (p k : ℕ) :
    delTerm p (k + 1) = delCert p (k + 1) - delCert p k := by
  have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have h1 := aCoeff_succ_succ (p + 1) k
  have h2 := aCoeff_succ_right (p + 1) k
  have h3 := aCoeff_down p k
  push_cast at h1 h2
  have e1 : (aCoeff (p + 1 + 1) (k + 1) : ℚ)
      = (aCoeff (p + 1) k : ℚ) * ((p : ℚ) + 1 + k + 2) * ((p : ℚ) + 1 + k + 1)
          / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h1
  have e2 : (aCoeff (p + 1) (k + 1) : ℚ)
      = (aCoeff (p + 1) k : ℚ) * ((p : ℚ) + 1 - k) * ((p : ℚ) + 1 + k + 1)
          / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h2
  have e3 : (aCoeff p (k + 1) : ℚ)
      = (aCoeff (p + 1) k : ℚ) * ((p : ℚ) + 1 - k) * ((p : ℚ) - k) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h3
  unfold delTerm delCert
  rw [show p + 2 = p + 1 + 1 from rfl, e1, e2, e3]
  field_simp
  ring

theorem sum_delTerm (p K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), delTerm p j = delCert p K := by
  induction K with
  | zero => simp [delTerm_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, delTerm_succ]; ring

/-- **The log 2 recurrence** for `D(n) = Σₖ aₖ(n)`, over ℚ:
`(n+1)D(n+1) = 3(2n+1)D(n) − nD(n−1)` for `n ≥ 1`. -/
theorem delannoyD_rec_rat (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℚ) + 1) * (delannoyD (n + 1) : ℚ)
      = 3 * (2 * (n : ℚ) + 1) * (delannoyD n : ℚ) - (n : ℚ) * (delannoyD (n - 1) : ℚ) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hs := sum_delTerm p (p + 2)
  have hc : delCert p (p + 2) = 0 := by
    simp [delCert, aCoeff_eq_zero (show p + 1 < p + 2 by omega)]
  rw [hc] at hs
  rw [show p + 1 + 1 = p + 2 from rfl, show p + 1 - 1 = p from rfl]
  rw [delannoyD_cast_eq (p + 2) (p + 2 + 1) (by omega),
    delannoyD_cast_eq (p + 1) (p + 2 + 1) (by omega),
    delannoyD_cast_eq p (p + 2 + 1) (by omega)]
  unfold delTerm at hs
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  push_cast
  linear_combination hs

/-- **The log 2 recurrence** over ℕ: `(n+1)D(n+1) + nD(n−1) = 3(2n+1)D(n)` for `n ≥ 1`. -/
theorem delannoyD_rec (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) * delannoyD (n + 1) + n * delannoyD (n - 1) = 3 * (2 * n + 1) * delannoyD n := by
  have h := delannoyD_rec_rat n hn
  have hq : ((n : ℚ) + 1) * (delannoyD (n + 1) : ℚ) + (n : ℚ) * (delannoyD (n - 1) : ℚ)
      = 3 * (2 * (n : ℚ) + 1) * (delannoyD n : ℚ) := by rw [h]; ring
  exact_mod_cast hq

-- CLAIMED: Zeta3.tableU_halfstep_tendsto_left, Zeta3.tableU_halfstep_tendsto_right, Zeta3.tableU_sq
-- CLAIMED: Zeta3.tableU_zero_right, Zeta3.tableU_zero_left, Zeta3.tableU_one_left, Zeta3.tableU_col
-- CLAIMED: Zeta3.delannoyD_zero, Zeta3.delannoyD_one, Zeta3.delannoyD_two, Zeta3.delannoyD_rec_rat, Zeta3.delannoyD_rec

end Zeta3
