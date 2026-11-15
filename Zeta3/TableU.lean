import Mathlib
import Zeta3.Apery
import Zeta3.AperyRec
import Zeta3.Recurrence

/-!
# The table U(n,m) = Σₖ aₖ(n)aₖ(m) (report §11.4) and Apéry's recurrence by the text's route

`tableU n m = Σ_{k=0}^{min n m} aₖ(n)·aₖ(m)` with `aₖ(n) = C(n,k)·C(n+k,k)` (`aCoeff`).
We prove, as finite binomial-sum identities, each by a telescoping certificate in `k`:

* (R)   `(n+1)³U(n+1,m) + n³U(n−1,m) = [n³ + (n+1)³ + 2m(m+1)(2n+1)]·U(n,m)` for `n ≥ 1`, `m ≥ 0`;
        certificate `c(k) = 2(2n+1)(k(k+1) − m(m+1))·aₖ(n)aₖ(m)`
        (the k-th term of the left side minus the right side equals `c(k) − c(k−1)`, and `c(m) = 0`);
* (MIX) `U(n+1,n+1) + U(n,n) = 6·U(n+1,n)` for `n ≥ 0`;
        certificate `c(k) = −4·((n+1+k)·aₖ(n)/(n+1))²` (vanishes at `k = n+1`);
* symmetry `U(n,m) = U(m,n)`;
* `U(n,n) = aperyU n`.

Then `Zeta3.apery_of_row_and_six` (Proposition 5's elimination) applied to the table cast to ℚ gives
Apéry's recurrence (A) for `aperyU`, without using `Zeta3.aperyU_recurrence`.

Differences from the text: the text obtains (R) and (MIX) by reading the rational-function identities
(ROW) and (MIX-id) "at the poles"; here the partial fractions are not formalised: (R) and (MIX) are
proved directly as identities between finite sums of products of binomial coefficients, by
certificates found as the double-pole coefficients of the functions `S` and `F_mix` of the text.
Only the table `U` is treated (not `Z` or `V`). (R) and (MIX) are stated over ℚ (casts of the
natural-number table); `n − 1` in (R) and in the final recurrence is natural subtraction with `n ≥ 1`.
-/

set_option autoImplicit false

namespace Zeta3

/-- The table U(n,m) = Σ_{k=0}^{min n m} aₖ(n)·aₖ(m). -/
def tableU (n m : ℕ) : ℕ := ∑ k ∈ Finset.range (min n m + 1), aCoeff n k * aCoeff m k

/-- U as a rational sum over any range k < N with N ≥ min n m + 1. -/
theorem tableU_cast_eq (n m N : ℕ) (h : min n m + 1 ≤ N) :
    (tableU n m : ℚ) = ∑ k ∈ Finset.range N, (aCoeff n k : ℚ) * (aCoeff m k : ℚ) := by
  unfold tableU
  push_cast
  apply Finset.sum_subset (Finset.range_subset_range.2 h)
  intro k _ hk
  have hk' : min n m < k := by rw [Finset.mem_range] at hk; omega
  rcases le_total n m with hnm | hnm
  · rw [min_eq_left hnm] at hk'
    simp [aCoeff_eq_zero hk']
  · rw [min_eq_right hnm] at hk'
    simp [aCoeff_eq_zero hk']

/-- Symmetry of the table. -/
theorem tableU_symm (n m : ℕ) : tableU n m = tableU m n := by
  unfold tableU
  rw [min_comm]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The diagonal of the table is Apéry's sequence. -/
theorem tableU_diag (n : ℕ) : tableU n n = aperyU n := by
  unfold tableU aperyU
  rw [min_self]
  exact Finset.sum_congr rfl fun k _ => (sq _).symm

/-! ## The row relation (R) -/

/-- k-th term of (R) at n = p + 1. -/
def rowTerm (p m k : ℕ) : ℚ :=
  ((p : ℚ) + 2) ^ 3 * (aCoeff (p + 2) k : ℚ) * (aCoeff m k : ℚ)
    - (((p : ℚ) + 1) ^ 3 + ((p : ℚ) + 2) ^ 3 + 2 * (m : ℚ) * ((m : ℚ) + 1) * (2 * ((p : ℚ) + 1) + 1))
        * (aCoeff (p + 1) k : ℚ) * (aCoeff m k : ℚ)
    + ((p : ℚ) + 1) ^ 3 * (aCoeff p k : ℚ) * (aCoeff m k : ℚ)

/-- Certificate for (R) at n = p + 1: c(k) = 2(2n+1)(k(k+1) − m(m+1))·aₖ(n)aₖ(m). -/
def rowCert (p m k : ℕ) : ℚ :=
  2 * (2 * ((p : ℚ) + 1) + 1) * ((k : ℚ) * ((k : ℚ) + 1) - (m : ℚ) * ((m : ℚ) + 1))
    * (aCoeff (p + 1) k : ℚ) * (aCoeff m k : ℚ)

theorem rowTerm_zero (p m : ℕ) : rowTerm p m 0 = rowCert p m 0 := by
  simp only [rowTerm, rowCert, aCoeff, Nat.choose_zero_right, add_zero]
  push_cast
  ring

theorem rowTerm_succ (p m k : ℕ) :
    rowTerm p m (k + 1) = rowCert p m (k + 1) - rowCert p m k := by
  have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have h1 := aCoeff_succ_succ (p + 1) k
  have h2 := aCoeff_succ_right (p + 1) k
  have h3 := aCoeff_down p k
  have h4 := aCoeff_succ_right m k
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
  have e4 : (aCoeff m (k + 1) : ℚ)
      = (aCoeff m k : ℚ) * ((m : ℚ) - k) * ((m : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h4
  unfold rowTerm rowCert
  rw [show p + 2 = p + 1 + 1 from rfl, e1, e2, e3, e4]
  push_cast
  field_simp
  ring

theorem sum_rowTerm (p m K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), rowTerm p m j = rowCert p m K := by
  induction K with
  | zero => simp [rowTerm_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, rowTerm_succ]; ring

/-- **(R)**, the row relation of the table, for n ≥ 1 and m ≥ 0, over ℚ. -/
theorem tableU_row (n m : ℕ) (hn : 1 ≤ n) :
    ((n : ℚ) + 1) ^ 3 * (tableU (n + 1) m : ℚ) + (n : ℚ) ^ 3 * (tableU (n - 1) m : ℚ)
      = ((n : ℚ) ^ 3 + ((n : ℚ) + 1) ^ 3 + 2 * (m : ℚ) * ((m : ℚ) + 1) * (2 * (n : ℚ) + 1))
          * (tableU n m : ℚ) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hs := sum_rowTerm p m m
  have hc : rowCert p m m = 0 := by unfold rowCert; ring
  rw [hc] at hs
  rw [show p + 1 + 1 = p + 2 from rfl, show p + 1 - 1 = p from rfl]
  rw [tableU_cast_eq (p + 2) m (m + 1) (by omega), tableU_cast_eq p m (m + 1) (by omega),
    tableU_cast_eq (p + 1) m (m + 1) (by omega)]
  unfold rowTerm at hs
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  simp only [mul_assoc] at hs
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  push_cast
  linear_combination hs

/-! ## The relation (MIX) between the diagonal and the line next to it -/

/-- k-th term of (MIX). -/
def mixTerm (n k : ℕ) : ℚ :=
  (aCoeff (n + 1) k : ℚ) ^ 2 + (aCoeff n k : ℚ) ^ 2 - 6 * (aCoeff (n + 1) k : ℚ) * (aCoeff n k : ℚ)

/-- Certificate for (MIX): c(k) = −4((n+1+k)·aₖ(n)/(n+1))². -/
def mixCert (n k : ℕ) : ℚ :=
  -4 * (((n : ℚ) + 1 + k) * (aCoeff n k : ℚ) / ((n : ℚ) + 1)) ^ 2

theorem mixTerm_zero (n : ℕ) : mixTerm n 0 = mixCert n 0 := by
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  simp only [mixTerm, mixCert, aCoeff, Nat.choose_zero_right, add_zero]
  push_cast
  field_simp
  ring

theorem mixTerm_succ (n k : ℕ) :
    mixTerm n (k + 1) = mixCert n (k + 1) - mixCert n k := by
  have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h1 := aCoeff_succ_succ n k
  have h2 := aCoeff_succ_right n k
  have e1 : (aCoeff (n + 1) (k + 1) : ℚ)
      = (aCoeff n k : ℚ) * ((n : ℚ) + k + 2) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h1
  have e2 : (aCoeff n (k + 1) : ℚ)
      = (aCoeff n k : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h2
  unfold mixTerm mixCert
  rw [e1, e2]
  push_cast
  field_simp
  ring

theorem sum_mixTerm (n K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), mixTerm n j = mixCert n K := by
  induction K with
  | zero => simp [mixTerm_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, mixTerm_succ]; ring

/-- **(MIX)**: U(n+1,n+1) + U(n,n) = 6·U(n+1,n), over ℚ. -/
theorem tableU_mix (n : ℕ) :
    (tableU (n + 1) (n + 1) : ℚ) + (tableU n n : ℚ) = 6 * (tableU (n + 1) n : ℚ) := by
  have hs := sum_mixTerm n (n + 1)
  have hc : mixCert n (n + 1) = 0 := by
    simp [mixCert, aCoeff_eq_zero (show n < n + 1 by omega)]
  rw [hc] at hs
  rw [tableU_cast_eq (n + 1) (n + 1) (n + 1 + 1) (by omega),
    tableU_cast_eq n n (n + 1 + 1) (by omega), tableU_cast_eq (n + 1) n (n + 1 + 1) (by omega)]
  unfold mixTerm at hs
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  simp only [mul_assoc] at hs
  rw [← Finset.mul_sum] at hs
  simp only [sq] at hs
  linear_combination hs

/-! ## Apéry's recurrence by elimination (Proposition 5) -/

/-- Apéry's recurrence (A) for uₙ = U(n,n), obtained from (R), (MIX) and symmetry by the
elimination of Proposition 5 (`apery_of_row_and_six`), not from the classical certificate. -/
theorem aperyU_recurrence_via_table (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℚ) + 1) ^ 3 * aperyU (n + 1)
      - (34 * (n : ℚ) ^ 3 + 51 * (n : ℚ) ^ 2 + 27 * (n : ℚ) + 5) * aperyU n
      + (n : ℚ) ^ 3 * aperyU (n - 1) = 0 := by
  have h := apery_of_row_and_six (K := ℚ) (fun a b => (tableU a b : ℚ))
    (fun a b => by simp only [tableU_symm a b])
    (fun a b ha => tableU_row a b ha)
    tableU_mix n hn
  simp only [tableU_diag] at h
  exact h

-- CLAIMED: Zeta3.tableU_symm, Zeta3.tableU_diag, Zeta3.tableU_row, Zeta3.tableU_mix, Zeta3.aperyU_recurrence_via_table

end Zeta3
