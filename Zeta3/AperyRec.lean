import Mathlib
import Zeta3.Apery

/-!
# Apéry's recurrence for Apéry's numbers (unconditional)

Route: the Zeilberger / Cohen–Zagier certificate. With aₖ(n) = C(n,k)²C(n+k,k)² and
B(n,k) = 4(2n+1)(k(2k+1) − (2n+1)²)·aₖ(n), one has, for every k,
  B(n,k) − B(n,k−1) = (n+1)³aₖ(n+1) − (34n³+51n²+27n+5)aₖ(n) + n³aₖ(n−1)
(with B(n,−1) = 0, and aₖ(n) = 0 for k > n), and summing over k = 0, …, n+1 telescopes to
B(n,n+1) = 0. Everything is written with n = m + 1, so no natural subtraction occurs.
-/

namespace Zeta3

/-- aₖ(n) = 0 for k > n. -/
theorem aCoeff_eq_zero {n k : ℕ} (h : n < k) : aCoeff n k = 0 := by
  simp [aCoeff, Nat.choose_eq_zero_of_lt h]

/-- aₖ₊₁(n+1)·(k+1)² = aₖ(n)·(n+k+2)(n+k+1). -/
theorem aCoeff_succ_succ (n k : ℕ) :
    (aCoeff (n + 1) (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2
      = (aCoeff n k : ℚ) * ((n : ℚ) + k + 2) * ((n : ℚ) + k + 1) := by
  have e1 : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq n k
  have e2 : (n + k + 1 + 1) * (n + k + 1).choose k
      = (n + k + 1 + 1).choose (k + 1) * (k + 1) := Nat.add_one_mul_choose_eq (n + k + 1) k
  have e3 : (n + k).choose k * (n + k + 1) = (n + k + 1).choose k * (n + k + 1 - k) :=
    Nat.choose_mul_succ_eq (n + k) k
  have e3' : n + k + 1 - k = n + 1 := by omega
  rw [e3'] at e3
  have hidx : n + 1 + (k + 1) = n + k + 1 + 1 := by ring
  unfold aCoeff
  rw [hidx]
  have q1 : ((n : ℚ) + 1) * (n.choose k : ℚ) = ((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
    exact_mod_cast e1
  have q2 : ((n : ℚ) + k + 1 + 1) * ((n + k + 1).choose k : ℚ)
      = ((n + k + 1 + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by exact_mod_cast e2
  have q3 : ((n + k).choose k : ℚ) * ((n : ℚ) + k + 1) = ((n + k + 1).choose k : ℚ) * ((n : ℚ) + 1) := by
    exact_mod_cast e3
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  apply mul_right_cancel₀ hn
  linear_combination
    (-(((n + k + 1 + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) * ((n : ℚ) + 1))) * q1
      - ((n : ℚ) + 1) * (n.choose k : ℚ) * ((n : ℚ) + 1) * q2
      - ((n : ℚ) + 1) * (n.choose k : ℚ) * ((n : ℚ) + k + 2) * q3

/-- aₖ₊₁(n)·(k+1)² = aₖ(n)·(n−k)(n+k+1), over ℚ (both sides vanish for k ≥ n). -/
theorem aCoeff_succ_right (n k : ℕ) :
    (aCoeff n (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2
      = (aCoeff n k : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + k + 1) := by
  rcases le_or_gt k n with h | h
  · have e1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
    have e2 : (n + k + 1) * (n + k).choose k = (n + k + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq (n + k) k
    have q1 : (n.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (n.choose k : ℚ) * ((n : ℚ) - k) := by
      have := congrArg (fun x : ℕ => (x : ℚ)) e1
      push_cast [Nat.cast_sub h] at this
      exact this
    have q2 : ((n : ℚ) + k + 1) * ((n + k).choose k : ℚ)
        = ((n + k + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by exact_mod_cast e2
    have hidx : n + (k + 1) = n + k + 1 := by ring
    unfold aCoeff
    rw [hidx]
    push_cast
    linear_combination
      (((n + k + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1)) * q1
        - (n.choose k : ℚ) * ((n : ℚ) - k) * q2
  · simp [aCoeff, Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_lt h)]

/-- aₖ(n+1)·(n+1−k) = aₖ(n)·(n+1+k), over ℚ (both sides vanish for k > n + 1). -/
theorem aCoeff_succ_left (n k : ℕ) :
    (aCoeff (n + 1) k : ℚ) * ((n : ℚ) + 1 - k) = (aCoeff n k : ℚ) * ((n : ℚ) + 1 + k) := by
  rcases le_or_gt k (n + 1) with h | h
  · have e1 : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) := Nat.choose_mul_succ_eq n k
    have e2 : (n + k).choose k * (n + k + 1) = (n + k + 1).choose k * (n + k + 1 - k) :=
      Nat.choose_mul_succ_eq (n + k) k
    have e2' : n + k + 1 - k = n + 1 := by omega
    rw [e2'] at e2
    have q1 : (n.choose k : ℚ) * ((n : ℚ) + 1) = ((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k) := by
      have := congrArg (fun x : ℕ => (x : ℚ)) e1
      push_cast [Nat.cast_sub h] at this
      exact this
    have q2 : ((n + k).choose k : ℚ) * ((n : ℚ) + k + 1)
        = ((n + k + 1).choose k : ℚ) * ((n : ℚ) + 1) := by exact_mod_cast e2
    have hidx : n + 1 + k = n + k + 1 := by ring
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    unfold aCoeff
    rw [hidx]
    push_cast
    apply mul_right_cancel₀ hn
    linear_combination
      (-(((n + k + 1).choose k : ℚ) * ((n : ℚ) + 1))) * q1
        - (n.choose k : ℚ) * ((n : ℚ) + 1) * q2
  · have h' : n < k := by omega
    simp [aCoeff, Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt h']

/-- aₖ₊₁(m)·(k+1)² = aₖ(m+1)·(m+1−k)(m−k), over ℚ. -/
theorem aCoeff_down (m k : ℕ) :
    (aCoeff m (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2
      = (aCoeff (m + 1) k : ℚ) * ((m : ℚ) + 1 - k) * ((m : ℚ) - k) := by
  have l2 := aCoeff_succ_right m k
  have l3 := aCoeff_succ_left m k
  have hpos : ((m : ℚ) + k + 1) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpos
  linear_combination ((m : ℚ) + k + 1) * l2 - ((m : ℚ) - k) * ((m : ℚ) + k + 1) * l3

/-- The certificate B(n,k) = 4(2n+1)(k(2k+1) − (2n+1)²)·aₖ(n)², over ℚ. -/
def certB (n k : ℕ) : ℚ :=
  4 * (2 * (n : ℚ) + 1) * ((k : ℚ) * (2 * k + 1) - (2 * (n : ℚ) + 1) ^ 2) * (aCoeff n k : ℚ) ^ 2

/-- The k-th term of the recurrence operator at n = m + 1:
(n+1)³aₖ(n+1)² − (34n³+51n²+27n+5)aₖ(n)² + n³aₖ(n−1)². -/
def recTerm (m k : ℕ) : ℚ :=
  ((m : ℚ) + 2) ^ 3 * (aCoeff (m + 2) k : ℚ) ^ 2
    - (34 * ((m : ℚ) + 1) ^ 3 + 51 * ((m : ℚ) + 1) ^ 2 + 27 * ((m : ℚ) + 1) + 5)
        * (aCoeff (m + 1) k : ℚ) ^ 2
    + ((m : ℚ) + 1) ^ 3 * (aCoeff m k : ℚ) ^ 2

theorem recTerm_zero (m : ℕ) : recTerm m 0 = certB (m + 1) 0 := by
  simp only [recTerm, certB, aCoeff, Nat.choose_zero_right, add_zero]
  push_cast
  ring

/-- The certificate identity: B(n,k+1) − B(n,k) = (k+1)-th term of the operator (n = m + 1). -/
theorem recTerm_succ (m k : ℕ) :
    recTerm m (k + 1) = certB (m + 1) (k + 1) - certB (m + 1) k := by
  have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have h1 := aCoeff_succ_succ (m + 1) k
  have h2 := aCoeff_succ_right (m + 1) k
  have h3 := aCoeff_down m k
  push_cast at h1 h2
  have e1 : (aCoeff (m + 1 + 1) (k + 1) : ℚ)
      = (aCoeff (m + 1) k : ℚ) * ((m : ℚ) + 1 + k + 2) * ((m : ℚ) + 1 + k + 1)
          / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h1
  have e2 : (aCoeff (m + 1) (k + 1) : ℚ)
      = (aCoeff (m + 1) k : ℚ) * ((m : ℚ) + 1 - k) * ((m : ℚ) + 1 + k + 1)
          / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h2
  have e3 : (aCoeff m (k + 1) : ℚ)
      = (aCoeff (m + 1) k : ℚ) * ((m : ℚ) + 1 - k) * ((m : ℚ) - k) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h3
  unfold recTerm certB
  rw [show m + 2 = m + 1 + 1 from rfl, e1, e2, e3]
  push_cast
  field_simp
  ring

/-- Telescoping: Σ_{j=0}^{K} (operator term j) = B(m+1, K). -/
theorem sum_recTerm (m K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), recTerm m j = certB (m + 1) K := by
  induction K with
  | zero => simp [recTerm_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, recTerm_succ]; ring

/-- uₙ as a rational sum over any range k < N with N ≥ n + 1. -/
theorem aperyU_cast_eq (n N : ℕ) (h : n + 1 ≤ N) :
    (aperyU n : ℚ) = ∑ j ∈ Finset.range N, (aCoeff n j : ℚ) ^ 2 := by
  unfold aperyU
  push_cast
  apply Finset.sum_subset (Finset.range_subset_range.2 h)
  intro j _ hj
  have : n < j := by simpa using hj
  simp [aCoeff_eq_zero this]

/-- Apéry's recurrence, shifted form (n = m + 1), over ℚ. -/
theorem aperyU_recurrence_shift (m : ℕ) :
    ((m : ℚ) + 2) ^ 3 * aperyU (m + 2)
      - (34 * ((m : ℚ) + 1) ^ 3 + 51 * ((m : ℚ) + 1) ^ 2 + 27 * ((m : ℚ) + 1) + 5)
          * aperyU (m + 1)
      + ((m : ℚ) + 1) ^ 3 * aperyU m = 0 := by
  have hs := sum_recTerm m (m + 2)
  have hB : certB (m + 1) (m + 2) = 0 := by
    simp [certB, aCoeff_eq_zero (show m + 1 < m + 2 by omega)]
  rw [hB] at hs
  rw [aperyU_cast_eq (m + 2) (m + 2 + 1) le_rfl, aperyU_cast_eq (m + 1) (m + 2 + 1) (by omega),
    aperyU_cast_eq m (m + 2 + 1) (by omega)]
  rw [← hs]
  unfold recTerm
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]

/-- **Apéry's recurrence (A)** for uₙ = Σₖ C(n,k)²C(n+k,k)², for n ≥ 1, over ℚ. -/
theorem aperyU_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℚ) + 1) ^ 3 * aperyU (n + 1)
      = (34 * (n : ℚ) ^ 3 + 51 * (n : ℚ) ^ 2 + 27 * (n : ℚ) + 5) * aperyU n
          - (n : ℚ) ^ 3 * aperyU (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := aperyU_recurrence_shift m
  rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 - 1 = m from rfl]
  push_cast
  linear_combination h

/-- Lemma 8 for Apéry's numbers, unconditionally: 30·uₙ ≤ uₙ₊₁ for n ≥ 15. -/
theorem aperyU_growth_uncond (n : ℕ) (hn : 15 ≤ n) :
    30 * (aperyU n : ℝ) ≤ (aperyU (n + 1) : ℝ) := by
  refine aperyU_growth (fun k hk => ?_) n hn
  have hq := aperyU_recurrence k hk
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
  push_cast at hr
  linear_combination hr

end Zeta3
