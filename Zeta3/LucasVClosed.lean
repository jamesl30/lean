import Mathlib
import Zeta3.Apery

-- CLAIMED: Zeta3.VClosed.aperyV_closed_of_beta, Zeta3.VClosed.aperyBeta_closed_small, Zeta3.VClosed.aperyV_closed_small, Zeta3.VClosed.aperyV_one, Zeta3.VClosed.aperyV_two, Zeta3.VClosed.aperyV_three

set_option autoImplicit false

namespace Zeta3.VClosed
open Finset

/-- `harm s k = H_k^{(s)} = ∑_{i=1}^{k} 1/i^s` (copied unchanged from `LucasV.lean`). -/
def harm (s k : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 k, 1 / (i : ℚ) ^ s

/-- The rational part `vₙ` of Apéry's linear form `uₙ ζ(3) − vₙ`, literally as in Lemma 2(ii)
(copied unchanged from `LucasV.lean`). -/
def aperyV (n : ℕ) : ℚ :=
  (∑ k ∈ range (n + 1), (aCoeff n k : ℚ) ^ 2 * harm 3 k)
  + ∑ k ∈ range (n + 1), ∑ l ∈ (range (n + 1)).erase k,
      (-1 : ℚ) ^ (k + l) * (aCoeff n k : ℚ) * (aCoeff n l : ℚ) * harm 2 k / ((l : ℚ) - (k : ℚ))

/-- `δ_j(n) = 2H_j − H_{n+j} − H_{n−j}` (natural subtraction `n - j`; used only for `j ≤ n`). -/
def aperyDelta (n j : ℕ) : ℚ := 2 * harm 1 j - harm 1 (n + j) - harm 1 (n - j)

example : harm 2 3 = 49 / 36 := by decide +kernel
example : aperyDelta 1 0 = -2 := by decide +kernel
example : aperyDelta 1 1 = 1 / 2 := by decide +kernel
example : aperyDelta 2 1 = -5 / 6 := by decide +kernel

theorem aperyV_one : aperyV 1 = 6 := by decide +kernel
theorem aperyV_two : aperyV 2 = 351 / 4 := by decide +kernel
theorem aperyV_three : aperyV 3 = 62531 / 36 := by decide +kernel

/-- Lemma D, closed form (Vδ), deduced from the residue identity for `β_j(n)` taken as the
explicit hypothesis `hD`. -/
theorem aperyV_closed_of_beta (n : ℕ)
    (hD : ∀ j ≤ n, ∑ l ∈ (range (n + 1)).erase j,
        (-1 : ℚ) ^ l * (aCoeff n l : ℚ) / ((l : ℚ) - (j : ℚ))
      = (-1 : ℚ) ^ j * (aCoeff n j : ℚ) * aperyDelta n j) :
    aperyV n = ∑ j ∈ range (n + 1),
      (aCoeff n j : ℚ) ^ 2 * (harm 3 j + aperyDelta n j * harm 2 j) := by
  have key : ∀ k ∈ range (n + 1), ∑ l ∈ (range (n + 1)).erase k,
      (-1 : ℚ) ^ (k + l) * (aCoeff n k : ℚ) * (aCoeff n l : ℚ) * harm 2 k / ((l : ℚ) - (k : ℚ))
        = (aCoeff n k : ℚ) ^ 2 * (aperyDelta n k * harm 2 k) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hfac : ∑ l ∈ (range (n + 1)).erase k,
        (-1 : ℚ) ^ (k + l) * (aCoeff n k : ℚ) * (aCoeff n l : ℚ) * harm 2 k / ((l : ℚ) - (k : ℚ))
        = ((-1 : ℚ) ^ k * (aCoeff n k : ℚ) * harm 2 k) * ∑ l ∈ (range (n + 1)).erase k,
            (-1 : ℚ) ^ l * (aCoeff n l : ℚ) / ((l : ℚ) - (k : ℚ)) := by
      rw [mul_sum]
      refine sum_congr rfl (fun l _ => ?_)
      rw [pow_add]
      ring
    rw [hfac, hD k hkn]
    have hsq : ((-1 : ℚ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    calc (-1 : ℚ) ^ k * (aCoeff n k : ℚ) * harm 2 k * ((-1 : ℚ) ^ k * (aCoeff n k : ℚ) * aperyDelta n k)
        = ((-1 : ℚ) ^ k) ^ 2 * ((aCoeff n k : ℚ) ^ 2 * (aperyDelta n k * harm 2 k)) := by ring
      _ = (aCoeff n k : ℚ) ^ 2 * (aperyDelta n k * harm 2 k) := by rw [hsq, one_mul]
  unfold aperyV
  rw [sum_congr rfl key, ← sum_add_distrib]
  refine sum_congr rfl (fun _ _ => ?_)
  ring

/-- The residue identity `β_j(n) = (−1)^j a_j(n) δ_j(n)` for `n ≤ 5`, by kernel computation. -/
theorem aperyBeta_closed_small : ∀ n ≤ 5, ∀ j ≤ n,
    ∑ l ∈ (range (n + 1)).erase j, (-1 : ℚ) ^ l * (aCoeff n l : ℚ) / ((l : ℚ) - (j : ℚ))
      = (-1 : ℚ) ^ j * (aCoeff n j : ℚ) * aperyDelta n j := by
  decide +kernel

/-- The closed form (Vδ) unconditionally for `n ≤ 5`. -/
theorem aperyV_closed_small : ∀ n ≤ 5, aperyV n = ∑ j ∈ range (n + 1),
      (aCoeff n j : ℚ) ^ 2 * (harm 3 j + aperyDelta n j * harm 2 j) :=
  fun n hn => aperyV_closed_of_beta n (aperyBeta_closed_small n hn)

end Zeta3.VClosed