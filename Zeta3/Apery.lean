import Mathlib
import Zeta3.Growth

/-!
# Apéry's numbers (Lemma 2(i) of the text) and the growth step for them

`aCoeff n k = C(n,k)·C(n+k,k)` and `aperyU n = Σ_{k=0}^{n} aCoeff n k ^ 2`.
We prove `aperyU n > 0`, `aperyU n ≤ aperyU (n+1)`, the values `u₀ = 1`, `u₁ = 5`, `u₂ = 73`,
and, assuming that `aperyU` satisfies Apéry's recurrence (A), the growth step of Lemma 8
(`growth_step` of `Zeta3.Growth`) for it. That (A) holds for `aperyU` is not proved here.
-/

namespace Zeta3

/-- aₖ(n) = C(n,k)·C(n+k,k). -/
def aCoeff (n k : ℕ) : ℕ := n.choose k * (n + k).choose k

/-- Apéry's numbers uₙ = Σ_{k=0}^{n} aₖ(n)². -/
def aperyU (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), aCoeff n k ^ 2

/-- uₙ > 0: the term k = 0 equals 1. -/
theorem aperyU_pos (n : ℕ) : 0 < aperyU n := by
  unfold aperyU
  have h0 : aCoeff n 0 ^ 2 = 1 := by simp [aCoeff]
  calc 0 < aCoeff n 0 ^ 2 := by rw [h0]; norm_num
    _ ≤ ∑ k ∈ Finset.range (n + 1), aCoeff n k ^ 2 :=
      Finset.single_le_sum (f := fun k => aCoeff n k ^ 2) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.succ_pos n))

/-- aₖ(n) ≤ aₖ(n+1) (both binomial factors grow with the upper index). -/
theorem aCoeff_mono (n k : ℕ) : aCoeff n k ≤ aCoeff (n + 1) k := by
  unfold aCoeff
  exact Nat.mul_le_mul (Nat.choose_le_choose k (Nat.le_succ n))
    (Nat.choose_le_choose k (by omega))

/-- uₙ ≤ uₙ₊₁: each term grows, and uₙ₊₁ has one more (nonnegative) term. -/
theorem aperyU_mono (n : ℕ) : aperyU n ≤ aperyU (n + 1) := by
  unfold aperyU
  rw [Finset.sum_range_succ _ (n + 1)]
  refine le_trans ?_ (Nat.le_add_right _ _)
  exact Finset.sum_le_sum fun k _ => Nat.pow_le_pow_left (aCoeff_mono n k) 2

theorem aperyU_zero : aperyU 0 = 1 := by decide

theorem aperyU_one : aperyU 1 = 5 := by decide

theorem aperyU_two : aperyU 2 = 73 := by decide

/-- Lemma 8 for Apéry's numbers, given the recurrence (A) for them as a hypothesis. -/
theorem aperyU_growth
    (hA : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 3 * (aperyU (n + 1) : ℝ)
        - (34 * (n : ℝ) ^ 3 + 51 * (n : ℝ) ^ 2 + 27 * (n : ℝ) + 5) * (aperyU n : ℝ)
        + (n : ℝ) ^ 3 * (aperyU (n - 1) : ℝ) = 0)
    (n : ℕ) (hn : 15 ≤ n) : 30 * (aperyU n : ℝ) ≤ (aperyU (n + 1) : ℝ) := by
  refine growth_step (fun n => (aperyU n : ℝ)) hA (fun n => Nat.cast_nonneg _) ?_ n hn
  intro m hm
  have h := aperyU_mono (m - 1)
  rw [Nat.sub_add_cancel hm] at h
  exact_mod_cast h

end Zeta3
