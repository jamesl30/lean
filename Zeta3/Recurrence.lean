import Mathlib

/-!
# Apéry's recurrence from the row and diagonal relations (Proposition 6 of the report)

The algebraic step of Proposition 6: if a symmetric two-index table `f` satisfies the row relation
(5.4) and the diagonal relation (5.5), then its diagonal `y n = f n n` satisfies Apéry's recurrence

  `(n+1)³ y (n+1) - (34n³+51n²+27n+5) y n + n³ y (n-1) = 0`   (n ≥ 1).

Only the instance `m = n` of (5.4) is used, together with (5.5) at `n` and at `n - 1`.

The second declaration is the Wronskian step of Proposition 8: two solutions of (A) have a
"Wronskian" `w k = u k * z (k-1) - u (k-1) * z k` with `(k+1)³ w (k+1) = k³ w k`.
-/

namespace Zeta3

/-- Proposition 6, the algebraic step: a symmetric two-index table satisfying the row relation
(5.4) and the diagonal relation (5.5) satisfies Apéry's recurrence (A) on its diagonal. -/
theorem apery_of_row_and_six {K : Type*} [Field K] (f : ℕ → ℕ → K)
    (hsymm : ∀ n m, f n m = f m n)
    (hrow : ∀ n m : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 3 * f (n + 1) m + (n : K) ^ 3 * f (n - 1) m
        = ((n : K) ^ 3 + ((n : K) + 1) ^ 3
            + 2 * (m : K) * ((m : K) + 1) * (2 * (n : K) + 1)) * f n m)
    (hsix : ∀ n : ℕ, f (n + 1) (n + 1) + f n n = 6 * f (n + 1) n)
    (n : ℕ) (hn : 1 ≤ n) :
    ((n : K) + 1) ^ 3 * f (n + 1) (n + 1)
      - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * f n n
      + (n : K) ^ 3 * f (n - 1) (n - 1) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hr := hrow (1 + k) (1 + k) hn
  have h1 := hsix (1 + k)
  have h0 := hsix k
  have hs := hsymm k (1 + k)
  have e : 1 + k - 1 = k := by omega
  have e2 : 1 + k + 1 = k + 1 + 1 := by omega
  have e3 : 1 + k = k + 1 := by omega
  rw [e] at hr ⊢
  rw [e2, e3] at hr h1 ⊢
  rw [e3] at hs
  rw [hs] at hr
  push_cast at hr h1 h0 ⊢
  linear_combination (6 : K) * hr + ((k : K) + 1 + 1) ^ 3 * h1 + ((k : K) + 1) ^ 3 * h0

/-- Proposition 8, the Wronskian step: if `u` and `z` both satisfy Apéry's recurrence (A) for all
`n ≥ 1`, then `w k = u k * z (k-1) - u (k-1) * z k` satisfies `(k+1)³ w (k+1) = k³ w k` for `k ≥ 1`. -/
theorem wronskian_step {K : Type*} [Field K] (u z : ℕ → K)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 3 * u (n + 1)
        - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * u n
        + (n : K) ^ 3 * u (n - 1) = 0)
    (hz : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 3 * z (n + 1)
        - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * z n
        + (n : K) ^ 3 * z (n - 1) = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    ((k : K) + 1) ^ 3 * (u (k + 1) * z k - u k * z (k + 1))
      = (k : K) ^ 3 * (u k * z (k - 1) - u (k - 1) * z k) := by
  linear_combination z k * hu k hk - u k * hz k hk

end Zeta3
