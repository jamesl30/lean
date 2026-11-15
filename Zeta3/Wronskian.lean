import Mathlib
import Zeta3.Recurrence

/-!
# The Wronskian of two solutions of Apéry's recurrence (Proposition 7 of the text)

If `u` and `z` both satisfy Apéry's recurrence (A) for all `n ≥ 1`, then
`w k = u k * z (k-1) - u (k-1) * z k` satisfies `k³ wₖ = w₁` for every `k ≥ 1`
(`wronskian_const`, by induction from `wronskian_step`). If moreover `u` never vanishes and the
field has characteristic zero, this telescopes to the finite form of the series of Proposition 7
(`series_partial`):

  `z n / u n - z N / u N = ∑_{n < k ≤ N} w₁ / (k³ uₖ uₖ₋₁)`   for `n ≤ N`.
-/

namespace Zeta3

/-- Proposition 7, `k³ wₖ = w₁`: for two solutions `u`, `z` of Apéry's recurrence (A),
`k³ (uₖ zₖ₋₁ - uₖ₋₁ zₖ) = u₁ z₀ - u₀ z₁` for every `k ≥ 1`. -/
theorem wronskian_const {K : Type*} [Field K] (u z : ℕ → K)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 3 * u (n + 1)
        - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * u n
        + (n : K) ^ 3 * u (n - 1) = 0)
    (hz : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 3 * z (n + 1)
        - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * z n
        + (n : K) ^ 3 * z (n - 1) = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (k : K) ^ 3 * (u k * z (k - 1) - u (k - 1) * z k) = u 1 * z 0 - u 0 * z 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h := wronskian_step u z hu hz m hm
    rw [Nat.add_sub_cancel]
    push_cast
    rw [h, ih]

/-- Proposition 7, finite form of the series: if moreover `u` never vanishes and `K` has
characteristic zero, then for `n ≤ N`,
`z n / u n - z N / u N = ∑_{k ∈ (n, N]} (u₁ z₀ - u₀ z₁) / (k³ uₖ uₖ₋₁)`. -/
theorem series_partial {K : Type*} [Field K] [CharZero K] (u z : ℕ → K)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 3 * u (n + 1)
        - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * u n
        + (n : K) ^ 3 * u (n - 1) = 0)
    (hz : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 3 * z (n + 1)
        - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * z n
        + (n : K) ^ 3 * z (n - 1) = 0)
    (hne : ∀ k, u k ≠ 0) (n N : ℕ) (hnN : n ≤ N) :
    z n / u n - z N / u N
      = ∑ k ∈ Finset.Ioc n N, (u 1 * z 0 - u 0 * z 1) / ((k : K) ^ 3 * u k * u (k - 1)) := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top hM, ← ih]
    have hw := wronskian_const u z hu hz (M + 1) (by omega)
    rw [Nat.add_sub_cancel] at hw ⊢
    have h1 := hne M
    have h2 := hne (M + 1)
    have h3 : ((M + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← hw]
    field_simp
    ring

end Zeta3
