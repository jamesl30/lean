import Mathlib
import Zeta3.AperyRec

/-!
# Apéry's recurrence for ζ(2) by the two steps of §11.6 of the report

Report: `zeta3/report/report.tex`, §11.6 "The same two steps for ζ(2)" (`\label{sec:11.6}`).

1. `zeta2_rec_of_three` — the paragraph "The recurrence": a two-index table `T` satisfying the row
   relation, the diagonal relation and the "no symmetry" identity has, on its diagonal
   `y n = T n n`, Apéry's ζ(2) recurrence `(n+1)² y(n+1) = (11n²+11n+3) y n + n² y(n-1)`, `n ≥ 1`.
2. `zeta2_wronskian_step`, `zeta2_wronskian_const`, `zeta2_series_partial` — paragraph
   "Smallness": `(k+1)² w(k+1) = -k² w k`, `k² w k = (-1)^(k-1) w 1`, and the telescoped finite sum.
3. `zeta2_growth_basic`, `zeta2_growth_three`, `zeta2_growth_three_all`, `zeta2_growth_ten`,
   `zeta2_growth_pow` — paragraph "Growth".
4. `U2 n m = Σₖ aₖ(n) C(m,k)` (the integers `U₂(n,m) = Pol[ρₙσₘ]` of the text):
   `U2_row`, `U2_diag`, `U2_third` (the three relations, as finite binomial-sum identities, proved by
   telescoping certificates in `k`, not by the partial-fraction argument of the text), and
   `zeta2B_recurrence` for `b n = Σₖ C(n,k)² C(n+k,k) = U2 n n`, with `b 0 = 1`, `b 1 = 3`,
   `b 2 = 19`, `b 3 = 147`, and the growth facts for `b`.

Differences from the text (all deliberate, listed so nothing is hidden):
* Item 1 is stated for an abstract table `T : ℕ → ℕ → K` over a field `K` with `2 ≠ 0` and
  `5 ≠ 0` (the text divides by 5 and 2). Only the instances of the three relations used by the text
  are used (row at `m = n`, diagonal at `n` and `n-1`, third at `n-1`).
* The row relation is used for `n ≥ 1`, the diagonal and third relations for all `n ≥ 0`, as in the text.
* Item 3 is stated for an abstract real sequence `u ≥ 0` satisfying the recurrence for `n ≥ 1`
  (the text uses `u*ₙ > 0`; only `≥ 0` is needed). The text's "`u*_{n+1} ≥ 3u*_n` for `n ≥ 0`"
  is `zeta2_growth_three_all`, with the hypothesis `3 u 0 ≤ u 1` (true for `b`: `b 1 = 3 b 0`).
* Item 4 proves the three relations only for the integers `U₂`, not for `Z₂(n,m)` (the sums with
  ζ(2)); the text derives them for both from the partial-fraction identities, which are not
  formalised here. The certificates: row `G(k) = -2(2n+1) k C(m,k) a_{k-1}(n)`, diagonal (times
  `(n+1)²`) `G(k) = -4 k (n+2-k) a_{k-1}(n+1) C(n+1,k)`; the third relation holds term by term.
  The recurrence for `b` is stated in `ℕ` (all its terms are nonnegative).
-/

set_option autoImplicit false

namespace Zeta3

/-! ## 1. The abstract elimination -/

/-- §11.6, "The recurrence": from the row relation (at `m = n`), the diagonal relation and the
identity `T(n,n) + T(n+1,n) = 2T(n,n+1)`, the diagonal `y n = T n n` satisfies Apéry's recurrence for
ζ(2): `(n+1)² y(n+1) = (11n²+11n+3) y n + n² y(n-1)` for `n ≥ 1`. -/
theorem zeta2_rec_of_three {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (T : ℕ → ℕ → K)
    (hrow : ∀ n m : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 2 * T (n + 1) m
        = (2 * (n : K) + 1) * (2 * (m : K) + 1) * T n m + (n : K) ^ 2 * T (n - 1) m)
    (hdiag : ∀ n : ℕ, 2 * T (n + 1) (n + 1) - T n n = 5 * T (n + 1) n)
    (hthird : ∀ n : ℕ, T n n + T (n + 1) n = 2 * T n (n + 1))
    (n : ℕ) (hn : 1 ≤ n) :
    ((n : K) + 1) ^ 2 * T (n + 1) (n + 1)
      = (11 * (n : K) ^ 2 + 11 * (n : K) + 3) * T n n + (n : K) ^ 2 * T (n - 1) (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hr := hrow (j + 1) (j + 1) hn
  have d1 := hdiag (j + 1)
  have d0 := hdiag j
  have t0 := hthird j
  simp only [Nat.add_sub_cancel] at hr ⊢
  have h20 : (20 : K) ≠ 0 := by
    have e : (20 : K) = 2 * 2 * 5 := by norm_num
    rw [e]
    exact mul_ne_zero (mul_ne_zero h2 h2) h5
  apply mul_left_cancel₀ h20
  push_cast at hr ⊢
  linear_combination 10 * ((j : K) + 1 + 1) ^ 2 * d1 + 50 * hr
    - 25 * ((j : K) + 1) ^ 2 * t0 - 5 * ((j : K) + 1) ^ 2 * d0

/-! ## 2. The Wronskian -/

/-- §11.6, "Smallness": for two solutions of the ζ(2) recurrence, `w k = u k z(k-1) - u(k-1) z k`
satisfies `(k+1)² w(k+1) = -k² w k` for `k ≥ 1`. -/
theorem zeta2_wronskian_step {K : Type*} [Field K] (u z : ℕ → K)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 2 * u (n + 1)
        = (11 * (n : K) ^ 2 + 11 * (n : K) + 3) * u n + (n : K) ^ 2 * u (n - 1))
    (hz : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 2 * z (n + 1)
        = (11 * (n : K) ^ 2 + 11 * (n : K) + 3) * z n + (n : K) ^ 2 * z (n - 1))
    (k : ℕ) (hk : 1 ≤ k) :
    ((k : K) + 1) ^ 2 * (u (k + 1) * z k - u k * z (k + 1))
      = -((k : K) ^ 2 * (u k * z (k - 1) - u (k - 1) * z k)) := by
  linear_combination z k * hu k hk - u k * hz k hk

/-- §11.6, "Smallness": `k² w k = (-1)^(k-1) w 1` for `k ≥ 1`. -/
theorem zeta2_wronskian_const {K : Type*} [Field K] (u z : ℕ → K)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 2 * u (n + 1)
        = (11 * (n : K) ^ 2 + 11 * (n : K) + 3) * u n + (n : K) ^ 2 * u (n - 1))
    (hz : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 2 * z (n + 1)
        = (11 * (n : K) ^ 2 + 11 * (n : K) + 3) * z n + (n : K) ^ 2 * z (n - 1))
    (k : ℕ) (hk : 1 ≤ k) :
    (k : K) ^ 2 * (u k * z (k - 1) - u (k - 1) * z k)
      = (-1) ^ (k - 1) * (u 1 * z 0 - u 0 * z 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h := zeta2_wronskian_step u z hu hz m hm
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel] at ih ⊢
    push_cast at h ih ⊢
    rw [h, ih, pow_succ]
    ring

/-- §11.6, "Smallness", finite form: if moreover `u` never vanishes and `K` has characteristic zero,
then for `n ≤ N`, `z n / u n - z N / u N = Σ_{n < k ≤ N} (-1)^(k-1) w₁ / (k² uₖ uₖ₋₁)`. -/
theorem zeta2_series_partial {K : Type*} [Field K] [CharZero K] (u z : ℕ → K)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 2 * u (n + 1)
        = (11 * (n : K) ^ 2 + 11 * (n : K) + 3) * u n + (n : K) ^ 2 * u (n - 1))
    (hz : ∀ n : ℕ, 1 ≤ n →
      ((n : K) + 1) ^ 2 * z (n + 1)
        = (11 * (n : K) ^ 2 + 11 * (n : K) + 3) * z n + (n : K) ^ 2 * z (n - 1))
    (hne : ∀ k, u k ≠ 0) (n N : ℕ) (hnN : n ≤ N) :
    z n / u n - z N / u N
      = ∑ k ∈ Finset.Ioc n N,
          (-1) ^ (k - 1) * (u 1 * z 0 - u 0 * z 1) / ((k : K) ^ 2 * u k * u (k - 1)) := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top hM, ← ih]
    have hw := zeta2_wronskian_const u z hu hz (M + 1) (by omega)
    rw [Nat.add_sub_cancel] at hw ⊢
    have h1 := hne M
    have h2 := hne (M + 1)
    have h3 : ((M + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← hw]
    field_simp
    ring

/-! ## 3. Growth -/

section Growth

variable (u : ℕ → ℝ)

/-- §11.6, "Growth", first inequality: a nonnegative solution satisfies
`(n+1)² u(n+1) ≥ (11n²+11n+3) u n` for `n ≥ 1`. -/
theorem zeta2_growth_basic
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 * u (n + 1)
        = (11 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 3) * u n + (n : ℝ) ^ 2 * u (n - 1))
    (hpos : ∀ n, 0 ≤ u n) (n : ℕ) (hn : 1 ≤ n) :
    (11 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 3) * u n ≤ ((n : ℝ) + 1) ^ 2 * u (n + 1) := by
  rw [hu n hn]
  have := mul_nonneg (pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 2) (hpos (n - 1))
  linarith

/-- §11.6, "Growth": `u(n+1) ≥ 3 u n` for `n ≥ 1` (as `11n²+11n+3 - 3(n+1)² = 8n²+5n ≥ 0`). -/
theorem zeta2_growth_three
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 * u (n + 1)
        = (11 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 3) * u n + (n : ℝ) ^ 2 * u (n - 1))
    (hpos : ∀ n, 0 ≤ u n) (n : ℕ) (hn : 1 ≤ n) : 3 * u n ≤ u (n + 1) := by
  have h := zeta2_growth_basic u hu hpos n hn
  set x : ℝ := (n : ℝ)
  have hx : 0 ≤ x := Nat.cast_nonneg n
  have key : 0 ≤ (x + 1) ^ 2 * (u (n + 1) - 3 * u n) := by
    have e : (x + 1) ^ 2 * (u (n + 1) - 3 * u n)
        = ((x + 1) ^ 2 * u (n + 1) - (11 * x ^ 2 + 11 * x + 3) * u n)
          + (8 * x ^ 2 + 5 * x) * u n := by ring
    rw [e]
    exact add_nonneg (by linarith) (mul_nonneg (by positivity) (hpos n))
  have hc : 0 < (x + 1) ^ 2 := by positivity
  have := (mul_nonneg_iff_of_pos_left hc).1 key
  linarith

/-- §11.6, "Growth": with `u 1 ≥ 3 u 0` (for the integers, `u*₁ = 3u*₀`), `u(n+1) ≥ 3 u n` for all
`n ≥ 0`. -/
theorem zeta2_growth_three_all
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 * u (n + 1)
        = (11 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 3) * u n + (n : ℝ) ^ 2 * u (n - 1))
    (hpos : ∀ n, 0 ≤ u n) (h01 : 3 * u 0 ≤ u 1) (n : ℕ) : 3 * u n ≤ u (n + 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simpa using h01
  · exact zeta2_growth_three u hu hpos n h

/-- §11.6, "Growth": `u(n+1) ≥ 10 u n` for `n ≥ 10` (as `11n²+11n+3 - 10(n+1)² = n²-9n-7 ≥ 3`). -/
theorem zeta2_growth_ten
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 * u (n + 1)
        = (11 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 3) * u n + (n : ℝ) ^ 2 * u (n - 1))
    (hpos : ∀ n, 0 ≤ u n) (n : ℕ) (hn : 10 ≤ n) : 10 * u n ≤ u (n + 1) := by
  have h := zeta2_growth_basic u hu hpos n (by omega)
  have hx10 : (10 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := (n : ℝ)
  have hp : 0 ≤ x ^ 2 - 9 * x - 7 := by
    have e : x ^ 2 - 9 * x - 7 = (x - 10) ^ 2 + 11 * (x - 10) + 3 := by ring
    rw [e]
    have : 0 ≤ x - 10 := by linarith
    positivity
  have key : 0 ≤ (x + 1) ^ 2 * (u (n + 1) - 10 * u n) := by
    have e : (x + 1) ^ 2 * (u (n + 1) - 10 * u n)
        = ((x + 1) ^ 2 * u (n + 1) - (11 * x ^ 2 + 11 * x + 3) * u n)
          + (x ^ 2 - 9 * x - 7) * u n := by ring
    rw [e]
    exact add_nonneg (by linarith) (mul_nonneg hp (hpos n))
  have hc : 0 < (x + 1) ^ 2 := by positivity
  have := (mul_nonneg_iff_of_pos_left hc).1 key
  linarith

/-- §11.6, "Growth": `u n ≥ 10^(n-10) u 10` for `n ≥ 10`. -/
theorem zeta2_growth_pow
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 * u (n + 1)
        = (11 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 3) * u n + (n : ℝ) ^ 2 * u (n - 1))
    (hpos : ∀ n, 0 ≤ u n) (n : ℕ) (hn : 10 ≤ n) : (10 : ℝ) ^ (n - 10) * u 10 ≤ u n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hs := zeta2_growth_ten u hu hpos m hm
    have e : m + 1 - 10 = (m - 10) + 1 := by omega
    rw [e, pow_succ]
    nlinarith

end Growth

/-! ## 4. The integers `U₂(n,m) = Σₖ aₖ(n) C(m,k)` -/

/-- `U₂(n,m) = Σₖ aₖ(n)·C(m,k)` with `aₖ(n) = C(n,k)C(n+k,k)` (terms with `k > n` vanish). -/
def U2 (n m : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), aCoeff n k * m.choose k

/-- Apéry's numbers for ζ(2): `b n = Σₖ C(n,k)² C(n+k,k)`. -/
def zeta2B (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k

theorem U2_diag_eq (n : ℕ) : U2 n n = zeta2B n := by
  unfold U2 zeta2B aCoeff
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem zeta2B_zero : zeta2B 0 = 1 := by decide

theorem zeta2B_one : zeta2B 1 = 3 := by decide

theorem zeta2B_two : zeta2B 2 = 19 := by decide

theorem zeta2B_three : zeta2B 3 = 147 := by decide

/-- `C(m,k+1)(k+1) = C(m,k)(m-k)` over ℚ, for all `k` (both sides vanish for `k ≥ m`). -/
theorem choose_succ_right_q (m k : ℕ) :
    (m.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (m.choose k : ℚ) * ((m : ℚ) - k) := by
  rcases le_or_gt k m with h | h
  · have e := Nat.choose_succ_right_eq m k
    have := congrArg (fun x : ℕ => (x : ℚ)) e
    push_cast [Nat.cast_sub h] at this
    exact this
  · simp [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_lt h)]

/-- `C(n+1,k+1)(k+1) = (n+1)C(n,k)` over ℚ. -/
theorem succ_choose_succ_q (n k : ℕ) :
    ((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((n : ℚ) + 1) * (n.choose k : ℚ) := by
  have e := Nat.add_one_mul_choose_eq n k
  exact_mod_cast e.symm

/-- `U₂(n,m)` as a rational sum over any range `k < N` with `N ≥ n + 1`. -/
theorem U2_cast_eq (n m N : ℕ) (h : n + 1 ≤ N) :
    (U2 n m : ℚ) = ∑ k ∈ Finset.range N, (aCoeff n k : ℚ) * (m.choose k : ℚ) := by
  unfold U2
  push_cast
  apply Finset.sum_subset (Finset.range_subset_range.2 h)
  intro j _ hj
  have : n < j := by simpa using hj
  simp [aCoeff_eq_zero this]

/-! ### The row relation -/

/-- The `k`-th term of the row operator at `n = j + 1`:
`(n+1)² aₖ(n+1) C(m,k) - (2n+1)(2m+1) aₖ(n) C(m,k) - n² aₖ(n-1) C(m,k)`. -/
def row2Term (j m k : ℕ) : ℚ :=
  ((j : ℚ) + 2) ^ 2 * (aCoeff (j + 2) k : ℚ) * (m.choose k : ℚ)
    - (2 * (j : ℚ) + 3) * (2 * (m : ℚ) + 1) * (aCoeff (j + 1) k : ℚ) * (m.choose k : ℚ)
    - ((j : ℚ) + 1) ^ 2 * (aCoeff j k : ℚ) * (m.choose k : ℚ)

/-- The row certificate at `n = j + 1`: `G(k) = -2(2n+1) k C(m,k) a_{k-1}(n)` (zero at `k = 0`). -/
def rowG (j m k : ℕ) : ℚ :=
  -2 * (2 * (j : ℚ) + 3) * (k : ℚ) * (m.choose k : ℚ) * (aCoeff (j + 1) (k - 1) : ℚ)

theorem row2Term_zero (j m : ℕ) : row2Term j m 0 = rowG j m 1 - rowG j m 0 := by
  simp only [row2Term, rowG, aCoeff, Nat.choose_zero_right, Nat.choose_one_right, add_zero,
    Nat.sub_self]
  push_cast
  ring

theorem row2Term_succ (j m k : ℕ) :
    row2Term j m (k + 1) = rowG j m (k + 1 + 1) - rowG j m (k + 1) := by
  have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have hK2 : ((k : ℚ) + 1 + 1) ≠ 0 := by positivity
  have h1 := aCoeff_succ_succ (j + 1) k
  have h2 := aCoeff_succ_right (j + 1) k
  have h3 := aCoeff_down j k
  have hc := choose_succ_right_q m (k + 1)
  push_cast at h1 h2 hc
  have e1 : (aCoeff (j + 2) (k + 1) : ℚ)
      = (aCoeff (j + 1) k : ℚ) * ((j : ℚ) + 1 + k + 2) * ((j : ℚ) + 1 + k + 1)
          / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h1
  have e2 : (aCoeff (j + 1) (k + 1) : ℚ)
      = (aCoeff (j + 1) k : ℚ) * ((j : ℚ) + 1 - k) * ((j : ℚ) + 1 + k + 1)
          / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h2
  have e3 : (aCoeff j (k + 1) : ℚ)
      = (aCoeff (j + 1) k : ℚ) * ((j : ℚ) + 1 - k) * ((j : ℚ) - k) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h3
  have ec : (m.choose (k + 1 + 1) : ℚ)
      = (m.choose (k + 1) : ℚ) * ((m : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1 + 1) := by
    rw [eq_div_iff hK2]; exact hc
  unfold row2Term rowG
  rw [show k + 1 + 1 - 1 = k + 1 from rfl, show k + 1 - 1 = k from rfl, e1, e2, e3, ec]
  push_cast
  field_simp
  ring

/-- Telescoping: `Σ_{k ≤ K} row2Term j m k = rowG j m (K+1)`. -/
theorem sum_row2Term (j m K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), row2Term j m k = rowG j m (K + 1) := by
  induction K with
  | zero =>
    rw [Finset.sum_range_one, row2Term_zero]
    simp [rowG]
  | succ K ih => rw [Finset.sum_range_succ, ih, row2Term_succ]; ring

/-- The row relation for `U₂` at `n = j + 1`, over ℚ. -/
theorem U2_row_shift (j m : ℕ) :
    ((j : ℚ) + 2) ^ 2 * U2 (j + 2) m - (2 * (j : ℚ) + 3) * (2 * (m : ℚ) + 1) * U2 (j + 1) m
      - ((j : ℚ) + 1) ^ 2 * U2 j m = 0 := by
  have hs := sum_row2Term j m (j + 2)
  have hG : rowG j m (j + 2 + 1) = 0 := by
    unfold rowG
    rw [show j + 2 + 1 - 1 = j + 2 from rfl, aCoeff_eq_zero (show j + 1 < j + 2 by omega)]
    simp
  rw [hG] at hs
  rw [U2_cast_eq (j + 2) m (j + 2 + 1) le_rfl, U2_cast_eq (j + 1) m (j + 2 + 1) (by omega),
    U2_cast_eq j m (j + 2 + 1) (by omega)]
  rw [← hs, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold row2Term
  ring

/-- **Row relation** (§11.6, "Along a row", for `T = U₂`): for `n ≥ 1` and every `m`,
`(n+1)² U₂(n+1,m) = (2n+1)(2m+1) U₂(n,m) + n² U₂(n-1,m)`. -/
theorem U2_row (n m : ℕ) (hn : 1 ≤ n) :
    ((n : ℚ) + 1) ^ 2 * (U2 (n + 1) m : ℚ)
      = (2 * (n : ℚ) + 1) * (2 * (m : ℚ) + 1) * (U2 n m : ℚ) + (n : ℚ) ^ 2 * (U2 (n - 1) m : ℚ) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have h := U2_row_shift j m
  rw [show j + 1 + 1 = j + 2 from rfl, Nat.add_sub_cancel]
  push_cast
  linear_combination h

/-! ### The diagonal relation -/

/-- The `k`-th term of `(n+1)²[2U₂(n+1,n+1) - U₂(n,n) - 5U₂(n+1,n)]`. -/
def diagTerm (n k : ℕ) : ℚ :=
  ((n : ℚ) + 1) ^ 2 * (2 * (aCoeff (n + 1) k : ℚ) * ((n + 1).choose k : ℚ)
    - (aCoeff n k : ℚ) * (n.choose k : ℚ) - 5 * (aCoeff (n + 1) k : ℚ) * (n.choose k : ℚ))

/-- The diagonal certificate: `G(k) = -4 k (n+2-k) a_{k-1}(n+1) C(n+1,k)` (zero at `k = 0`). -/
def diagG (n k : ℕ) : ℚ :=
  -4 * (k : ℚ) * ((n : ℚ) + 2 - k) * (aCoeff (n + 1) (k - 1) : ℚ) * ((n + 1).choose k : ℚ)

theorem diagTerm_zero (n : ℕ) : diagTerm n 0 = diagG n 1 - diagG n 0 := by
  simp only [diagTerm, diagG, aCoeff, Nat.choose_zero_right, Nat.choose_one_right, add_zero,
    Nat.sub_self]
  push_cast
  ring

theorem diagG_succ (n k : ℕ) :
    diagG n (k + 1)
      = -4 * ((k : ℚ) + 1) * ((aCoeff n k : ℚ) * ((n : ℚ) + 1 + k))
          * ((n + 1).choose (k + 1) : ℚ) := by
  unfold diagG
  rw [show k + 1 - 1 = k from rfl, ← aCoeff_succ_left n k]
  push_cast
  ring

theorem diagTerm_succ (n k : ℕ) :
    diagTerm n (k + 1) = diagG n (k + 1 + 1) - diagG n (k + 1) := by
  have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have hK1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hK2 : ((k : ℚ) + 1 + 1) ≠ 0 := by positivity
  rw [diagG_succ n k]
  have h1 := aCoeff_succ_succ n k
  have h2 := aCoeff_succ_right n k
  have hc1 := succ_choose_succ_q n k
  have hc2 := choose_succ_right_q n k
  have hc3 := choose_succ_right_q (n + 1) (k + 1)
  push_cast at hc3
  have e1 : (aCoeff (n + 1) (k + 1) : ℚ)
      = (aCoeff n k : ℚ) * ((n : ℚ) + k + 2) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h1
  have e2 : (aCoeff n (k + 1) : ℚ)
      = (aCoeff n k : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [eq_div_iff hK]; exact h2
  have ec3 : ((n + 1).choose (k + 1 + 1) : ℚ)
      = ((n + 1).choose (k + 1) : ℚ) * ((n : ℚ) + 1 - ((k : ℚ) + 1)) / ((k : ℚ) + 1 + 1) := by
    rw [eq_div_iff hK2]; exact hc3
  have ec1 : ((n + 1).choose (k + 1) : ℚ) = ((n : ℚ) + 1) * (n.choose k : ℚ) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hK1]; exact hc1
  have ec2 : (n.choose (k + 1) : ℚ) = (n.choose k : ℚ) * ((n : ℚ) - k) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hK1]; exact hc2
  unfold diagTerm diagG
  rw [show k + 1 + 1 - 1 = k + 1 from rfl, ec3, e1, e2, ec1, ec2]
  push_cast
  field_simp
  ring

/-- Telescoping: `Σ_{k ≤ K} diagTerm n k = diagG n (K+1)`. -/
theorem sum_diagTerm (n K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), diagTerm n k = diagG n (K + 1) := by
  induction K with
  | zero =>
    rw [Finset.sum_range_one, diagTerm_zero]
    simp [diagG]
  | succ K ih => rw [Finset.sum_range_succ, ih, diagTerm_succ]; ring

/-- **Diagonal relation** (§11.6, "Along the diagonal", for `T = U₂`): for every `n ≥ 0`,
`2 U₂(n+1,n+1) - U₂(n,n) = 5 U₂(n+1,n)`. -/
theorem U2_diag (n : ℕ) :
    2 * (U2 (n + 1) (n + 1) : ℚ) - (U2 n n : ℚ) = 5 * (U2 (n + 1) n : ℚ) := by
  have hs := sum_diagTerm n (n + 2)
  have hG : diagG n (n + 2 + 1) = 0 := by
    unfold diagG
    rw [Nat.choose_eq_zero_of_lt (show n + 1 < n + 2 + 1 by omega)]
    simp
  rw [hG] at hs
  have hn : ((n : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  rw [U2_cast_eq (n + 1) (n + 1) (n + 2 + 1) (by omega), U2_cast_eq n n (n + 2 + 1) (by omega),
    U2_cast_eq (n + 1) n (n + 2 + 1) (by omega)]
  have key : ((n : ℚ) + 1) ^ 2 *
      (2 * ∑ k ∈ Finset.range (n + 2 + 1), (aCoeff (n + 1) k : ℚ) * ((n + 1).choose k : ℚ)
        - ∑ k ∈ Finset.range (n + 2 + 1), (aCoeff n k : ℚ) * (n.choose k : ℚ)
        - 5 * ∑ k ∈ Finset.range (n + 2 + 1), (aCoeff (n + 1) k : ℚ) * (n.choose k : ℚ))
      = ∑ k ∈ Finset.range (n + 2 + 1), diagTerm n k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold diagTerm
    ring
  rw [hs] at key
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h hn
  · linarith

/-! ### The third relation (term by term) -/

theorem third_term (n k : ℕ) :
    (aCoeff n k : ℚ) * (n.choose k : ℚ) + (aCoeff (n + 1) k : ℚ) * (n.choose k : ℚ)
      = 2 * ((aCoeff n k : ℚ) * ((n + 1).choose k : ℚ)) := by
  cases k with
  | zero => simp [aCoeff]; norm_num
  | succ k =>
    have hK : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
    have hK1 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h1 := aCoeff_succ_succ n k
    have h2 := aCoeff_succ_right n k
    have hc1 := succ_choose_succ_q n k
    have hc2 := choose_succ_right_q n k
    have e1 : (aCoeff (n + 1) (k + 1) : ℚ)
        = (aCoeff n k : ℚ) * ((n : ℚ) + k + 2) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
      rw [eq_div_iff hK]; exact h1
    have e2 : (aCoeff n (k + 1) : ℚ)
        = (aCoeff n k : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2 := by
      rw [eq_div_iff hK]; exact h2
    have ec1 : ((n + 1).choose (k + 1) : ℚ)
        = ((n : ℚ) + 1) * (n.choose k : ℚ) / ((k : ℚ) + 1) := by
      rw [eq_div_iff hK1]; exact hc1
    have ec2 : (n.choose (k + 1) : ℚ) = (n.choose k : ℚ) * ((n : ℚ) - k) / ((k : ℚ) + 1) := by
      rw [eq_div_iff hK1]; exact hc2
    rw [e1, e2, ec1, ec2]
    field_simp
    ring

/-- **Third relation** (§11.6, "Second change: no symmetry", for `T = U₂`): for every `n ≥ 0`,
`U₂(n,n) + U₂(n+1,n) = 2 U₂(n,n+1)`. -/
theorem U2_third (n : ℕ) :
    (U2 n n : ℚ) + (U2 (n + 1) n : ℚ) = 2 * (U2 n (n + 1) : ℚ) := by
  rw [U2_cast_eq n n (n + 2) (by omega), U2_cast_eq (n + 1) n (n + 2) le_rfl,
    U2_cast_eq n (n + 1) (n + 2) (by omega), ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => third_term n k)

/-! ### Apéry's recurrence for ζ(2) -/

/-- **Apéry's recurrence for ζ(2)** (§11.6, "The recurrence", for the integers `U₂(n,n)`):
for `n ≥ 1`, `(n+1)² b(n+1) = (11n²+11n+3) b n + n² b(n-1)`, with `b n = Σₖ C(n,k)² C(n+k,k)`. -/
theorem zeta2B_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) ^ 2 * zeta2B (n + 1) = (11 * n ^ 2 + 11 * n + 3) * zeta2B n + n ^ 2 * zeta2B (n - 1) := by
  have h := zeta2_rec_of_three (K := ℚ) (by norm_num) (by norm_num) (fun a b => (U2 a b : ℚ))
    U2_row U2_diag U2_third n hn
  simp only [U2_diag_eq] at h
  exact_mod_cast h

/-- The recurrence for `b` over ℝ, in the form used by the growth lemmas. -/
theorem zeta2B_recurrence_real (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ 2 * (zeta2B (n + 1) : ℝ)
      = (11 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 3) * (zeta2B n : ℝ)
          + (n : ℝ) ^ 2 * (zeta2B (n - 1) : ℝ) := by
  have h := zeta2B_recurrence n hn
  exact_mod_cast h

theorem zeta2B_pos (n : ℕ) : 1 ≤ zeta2B n := by
  unfold zeta2B
  calc 1 = n.choose 0 ^ 2 * (n + 0).choose 0 := by simp
    _ ≤ ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k :=
      Finset.single_le_sum (f := fun k => n.choose k ^ 2 * (n + k).choose k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.succ_pos n))

/-- "Growth" for the integers: `b(n+1) ≥ 3 b n` for all `n ≥ 0`. -/
theorem zeta2B_growth_three (n : ℕ) : 3 * zeta2B n ≤ zeta2B (n + 1) := by
  have h := zeta2_growth_three_all (fun k => (zeta2B k : ℝ)) zeta2B_recurrence_real
    (fun k => Nat.cast_nonneg _) (by simp [zeta2B_zero, zeta2B_one]) n
  exact_mod_cast h

/-- "Growth" for the integers: `b(n+1) ≥ 10 b n` for `n ≥ 10`, and `b n ≥ 10^(n-10)` for `n ≥ 10`. -/
theorem zeta2B_growth_ten (n : ℕ) (hn : 10 ≤ n) :
    10 * zeta2B n ≤ zeta2B (n + 1) ∧ 10 ^ (n - 10) ≤ zeta2B n := by
  constructor
  · have h := zeta2_growth_ten (fun k => (zeta2B k : ℝ)) zeta2B_recurrence_real
      (fun k => Nat.cast_nonneg _) n hn
    exact_mod_cast h
  · have h := zeta2_growth_pow (fun k => (zeta2B k : ℝ)) zeta2B_recurrence_real
      (fun k => Nat.cast_nonneg _) n hn
    have h10 : (1 : ℝ) ≤ zeta2B 10 := by exact_mod_cast zeta2B_pos 10
    have hp : (0 : ℝ) ≤ 10 ^ (n - 10) := by positivity
    have : ((10 ^ (n - 10) : ℕ) : ℝ) ≤ (zeta2B n : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this

-- CLAIMED: Zeta3.zeta2_rec_of_three, Zeta3.zeta2_wronskian_step, Zeta3.zeta2_wronskian_const
-- CLAIMED: Zeta3.zeta2_series_partial, Zeta3.zeta2_growth_basic, Zeta3.zeta2_growth_three
-- CLAIMED: Zeta3.zeta2_growth_three_all, Zeta3.zeta2_growth_ten, Zeta3.zeta2_growth_pow
-- CLAIMED: Zeta3.U2_row, Zeta3.U2_diag, Zeta3.U2_third, Zeta3.zeta2B_recurrence
-- CLAIMED: Zeta3.zeta2B_zero, Zeta3.zeta2B_one, Zeta3.zeta2B_two, Zeta3.zeta2B_three
-- CLAIMED: Zeta3.zeta2B_growth_three, Zeta3.zeta2B_growth_ten

end Zeta3
