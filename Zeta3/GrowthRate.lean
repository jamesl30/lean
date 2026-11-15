import Mathlib
import Zeta3.AperyRec

/-!
# The growth rates (Proposition 12 of the report, parts "The integers" and "The half-steps")

Report, Proposition 12: with `μ = (1+√2)^4 = 17 + 12√2`, the larger root of `x + 1/x = 34`,
`u_{n+1}/u_n → μ` and both half-step ratios `u_{n+1/2}/u_n`, `u_{n+1}/u_{n+1/2}` tend to `3 + 2√2`.

Differences between the Lean statements and the text:
* `ratio_tendsto` is abstract: any real sequence `u` with `u n > 0` for all `n`, satisfying (A) for
  `n ≥ 1` (written with `u (n-1)`, natural subtraction, as in `Zeta3.growth_step`), and with
  `30 u n ≤ u (n+1)` for `n ≥ 15` (the conclusion of Lemma 9 / `growth_step`, taken as a hypothesis).
  `aperyU_ratio_tendsto` is the statement for the actual integers `u_n = Σ C(n,k)²C(n+k,k)²`,
  cast to `ℝ`, with no hypotheses.
* The contraction step of the text ("let L be the upper limit; L ≤ L/900") is replaced by the
  general lemma `tendsto_zero_of_contract` (ε–N argument with geometric decay), which also does
  not need the boundedness of `|x_n - μ|`.
* `ε_n → 0` is replaced by the explicit bound `|ε_{n+1}| ≤ 75/(n+2) + 1/(10(n+2)) ≤ 76/(n+1)`
  for `n ≥ 15`.
* Half-steps (`halfstep_tendsto`): abstract. The half-step numbers `u_{n+1/2}` are not defined in
  the Lean library; the statement takes any `h : ℕ → ℝ` with `u (n+1) + u n = 6 h n` (this is
  (MIX)), and a positive `u` whose ratio tends to `17 + 12√2`. The corollary `aperyU_halfstep_tendsto`
  applies it to `aperyU`, still with an arbitrary `h` satisfying (MIX).
* The part on `z_{n+1}/z_n` is not covered.
-/

-- CLAIMED: Zeta3.tendsto_zero_of_contract, Zeta3.mu_eq_pow_four, Zeta3.mu_add_inv
-- CLAIMED: Zeta3.ratio_tendsto, Zeta3.aperyU_ratio_tendsto
-- CLAIMED: Zeta3.halfstep_tendsto, Zeta3.aperyU_halfstep_tendsto

set_option autoImplicit false

open Filter Topology

namespace Zeta3

/-- A nonnegative sequence with `e (n+1) ≤ δ n + c e n` eventually, `δ → 0`, `0 ≤ c < 1`,
tends to `0`. -/
theorem tendsto_zero_of_contract (e δ : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (he : ∀ n, 0 ≤ e n) (hδ : Tendsto δ atTop (𝓝 0)) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hrec : ∀ n, N ≤ n → e (n + 1) ≤ δ n + c * e n) :
    Tendsto e atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : 0 < ε * (1 - c) / 2 := by
    have : 0 < 1 - c := by linarith
    positivity
  obtain ⟨M0, hM0⟩ := Metric.tendsto_atTop.1 hδ _ hη
  set M := max N M0 with hM
  have key : ∀ k : ℕ, e (M + k) ≤ c ^ k * e M + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have h1 := hrec (M + k) (by omega)
      have h2 := hM0 (M + k) (by omega)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : δ (M + k) ≤ ε * (1 - c) / 2 := le_trans (le_abs_self _) h2.le
      have h4 := mul_le_mul_of_nonneg_left ih hc0
      have e1 : c * (c ^ k * e M + ε / 2) = c ^ (k + 1) * e M + c * ε / 2 := by ring
      rw [show M + (k + 1) = M + k + 1 from rfl]
      nlinarith
  have hpow : Tendsto (fun k : ℕ => c ^ k * e M) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const (e M)
    simpa using this
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hpow (ε / 2) (by linarith)
  refine ⟨M + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = M + k := ⟨n - M, by omega⟩
  have h1 := key k
  have h2 := hK k (by omega)
  rw [Real.dist_eq, sub_zero] at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he _)]
  have := le_abs_self (c ^ k * e M)
  linarith

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `17 + 12√2 = (1+√2)^4`. -/
theorem mu_eq_pow_four : (17 + 12 * Real.sqrt 2 : ℝ) = (1 + Real.sqrt 2) ^ 4 := by
  have hs := sqrt_two_sq
  linear_combination (-(Real.sqrt 2 ^ 2 + 4 * Real.sqrt 2 + 8)) * hs

theorem mu_mul : (17 + 12 * Real.sqrt 2 : ℝ) * (34 - (17 + 12 * Real.sqrt 2)) = 1 := by
  have hs := sqrt_two_sq
  linear_combination (-144) * hs

theorem mu_ge : (30 : ℝ) ≤ 17 + 12 * Real.sqrt 2 := by
  have h : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith

/-- `μ + 1/μ = 34` for `μ = 17 + 12√2`. -/
theorem mu_add_inv :
    (17 + 12 * Real.sqrt 2 : ℝ) + 1 / (17 + 12 * Real.sqrt 2) = 34 := by
  have h := eq_one_div_of_mul_eq_one_right mu_mul
  rw [← h]; ring

/-- The one-step estimate: with `x = b/a` and `c/b` the next ratio, given by (A) at index `m`. -/
theorem ratio_step (m a b c : ℝ) (hm' : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (hrec : (m + 1) ^ 3 * c = (34 * m ^ 3 + 51 * m ^ 2 + 27 * m + 5) * b - m ^ 3 * a)
    (hx : 30 ≤ b / a) :
    |c / b - (17 + 12 * Real.sqrt 2)| ≤
      76 / m + |b / a - (17 + 12 * Real.sqrt 2)| / 900 := by
  set μ : ℝ := 17 + 12 * Real.sqrt 2 with hμ
  set x : ℝ := b / a with hxdef
  have hμ30 : 30 ≤ μ := mu_ge
  have hμinv : 1 / μ = 34 - μ := (eq_one_div_of_mul_eq_one_right mu_mul).symm
  have hx0 : 0 < x := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have hm13 : 0 < (m + 1) ^ 3 := by positivity
  set T1 : ℝ := (34 * m ^ 3 + 51 * m ^ 2 + 27 * m + 5) / (m + 1) ^ 3 - 34 with hT1
  set T2 : ℝ := 1 - m ^ 3 / (m + 1) ^ 3 with hT2
  have hcb : c / b - μ = T1 + T2 / x + (x - μ) / (μ * x) := by
    have hc : c = ((34 * m ^ 3 + 51 * m ^ 2 + 27 * m + 5) * b - m ^ 3 * a) / (m + 1) ^ 3 := by
      rw [← hrec]; field_simp
    have hμ0 : μ ≠ 0 := by linarith
    have e3 : (x - μ) / (μ * x) = 1 / μ - 1 / x := by field_simp
    have e4 : 1 / μ = 34 - μ := hμinv
    rw [e3, e4, hc, hT1, hT2, hxdef]
    field_simp
    ring
  have hT1b : |T1| ≤ 75 / (m + 1) := by
    have e : T1 = -((51 * m ^ 2 + 75 * m + 29) / (m + 1) ^ 3) := by
      rw [hT1]; field_simp; ring
    rw [e, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ hm13 hm1]
    nlinarith [sq_nonneg m, mul_pos hm' hm']
  have hT2b : |T2| ≤ 3 / (m + 1) := by
    have e : T2 = (3 * m ^ 2 + 3 * m + 1) / (m + 1) ^ 3 := by
      rw [hT2]; field_simp; ring
    rw [e, abs_of_nonneg (by positivity), div_le_div_iff₀ hm13 hm1]
    nlinarith [sq_nonneg m, mul_pos hm' hm']
  have hT2x : |T2 / x| ≤ 3 / (m + 1) / 30 := by
    rw [abs_div, abs_of_pos hx0]
    calc |T2| / x ≤ (3 / (m + 1)) / x := by gcongr
      _ ≤ 3 / (m + 1) / 30 := by gcongr
  have hT3 : |(x - μ) / (μ * x)| ≤ |x - μ| / 900 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < μ * x)]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
    nlinarith
  have hsum : |c / b - μ| ≤ |T1| + |T2 / x| + |(x - μ) / (μ * x)| := by
    rw [hcb]; exact abs_add_three _ _ _
  have hfin : 75 / (m + 1) + 3 / (m + 1) / 30 ≤ 76 / m := by
    rw [div_div, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) hm']
    nlinarith
  linarith

/-- **Proposition 12, the integers (abstract form).** A positive solution of Apéry's recurrence (A)
with `u (n+1) ≥ 30 u n` for `n ≥ 15` satisfies `u (n+1) / u n → 17 + 12√2 = (1+√2)^4`. -/
theorem ratio_tendsto (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 3 * u (n + 1)
        - (34 * (n : ℝ) ^ 3 + 51 * (n : ℝ) ^ 2 + 27 * (n : ℝ) + 5) * u n
        + (n : ℝ) ^ 3 * u (n - 1) = 0)
    (hpos : ∀ n, 0 < u n) (hg : ∀ n : ℕ, 15 ≤ n → 30 * u n ≤ u (n + 1)) :
    Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 (17 + 12 * Real.sqrt 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  refine tendsto_zero_of_contract _ (fun n : ℕ => 76 / ((n : ℝ) + 1)) (1 / 900) 15
    (fun n => abs_nonneg _) ?_ (by norm_num) (by norm_num) ?_
  · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (76 : ℝ)
    simpa [div_eq_mul_inv] using this
  · intro n hn
    have hr := hu (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    push_cast at hr
    have hx : 30 ≤ u (n + 1) / u n := by
      rw [le_div_iff₀ (hpos n)]; exact hg n hn
    have := ratio_step ((n : ℝ) + 1) (u n) (u (n + 1)) (u (n + 1 + 1)) (by positivity)
      (hpos n) (hpos (n + 1)) (by linear_combination hr) hx
    linarith

/-- **Proposition 12, the integers**, for Apéry's numbers `u_n = Σₖ C(n,k)²C(n+k,k)²`:
`u_{n+1}/u_n → 17 + 12√2 = (1+√2)^4`. -/
theorem aperyU_ratio_tendsto :
    Tendsto (fun n => (aperyU (n + 1) : ℝ) / (aperyU n : ℝ)) atTop
      (𝓝 (17 + 12 * Real.sqrt 2)) := by
  refine ratio_tendsto (fun n => (aperyU n : ℝ)) (fun n hn => ?_)
    (fun n => by exact_mod_cast aperyU_pos n) aperyU_growth_uncond
  have hq := aperyU_recurrence n hn
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
  push_cast at hr
  linear_combination hr

/-- **Proposition 12, the half-steps (abstract form).** If `u > 0`, `u (n+1)/u n → 17 + 12√2`
and `u (n+1) + u n = 6 h n` (this is (MIX), with `h n` in the role of `u_{n+1/2}`), then
`h n / u n → 3 + 2√2` and `u (n+1) / h n → 3 + 2√2`. -/
theorem halfstep_tendsto (u h : ℕ → ℝ) (hpos : ∀ n, 0 < u n)
    (hlim : Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 (17 + 12 * Real.sqrt 2)))
    (hmix : ∀ n, u (n + 1) + u n = 6 * h n) :
    Tendsto (fun n => h n / u n) atTop (𝓝 (3 + 2 * Real.sqrt 2)) ∧
      Tendsto (fun n => u (n + 1) / h n) atTop (𝓝 (3 + 2 * Real.sqrt 2)) := by
  have hs := sqrt_two_sq
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hmu1 : (17 + 12 * Real.sqrt 2 : ℝ) + 1 ≠ 0 := by positivity
  constructor
  · have h1 := (hlim.add_const 1).div_const 6
    have e : (17 + 12 * Real.sqrt 2 + 1) / 6 = 3 + 2 * Real.sqrt 2 := by ring
    rw [e] at h1
    refine h1.congr (fun n => ?_)
    have hu0 := (hpos n).ne'
    have hh : h n = (u (n + 1) + u n) / 6 := by rw [hmix n]; ring
    rw [hh]; field_simp
  · have h1 := (hlim.const_mul 6).div (hlim.add_const 1) hmu1
    have e : 6 * (17 + 12 * Real.sqrt 2) / (17 + 12 * Real.sqrt 2 + 1) = 3 + 2 * Real.sqrt 2 := by
      rw [div_eq_iff hmu1]
      linear_combination (-24) * hs
    rw [e] at h1
    refine h1.congr (fun n => ?_)
    have hu0 := (hpos n).ne'
    have hu1 := hpos (n + 1)
    have hh : h n = (u (n + 1) + u n) / 6 := by rw [hmix n]; ring
    have hne : u (n + 1) + u n ≠ 0 := by linarith [hpos n]
    show 6 * (u (n + 1) / u n) / (u (n + 1) / u n + 1) = u (n + 1) / h n
    rw [hh]; field_simp

/-- The half-steps for Apéry's numbers: for any `h` with `u_{n+1} + u_n = 6 h n` (MIX),
`h n / u_n → 3 + 2√2` and `u_{n+1} / h n → 3 + 2√2`. -/
theorem aperyU_halfstep_tendsto (h : ℕ → ℝ)
    (hmix : ∀ n, (aperyU (n + 1) : ℝ) + (aperyU n : ℝ) = 6 * h n) :
    Tendsto (fun n => h n / (aperyU n : ℝ)) atTop (𝓝 (3 + 2 * Real.sqrt 2)) ∧
      Tendsto (fun n => (aperyU (n + 1) : ℝ) / h n) atTop (𝓝 (3 + 2 * Real.sqrt 2)) :=
  halfstep_tendsto (fun n => (aperyU n : ℝ)) h (fun n => by exact_mod_cast aperyU_pos n)
    aperyU_ratio_tendsto hmix

end Zeta3
