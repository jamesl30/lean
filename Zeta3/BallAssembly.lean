import Mathlib

/-!
# Ball's series: the assembly step (thread `work/ball-series`, step 3a)

The last step of the proof of Apéry's theorem from Ball's series
(`work/ball-series/paper.tex`, §5, Theorem): a purely abstract statement. If a real number `x`
admits linear forms `F n = U n * x - V n` (`U n`, `V n` rational) with
`0 < F n < 20 (n+1)^4 ρ^n`, `ρ = (√2 - 1)^4`, and with denominators controlled by
`E n * U n ∈ ℤ`, `E n * D n ^ 3 * V n ∈ ℤ`, where `D n < 3^n` and `E n` is subexponential,
then `x` is irrational. Every property of Ball's series is a hypothesis here; nothing about
the series itself is formalised in this file.

Contents.
* `Zeta3.ball_rho_lt`: `27 * (√2 - 1)^4 < 1` (i.e. `459 - 324√2 < 1`).
* `Zeta3.ball_assembly`: the assembly with `E` subexponential in the form
  `∀ c > 1, ∃ N, ∀ n ≥ N, E n ≤ c^n`.
* `Zeta3.rpow_sqrt_subexp`: `∀ c > 1, ∃ N, ∀ n ≥ N, n^(√(2n)) ≤ c^n`.
* `Zeta3.ball_assembly_sqrt`: the assembly with the paper's bound `E n ≤ n^(√(2n))`.
* `Zeta3.riemannZeta_three_eq`: `ζ(3) = ∑' k, 1/(k+1)^3` (Mathlib's `riemannZeta`).
* `Zeta3.ball_zeta3`, `Zeta3.ball_riemannZeta3`: the two corollaries for `x = ζ(3)`.
-/

-- CLAIMED: Zeta3.BallAsm.ball_rho_lt, Zeta3.BallAsm.ball_assembly, Zeta3.BallAsm.rpow_sqrt_subexp, Zeta3.BallAsm.ball_assembly_sqrt, Zeta3.BallAsm.riemannZeta_three_eq, Zeta3.BallAsm.ball_zeta3, Zeta3.BallAsm.ball_riemannZeta3

set_option autoImplicit false

namespace Zeta3.BallAsm
open Filter Topology

/-- `27 ρ = 27 (√2 - 1)^4 = 459 - 324 √2 < 1`, because `√2 > 229/162`. -/
theorem ball_rho_lt : 27 * (Real.sqrt 2 - 1) ^ 4 < 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h4 : (Real.sqrt 2 - 1) ^ 4 = 17 - 12 * Real.sqrt 2 := by
    linear_combination (Real.sqrt 2 ^ 2 - 4 * Real.sqrt 2 + 8) * h2
  rw [h4]
  nlinarith [h2, hs]

/-- The assembly step, with `E` subexponential. -/
theorem ball_assembly (x : ℝ) (U V : ℕ → ℚ) (F : ℕ → ℝ) (E D : ℕ → ℕ)
    (hUV : ∀ n ≥ 1, F n = U n * x - V n)
    (hpos : ∀ n ≥ 1, 0 < F n)
    (hball : ∀ n ≥ 1, F n < 20 * ((n : ℝ) + 1) ^ 4 * ((Real.sqrt 2 - 1) ^ 4) ^ n)
    (hEU : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * U n = z)
    (hEV : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * (D n : ℚ) ^ 3 * V n = z)
    (hE1 : ∀ n ≥ 1, 1 ≤ E n)
    (hD1 : ∀ n ≥ 1, 1 ≤ D n)
    (hE : ∀ c : ℝ, 1 < c → ∃ N : ℕ, ∀ n ≥ N, (E n : ℝ) ≤ c ^ n)
    (hD : ∀ n ≥ 1, D n < 3 ^ n) : Irrational x := by
  rintro ⟨r, hr⟩
  have hρ0 : 0 ≤ (Real.sqrt 2 - 1) ^ 4 := by positivity
  have hρ1 : 27 * (Real.sqrt 2 - 1) ^ 4 < 1 := ball_rho_lt
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (Real.sqrt 2 - 1) ^ 4 := ⟨_, rfl⟩
  rw [← hρ] at hρ0 hρ1
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 / (1 + 27 * ρ) := ⟨_, rfl⟩
  have hc1 : 1 < c := by
    rw [hc, lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = c * (27 * ρ) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1 : s < 1 := by
    rw [hs, hc, div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
  obtain ⟨N, hN⟩ := hE c hc1
  have hq : (1 : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hlim : Tendsto (fun n : ℕ => (320 * (r.den : ℝ)) * ((n : ℝ) ^ 4 * s ^ n)) atTop (𝓝 0) := by
    have := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 4
      (show |s| < 1 by rw [abs_of_nonneg hs0]; exact hs1)).const_mul (320 * (r.den : ℝ))
    rwa [mul_zero] at this
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = max (max N M) 1 := ⟨_, rfl⟩
  have hn1 : n ≥ 1 := hn ▸ le_max_right _ _
  have hnN : n ≥ N := hn ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hnM : n ≥ M := hn ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hsmall := hM n hnM
  obtain ⟨z1, hz1⟩ := hEU n hn1
  obtain ⟨z2, hz2⟩ := hEV n hn1
  have hz1' : (E n : ℝ) * (U n : ℝ) = z1 := by
    exact_mod_cast congrArg (fun t : ℚ => (t : ℝ)) hz1
  have hz2' : (E n : ℝ) * (D n : ℝ) ^ 3 * (V n : ℝ) = z2 := by
    exact_mod_cast congrArg (fun t : ℚ => (t : ℝ)) hz2
  have hxr : (r.den : ℝ) * x = r.num := by
    have h := congrArg (fun t : ℚ => (t : ℝ)) (Rat.mul_den_eq_num r)
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] at h
    rw [← hr, mul_comm]; exact h
  -- `N_n = q E_n D_n^3 F_n` is an integer
  have hint : (r.den : ℝ) * E n * (D n : ℝ) ^ 3 * F n
      = ((z1 * (D n : ℤ) ^ 3 * r.num - (r.den : ℤ) * z2 : ℤ) : ℝ) := by
    rw [hUV n hn1]
    push_cast
    linear_combination ((D n : ℝ) ^ 3 * (r.den : ℝ) * x) * hz1' + ((D n : ℝ) ^ 3 * z1) * hxr
      - (r.den : ℝ) * hz2'
  have hE1' : (1 : ℝ) ≤ E n := by exact_mod_cast hE1 n hn1
  have hD1' : (1 : ℝ) ≤ D n := by exact_mod_cast hD1 n hn1
  have hNpos : 0 < (r.den : ℝ) * E n * (D n : ℝ) ^ 3 * F n :=
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (pow_pos (by linarith) 3)) (hpos n hn1)
  -- hence `N_n ≥ 1`
  have hN1 : (1 : ℝ) ≤ (r.den : ℝ) * E n * (D n : ℝ) ^ 3 * F n := by
    rw [hint] at hNpos ⊢
    have h0 : (0 : ℤ) < z1 * (D n : ℤ) ^ 3 * r.num - (r.den : ℤ) * z2 := by exact_mod_cast hNpos
    have h1 : (1 : ℤ) ≤ z1 * (D n : ℤ) ^ 3 * r.num - (r.den : ℤ) * z2 := by omega
    exact_mod_cast h1
  -- but `N_n < 320 q n^4 s^n < 1`
  have hEc : (E n : ℝ) ≤ c ^ n := hN n hnN
  have hD3 : (D n : ℝ) ^ 3 ≤ 27 ^ n := by
    have h3 : (D n : ℝ) ≤ 3 ^ n := by exact_mod_cast (hD n hn1).le
    calc (D n : ℝ) ^ 3 ≤ ((3 : ℝ) ^ n) ^ 3 := pow_le_pow_left₀ (by linarith) h3 3
      _ = 27 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn4 : ((n : ℝ) + 1) ^ 4 ≤ 16 * (n : ℝ) ^ 4 := by
    calc ((n : ℝ) + 1) ^ 4 ≤ (2 * (n : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      _ = 16 * (n : ℝ) ^ 4 := by ring
  have hF := hball n hn1
  rw [← hρ] at hF
  have hρn : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
  have hX : 0 ≤ 20 * ((n : ℝ) + 1) ^ 4 * ρ ^ n := by positivity
  have hsn : 0 ≤ s ^ n := pow_nonneg hs0 n
  have : (r.den : ℝ) * E n * (D n : ℝ) ^ 3 * F n < 1 := by
    calc (r.den : ℝ) * E n * (D n : ℝ) ^ 3 * F n
        < (r.den : ℝ) * E n * (D n : ℝ) ^ 3 * (20 * ((n : ℝ) + 1) ^ 4 * ρ ^ n) :=
          mul_lt_mul_of_pos_left hF (mul_pos (mul_pos (by linarith) (by linarith))
            (pow_pos (by linarith) 3))
      _ ≤ (r.den : ℝ) * c ^ n * 27 ^ n * (20 * ((n : ℝ) + 1) ^ 4 * ρ ^ n) := by
          gcongr
      _ = 20 * (r.den : ℝ) * ((n : ℝ) + 1) ^ 4 * s ^ n := by
          rw [hs, mul_pow, mul_pow]; ring
      _ ≤ 20 * (r.den : ℝ) * (16 * (n : ℝ) ^ 4) * s ^ n := by
          gcongr
      _ = (320 * (r.den : ℝ)) * ((n : ℝ) ^ 4 * s ^ n) := by ring
      _ < 1 := hsmall
  linarith

/-- `n^(√(2n))` is subexponential: below `c^n` for every `c > 1` and all large `n`. -/
theorem rpow_sqrt_subexp (c : ℝ) (hc : 1 < c) :
    ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ Real.sqrt (2 * n) ≤ c ^ n := by
  have hL : 0 < Real.log c := Real.log_pos hc
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * Real.sqrt 2 / Real.log c := ⟨_, rfl⟩
  refine ⟨⌈K ^ 4⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnK : K ^ 4 ≤ n := by
    have h1 := Nat.le_ceil (K ^ 4)
    have h2 : (⌈K ^ 4⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (n : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := hw ▸ Real.rpow_nonneg hn0.le _
  have hw4 : w ^ 4 = n := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hwK : K ≤ w := by
    have h : K ^ 4 ≤ w ^ 4 := hw4 ▸ hnK
    exact (pow_le_pow_iff_left₀ hK0 hw0 (by norm_num)).mp h
  have hlog : Real.log n ≤ 4 * w := by
    have h := Real.log_le_rpow_div hn0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [← hw] at h
    linarith [h, show w / (1 / 4) = 4 * w by ring]
  have hsq : Real.sqrt (2 * n) = Real.sqrt 2 * w ^ 2 := by
    rw [Real.sqrt_mul (by norm_num), ← hw4, show w ^ 4 = (w ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [← Real.rpow_natCast c n, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  have hKL : K * Real.log c = 4 * Real.sqrt 2 := by rw [hK, div_mul_cancel₀ _ hL.ne']
  calc Real.log n * Real.sqrt (2 * n) = Real.log n * (Real.sqrt 2 * w ^ 2) := by rw [hsq]
    _ ≤ (4 * w) * (Real.sqrt 2 * w ^ 2) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = (K * Real.log c) * w ^ 3 := by rw [hKL]; ring
    _ ≤ (w * Real.log c) * w ^ 3 := by gcongr
    _ = Real.log c * w ^ 4 := by ring
    _ = Real.log c * n := by rw [hw4]

/-- The assembly step, with the paper's bound `E n ≤ n^(√(2n))` (its equation (E)). -/
theorem ball_assembly_sqrt (x : ℝ) (U V : ℕ → ℚ) (F : ℕ → ℝ) (E D : ℕ → ℕ)
    (hUV : ∀ n ≥ 1, F n = U n * x - V n)
    (hpos : ∀ n ≥ 1, 0 < F n)
    (hball : ∀ n ≥ 1, F n < 20 * ((n : ℝ) + 1) ^ 4 * ((Real.sqrt 2 - 1) ^ 4) ^ n)
    (hEU : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * U n = z)
    (hEV : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * (D n : ℚ) ^ 3 * V n = z)
    (hE1 : ∀ n ≥ 1, 1 ≤ E n)
    (hD1 : ∀ n ≥ 1, 1 ≤ D n)
    (hE : ∀ n ≥ 1, (E n : ℝ) ≤ (n : ℝ) ^ Real.sqrt (2 * n))
    (hD : ∀ n ≥ 1, D n < 3 ^ n) : Irrational x := by
  refine ball_assembly x U V F E D hUV hpos hball hEU hEV hE1 hD1 ?_ hD
  intro c hc
  obtain ⟨N, hN⟩ := rpow_sqrt_subexp c hc
  exact ⟨max N 1, fun n hn => (hE n (le_trans (le_max_right _ _) hn)).trans
    (hN n (le_trans (le_max_left _ _) hn))⟩

/-- Mathlib's `riemannZeta 3` is the real number `∑_{k ≥ 1} 1/k^3`. -/
theorem riemannZeta_three_eq :
    riemannZeta 3 = ((∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum, zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num)]
  congr 1
  ext k
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  push_cast
  ring

/-- Corollary for `ζ(3) = ∑_{k ≥ 1} k^{-3}`, written as a real series. -/
theorem ball_zeta3 (U V : ℕ → ℚ) (F : ℕ → ℝ) (E D : ℕ → ℕ)
    (hUV : ∀ n ≥ 1, F n = U n * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) - V n)
    (hpos : ∀ n ≥ 1, 0 < F n)
    (hball : ∀ n ≥ 1, F n < 20 * ((n : ℝ) + 1) ^ 4 * ((Real.sqrt 2 - 1) ^ 4) ^ n)
    (hEU : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * U n = z)
    (hEV : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * (D n : ℚ) ^ 3 * V n = z)
    (hE1 : ∀ n ≥ 1, 1 ≤ E n)
    (hD1 : ∀ n ≥ 1, 1 ≤ D n)
    (hE : ∀ n ≥ 1, (E n : ℝ) ≤ (n : ℝ) ^ Real.sqrt (2 * n))
    (hD : ∀ n ≥ 1, D n < 3 ^ n) : Irrational (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) :=
  ball_assembly_sqrt _ U V F E D hUV hpos hball hEU hEV hE1 hD1 hE hD

/-- Corollary for Mathlib's `riemannZeta 3`: it is a real number, and that number is
irrational. The hypotheses are those of `ball_zeta3`. -/
theorem ball_riemannZeta3 (U V : ℕ → ℚ) (F : ℕ → ℝ) (E D : ℕ → ℕ)
    (hUV : ∀ n ≥ 1, F n = U n * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) - V n)
    (hpos : ∀ n ≥ 1, 0 < F n)
    (hball : ∀ n ≥ 1, F n < 20 * ((n : ℝ) + 1) ^ 4 * ((Real.sqrt 2 - 1) ^ 4) ^ n)
    (hEU : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * U n = z)
    (hEV : ∀ n ≥ 1, ∃ z : ℤ, (E n : ℚ) * (D n : ℚ) ^ 3 * V n = z)
    (hE1 : ∀ n ≥ 1, 1 ≤ E n)
    (hD1 : ∀ n ≥ 1, 1 ≤ D n)
    (hE : ∀ n ≥ 1, (E n : ℝ) ≤ (n : ℝ) ^ Real.sqrt (2 * n))
    (hD : ∀ n ≥ 1, D n < 3 ^ n) :
    riemannZeta 3 = (((riemannZeta 3).re : ℝ) : ℂ) ∧ Irrational (riemannZeta 3).re := by
  have h := riemannZeta_three_eq
  have hre : (riemannZeta 3).re = ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3 := by
    rw [h, Complex.ofReal_re]
  refine ⟨by rw [hre, h], ?_⟩
  rw [hre]
  exact ball_zeta3 U V F E D hUV hpos hball hEU hEV hE1 hD1 hE hD

end Zeta3.BallAsm