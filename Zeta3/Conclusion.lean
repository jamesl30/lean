import Mathlib
import Zeta3.Criterion
import Zeta3.Apery
import Zeta3.AperyRec

/-!
# The conclusion (§10 of the report) and its ζ(2) twin (end of §11.6), as conditional theorems

This file formalises only the LAST STEP of the proof: "the lemmas imply irrationality". The lemmas
of the report that are not formalised in Lean appear as explicit, named hypotheses. Nothing here is
a Lean proof of Apéry's theorem.

* `irrational_of_small_forms`, `irrational_of_small_forms_abs`: Lemma 1 in the form used at the end
  of §2 ("integers `p_n`, `q_n` with `0 < q_n ξ - p_n → 0` cannot exist for rational `ξ`"), stated
  as: if for every `ε > 0` there are integers `p`, `q` with `0 < q ξ - p < ε` (resp.
  `0 < |q ξ - p| < ε`), then `ξ` is irrational. Unconditional.

* `irrational_of_apery_data` (abstract §10). Sequences `u : ℕ → ℤ`, `v : ℕ → ℚ`, `d : ℕ → ℕ`, with
  - (H0) `0 < d n` for `n ≥ 1`                     [d_n = lcm(1,…,n) ≥ 1; not stated in the text
                                                      because it is obvious for the lcm]
  - (H1) `d n ^ 3 * v n` is an integer (all `n`)   [Lemma 2(ii)]
  - (H2) `0 < u n ξ - v n < 3 / (n² u n)` (n ≥ 1)  [Proposition 8]
  - (H3) `30^(n-15) ≤ u n` (n ≥ 15)                [Lemma 9]
  - (H4) `d n < 3^n` (n ≥ 1)                       [Hanson's bound, cited in §10]
  conclude `Irrational ξ`. The proof follows the display of §10:
  `0 < q_n ξ - p_n < 3 d_n³/(n² u_n) ≤ 3·27^n/30^(n-15) = 3·27^15·(9/10)^(n-15) → 0`,
  with `q_n = d_n³ u_n`, `p_n = d_n³ v_n`.

* `irrational_zeta3_of_lemmas`: the same with `ξ = ∑_{k≥1} 1/k³` (written
  `∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3`), `u = Zeta3.aperyU` (Apéry's numbers, defined in `Zeta3.Apery`),
  `d = lcmOneTo` (`lcm(1,…,n)`, defined here). (H0) is proved, and (H3) is DISCHARGED by the
  Lean-proved `Zeta3.aperyU_growth_uncond` and `Zeta3.aperyU_pos`. It is CONDITIONAL on
    (H1) `lcm(1..n)³ v_n ∈ ℤ`  (Lemma 2(ii), not formalised),
    (H2) `0 < u_n ζ(3) - v_n < 3/(n² u_n)` for n ≥ 1  (Proposition 8, not formalised; it rests on
         Lemma 2, Lemma 7, Proposition 6 and the Wronskian identity, of which only the last is in
         Lean as `Zeta3.wronskian_const` / `Zeta3.series_partial`),
    (H4) `lcm(1..n) < 3^n` for n ≥ 1  (Hanson 1972, cited, not formalised),
  for an arbitrary sequence `v : ℕ → ℚ`. It is NOT a Lean proof of Apéry's theorem.
  `riemannZeta_three_eq_tsum` records that this `ξ` is Mathlib's `riemannZeta 3`.

* `irrational_of_apery_data_zeta2` (end of §11.6). Sequences `u : ℕ → ℤ`, `r : ℕ → ℚ`, `d : ℕ → ℕ`:
  (H0) `0 < d n` (n ≥ 1); (H1) `d n ^ 2 * r n ∈ ℤ`; (H2) for n ≥ 1, `0 < (-1)^n (u n ξ - r n)` and
  `|u n ξ - r n| < 5 / (n u n)`; (H3) `10^(n-10) ≤ u n` (n ≥ 10); (H4) `d n < 3^n` (n ≥ 1);
  conclude `Irrational ξ`. Display of the text: `0 < (-1)^n (q_n ξ - p_n) = d_n² |z*_n| <
  5·9^n/(n·10^(n-10)) → 0`. Instead of applying Lemma 1 to `(-1)^n q_n`, `(-1)^n p_n` we use the
  absolute-value form `irrational_of_small_forms_abs` (equivalent).

Differences from the text: abstract sequences instead of the specific `u_n`, `v_n`, `d_n` (except in
`irrational_zeta3_of_lemmas`); the hypothesis (H0) `d n > 0`, implicit in the text (`d_n` is an lcm);
(H1) is stated for every `n` as in Lemma 2 (only `n ≥ 15`, resp. `n ≥ 10`, is used); the bounds
(H3) are stated in `ℝ` (`(30 : ℝ)^(n-15) ≤ (u n : ℝ)`), which for integers is the same statement.
-/

set_option autoImplicit false

namespace Zeta3

-- CLAIMED: Zeta3.irrational_of_small_forms, Zeta3.irrational_of_small_forms_abs
-- CLAIMED: Zeta3.irrational_of_apery_data, Zeta3.irrational_zeta3_of_lemmas
-- CLAIMED: Zeta3.riemannZeta_three_eq_tsum, Zeta3.irrational_of_apery_data_zeta2

/-- Lemma 1, end of §2: if integer linear forms `q ξ - p` take arbitrarily small positive values,
then `ξ` is irrational. -/
theorem irrational_of_small_forms (ξ : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ p q : ℤ, 0 < (q : ℝ) * ξ - p ∧ (q : ℝ) * ξ - p < ε) :
    Irrational ξ := by
  rintro ⟨x, rfl⟩
  have hb : (1 : ℕ) ≤ x.den := x.den_pos
  have hb' : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  obtain ⟨p, q, h1, h2⟩ := h (1 / x.den) (by positivity)
  have hx : ((x : ℚ) : ℝ) = (x.num : ℝ) / x.den := by
    rw [Rat.cast_def]
  rw [hx] at h1 h2
  have := criterion x.num p q x.den hb h1
  linarith

/-- Variant of Lemma 1 with `0 < |q ξ - p| < ε`. -/
theorem irrational_of_small_forms_abs (ξ : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ p q : ℤ, 0 < |(q : ℝ) * ξ - p| ∧ |(q : ℝ) * ξ - p| < ε) :
    Irrational ξ := by
  refine irrational_of_small_forms ξ (fun ε hε => ?_)
  obtain ⟨p, q, h1, h2⟩ := h ε hε
  rcases le_or_gt 0 ((q : ℝ) * ξ - p) with hs | hs
  · refine ⟨p, q, ?_, ?_⟩
    · rw [abs_of_nonneg hs] at h1; exact h1
    · rw [abs_of_nonneg hs] at h2; exact h2
  · refine ⟨-p, -q, ?_, ?_⟩
    · rw [abs_of_neg hs] at h1; push_cast; linarith
    · rw [abs_of_neg hs] at h2; push_cast; linarith

/-- The geometric tail used in both conclusions: for `C > 0` and `0 < ρ < 1`, `C ρ^m` gets below
any `ε > 0`. -/
private theorem exists_small (C ρ ε : ℝ) (hC : 0 < C) (_hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hε : 0 < ε) :
    ∃ m : ℕ, C * ρ ^ m < ε := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hρ1
  refine ⟨m, ?_⟩
  have := (lt_div_iff₀ hC).1 hm
  linarith [mul_comm C (ρ ^ m)]

/-- **§10, abstract form.** Lemma 2 (H1), Proposition 8 (H2), Lemma 9 (H3) and Hanson's bound (H4)
imply that `ξ` is irrational. -/
theorem irrational_of_apery_data (ξ : ℝ) (u : ℕ → ℤ) (v : ℕ → ℚ) (d : ℕ → ℕ)
    (H0 : ∀ n : ℕ, 1 ≤ n → 0 < d n)
    (H1 : ∀ n : ℕ, ∃ P : ℤ, ((d n : ℚ)) ^ 3 * v n = P)
    (H2 : ∀ n : ℕ, 1 ≤ n →
      0 < (u n : ℝ) * ξ - (v n : ℝ) ∧ (u n : ℝ) * ξ - (v n : ℝ) < 3 / ((n : ℝ) ^ 2 * u n))
    (H3 : ∀ n : ℕ, 15 ≤ n → (30 : ℝ) ^ (n - 15) ≤ (u n : ℝ))
    (H4 : ∀ n : ℕ, 1 ≤ n → (d n : ℝ) < 3 ^ n) :
    Irrational ξ := by
  refine irrational_of_small_forms ξ (fun ε hε => ?_)
  obtain ⟨m, hm⟩ := exists_small (3 * 27 ^ 15) (9 / 10) ε (by norm_num) (by norm_num)
    (by norm_num) hε
  set n := m + 15 with hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨P, hP⟩ := H1 n
  refine ⟨P, (d n : ℤ) ^ 3 * u n, ?_, ?_⟩
  · -- the form equals d_n³ (u_n ξ - v_n)
    have hPr : ((P : ℚ) : ℝ) = ((d n : ℝ)) ^ 3 * (v n : ℝ) := by
      rw [← hP]; push_cast; ring
    have hdpos : (0 : ℝ) < d n := by exact_mod_cast H0 n hn1
    have key : (((d n : ℤ) ^ 3 * u n : ℤ) : ℝ) * ξ - (P : ℝ)
        = (d n : ℝ) ^ 3 * ((u n : ℝ) * ξ - (v n : ℝ)) := by
      have : ((P : ℤ) : ℝ) = ((P : ℚ) : ℝ) := by push_cast; rfl
      rw [this, hPr]; push_cast; ring
    rw [key]
    exact mul_pos (pow_pos hdpos 3) (H2 n hn1).1
  · have hPr : ((P : ℚ) : ℝ) = ((d n : ℝ)) ^ 3 * (v n : ℝ) := by
      rw [← hP]; push_cast; ring
    have key : (((d n : ℤ) ^ 3 * u n : ℤ) : ℝ) * ξ - (P : ℝ)
        = (d n : ℝ) ^ 3 * ((u n : ℝ) * ξ - (v n : ℝ)) := by
      have : ((P : ℤ) : ℝ) = ((P : ℚ) : ℝ) := by push_cast; rfl
      rw [this, hPr]; push_cast; ring
    rw [key]
    set x := (u n : ℝ) * ξ - (v n : ℝ) with hx
    obtain ⟨hx0, hx1⟩ := H2 n hn1
    have hu : (30 : ℝ) ^ m ≤ (u n : ℝ) := by
      have := H3 n (by omega)
      rwa [show n - 15 = m by omega] at this
    have hupos : (0 : ℝ) < u n := lt_of_lt_of_le (by positivity) hu
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
    -- x * u_n < 3
    have hxu : x * (u n : ℝ) < 3 := by
      have h1 : x * ((n : ℝ) ^ 2 * u n) < 3 := by
        have hden : (0 : ℝ) < (n : ℝ) ^ 2 * u n := by positivity
        have := (lt_div_iff₀ hden).1 hx1
        linarith
      nlinarith
    -- 30^m x < 3
    have h30 : (30 : ℝ) ^ m * x < 3 := by nlinarith
    -- d_n³ < 27^n
    have hd3 : (d n : ℝ) ^ 3 < 27 ^ n := by
      have h := pow_lt_pow_left₀ (H4 n hn1) (Nat.cast_nonneg _) (by norm_num : (3 : ℕ) ≠ 0)
      calc (d n : ℝ) ^ 3 < ((3 : ℝ) ^ n) ^ 3 := h
        _ = 27 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e27 : (27 : ℝ) ^ n * x = 27 ^ 15 * ((9 / 10) ^ m * ((30 : ℝ) ^ m * x)) := by
      rw [hn, pow_add, ← mul_assoc ((9 / 10 : ℝ) ^ m), ← mul_pow]
      norm_num; ring
    have hpow : (0 : ℝ) < (9 / 10) ^ m := by positivity
    calc (d n : ℝ) ^ 3 * x < 27 ^ n * x := mul_lt_mul_of_pos_right hd3 hx0
      _ = 27 ^ 15 * ((9 / 10) ^ m * ((30 : ℝ) ^ m * x)) := e27
      _ ≤ 27 ^ 15 * ((9 / 10) ^ m * 3) := by gcongr
      _ = 3 * 27 ^ 15 * (9 / 10) ^ m := by ring
      _ < ε := hm

/-- `lcm(1, …, n)`, the number `d_n` of the report (`lcmOneTo 0 = 1`). -/
def lcmOneTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

theorem lcmOneTo_pos (n : ℕ) : 0 < lcmOneTo n := by
  unfold lcmOneTo
  refine Nat.pos_of_ne_zero (fun h => ?_)
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨k, hk, hk0⟩ := h
  simp at hk hk0
  omega

/-- Lemma 9 for Apéry's numbers, from the Lean-proved growth step: `u_n ≥ 30^(n-15)` for `n ≥ 15`. -/
theorem aperyU_ge_pow (n : ℕ) (hn : 15 ≤ n) : (30 : ℝ) ^ (n - 15) ≤ (aperyU n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have : (1 : ℝ) ≤ aperyU 15 := by exact_mod_cast aperyU_pos 15
    simpa using this
  | succ k hk ih =>
    have hs := aperyU_growth_uncond k hk
    rw [show k + 1 - 15 = (k - 15) + 1 by omega, pow_succ]
    nlinarith

/-- The `ξ` used below is Mathlib's `ζ(3)`. -/
theorem riemannZeta_three_eq_tsum :
    riemannZeta 3 = (((∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3 : ℝ)) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num), Complex.ofReal_tsum]
  congr 1
  funext k
  have h3 : (3 : ℂ) = ((3 : ℕ) : ℂ) := by norm_num
  rw [h3, Complex.cpow_natCast]
  push_cast
  ring

/-- **§10 for `ζ(3)`, conditional.** With `u = aperyU` (Lemma 9 proved in Lean) and `d = lcm(1..n)`,
for any rationals `v_n` satisfying Lemma 2(ii) (H1) and Proposition 8 (H2), Hanson's bound (H4)
implies that `ζ(3) = ∑_{k≥1} 1/k³` is irrational. NOT a proof of Apéry's theorem: (H1), (H2), (H4)
are hypotheses. -/
theorem irrational_zeta3_of_lemmas (v : ℕ → ℚ)
    (H1 : ∀ n : ℕ, ∃ P : ℤ, ((lcmOneTo n : ℚ)) ^ 3 * v n = P)
    (H2 : ∀ n : ℕ, 1 ≤ n →
      0 < (aperyU n : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) - (v n : ℝ) ∧
      (aperyU n : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) - (v n : ℝ)
        < 3 / ((n : ℝ) ^ 2 * aperyU n))
    (H4 : ∀ n : ℕ, 1 ≤ n → (lcmOneTo n : ℝ) < 3 ^ n) :
    Irrational (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) := by
  refine irrational_of_apery_data _ (fun n => (aperyU n : ℤ)) v lcmOneTo
    (fun n _ => lcmOneTo_pos n) H1 ?_ ?_ H4
  · intro n hn
    have := H2 n hn
    push_cast
    exact this
  · intro n hn
    have := aperyU_ge_pow n hn
    push_cast
    exact this

/-- **End of §11.6, the ζ(2) twin, abstract form.** -/
theorem irrational_of_apery_data_zeta2 (ξ : ℝ) (u : ℕ → ℤ) (r : ℕ → ℚ) (d : ℕ → ℕ)
    (H0 : ∀ n : ℕ, 1 ≤ n → 0 < d n)
    (H1 : ∀ n : ℕ, ∃ P : ℤ, ((d n : ℚ)) ^ 2 * r n = P)
    (H2 : ∀ n : ℕ, 1 ≤ n →
      0 < (-1 : ℝ) ^ n * ((u n : ℝ) * ξ - (r n : ℝ)) ∧
      |(u n : ℝ) * ξ - (r n : ℝ)| < 5 / ((n : ℝ) * u n))
    (H3 : ∀ n : ℕ, 10 ≤ n → (10 : ℝ) ^ (n - 10) ≤ (u n : ℝ))
    (H4 : ∀ n : ℕ, 1 ≤ n → (d n : ℝ) < 3 ^ n) :
    Irrational ξ := by
  refine irrational_of_small_forms_abs ξ (fun ε hε => ?_)
  obtain ⟨m, hm⟩ := exists_small (5 * 9 ^ 10) (9 / 10) ε (by norm_num) (by norm_num)
    (by norm_num) hε
  set n := m + 10 with hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨P, hP⟩ := H1 n
  refine ⟨P, (d n : ℤ) ^ 2 * u n, ?_⟩
  have hPr : ((P : ℚ) : ℝ) = ((d n : ℝ)) ^ 2 * (r n : ℝ) := by
    rw [← hP]; push_cast; ring
  have key : (((d n : ℤ) ^ 2 * u n : ℤ) : ℝ) * ξ - (P : ℝ)
      = (d n : ℝ) ^ 2 * ((u n : ℝ) * ξ - (r n : ℝ)) := by
    have : ((P : ℤ) : ℝ) = ((P : ℚ) : ℝ) := by push_cast; rfl
    rw [this, hPr]; push_cast; ring
  rw [key, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d n : ℝ) ^ 2)]
  set x := (u n : ℝ) * ξ - (r n : ℝ) with hx
  obtain ⟨hs, hx1⟩ := H2 n hn1
  have hdpos : (0 : ℝ) < d n := by exact_mod_cast H0 n hn1
  have hxne : x ≠ 0 := by
    rintro h0; rw [hx] at h0; rw [h0, mul_zero] at hs; exact lt_irrefl _ hs
  have hax : 0 < |x| := abs_pos.2 hxne
  refine ⟨mul_pos (pow_pos hdpos 2) hax, ?_⟩
  have hu : (10 : ℝ) ^ m ≤ (u n : ℝ) := by
    have := H3 n (by omega)
    rwa [show n - 10 = m by omega] at this
  have hupos : (0 : ℝ) < u n := lt_of_lt_of_le (by positivity) hu
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hxu : |x| * (u n : ℝ) < 5 := by
    have h1 : |x| * ((n : ℝ) * u n) < 5 := by
      have hden : (0 : ℝ) < (n : ℝ) * u n := by positivity
      have := (lt_div_iff₀ hden).1 hx1
      linarith
    nlinarith
  have h10 : (10 : ℝ) ^ m * |x| < 5 := by nlinarith
  have hd2 : (d n : ℝ) ^ 2 < 9 ^ n := by
    have h := pow_lt_pow_left₀ (H4 n hn1) (Nat.cast_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)
    calc (d n : ℝ) ^ 2 < ((3 : ℝ) ^ n) ^ 2 := h
      _ = 9 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e9 : (9 : ℝ) ^ n * |x| = 9 ^ 10 * ((9 / 10) ^ m * ((10 : ℝ) ^ m * |x|)) := by
    rw [hn, pow_add, ← mul_assoc ((9 / 10 : ℝ) ^ m), ← mul_pow]
    norm_num; ring
  have hpow : (0 : ℝ) < (9 / 10) ^ m := by positivity
  calc (d n : ℝ) ^ 2 * |x| < 9 ^ n * |x| := mul_lt_mul_of_pos_right hd2 hax
    _ = 9 ^ 10 * ((9 / 10) ^ m * ((10 : ℝ) ^ m * |x|)) := e9
    _ ≤ 9 ^ 10 * ((9 / 10) ^ m * 5) := by gcongr
    _ = 5 * 9 ^ 10 * (9 / 10) ^ m := by ring
    _ < ε := hm

end Zeta3
