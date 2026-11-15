import Mathlib

/-!
Saving at large primes gives corrected denominators (ball-series text, §5, (finalarith), (E)).
`lcmUpTo n = lcm(1,…,n)`, `ballE n = ∏_{p prime, p² ≤ 2n} p^{⌊log_p n⌋}`.
-/

-- CLAIMED: Zeta3.BallDen.ball_corrected, Zeta3.BallDen.ballE_le, Zeta3.BallDen.lcmUpTo_small, Zeta3.BallDen.ballE_small

set_option autoImplicit false

namespace Zeta3.BallDen

/-- `lcm(1, …, n)`. -/
def lcmUpTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- `∏_{p prime, p ≤ n, p² ≤ 2n} p ^ ⌊log_p n⌋`. -/
def ballE (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p * p ≤ 2 * n), p ^ (Nat.log p n)

theorem lcmUpTo_small :
    lcmUpTo 0 = 1 ∧ lcmUpTo 1 = 1 ∧ lcmUpTo 4 = 12 ∧ lcmUpTo 6 = 60 ∧ lcmUpTo 10 = 2520 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem ballE_small :
    ballE 1 = 1 ∧ ballE 2 = 2 ∧ ballE 8 = 24 ∧ ballE 12 = 72 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  unfold lcmUpTo
  apply Nat.pos_of_ne_zero
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

theorem dvd_lcmUpTo {n k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : k ∣ lcmUpTo n :=
  Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) (Finset.mem_Icc.2 ⟨h1, h2⟩)

theorem ballE_pos (n : ℕ) : 0 < ballE n := by
  unfold ballE
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact pow_pos hp.2.1.pos _

theorem pow_log_dvd_ballE {n p : ℕ} (hp : p.Prime) (hpp : p * p ≤ 2 * n) :
    p ^ Nat.log p n ∣ ballE n := by
  apply Finset.dvd_prod_of_mem
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hp, hpp⟩
  have h2 := hp.two_le
  nlinarith

/-- The core divisibility: if every prime `p` with `p ≤ n < p²/2` divides `m`, then
`lcm(1..n) ∣ E n * m`. -/
theorem lcmUpTo_dvd (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hm : ∀ p : ℕ, p.Prime → 2 * n < p * p → p ≤ n → p ∣ m) :
    lcmUpTo n ∣ ballE n * m := by
  rcases Nat.eq_zero_or_pos m with h0 | hm0
  · simp [h0]
  unfold lcmUpTo
  apply Finset.lcm_dvd
  intro k hk
  simp only [Finset.mem_Icc] at hk
  simp only [id]
  have hE := ballE_pos n
  rw [← Nat.factorization_prime_le_iff_dvd (by omega) (by positivity)]
  intro p hp
  rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
  set v := k.factorization p with hv
  have hpv : p ^ v ≤ n := by
    have : p ^ v ∣ k := Nat.ordProj_dvd k p
    exact le_trans (Nat.le_of_dvd (by omega) this) hk.2
  by_cases hpp : p * p ≤ 2 * n
  · have h1 : v ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt hpv
    have h2 : Nat.log p n ≤ (ballE n).factorization p :=
      (hp.pow_dvd_iff_le_factorization (by omega)).1 (pow_log_dvd_ballE hp hpp)
    omega
  · rw [not_le] at hpp
    by_cases hpn : p ≤ n
    · have h1 : v ≤ 1 := by
        by_contra hc
        rw [not_le] at hc
        have : p ^ 2 ≤ p ^ v := Nat.pow_le_pow_right hp.pos hc
        nlinarith
      have h2 : 1 ≤ m.factorization p :=
        (hp.dvd_iff_one_le_factorization (by omega)).1 (hm p hp hpp hpn)
      omega
    · rw [not_le] at hpn
      have h1 : v = 0 := by
        by_contra hc
        have : p ^ 1 ≤ p ^ v := Nat.pow_le_pow_right hp.pos (by omega)
        simp at this
        omega
      omega

/-- Integer version of the core divisibility. -/
theorem lcmUpTo_dvd_int (n : ℕ) (hn : 1 ≤ n) (z : ℤ)
    (hz : ∀ p : ℕ, p.Prime → 2 * n < p * p → p ≤ n → (p : ℤ) ∣ z) :
    (lcmUpTo n : ℤ) ∣ (ballE n : ℤ) * z := by
  have h := lcmUpTo_dvd n hn z.natAbs (fun p hp h1 h2 => Int.natCast_dvd.1 (hz p hp h1 h2))
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  exact h

/-- From the saving `k·v_p(lcm) - c ≤ v_p(z / lcm^k)` with `c < k` deduce `p ∣ z`. -/
theorem prime_dvd_of_val (n : ℕ) (p : ℕ) (hp : p.Prime) (hpn : p ≤ n) (k : ℕ) (c : ℤ)
    (hc : c < k) (z : ℤ)
    (h : -c ≤ padicValRat p ((z : ℚ) / (lcmUpTo n : ℚ) ^ k)) : (p : ℤ) ∣ z := by
  have := Fact.mk hp
  rcases eq_or_ne z 0 with h0 | h0
  · simp [h0]
  have hD : (lcmUpTo n : ℚ) ≠ 0 := by exact_mod_cast (lcmUpTo_pos n).ne'
  rw [padicValRat.div (by exact_mod_cast h0) (pow_ne_zero _ hD), padicValRat.pow,
    padicValRat.of_int, padicValRat.of_nat] at h
  have h1 : 1 ≤ padicValNat p (lcmUpTo n) :=
    one_le_padicValNat_of_dvd (lcmUpTo_pos n).ne' (dvd_lcmUpTo hp.one_lt.le hpn)
  have h2 : 1 ≤ padicValInt p z := by
    have : ((k : ℤ) * (padicValNat p (lcmUpTo n) : ℤ)) ≥ k := by
      have : (1 : ℤ) ≤ padicValNat p (lcmUpTo n) := by exact_mod_cast h1
      nlinarith
    omega
  have := (padicValInt_dvd_iff (p := p) 1 z).2 (Or.inr h2)
  simpa using this

theorem ball_corrected (n : ℕ) (hn : 1 ≤ n) (U V : ℚ)
    (hU : ∃ z : ℤ, (lcmUpTo n : ℚ) * U = z) (hV : ∃ z : ℤ, (lcmUpTo n : ℚ) ^ 4 * V = z)
    (hsU : ∀ p : ℕ, p.Prime → 2 * n < p * p → p ≤ n → 0 ≤ padicValRat p U)
    (hsV : ∀ p : ℕ, p.Prime → 2 * n < p * p → p ≤ n → -3 ≤ padicValRat p V) :
    (∃ z : ℤ, (ballE n : ℚ) * U = z) ∧
      (∃ z : ℤ, (ballE n : ℚ) * (lcmUpTo n : ℚ) ^ 3 * V = z) := by
  have hD : (lcmUpTo n : ℚ) ≠ 0 := by exact_mod_cast (lcmUpTo_pos n).ne'
  obtain ⟨a, ha⟩ := hU
  obtain ⟨b, hb⟩ := hV
  have hUa : U = (a : ℚ) / (lcmUpTo n : ℚ) ^ 1 := by
    rw [← ha]; field_simp
  have hVb : V = (b : ℚ) / (lcmUpTo n : ℚ) ^ 4 := by
    rw [← hb]; field_simp
  constructor
  · obtain ⟨w, hw⟩ := lcmUpTo_dvd_int n hn a (fun p hp h1 h2 =>
      prime_dvd_of_val n p hp h2 1 0 (by norm_num) a (by rw [← hUa]; simpa using hsU p hp h1 h2))
    refine ⟨w, ?_⟩
    have hw' : ((ballE n : ℤ) : ℚ) * (a : ℚ) = ((lcmUpTo n : ℤ) : ℚ) * (w : ℚ) := by
      exact_mod_cast hw
    push_cast at hw'
    rw [hUa]
    field_simp
    linarith
  · obtain ⟨w, hw⟩ := lcmUpTo_dvd_int n hn b (fun p hp h1 h2 =>
      prime_dvd_of_val n p hp h2 4 3 (by norm_num) b (by rw [← hVb]; exact hsV p hp h1 h2))
    refine ⟨w, ?_⟩
    have hw' : ((ballE n : ℤ) : ℚ) * (b : ℚ) = ((lcmUpTo n : ℤ) : ℚ) * (w : ℚ) := by
      exact_mod_cast hw
    push_cast at hw'
    rw [hVb]
    field_simp
    linarith

theorem ballE_le (n : ℕ) (hn : 1 ≤ n) : (ballE n : ℝ) ≤ (n : ℝ) ^ Real.sqrt (2 * n) := by
  set S := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p * p ≤ 2 * n) with hS
  have h1 : ballE n ≤ n ^ S.card := by
    unfold ballE
    apply Finset.prod_le_pow_card
    intro p hp
    exact Nat.pow_log_le_self p (by omega)
  have h2 : S.card ≤ Nat.sqrt (2 * n) := by
    have hsub : S ⊆ Finset.Icc 1 (Nat.sqrt (2 * n)) := by
      intro p hp
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hp
      simp only [Finset.mem_Icc]
      exact ⟨hp.2.1.one_lt.le, Nat.le_sqrt.2 hp.2.2⟩
    have := Finset.card_le_card hsub
    simpa using this
  have h3 : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ Real.sqrt (2 * n) := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    simpa using this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (ballE n : ℝ) ≤ ((n ^ S.card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (n : ℝ) ^ (S.card : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ (n : ℝ) ^ Real.sqrt (2 * n) := by
      apply Real.rpow_le_rpow_of_exponent_le hn1
      have : (S.card : ℝ) ≤ (Nat.sqrt (2 * n) : ℝ) := by exact_mod_cast h2
      linarith

end Zeta3.BallDen
