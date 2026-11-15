import Mathlib
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Mathathon.LemmaF

/-- f = μ^{[3]} * d_3 -/
noncomputable def fTCH (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ∣ n), (μ d : ℤ) * (((ζ * ζ * ζ : ArithmeticFunction ℕ) (n / d ^ 3) : ℕ) : ℤ)

lemma d3_mult : IsMultiplicative (ζ * ζ * ζ : ArithmeticFunction ℕ) :=
  (isMultiplicative_zeta.mul isMultiplicative_zeta).mul isMultiplicative_zeta

theorem fTCH_one : fTCH 1 = 1 := by
  unfold fTCH
  rw [Nat.divisors_one, sum_filter, sum_singleton, if_pos (by norm_num)]
  simp only [one_pow, Nat.div_one, moebius_apply_one, d3_mult.map_one]
  norm_num

lemma zz_prime_pow (p i : ℕ) (hp : p.Prime) : (ζ * ζ : ArithmeticFunction ℕ) (p ^ i) = i + 1 := by
  rw [mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  simp [zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]

lemma d3_prime_pow (p j : ℕ) (hp : p.Prime) :
    2 * (ζ * ζ * ζ : ArithmeticFunction ℕ) (p ^ j) = (j + 1) * (j + 2) := by
  rw [mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  simp only [zz_prime_pow _ _ hp]
  induction j with
  | zero => simp
  | succ j ih => rw [sum_range_succ, mul_add, ih]; ring

theorem fTCH_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) : fTCH (p ^ k) = 3 * k := by
  unfold fTCH
  rw [sum_filter, Nat.sum_divisors_prime_pow hp, sum_range_succ']
  rw [Finset.sum_eq_single 0]
  · simp only [zero_add, pow_one, pow_zero, one_pow, one_dvd, if_true, Nat.div_one,
      moebius_apply_one, one_mul]
    have hA := d3_prime_pow p k hp
    by_cases h3 : 3 ≤ k
    · rw [if_pos ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).2 h3), Nat.pow_div h3 hp.pos,
        moebius_apply_prime hp]
      have hB := d3_prime_pow p (k - 3) hp
      have hA' : (2 : ℤ) * ((ζ * ζ * ζ : ArithmeticFunction ℕ) (p ^ k) : ℤ) = (k + 1) * (k + 2) := by
        exact_mod_cast hA
      have hB' : (2 : ℤ) * ((ζ * ζ * ζ : ArithmeticFunction ℕ) (p ^ (k - 3)) : ℤ)
          = ((k - 3 : ℕ) + 1) * ((k - 3 : ℕ) + 2) := by
        exact_mod_cast hB
      push_cast [h3] at hB' ⊢
      linarith
    · rw [if_neg (fun h => h3 ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h))]
      have hA' : (2 : ℤ) * ((ζ * ζ * ζ : ArithmeticFunction ℕ) (p ^ k) : ℤ) = (k + 1) * (k + 2) := by
        exact_mod_cast hA
      interval_cases k <;> push_cast at hA' ⊢ <;> linarith
  · intro i _ hi
    rw [moebius_apply_prime_pow hp (by omega), if_neg (show ¬ (i + 1 = 1) by omega)]
    simp
  · intro h; exact absurd (mem_range.2 (by omega)) h

theorem fTCH_mul (m n : ℕ) (h : m.Coprime n) : fTCH (m * n) = fTCH m * fTCH n := by
  unfold fTCH
  simp only [sum_filter]
  rw [Nat.Coprime.divisors_mul h, sum_map, sum_mul_sum, ← sum_product', ← Finset.sum_attach
    (Nat.divisors m ×ˢ Nat.divisors n)]
  apply Finset.sum_congr rfl
  rintro ⟨⟨d1, d2⟩, hd⟩ _
  show (if (d1 * d2) ^ 3 ∣ m * n then (μ (d1 * d2) : ℤ) *
      (((ζ * ζ * ζ : ArithmeticFunction ℕ) (m * n / (d1 * d2) ^ 3) : ℕ) : ℤ) else 0) = _
  rw [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hd
  obtain ⟨⟨hd1, hm⟩, ⟨hd2, hn⟩⟩ := hd
  have c1 : (d1 ^ 3).Coprime n := (Nat.Coprime.coprime_dvd_left hd1 h).pow_left 3
  have c2 : (d2 ^ 3).Coprime m := (Nat.Coprime.coprime_dvd_left hd2 h.symm).pow_left 3
  have hiff : (d1 * d2) ^ 3 ∣ m * n ↔ d1 ^ 3 ∣ m ∧ d2 ^ 3 ∣ n := by
    constructor
    · intro hx
      rw [mul_pow] at hx
      refine ⟨c1.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hx), ?_⟩
      exact c2.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hx)
    · rintro ⟨h1, h2⟩; rw [mul_pow]; exact mul_dvd_mul h1 h2
  by_cases hc : d1 ^ 3 ∣ m ∧ d2 ^ 3 ∣ n
  · rw [if_pos (hiff.2 hc), if_pos hc.1, if_pos hc.2]
    have cd : d1.Coprime d2 := Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.coprime_dvd_right hd2 h)
    rw [isMultiplicative_moebius.map_mul_of_coprime cd, mul_pow,
      ← Nat.div_mul_div_comm hc.1 hc.2]
    have cq : (m / d1 ^ 3).Coprime (n / d2 ^ 3) :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hc.1)
        (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hc.2) h)
    rw [d3_mult.map_mul_of_coprime cq]
    push_cast; ring
  · rw [if_neg (fun hx => hc (hiff.1 hx))]
    rw [not_and_or] at hc
    rcases hc with hc | hc
    · rw [if_neg hc, zero_mul]
    · rw [if_neg hc, mul_zero]

lemma three_dvd_fTCH (m q : ℕ) (hm : m ≠ 0) (hq : q.Prime) (hqm : q ∣ m) : (3 : ℤ) ∣ fTCH m := by
  rw [← Nat.ordProj_mul_ordCompl_eq_self m q,
    fTCH_mul _ _ ((Nat.coprime_ordCompl hq hm).pow_left _),
    fTCH_prime_pow q _ hq (hq.factorization_pos_of_dvd hm hqm)]
  exact dvd_mul_of_dvd_left (Dvd.intro _ rfl) _

theorem fTCH_dvd_nine (n : ℕ) (hn : 2 ≤ n.primeFactors.card) : (9 : ℤ) ∣ fTCH n := by
  obtain ⟨p, hp, q, hq, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < n.primeFactors.card)
  have hn0 : n ≠ 0 := by rintro rfl; simp at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq
  set a := n.factorization p
  set m := n / p ^ a
  have hnm : p ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hm0 : m ≠ 0 := by rintro hm; rw [hm, mul_zero] at hnm; exact hn0 hnm.symm
  have cqp : q.Coprime (p ^ a) := Nat.Coprime.pow_right a ((Nat.coprime_primes hqp hpp).2 hne.symm)
  have hqm : q ∣ m := cqp.dvd_of_dvd_mul_left (hnm ▸ hqn)
  rw [← hnm, fTCH_mul _ _ ((Nat.coprime_ordCompl hpp hn0).pow_left _),
    fTCH_prime_pow p _ hpp (hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp))]
  obtain ⟨t, ht⟩ := three_dvd_fTCH m q hm0 hqp hqm
  rw [ht]
  exact ⟨a * t, by ring⟩

end Mathathon.LemmaF
