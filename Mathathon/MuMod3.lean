import Mathlib
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

/-!
# The pointwise congruence μ(n) ≡ Σ_{d³ ∣ n} μ(d) σ₀(n/d³) (mod 3)

Here `μ` is Mathlib's `ArithmeticFunction.moebius` and σ₀(m) is the number of divisors of `m`,
written `(Nat.divisors m).card`. Both sides are multiplicative in `n`; on a prime power `p ^ e`
the right side is `(e + 1) - [e ≥ 3] (e - 2)`, i.e. `1, 2, 3, 3, 3, …`, which is `μ(p ^ e) = 1, -1, 0, 0, …`
modulo 3.
-/

namespace Mathathon.MuMod3

/-- Generic cube-dilated convolution `Σ_{d³ ∣ n} a(d) b(n / d³)`. -/
noncomputable def Cu (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ∣ n), a d * b (n / d ^ 3)

lemma Cu_mul (a b : ℕ → ℤ) (ha : ∀ x y, x.Coprime y → a (x * y) = a x * a y)
    (hb : ∀ x y, x.Coprime y → b (x * y) = b x * b y) (m n : ℕ) (h : m.Coprime n) :
    Cu a b (m * n) = Cu a b m * Cu a b n := by
  unfold Cu
  simp only [sum_filter]
  rw [Nat.Coprime.divisors_mul h, sum_map, sum_mul_sum, ← sum_product', ← Finset.sum_attach
    (Nat.divisors m ×ˢ Nat.divisors n)]
  apply Finset.sum_congr rfl
  rintro ⟨⟨d1, d2⟩, hd⟩ _
  show (if (d1 * d2) ^ 3 ∣ m * n then a (d1 * d2) * b (m * n / (d1 * d2) ^ 3) else 0) = _
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
    have cd : d1.Coprime d2 :=
      Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.coprime_dvd_right hd2 h)
    rw [ha _ _ cd, mul_pow, ← Nat.div_mul_div_comm hc.1 hc.2]
    have cq : (m / d1 ^ 3).Coprime (n / d2 ^ 3) :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hc.1)
        (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hc.2) h)
    rw [hb _ _ cq]
    ring
  · rw [if_neg (fun hx => hc (hiff.1 hx))]
    rw [not_and_or] at hc
    rcases hc with hc | hc
    · rw [if_neg hc, zero_mul]
    · rw [if_neg hc, mul_zero]

lemma Cu_prime_pow (a b : ℕ → ℤ) (p e : ℕ) (hp : p.Prime) :
    Cu a b (p ^ e) =
      ∑ i ∈ range (e + 1), if 3 * i ≤ e then a (p ^ i) * b (p ^ (e - 3 * i)) else 0 := by
  unfold Cu
  rw [sum_filter, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i _
  rw [← pow_mul, mul_comm i 3]
  by_cases h : 3 * i ≤ e
  · rw [if_pos ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).2 h), if_pos h, Nat.pow_div h hp.pos]
  · rw [if_neg (fun h' => h ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h')), if_neg h]

lemma mu_pp (p j : ℕ) (hp : p.Prime) :
    (μ (p ^ j) : ℤ) = if j = 0 then 1 else if j = 1 then -1 else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [moebius_apply_prime_pow hp hj.ne', if_neg hj.ne']

/-- σ₀ as an integer-valued function. -/
lemma card_divisors_eq (m : ℕ) : ((m.divisors.card : ℕ) : ℤ) = ((σ 0 m : ℕ) : ℤ) := by
  rw [sigma_zero_apply]

lemma card_divisors_pp (p k : ℕ) (hp : p.Prime) : (((p ^ k).divisors.card : ℕ) : ℤ) = k + 1 := by
  rw [card_divisors_eq, sigma_zero_apply_prime_pow hp]; push_cast; ring

/-- The right-hand side of the congruence, as a cube-dilated convolution. -/
lemma rhs_eq (n : ℕ) :
    (∑ d ∈ n.divisors.filter (fun d => d ^ 3 ∣ n), (μ d : ℤ) * ((n / d ^ 3).divisors.card : ℤ))
      = Cu (fun d => (μ d : ℤ)) (fun m => (m.divisors.card : ℤ)) n := rfl

lemma rhs_mul (m n : ℕ) (h : m.Coprime n) :
    Cu (fun d => (μ d : ℤ)) (fun m => (m.divisors.card : ℤ)) (m * n)
      = Cu (fun d => (μ d : ℤ)) (fun m => (m.divisors.card : ℤ)) m
        * Cu (fun d => (μ d : ℤ)) (fun m => (m.divisors.card : ℤ)) n := by
  apply Cu_mul _ _ _ _ m n h
  · intro x y hxy
    exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hxy
  · intro x y hxy
    simp only [card_divisors_eq]
    rw [isMultiplicative_sigma.map_mul_of_coprime hxy]
    push_cast; ring

/-- On a prime power, the right-hand side is `(e + 1) - [e ≥ 3] (e - 2)`. -/
lemma rhs_prime_pow (p e : ℕ) (hp : p.Prime) :
    Cu (fun d => (μ d : ℤ)) (fun m => (m.divisors.card : ℤ)) (p ^ e)
      = if e = 0 then 1 else if e = 1 then 2 else 3 := by
  rw [Cu_prime_pow _ _ p e hp]
  simp only [mu_pp _ _ hp, card_divisors_pp _ _ hp]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ 3 ≤ e) with h | h | h | h
  · subst h; norm_num
  · subst h; norm_num [sum_range_succ]
  · subst h; norm_num [sum_range_succ]
  · obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
    rw [show f + 3 + 1 = f + 2 + 1 + 1 by ring, sum_range_succ', sum_range_succ',
      sum_eq_zero (fun i _ => by simp)]
    have e1 : f + 3 - 3 * (0 + 1) = f := by omega
    have e0 : f + 3 - 3 * 0 = f + 3 := by omega
    simp only [e1, e0, if_pos (show 3 * (0 + 1) ≤ f + 3 by omega), if_pos (show 3 * 0 ≤ f + 3 by omega),
      if_neg (show f + 3 ≠ 0 by omega), if_neg (show f + 3 ≠ 1 by omega)]
    norm_num
    ring

/-- **Pointwise congruence for μ modulo 3.** For every `n ≥ 1`,
`μ(n) ≡ Σ_{d ≥ 1, d³ ∣ n} μ(d) · σ₀(n / d³)  (mod 3)`,
where `σ₀(m) = #{divisors of m}` is written `(Nat.divisors m).card`. -/
theorem mu_mod3 (n : ℕ) (hn : 1 ≤ n) :
    (μ n : ℤ) ≡ ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ∣ n),
      (μ d : ℤ) * ((n / d ^ 3).divisors.card : ℤ) [ZMOD 3] := by
  rw [rhs_eq]
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one =>
    have := rhs_prime_pow 2 0 Nat.prime_two
    rw [pow_zero] at this
    rw [this]; simp
  | prime_pow p e hp he =>
    rw [rhs_prime_pow p e hp, mu_pp p e hp]
    rcases (by omega : e = 1 ∨ 2 ≤ e) with h | h
    · subst h; decide
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; decide
  | coprime a b ha hb hab iha ihb =>
    rw [isMultiplicative_moebius.map_mul_of_coprime hab, rhs_mul a b hab]
    exact (iha (by omega)).mul (ihb (by omega))

/-- Rearrangement of the finite double sum: `n = d³ m`. -/
lemma rearrange (N : ℕ) (F : ℕ → ℕ → ℤ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ∣ n), F d (n / d ^ 3)
      = ∑ d ∈ (Icc 1 N).filter (fun d => d ^ 3 ≤ N), ∑ m ∈ Icc 1 (N / d ^ 3), F d m := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1 / x.2 ^ 3⟩) (fun y _ => ⟨y.1 ^ 3 * y.2, y.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨h1, h2⟩, ⟨hdn, hn0⟩, hd3⟩ := hx
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
    have hd3pos : 0 < d ^ 3 := pow_pos hd 3
    have hle : d ^ 3 ≤ n := Nat.le_of_dvd (by omega) hd3
    refine ⟨⟨⟨hd, le_trans (Nat.le_of_dvd (by omega) hdn) h2⟩, le_trans hle h2⟩, ?_,
      Nat.div_le_div_right h2⟩
    exact (Nat.le_div_iff_mul_le hd3pos).2 (by simpa using hle)
  · rintro ⟨d, m⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hy ⊢
    obtain ⟨⟨⟨hd1, hdN⟩, hd3N⟩, hm1, hmN⟩ := hy
    have hd3pos : 0 < d ^ 3 := pow_pos (by omega) 3
    have hle : m * d ^ 3 ≤ N := (Nat.le_div_iff_mul_le hd3pos).1 hmN
    refine ⟨⟨?_, by rw [mul_comm]; exact hle⟩, ⟨(dvd_pow_self d (by norm_num)).mul_right m, ?_⟩,
      Dvd.intro m rfl⟩
    · exact Nat.mul_pos hd3pos (by omega)
    · exact (Nat.mul_pos hd3pos (by omega)).ne'
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hx
    simp only [Nat.mul_div_cancel' hx.2.2]
  · rintro ⟨d, m⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at hy
    have hd3pos : 0 < d ^ 3 := pow_pos (by omega) 3
    simp only [Nat.mul_div_cancel_left m hd3pos]
  · rintro ⟨n, d⟩ _
    rfl

/-- **Summed form.** For every `N`, with `M(N) = Σ_{n=1}^{N} μ(n)` and `D(y) = Σ_{m=1}^{y} σ₀(m)`,
`M(N) ≡ Σ_{1 ≤ d, d³ ≤ N} μ(d) · D(⌊N / d³⌋)  (mod 3)`,
where `σ₀(m) = #{divisors of m}` is written `(Nat.divisors m).card`. -/
theorem mertens_mod3 (N : ℕ) :
    (∑ n ∈ Icc 1 N, (μ n : ℤ)) ≡
      ∑ d ∈ (Icc 1 N).filter (fun d => d ^ 3 ≤ N),
        (μ d : ℤ) * ∑ m ∈ Icc 1 (N / d ^ 3), (m.divisors.card : ℤ) [ZMOD 3] := by
  have hr := rearrange N (fun d m => (μ d : ℤ) * (m.divisors.card : ℤ))
  simp only [← Finset.mul_sum] at hr
  rw [← hr, Int.modEq_iff_dvd, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro n hn
  exact Int.modEq_iff_dvd.1 (mu_mod3 n (Finset.mem_Icc.1 hn).1)

end Mathathon.MuMod3
