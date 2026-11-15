import Mathlib
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Mathathon.MuMod8

noncomputable def hH (n : ℕ) : ℤ := ((n.divisors.filter (fun s => Squarefree s ∧ s ^ 2 ∣ n)).card : ℤ)
noncomputable def uM (n : ℕ) : ℤ :=
  ∑ w ∈ n.divisors.filter (fun w => w ^ 2 ∣ n), ((μ * μ : ArithmeticFunction ℤ) w) * (((ζ * ζ * ζ : ArithmeticFunction ℕ) (n / w ^ 2) : ℕ) : ℤ)

/-- generic square-dilated convolution -/
noncomputable def Sq (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ w ∈ n.divisors.filter (fun w => w ^ 2 ∣ n), a w * b (n / w ^ 2)

lemma Sq_mul (a b : ℕ → ℤ) (ha : ∀ x y, x.Coprime y → a (x * y) = a x * a y)
    (hb : ∀ x y, x.Coprime y → b (x * y) = b x * b y) (m n : ℕ) (h : m.Coprime n) :
    Sq a b (m * n) = Sq a b m * Sq a b n := by
  unfold Sq
  simp only [sum_filter]
  rw [Nat.Coprime.divisors_mul h, sum_map, sum_mul_sum, ← sum_product', ← Finset.sum_attach
    (Nat.divisors m ×ˢ Nat.divisors n)]
  apply Finset.sum_congr rfl
  rintro ⟨⟨d1, d2⟩, hd⟩ _
  show (if (d1 * d2) ^ 2 ∣ m * n then a (d1 * d2) * b (m * n / (d1 * d2) ^ 2) else 0) = _
  rw [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hd
  obtain ⟨⟨hd1, hm⟩, ⟨hd2, hn⟩⟩ := hd
  have c1 : (d1 ^ 2).Coprime n := (Nat.Coprime.coprime_dvd_left hd1 h).pow_left 2
  have c2 : (d2 ^ 2).Coprime m := (Nat.Coprime.coprime_dvd_left hd2 h.symm).pow_left 2
  have hiff : (d1 * d2) ^ 2 ∣ m * n ↔ d1 ^ 2 ∣ m ∧ d2 ^ 2 ∣ n := by
    constructor
    · intro hx
      rw [mul_pow] at hx
      refine ⟨c1.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hx), ?_⟩
      exact c2.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hx)
    · rintro ⟨h1, h2⟩; rw [mul_pow]; exact mul_dvd_mul h1 h2
  by_cases hc : d1 ^ 2 ∣ m ∧ d2 ^ 2 ∣ n
  · rw [if_pos (hiff.2 hc), if_pos hc.1, if_pos hc.2]
    have cd : d1.Coprime d2 := Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.coprime_dvd_right hd2 h)
    rw [ha _ _ cd, mul_pow, ← Nat.div_mul_div_comm hc.1 hc.2]
    have cq : (m / d1 ^ 2).Coprime (n / d2 ^ 2) :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hc.1)
        (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hc.2) h)
    rw [hb _ _ cq]
    ring
  · rw [if_neg (fun hx => hc (hiff.1 hx))]
    rw [not_and_or] at hc
    rcases hc with hc | hc
    · rw [if_neg hc, zero_mul]
    · rw [if_neg hc, mul_zero]

lemma Sq_prime_pow (a b : ℕ → ℤ) (p e : ℕ) (hp : p.Prime) :
    Sq a b (p ^ e) = ∑ i ∈ range (e + 1), if 2 * i ≤ e then a (p ^ i) * b (p ^ (e - 2 * i)) else 0 := by
  unfold Sq
  rw [sum_filter, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i _
  rw [← pow_mul, mul_comm i 2]
  by_cases h : 2 * i ≤ e
  · rw [if_pos ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).2 h), if_pos h, Nat.pow_div h hp.pos]
  · rw [if_neg (fun h' => h ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h')), if_neg h]

lemma uM_eq (n : ℕ) : uM n = Sq (fun w => (μ * μ : ArithmeticFunction ℤ) w)
    (fun m => (((ζ * ζ * ζ : ArithmeticFunction ℕ) m : ℕ) : ℤ)) n := rfl

lemma hH_eq (n : ℕ) : hH n = Sq (fun w => if Squarefree w then 1 else 0) (fun _ => 1) n := by
  unfold hH Sq
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
  push_cast
  apply sum_congr rfl; intro x _
  by_cases h1 : Squarefree x <;> by_cases h2 : x ^ 2 ∣ n <;> simp [h1, h2]

theorem uM_mul (m n : ℕ) (h : m.Coprime n) : uM (m * n) = uM m * uM n := by
  simp only [uM_eq]
  apply Sq_mul _ _ _ _ m n h
  · intro x y hxy
    exact (isMultiplicative_moebius.mul isMultiplicative_moebius).map_mul_of_coprime hxy
  · intro x y hxy
    rw [((isMultiplicative_zeta.mul isMultiplicative_zeta).mul isMultiplicative_zeta).map_mul_of_coprime hxy]
    push_cast; ring

theorem hH_mul (m n : ℕ) (h : m.Coprime n) : hH (m * n) = hH m * hH n := by
  simp only [hH_eq]
  apply Sq_mul _ _ _ _ m n h
  · intro x y hxy
    by_cases hx : Squarefree x <;> by_cases hy : Squarefree y <;>
      simp [Nat.squarefree_mul_iff, hxy, hx, hy]
  · intro x y _; ring

lemma mu_pp (p j : ℕ) (hp : p.Prime) :
    (μ (p ^ j) : ℤ) = if j = 0 then 1 else if j = 1 then -1 else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [moebius_apply_prime_pow hp hj.ne', if_neg hj.ne']

lemma mumu_pp (p i : ℕ) (hp : p.Prime) :
    (μ * μ : ArithmeticFunction ℤ) (p ^ i) = if i = 0 then 1 else if i = 1 then -2 else if i = 2 then 1 else 0 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => μ x * μ y), Nat.sum_divisors_prime_pow hp]
  have e : ∀ j ∈ range (i + 1), (μ (p ^ j) : ℤ) * μ (p ^ i / p ^ j)
      = (if j = 0 then 1 else if j = 1 then -1 else 0) * (if i - j = 0 then 1 else if i - j = 1 then -1 else 0) := by
    intro j hj
    rw [Nat.pow_div (by simp at hj; omega) hp.pos, mu_pp p j hp, mu_pp p (i - j) hp]
  rw [sum_congr rfl e]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h | h
  · subst h; simp
  · subst h; simp [sum_range_succ]
  · subst h; simp [sum_range_succ]
  · rw [sum_eq_zero]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · intro j _
      by_cases h0 : j = 0
      · rw [if_pos h0, if_neg (by omega), if_neg (by omega)]; simp
      · by_cases h1 : j = 1
        · rw [if_neg h0, if_pos h1, if_neg (by omega), if_neg (by omega)]; simp
        · rw [if_neg h0, if_neg h1]; simp

lemma d3_pp (p j : ℕ) (hp : p.Prime) :
    2 * ((((ζ * ζ * ζ : ArithmeticFunction ℕ) (p ^ j)) : ℕ) : ℤ) = (j + 1) * (j + 2) := by
  have : 2 * (ζ * ζ * ζ : ArithmeticFunction ℕ) (p ^ j) = (j + 1) * (j + 2) := by
    rw [mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    have hz : ∀ i, (ζ * ζ : ArithmeticFunction ℕ) (p ^ i) = i + 1 := by
      intro i
      rw [mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
      simp [zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
    simp only [hz]
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ, mul_add, ih]; ring
  exact_mod_cast this

noncomputable def D3 (p j : ℕ) : ℤ := (((ζ * ζ * ζ : ArithmeticFunction ℕ) (p ^ j) : ℕ) : ℤ)

theorem uM_prime_pow (p e : ℕ) (hp : p.Prime) : uM (p ^ e) = if e = 0 then 1 else if e = 1 then 3 else 4 := by
  rw [uM_eq, Sq_prime_pow _ _ p e hp]
  simp only [mumu_pp _ _ hp]
  have h0 := d3_pp p 0 hp
  have h1 := d3_pp p 1 hp
  have h2 := d3_pp p 2 hp
  have h3 := d3_pp p 3 hp
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ 4 ≤ e) with h | h | h | h | h
  · subst h; norm_num at h0 ⊢; first | done | linarith
  · subst h; norm_num [sum_range_succ] at h0 h1 ⊢; first | done | linarith
  · subst h; norm_num [sum_range_succ] at h0 h1 h2 ⊢; first | done | linarith
  · subst h; norm_num [sum_range_succ] at h0 h1 h2 h3 ⊢; first | done | linarith
  · obtain ⟨f, rfl⟩ : ∃ f, e = f + 4 := ⟨e - 4, by omega⟩
    change ∑ i ∈ range (f + 4 + 1), (if 2 * i ≤ f + 4 then
      (if i = 0 then 1 else if i = 1 then -2 else if i = 2 then 1 else 0) * D3 p (f + 4 - 2 * i) else 0) = _
    have hpt : ∀ i ∈ range (f + 4 + 1), (if 2 * i ≤ f + 4 then
        (if i = 0 then 1 else if i = 1 then -2 else if i = 2 then 1 else 0) * D3 p (f + 4 - 2 * i) else 0)
        = (if i = 0 then D3 p (f + 4) else 0) + (if i = 1 then -2 * D3 p (f + 2) else 0)
          + (if i = 2 then D3 p f else 0) := by
      intro i _
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with hi | hi | hi | hi
      · subst hi; simp
      · subst hi; simp [show f + 4 - 2 = f + 2 by omega]
      · subst hi; simp [show f + 4 - 4 = f by omega]
      · split_ifs <;> first | omega | simp
    rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', sum_ite_eq']
    rw [if_pos (by simp), if_pos (by simp), if_pos (by simp)]
    have hA : 2 * D3 p (f + 4) = ((f + 4 : ℕ) + 1) * ((f + 4 : ℕ) + 2) := d3_pp p (f + 4) hp
    have hB : 2 * D3 p (f + 2) = ((f + 2 : ℕ) + 1) * ((f + 2 : ℕ) + 2) := d3_pp p (f + 2) hp
    have hC : 2 * D3 p f = ((f : ℕ) + 1) * ((f : ℕ) + 2) := d3_pp p f hp
    push_cast at hA hB hC
    rw [if_neg (by omega), if_neg (by omega)]
    linarith

lemma sqf_pp (p i : ℕ) (hp : p.Prime) :
    (if Squarefree (p ^ i) then (1 : ℤ) else 0) = if i ≤ 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · simp only [Nat.squarefree_pow_iff hp.ne_one hi.ne']
    by_cases h1 : i = 1
    · subst h1; simp [hp.squarefree]
    · have : ¬ i ≤ 1 := by omega
      simp [h1, this]

theorem hH_prime_pow (p e : ℕ) (hp : p.Prime) : hH (p ^ e) = if e ≤ 1 then 1 else 2 := by
  rw [hH_eq, Sq_prime_pow _ _ p e hp]
  simp only [sqf_pp _ _ hp, mul_one]
  rcases (by omega : e = 0 ∨ e = 1 ∨ 2 ≤ e) with h | h | h
  · subst h; simp
  · subst h; simp [sum_range_succ]
  · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
    rw [show f + 2 + 1 = f + 1 + 1 + 1 by ring, sum_range_succ', sum_range_succ',
      sum_eq_zero (fun i _ => by split_ifs <;> first | rfl | omega)]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    norm_num

theorem mu_pattern (n : ℕ) (hn : 1 ≤ n) : ∃ k a : ℕ, uM n = 3 ^ k * 4 ^ a ∧ hH n = 2 ^ a ∧
    (μ n : ℤ) = if a = 0 then (-1) ^ k else 0 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one =>
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · have := uM_prime_pow 2 0 Nat.prime_two; simpa using this
    · have := hH_prime_pow 2 0 Nat.prime_two; simpa using this
    · simp
  | prime_pow p e hp he =>
    rcases (by omega : e = 1 ∨ 2 ≤ e) with h | h
    · subst h
      refine ⟨1, 0, ?_, ?_, ?_⟩
      · rw [uM_prime_pow p 1 hp]; simp
      · rw [hH_prime_pow p 1 hp]; simp
      · rw [pow_one, moebius_apply_prime hp]; simp
    · refine ⟨0, 1, ?_, ?_, ?_⟩
      · rw [uM_prime_pow p e hp, if_neg (by omega), if_neg (by omega)]; simp
      · rw [hH_prime_pow p e hp, if_neg (by omega)]; simp
      · rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]; simp
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨k1, a1, hu1, hh1, hm1⟩ := iha (by omega)
    obtain ⟨k2, a2, hu2, hh2, hm2⟩ := ihb (by omega)
    refine ⟨k1 + k2, a1 + a2, ?_, ?_, ?_⟩
    · rw [uM_mul a b hab, hu1, hu2]; ring
    · rw [hH_mul a b hab, hh1, hh2]; ring
    · rw [isMultiplicative_moebius.map_mul_of_coprime hab]
      push_cast
      rw [hm1, hm2]
      by_cases h1 : a1 = 0 <;> by_cases h2 : a2 = 0 <;> simp [h1, h2, pow_add]

theorem mu_mod8 (n : ℕ) (hn : 1 ≤ n) : (μ n : ℤ) ≡ 2 * hH n - uM n [ZMOD 8] := by
  obtain ⟨k, a, hu, hh, hm⟩ := mu_pattern n hn
  rw [hu, hh, hm, Int.modEq_iff_dvd]
  have h9 : ∀ j : ℕ, (8 : ℤ) ∣ 1 - 9 ^ j := by
    intro j
    exact Int.modEq_iff_dvd.1 ((show (9 : ℤ) ≡ 1 [ZMOD 8] by decide).pow j |>.trans (by rw [one_pow]))
  rcases (by omega : a = 0 ∨ a = 1 ∨ 2 ≤ a) with ha | ha | ha
  · subst ha
    rw [if_pos rfl]
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have e : (2 : ℤ) * 2 ^ 0 - 3 ^ (2 * j) * 4 ^ 0 - (-1) ^ (2 * j) = 1 - 9 ^ j := by
        rw [pow_mul, pow_mul]; norm_num; ring
      rw [e]; exact h9 j
    · have e : (2 : ℤ) * 2 ^ 0 - 3 ^ (2 * j + 1) * 4 ^ 0 - (-1) ^ (2 * j + 1) = 3 * (1 - 9 ^ j) := by
        rw [pow_succ, pow_succ, pow_mul, pow_mul]; norm_num; ring
      rw [e]; exact dvd_mul_of_dvd_right (h9 j) 3
  · subst ha
    rw [if_neg (by norm_num)]
    have hodd : Odd ((3 : ℤ) ^ k) := Odd.pow (by decide)
    obtain ⟨t, ht⟩ := hodd
    exact ⟨-t, by rw [ht]; ring⟩
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    rw [if_neg (by omega)]
    exact ⟨2 ^ b - 2 * 3 ^ k * 4 ^ b, by ring⟩

end Mathathon.MuMod8
