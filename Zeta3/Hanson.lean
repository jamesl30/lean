import Mathlib

/-!
# `lcm(1, …, n) < 3 ^ n` for every `n ≥ 1` (Hanson 1972, Theorem 1)

Route (a truncation of Hanson's argument, with Sylvester's numbers `2, 3, 7, 43` and
`1806 = 2 · 3 · 7 · 43`, so that `1/2 + 1/3 + 1/7 + 1/43 + 1/1806 = 1`):

* `key_dvd`: `d_n · ⌊n/2⌋! ⌊n/3⌋! ⌊n/7⌋! ⌊n/43⌋! ⌊n/1806⌋!` divides `d_⌊n/1806⌋ · n!`
  (Legendre's formula; for `1 ≤ m < 1806`, `⌊m/2⌋ + ⌊m/3⌋ + ⌊m/7⌋ + ⌊m/43⌋ ≤ m - 1`).
* `multinomial_bound`: `(a+b+c+d+e)! ≤ 2^a 3^b 7^c 43^d 1806^e · a! b! c! d! e!`
  (one term of the multinomial expansion of `(1/2 + 1/3 + 1/7 + 1/43 + 1/1806)^(a+b+c+d+e) = 1`).
* `lcm_le`: `d_n ≤ d_⌊n/1806⌋ · n^4 · 2^⌊n/2⌋ 3^⌊n/3⌋ 7^⌊n/7⌋ 43^⌊n/43⌋ 1806^⌊n/1806⌋`.
* `H_lt`: the right-hand side with `d_⌊n/1806⌋` replaced by `3^⌊n/1806⌋` is `< 3^n` for `n ≥ 1850`
  (kernel evaluation for `1850 ≤ n < 3656`, then a step of length `1806`).
* `loop_1849`: `d_n < 3^n` for `1 ≤ n ≤ 1849` by kernel evaluation.
-/

set_option autoImplicit false

-- CLAIMED: Zeta3.Hanson.lcm_Icc_lt_three_pow, Zeta3.Hanson.lcm_Icc_lt_three_pow_real

namespace Zeta3.Hanson

open Finset

/-! ### The multinomial bound -/

lemma binom_step (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (s t : ℕ) :
    ((s + t).factorial : ℝ) * (x ^ s * y ^ t)
      ≤ (x + y) ^ (s + t) * ((s.factorial : ℝ) * t.factorial) := by
  have hterm : x ^ s * y ^ t * ((s + t).choose s : ℝ) ≤ (x + y) ^ (s + t) := by
    rw [add_pow x y (s + t)]
    have := Finset.single_le_sum
      (f := fun m => x ^ m * y ^ (s + t - m) * ((s + t).choose m : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.2 (by omega : s < s + t + 1))
    simpa using this
  have hc : (((s + t).choose s : ℕ) : ℝ) * ((s.factorial : ℝ) * t.factorial)
      = (s + t).factorial := by
    have h := Nat.add_choose_mul_factorial_mul_factorial t s
    rw [add_comm t s] at h
    have h' := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at h'
    rw [← h']
    ring
  calc ((s + t).factorial : ℝ) * (x ^ s * y ^ t)
      = (x ^ s * y ^ t * ((s + t).choose s : ℝ)) * ((s.factorial : ℝ) * t.factorial) := by
        rw [← hc]; ring
    _ ≤ (x + y) ^ (s + t) * ((s.factorial : ℝ) * t.factorial) := by
        exact mul_le_mul_of_nonneg_right hterm (by positivity)

lemma multi_step (σ x w P : ℝ) (T k : ℕ) (hσ : 0 < σ) (hx : 0 ≤ x) (hw : 0 ≤ w) (_hP : 0 ≤ P)
    (h : (T.factorial : ℝ) * w ≤ σ ^ T * P) :
    ((T + k).factorial : ℝ) * (w * x ^ k) ≤ (σ + x) ^ (T + k) * (P * k.factorial) := by
  have h1 := binom_step σ x hσ.le hx T k
  have hpos : (0 : ℝ) < σ ^ T * T.factorial := by positivity
  have h2 := mul_le_mul h1 h (by positivity) (by positivity)
  refine le_of_mul_le_mul_right ?_ hpos
  calc ((T + k).factorial : ℝ) * (w * x ^ k) * (σ ^ T * T.factorial)
      = ((T + k).factorial : ℝ) * (σ ^ T * x ^ k) * ((T.factorial : ℝ) * w) := by ring
    _ ≤ (σ + x) ^ (T + k) * ((T.factorial : ℝ) * k.factorial) * (σ ^ T * P) := h2
    _ = (σ + x) ^ (T + k) * (P * k.factorial) * (σ ^ T * T.factorial) := by ring

lemma multinomial_bound (a b c d e : ℕ) :
    (a + b + c + d + e).factorial
      ≤ 2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ e
        * (a.factorial * b.factorial * c.factorial * d.factorial * e.factorial) := by
  have h0 : (a.factorial : ℝ) * (1 / 2 : ℝ) ^ a ≤ (1 / 2 : ℝ) ^ a * a.factorial :=
    le_of_eq (mul_comm _ _)
  have h1 := multi_step (1 / 2) (1 / 3) ((1 / 2 : ℝ) ^ a) a.factorial a b
    (by norm_num) (by norm_num) (by positivity) (by positivity) h0
  have h2 := multi_step (1 / 2 + 1 / 3) (1 / 7) _ _ (a + b) c
    (by norm_num) (by norm_num) (by positivity) (by positivity) h1
  have h3 := multi_step (1 / 2 + 1 / 3 + 1 / 7) (1 / 43) _ _ (a + b + c) d
    (by norm_num) (by norm_num) (by positivity) (by positivity) h2
  have h4 := multi_step (1 / 2 + 1 / 3 + 1 / 7 + 1 / 43) (1 / 1806) _ _ (a + b + c + d) e
    (by norm_num) (by norm_num) (by positivity) (by positivity) h3
  have hone : (1 / 2 + 1 / 3 + 1 / 7 + 1 / 43 + 1 / 1806 : ℝ) = 1 := by norm_num
  rw [hone, one_pow, one_mul] at h4
  have hw : ((1 / 2 : ℝ) ^ a * (1 / 3) ^ b * (1 / 7) ^ c * (1 / 43) ^ d * (1 / 1806) ^ e)
      * (2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ e) = 1 := by
    simp only [one_div, inv_pow]
    field_simp
  have hreal : ((a + b + c + d + e).factorial : ℝ)
      ≤ 2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ e
        * ((a.factorial : ℝ) * b.factorial * c.factorial * d.factorial * e.factorial) := by
    calc ((a + b + c + d + e).factorial : ℝ)
        = ((a + b + c + d + e).factorial : ℝ)
            * ((1 / 2 : ℝ) ^ a * (1 / 3) ^ b * (1 / 7) ^ c * (1 / 43) ^ d * (1 / 1806) ^ e)
            * (2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ e) := by
          rw [mul_assoc, hw, mul_one]
      _ ≤ ((a.factorial : ℝ) * b.factorial * c.factorial * d.factorial * e.factorial)
            * (2 ^ a * 3 ^ b * 7 ^ c * 43 ^ d * 1806 ^ e) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := mul_comm _ _
  exact_mod_cast hreal

lemma fact_le (S r : ℕ) : (S + r).factorial ≤ S.factorial * (S + r) ^ r := by
  rw [← Nat.factorial_mul_ascFactorial]
  exact Nat.mul_le_mul_left _ (Nat.ascFactorial_le_pow_add S r)

/-! ### The divisibility -/

lemma key_dvd (n : ℕ) :
    Nat.lcmUpto n * ((n / 2).factorial * (n / 3).factorial * (n / 7).factorial
        * (n / 43).factorial * (n / 1806).factorial)
      ∣ Nat.lcmUpto (n / 1806) * n.factorial := by
  have hF : 0 < (n / 2).factorial * (n / 3).factorial * (n / 7).factorial
        * (n / 43).factorial * (n / 1806).factorial := by positivity
  rw [← Nat.factorization_prime_le_iff_dvd (mul_pos (Nat.lcmUpto_pos n) hF).ne'
    (mul_pos (Nat.lcmUpto_pos _) (Nat.factorial_pos n)).ne']
  intro p hp
  have hB : ∀ m ≤ n, Nat.log p m < Nat.log p n + 1 :=
    fun m hm => Nat.lt_succ_of_le (Nat.log_mono_right hm)
  rw [Nat.factorization_mul (Nat.lcmUpto_ne_zero n) hF.ne',
    Nat.factorization_mul (Nat.lcmUpto_ne_zero _) (Nat.factorial_ne_zero n),
    Nat.factorization_mul (by positivity) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (by positivity) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (by positivity) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_lcmUpto n hp, Nat.factorization_lcmUpto _ hp,
    Nat.factorization_factorial hp (hB n le_rfl),
    Nat.factorization_factorial hp (hB (n / 2) (Nat.div_le_self _ _)),
    Nat.factorization_factorial hp (hB (n / 3) (Nat.div_le_self _ _)),
    Nat.factorization_factorial hp (hB (n / 7) (Nat.div_le_self _ _)),
    Nat.factorization_factorial hp (hB (n / 43) (Nat.div_le_self _ _)),
    Nat.factorization_factorial hp (hB (n / 1806) (Nat.div_le_self _ _))]
  have key : ∀ i ∈ Ico 1 (Nat.log p n + 1),
      1 + (n / 2 / p ^ i + n / 3 / p ^ i + n / 7 / p ^ i + n / 43 / p ^ i + n / 1806 / p ^ i)
        ≤ (if p ^ i ≤ n / 1806 then 1 else 0) + n / p ^ i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [Nat.log_zero_right] at hi
      omega
    have hq : 0 < p ^ i := pow_pos hp.pos i
    have hqn : p ^ i ≤ n := Nat.pow_le_of_le_log hn0 (by omega)
    have he : (p ^ i ≤ n / 1806) ↔ 1806 ≤ n / p ^ i := by
      rw [Nat.le_div_iff_mul_le (by norm_num), Nat.le_div_iff_mul_le hq, mul_comm]
    have hm : 1 ≤ n / p ^ i := (Nat.le_div_iff_mul_le hq).2 (by simpa using hqn)
    rw [Nat.div_right_comm n 2, Nat.div_right_comm n 3, Nat.div_right_comm n 7,
      Nat.div_right_comm n 43, Nat.div_right_comm n 1806]
    simp only [he]
    generalize n / p ^ i = m at hm ⊢
    split_ifs with h <;> omega
  have hs := Finset.sum_le_sum key
  have hcard : ∑ i ∈ Ico 1 (Nat.log p n + 1), (if p ^ i ≤ n / 1806 then 1 else 0)
      ≤ Nat.log p (n / 1806) := by
    rw [← Finset.card_filter]
    calc _ ≤ (Ico 1 (Nat.log p (n / 1806) + 1)).card := Finset.card_le_card (fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
            exact ⟨hi.1.1, Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp.one_lt hi.2)⟩)
      _ = _ := by simp
  have h1 : ∑ _i ∈ Ico 1 (Nat.log p n + 1), 1 = Nat.log p n := by simp
  simp only [Finset.sum_add_distrib] at hs
  rw [h1] at hs
  omega

/-! ### The recursive inequality -/

/-- `2^⌊n/2⌋ 3^⌊n/3⌋ 7^⌊n/7⌋ 43^⌊n/43⌋ 1806^⌊n/1806⌋`. -/
def G (n : ℕ) : ℕ := 2 ^ (n / 2) * 3 ^ (n / 3) * 7 ^ (n / 7) * 43 ^ (n / 43) * 1806 ^ (n / 1806)

lemma lcm_le (n : ℕ) (hn : 1 ≤ n) :
    Nat.lcmUpto n ≤ Nat.lcmUpto (n / 1806) * (n ^ 4 * G n) := by
  have hF : 0 < (n / 2).factorial * (n / 3).factorial * (n / 7).factorial
        * (n / 43).factorial * (n / 1806).factorial := by positivity
  have hd := Nat.le_of_dvd (mul_pos (Nat.lcmUpto_pos _) (Nat.factorial_pos n)) (key_dvd n)
  obtain ⟨r, hr, hr4⟩ : ∃ r, n = (n / 2 + n / 3 + n / 7 + n / 43 + n / 1806) + r ∧ r ≤ 4 :=
    ⟨n - (n / 2 + n / 3 + n / 7 + n / 43 + n / 1806), by omega, by omega⟩
  have hfac : n.factorial ≤ G n * ((n / 2).factorial * (n / 3).factorial * (n / 7).factorial
        * (n / 43).factorial * (n / 1806).factorial) * n ^ 4 := by
    calc n.factorial = ((n / 2 + n / 3 + n / 7 + n / 43 + n / 1806) + r).factorial :=
          congrArg Nat.factorial hr
      _ ≤ (n / 2 + n / 3 + n / 7 + n / 43 + n / 1806).factorial
            * ((n / 2 + n / 3 + n / 7 + n / 43 + n / 1806) + r) ^ r := fact_le _ _
      _ = (n / 2 + n / 3 + n / 7 + n / 43 + n / 1806).factorial * n ^ r := by rw [← hr]
      _ ≤ _ := Nat.mul_le_mul (multinomial_bound _ _ _ _ _) (Nat.pow_le_pow_right hn hr4)
  refine Nat.le_of_mul_le_mul_right ?_ hF
  calc Nat.lcmUpto n * ((n / 2).factorial * (n / 3).factorial * (n / 7).factorial
        * (n / 43).factorial * (n / 1806).factorial)
      ≤ Nat.lcmUpto (n / 1806) * n.factorial := hd
    _ ≤ Nat.lcmUpto (n / 1806) * (G n * ((n / 2).factorial * (n / 3).factorial
        * (n / 7).factorial * (n / 43).factorial * (n / 1806).factorial) * n ^ 4) :=
        Nat.mul_le_mul_left _ hfac
    _ = _ := by ring

/-! ### The explicit majorant is below `3 ^ n` from `1850` on -/

/-- The majorant of `lcm_le` with `3 ^ ⌊n/1806⌋` in place of `lcm(1..⌊n/1806⌋)`. -/
def H (n : ℕ) : ℕ := 3 ^ (n / 1806) * (n ^ 4 * G n)

/-- `G (m + 1806) = G m * K`. -/
def K : ℕ := 2 ^ 903 * 3 ^ 602 * 7 ^ 258 * 43 ^ 42 * 1806

lemma K_pos : 0 < K := by unfold K; positivity

lemma K_le : 48 * K ≤ 3 ^ 1806 := by unfold K; decide +kernel

lemma G_add (m : ℕ) : G (m + 1806) = G m * K := by
  unfold G K
  rw [show (m + 1806) / 2 = m / 2 + 903 by omega, show (m + 1806) / 3 = m / 3 + 602 by omega,
    show (m + 1806) / 7 = m / 7 + 258 by omega, show (m + 1806) / 43 = m / 43 + 42 by omega,
    show (m + 1806) / 1806 = m / 1806 + 1 by omega]
  simp only [pow_add, pow_one]
  generalize (2 : ℕ) ^ 903 = c2
  generalize (3 : ℕ) ^ 602 = c3
  generalize (7 : ℕ) ^ 258 = c7
  generalize (43 : ℕ) ^ 42 = c43
  ring

lemma H_step (m : ℕ) (hm : 1806 ≤ m) (h : H m < 3 ^ m) : H (m + 1806) < 3 ^ (m + 1806) := by
  have h4 : (m + 1806) ^ 4 ≤ 16 * m ^ 4 := by
    calc (m + 1806) ^ 4 ≤ (2 * m) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = 16 * m ^ 4 := by ring
  have e : H (m + 1806) = 3 * 3 ^ (m / 1806) * ((m + 1806) ^ 4 * (G m * K)) := by
    unfold H
    rw [G_add, show (m + 1806) / 1806 = m / 1806 + 1 by omega, pow_succ]
    ring
  calc H (m + 1806) = 3 * 3 ^ (m / 1806) * ((m + 1806) ^ 4 * (G m * K)) := e
    _ ≤ 3 * 3 ^ (m / 1806) * ((16 * m ^ 4) * (G m * K)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4)
    _ = (48 * K) * H m := by unfold H; ring
    _ < (48 * K) * 3 ^ m := Nat.mul_lt_mul_of_pos_left h (by have := K_pos; omega)
    _ ≤ 3 ^ 1806 * 3 ^ m := Nat.mul_le_mul_right _ K_le
    _ = 3 ^ (m + 1806) := by rw [← pow_add, add_comm]

/-- Checks `H (1850 + j) < 3 ^ (1850 + j)` for `j < f`. -/
def chkH : ℕ → Bool
  | 0 => true
  | f + 1 => decide (H (1850 + f) < 3 ^ (1850 + f)) && chkH f

lemma chkH_sound : ∀ f, chkH f = true → ∀ j < f, H (1850 + j) < 3 ^ (1850 + j) := by
  intro f
  induction f with
  | zero => intro _ j hj; omega
  | succ f ih =>
    intro h j hj
    simp only [chkH, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
    · exact ih h.2 j hlt
    · exact h.1

theorem chkH_1806 : chkH 1806 = true := by decide +kernel

theorem H_lt (n : ℕ) (hn : 1850 ≤ n) : H n < 3 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 1850 + 1806
    · have := chkH_sound 1806 chkH_1806 (n - 1850) (by omega)
      rwa [show 1850 + (n - 1850) = n by omega] at this
    · have := H_step (n - 1806) (by omega) (ih (n - 1806) (by omega) (by omega))
      rwa [show n - 1806 + 1806 = n by omega] at this

/-! ### The finite range `1 ≤ n ≤ 1849` -/

lemma lcmUpto_succ (k : ℕ) : Nat.lcmUpto (k + 1) = Nat.lcm (Nat.lcmUpto k) (k + 1) := by
  unfold Nat.lcmUpto
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert]
  exact Nat.lcm_comm _ _

/-- With `d = lcm(1..N-f)`, checks `lcm(1..j) < 3^j` for `N - f < j ≤ N`. -/
def loop (N : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, d =>
    match Nat.lcm d (N - f) with
    | 0 => false
    | d' + 1 => decide (d' + 1 < 3 ^ (N - f)) && loop N f (d' + 1)

lemma loop_sound (N : ℕ) : ∀ f, f ≤ N → loop N f (Nat.lcmUpto (N - f)) = true →
    ∀ j, N - f < j → j ≤ N → Nat.lcmUpto j < 3 ^ j := by
  intro f
  induction f with
  | zero => intro _ _ j h1 h2; omega
  | succ f ih =>
    intro hf h j h1 h2
    have hl : Nat.lcm (Nat.lcmUpto (N - (f + 1))) (N - f) = Nat.lcmUpto (N - f) := by
      have e : N - f = (N - (f + 1)) + 1 := by omega
      rw [e, lcmUpto_succ]
    rw [loop] at h
    split at h
    · rename_i heq
      rw [hl] at heq
      exact absurd heq (Nat.lcmUpto_ne_zero _)
    · rename_i d' heq
      rw [Nat.succ_eq_add_one] at heq
      rw [← heq, hl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hj : j = N - f
      · rw [hj]; exact h.1
      · exact ih (by omega) h.2 j (by omega) h2

theorem loop_1849 : loop 1849 1849 1 = true := by decide +kernel

theorem lcmUpto_lt_small (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 1849) : Nat.lcmUpto j < 3 ^ j := by
  refine loop_sound 1849 1849 le_rfl ?_ j (by omega) h2
  have h0 : Nat.lcmUpto (1849 - 1849) = 1 := by simp [Nat.lcmUpto]
  rw [h0]
  exact loop_1849

/-! ### The theorem -/

theorem lcmUpto_lt_three_pow (n : ℕ) (hn : 1 ≤ n) : Nat.lcmUpto n < 3 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 1849
    · exact lcmUpto_lt_small n hn h
    · have he : Nat.lcmUpto (n / 1806) ≤ 3 ^ (n / 1806) := by
        by_cases h0 : n / 1806 = 0
        · rw [h0]; simp [Nat.lcmUpto]
        · exact (ih (n / 1806) (by omega) (by omega)).le
      calc Nat.lcmUpto n ≤ Nat.lcmUpto (n / 1806) * (n ^ 4 * G n) := lcm_le n hn
        _ ≤ 3 ^ (n / 1806) * (n ^ 4 * G n) := Nat.mul_le_mul_right _ he
        _ = H n := rfl
        _ < 3 ^ n := H_lt n (by omega)

/-- **Hanson 1972, Theorem 1.** `lcm(1, …, n) < 3 ^ n` for every `n ≥ 1`. -/
theorem lcm_Icc_lt_three_pow (n : ℕ) (hn : 1 ≤ n) : (Finset.Icc 1 n).lcm id < 3 ^ n :=
  lcmUpto_lt_three_pow n hn

/-- The same bound in `ℝ`, in the form of hypothesis (H4) of `Zeta3.irrational_zeta3_of_lemmas`
(`Zeta3.lcmOneTo n` unfolds to `(Finset.Icc 1 n).lcm id`). -/
theorem lcm_Icc_lt_three_pow_real (n : ℕ) (hn : 1 ≤ n) :
    (((Finset.Icc 1 n).lcm id : ℕ) : ℝ) < 3 ^ n := by
  exact_mod_cast lcm_Icc_lt_three_pow n hn

end Zeta3.Hanson

