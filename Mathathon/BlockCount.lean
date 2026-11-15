import Mathlib
open Finset

namespace Mathathon.BlockCount

open Polynomial in
theorem pow4_congr_mod4 : ((1 - X : ℤ[X]) ^ 4 - (1 - X ^ 2) ^ 2) = C 4 * (-(X * (1 - X) ^ 2)) := by
  rw [show (C 4 : ℤ[X]) = 4 from map_ofNat C 4]
  ring

lemma pow_sub_pow_le_aux (x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x) (m : ℕ) :
    x ^ (m + 1) - y ^ (m + 1) ≤ (m + 1) * x ^ m * (x - y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hx : 0 ≤ x := le_trans hy hxy
    have h1 : y ^ (m + 1) ≤ x ^ (m + 1) := pow_le_pow_left₀ hy hxy _
    have e : x ^ (m + 1 + 1) - y ^ (m + 1 + 1)
        = x * (x ^ (m + 1) - y ^ (m + 1)) + y ^ (m + 1) * (x - y) := by ring
    rw [e]
    have hxm : x * ((m + 1) * x ^ m * (x - y)) = (m + 1) * x ^ (m + 1) * (x - y) := by ring
    have hd : 0 ≤ x - y := by linarith
    have a1 : x * (x ^ (m + 1) - y ^ (m + 1)) ≤ x * ((m + 1) * x ^ m * (x - y)) :=
      mul_le_mul_of_nonneg_left ih hx
    have a2 : y ^ (m + 1) * (x - y) ≤ x ^ (m + 1) * (x - y) := mul_le_mul_of_nonneg_right h1 hd
    push_cast
    nlinarith

lemma rpow_step (n : ℕ) :
    ((n : ℝ) + 1) ^ (-(11/12) : ℝ) ≤ 12 * (((n : ℝ) + 1) ^ ((1/12) : ℝ) - (n : ℝ) ^ ((1/12) : ℝ)) := by
  set a := (n : ℝ) ^ ((1/12) : ℝ) with ha
  set b := ((n : ℝ) + 1) ^ ((1/12) : ℝ) with hb
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hab : a ≤ b := Real.rpow_le_rpow hn0 (by linarith) (by norm_num)
  have ha12 : a ^ 12 = n := by
    rw [ha, one_div]; exact Real.rpow_inv_natCast_pow hn0 (by norm_num)
  have hb12 : b ^ 12 = n + 1 := by
    rw [hb, one_div]; exact Real.rpow_inv_natCast_pow hn1.le (by norm_num)
  have hb11 : b ^ 11 * ((n : ℝ) + 1) ^ (-(11/12) : ℝ) = 1 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hn1.le, ← Real.rpow_add hn1]
    norm_num
  have key := pow_sub_pow_le_aux b a ha0 hab 11
  rw [hb12, ha12] at key
  set t := ((n : ℝ) + 1) ^ (-(11/12) : ℝ)
  have ht : 0 ≤ t := by positivity
  have : t * 1 ≤ t * ((11 + 1) * b ^ 11 * (b - a)) := by
    apply mul_le_mul_of_nonneg_left _ ht; push_cast at key; linarith
  have e : t * ((11 + 1) * b ^ 11 * (b - a)) = 12 * (b - a) * (b ^ 11 * t) := by ring
  rw [e, hb11] at this
  linarith

theorem sum_rpow_le (n : ℕ) :
    ∑ c ∈ Finset.Icc 1 n, (c : ℝ) ^ (-(11/12) : ℝ) ≤ 12 * (n : ℝ) ^ ((1/12) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := rpow_step n
    push_cast
    linarith

/-- single-block charging step -/
theorem block_charge (κ : ℝ) (B K : ℕ) (h1 : 1 ≤ B) (hsm : 8 * K ≤ B)
    (hδ : κ * (B : ℝ) ^ ((11/12) : ℝ) < K) :
    κ / (9/8 : ℝ) ^ ((11/12) : ℝ) < ∑ c ∈ Finset.Ico B (B + K), (c : ℝ) ^ (-(11/12) : ℝ) := by
  set s := (9/8 : ℝ) ^ ((11/12) : ℝ) with hs
  set β := (B : ℝ) ^ ((11/12) : ℝ) with hβ
  have hs0 : 0 < s := by positivity
  have hB0 : (0 : ℝ) < B := by exact_mod_cast h1
  have hβ0 : 0 < β := by positivity
  have hterm : ∀ c ∈ Finset.Ico B (B + K), (s * β)⁻¹ ≤ (c : ℝ) ^ (-(11/12) : ℝ) := by
    intro c hc
    rw [Finset.mem_Ico] at hc
    have hc0 : (0 : ℝ) < c := by have : 1 ≤ c := by omega
                                 exact_mod_cast this
    have h8 : 8 * c ≤ 9 * B := by omega
    have hcle : (c : ℝ) ≤ (9/8) * B := by
      have : (8 : ℝ) * c ≤ 9 * B := by exact_mod_cast h8
      linarith
    have hpow : (c : ℝ) ^ ((11/12) : ℝ) ≤ s * β := by
      rw [hs, hβ, ← Real.mul_rpow (by norm_num) hB0.le]
      exact Real.rpow_le_rpow hc0.le hcle (by norm_num)
    rw [Real.rpow_neg hc0.le]
    exact inv_anti₀ (by positivity) hpow
  have hsum : (K : ℝ) * (s * β)⁻¹ ≤ ∑ c ∈ Finset.Ico B (B + K), (c : ℝ) ^ (-(11/12) : ℝ) := by
    have := Finset.card_nsmul_le_sum _ _ _ hterm
    simpa [nsmul_eq_mul] using this
  have hlt : κ / s < (K : ℝ) * (s * β)⁻¹ := by
    rw [mul_inv, div_eq_mul_inv]
    have : κ < (K : ℝ) * β⁻¹ := by
      rw [lt_mul_inv_iff₀ hβ0]; linarith
    calc κ * s⁻¹ < (K : ℝ) * β⁻¹ * s⁻¹ := mul_lt_mul_of_pos_right this (by positivity)
      _ = (K : ℝ) * (s⁻¹ * β⁻¹) := by ring
  linarith

theorem block_count (κ : ℝ) (hκ : 0 < κ) (ce n : ℕ) (B K : Fin n → ℕ)
    (hord : ∀ i j : Fin n, i < j → B i + K i ≤ B j) (h1 : ∀ i, 1 ≤ B i)
    (hin : ∀ i, B i + K i ≤ ce + 1) (hsm : ∀ i, 8 * K i ≤ B i)
    (hδ : ∀ i, κ * (B i : ℝ) ^ ((11/12) : ℝ) < K i) :
    (n : ℝ) ≤ (12 / κ) * (9/8 : ℝ) ^ ((11/12) : ℝ) * (ce : ℝ) ^ ((1/12) : ℝ) := by
  set s := (9/8 : ℝ) ^ ((11/12) : ℝ) with hs
  have hs0 : 0 < s := by positivity
  set f : ℕ → ℝ := fun c => (c : ℝ) ^ (-(11/12) : ℝ) with hf
  have hdisj : (Set.univ : Set (Fin n)).PairwiseDisjoint (fun i => Finset.Ico (B i) (B i + K i)) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro c hci hcj
    rw [Finset.mem_Ico] at hci hcj
    rcases lt_or_gt_of_ne hij with h | h
    · have := hord i j h; omega
    · have := hord j i h; omega
  have hsub : (Finset.univ.biUnion fun i => Finset.Ico (B i) (B i + K i)) ⊆ Finset.Icc 1 ce := by
    intro c hc
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_Ico] at hc
    obtain ⟨i, hi1, hi2⟩ := hc
    have := h1 i; have := hin i
    rw [Finset.mem_Icc]; omega
  have hchain : (n : ℝ) * (κ / s) ≤ 12 * (ce : ℝ) ^ ((1/12) : ℝ) := by
    calc (n : ℝ) * (κ / s) = ∑ _i : Fin n, κ / s := by simp
      _ ≤ ∑ i : Fin n, ∑ c ∈ Finset.Ico (B i) (B i + K i), f c :=
          Finset.sum_le_sum fun i _ => (block_charge κ (B i) (K i) (h1 i) (hsm i) (hδ i)).le
      _ = ∑ c ∈ Finset.univ.biUnion (fun i => Finset.Ico (B i) (B i + K i)), f c := by
          rw [Finset.sum_biUnion (by simpa using hdisj)]
      _ ≤ ∑ c ∈ Finset.Icc 1 ce, f c := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro c _ _; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      _ ≤ 12 * (ce : ℝ) ^ ((1/12) : ℝ) := sum_rpow_le ce
  have e : (12 / κ) * s * (ce : ℝ) ^ ((1/12) : ℝ) = (12 * (ce : ℝ) ^ ((1/12) : ℝ)) / (κ / s) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  exact hchain

end Mathathon.BlockCount
