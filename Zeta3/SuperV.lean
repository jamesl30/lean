import Mathlib
import Zeta3.Apery

-- CLAIMED: Zeta3.SuperV.aperyV_zero, Zeta3.SuperV.aperyV_one, Zeta3.SuperV.aperyV_two, Zeta3.SuperV.aperyV_three, Zeta3.SuperV.pcongPow_iff, Zeta3.SuperV.super_v_two, Zeta3.SuperV.super_v_three, Zeta3.SuperV.super_v_five, Zeta3.SuperV.super_v_two_pred, Zeta3.SuperV.super_v_three_pred, Zeta3.SuperV.super_v_five_pred, Zeta3.SuperV.super_v_seven, Zeta3.SuperV.super_v_seven_pred, Zeta3.SuperV.super_v_five_sharp

set_option autoImplicit false

namespace Zeta3.SuperV
open Finset

/-- `harm s k = H_k^{(s)} = ∑_{i=1}^{k} 1/i^s`. -/
def harm (s k : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 k, 1 / (i : ℚ) ^ s

/-- The rational part `vₙ` of Apéry's linear form `uₙ ζ(3) − vₙ`, literally as in Lemma 2(ii). -/
def aperyV (n : ℕ) : ℚ :=
  (∑ k ∈ range (n + 1), (aCoeff n k : ℚ) ^ 2 * harm 3 k)
  + ∑ k ∈ range (n + 1), ∑ l ∈ (range (n + 1)).erase k,
      (-1 : ℚ) ^ (k + l) * (aCoeff n k : ℚ) * (aCoeff n l : ℚ) * harm 2 k / ((l : ℚ) - (k : ℚ))

example : harm 2 3 = 49 / 36 := by decide +kernel

theorem aperyV_zero : aperyV 0 = 0 := by decide +kernel
theorem aperyV_one : aperyV 1 = 6 := by decide +kernel
theorem aperyV_two : aperyV 2 = 351 / 4 := by decide +kernel
theorem aperyV_three : aperyV 3 = 62531 / 36 := by decide +kernel

/-- `PCongPow p k x y`: `x ≡ y (mod p^k)` in `ℤ_(p)`, i.e. `x − y = p^k z` with `z` a rational
whose denominator is prime to `p`. (No trap at `x = y`: then `z = 0` works.) -/
def PCongPow (p k : ℕ) (x y : ℚ) : Prop := ∃ z : ℚ, ¬ p ∣ z.den ∧ x - y = (p : ℚ) ^ k * z

/-- For a prime `p`, `PCongPow p k x y` holds iff the reduced denominator of `x − y` is prime
to `p` and `p^k` divides its reduced numerator. -/
theorem pcongPow_iff (p k : ℕ) (hp : p.Prime) (x y : ℚ) :
    PCongPow p k x y ↔ ¬ p ∣ (x - y).den ∧ ((p : ℤ) ^ k ∣ (x - y).num) := by
  unfold PCongPow
  generalize x - y = q
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hden : ((p : ℚ) ^ k * z).den ∣ z.den := by
      have h := Rat.mul_den_dvd ((p : ℚ) ^ k) z
      have h1 : ((p : ℚ) ^ k).den = 1 := by
        rw [show ((p : ℚ) ^ k) = ((p ^ k : ℕ) : ℚ) by push_cast; ring]
        exact Rat.den_natCast _
      rwa [h1, one_mul] at h
    refine ⟨fun h => hz (dvd_trans h hden), ?_⟩
    set q := (p : ℚ) ^ k * z with hq
    have hcop : IsCoprime ((p : ℤ) ^ k) (z.den : ℤ) := by
      have : Nat.Coprime (p ^ k) z.den :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hz)
      have h2 := Nat.isCoprime_iff_coprime.mpr this
      push_cast at h2
      exact h2
    have key : q.num * (z.den : ℤ) = (p : ℤ) ^ k * z.num * (q.den : ℤ) := by
      have e1 : (q.num : ℚ) = q * q.den := by
        rw [Rat.mul_den_eq_num]
      have e2 : (z.num : ℚ) = z * z.den := by
        rw [Rat.mul_den_eq_num]
      have : ((q.num * (z.den : ℤ) : ℤ) : ℚ) = (((p : ℤ) ^ k * z.num * (q.den : ℤ) : ℤ) : ℚ) := by
        push_cast
        rw [e1, e2, hq]
        ring
      exact_mod_cast this
    apply hcop.dvd_of_dvd_mul_right
    rw [key, mul_assoc]
    exact dvd_mul_right _ _
  · rintro ⟨hd, c, hc⟩
    refine ⟨(c : ℚ) * (1 / (q.den : ℚ)), ?_, ?_⟩
    · intro h
      have h1 := Rat.mul_den_dvd (c : ℚ) (1 / (q.den : ℚ))
      have h2 : (1 / (q.den : ℚ)).den = q.den := by
        rw [one_div]
        exact Rat.inv_natCast_den_of_pos q.den_pos
      rw [Rat.den_intCast, h2, one_mul] at h1
      exact hd (dvd_trans h h1)
    · have e : q = ((p : ℚ) ^ k * c) / q.den := by
        conv_lhs => rw [← Rat.num_div_den q]
        rw [hc]; push_cast; ring
      conv_lhs => rw [e]
      ring

example : PCongPow 5 3 (126 : ℚ) 1 := by
  rw [pcongPow_iff 5 3 (by norm_num)]; decide +kernel
example : ¬ PCongPow 5 3 (26 : ℚ) 1 := by
  rw [pcongPow_iff 5 3 (by norm_num)]; decide +kernel
example : PCongPow 3 1 (1 / 2 : ℚ) 2 := by
  rw [pcongPow_iff 3 1 (by norm_num)]; decide +kernel

/-! ### The supercongruence `p³ v_{pm} ≡ v_m (mod p³)` for `p = 2, 3, 5`, by kernel computation -/

theorem super_v_two : PCongPow 2 3 (2 ^ 3 * aperyV 2) (aperyV 1) := by
  rw [pcongPow_iff 2 3 Nat.prime_two]; decide +kernel

theorem super_v_three : ∀ m, 1 ≤ m → m < 3 →
    PCongPow 3 3 (3 ^ 3 * aperyV (3 * m)) (aperyV m) := by
  intro m h1 h2
  rw [pcongPow_iff 3 3 Nat.prime_three]
  interval_cases m <;> decide +kernel

theorem super_v_five : ∀ m, 1 ≤ m → m < 5 →
    PCongPow 5 3 (5 ^ 3 * aperyV (5 * m)) (aperyV m) := by
  intro m h1 h2
  rw [pcongPow_iff 5 3 (by norm_num)]
  interval_cases m <;> decide +kernel

theorem super_v_two_pred : PCongPow 2 3 (2 ^ 3 * aperyV (2 * 1 - 1)) (aperyV (1 - 1)) := by
  rw [pcongPow_iff 2 3 Nat.prime_two]; decide +kernel

theorem super_v_three_pred : ∀ m, 1 ≤ m → m < 3 →
    PCongPow 3 3 (3 ^ 3 * aperyV (3 * m - 1)) (aperyV (m - 1)) := by
  intro m h1 h2
  rw [pcongPow_iff 3 3 Nat.prime_three]
  interval_cases m <;> decide +kernel

theorem super_v_five_pred : ∀ m, 1 ≤ m → m < 5 →
    PCongPow 5 3 (5 ^ 3 * aperyV (5 * m - 1)) (aperyV (m - 1)) := by
  intro m h1 h2
  rw [pcongPow_iff 5 3 (by norm_num)]
  interval_cases m <;> decide +kernel

set_option maxRecDepth 100000 in
theorem super_v_seven : ∀ m, 1 ≤ m → m < 7 →
    PCongPow 7 3 (7 ^ 3 * aperyV (7 * m)) (aperyV m) := by
  intro m h1 h2
  rw [pcongPow_iff 7 3 (by norm_num)]
  interval_cases m <;> decide +kernel

set_option maxRecDepth 100000 in
theorem super_v_seven_pred : ∀ m, 1 ≤ m → m < 7 →
    PCongPow 7 3 (7 ^ 3 * aperyV (7 * m - 1)) (aperyV (m - 1)) := by
  intro m h1 h2
  rw [pcongPow_iff 7 3 (by norm_num)]
  interval_cases m <;> decide +kernel

/-- Sharpness: `125 v₅ − v₁` has `5`-adic valuation exactly `3`, so `p³` cannot be `p⁴`. -/
theorem super_v_five_sharp : ¬ PCongPow 5 4 (5 ^ 3 * aperyV 5) (aperyV 1) := by
  rw [pcongPow_iff 5 4 (by norm_num)]; decide +kernel

end Zeta3.SuperV