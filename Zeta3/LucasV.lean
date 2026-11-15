import Mathlib
import Zeta3.Apery

-- CLAIMED: Zeta3.LucasV.aperyV_zero, Zeta3.LucasV.aperyV_one, Zeta3.LucasV.aperyV_two, Zeta3.LucasV.aperyV_three, Zeta3.LucasV.pcong_iff_dvd_num, Zeta3.LucasV.lucas_v_two, Zeta3.LucasV.lucas_v_three, Zeta3.LucasV.lucas_v_five

set_option autoImplicit false

namespace Zeta3.LucasV
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

/-- `PCong p x y`: `x − y` lies in `p ℤ_(p)`, i.e. it is `0` or has positive `p`-adic valuation. -/
def PCong (p : ℕ) (x y : ℚ) : Prop := x - y = 0 ∨ 0 < padicValRat p (x - y)

/-- For a prime `p`, `PCong p x y` holds iff `p` divides the reduced numerator of `x − y`. -/
theorem pcong_iff_dvd_num (p : ℕ) [hp : Fact p.Prime] (x y : ℚ) :
    PCong p x y ↔ (p : ℤ) ∣ (x - y).num := by
  unfold PCong
  generalize x - y = q
  constructor
  · rintro (h | h)
    · simp [h]
    · by_contra hn
      have h0 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hn
      have : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
      omega
  · intro h
    by_cases hq : q = 0
    · exact Or.inl hq
    · right
      have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
      have hden : ¬ p ∣ q.den := by
        intro hd
        have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp h
        have hc : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
        have h5 : p ∣ 1 := hc ▸ Nat.dvd_gcd h1 hd
        exact hp.out.one_lt.ne' (Nat.dvd_one.mp h5)
      have h2 : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hden
      have h3 : 1 ≤ padicValNat p q.num.natAbs :=
        one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum) (Int.natCast_dvd.mp h)
      have : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
      have h4 : padicValInt p q.num = padicValNat p q.num.natAbs := rfl
      omega

/-- Verified instances of the Lucas congruence `p³ v_{ap+b} ≡ u_b v_a (mod p)` for `p = 2, 3, 5`
(all digits `a, b < p`), by kernel computation (`decide +kernel`; the native evaluator is not used). -/
theorem lucas_v_two : ∀ a < 2, ∀ b < 2,
    PCong 2 ((2 : ℚ) ^ 3 * aperyV (a * 2 + b)) ((aperyU b : ℚ) * aperyV a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [pcong_iff_dvd_num]
  decide +kernel

theorem lucas_v_three : ∀ a < 3, ∀ b < 3,
    PCong 3 ((3 : ℚ) ^ 3 * aperyV (a * 3 + b)) ((aperyU b : ℚ) * aperyV a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [pcong_iff_dvd_num]
  decide +kernel

theorem lucas_v_five : ∀ a < 5, ∀ b < 5,
    PCong 5 ((5 : ℚ) ^ 3 * aperyV (a * 5 + b)) ((aperyU b : ℚ) * aperyV a) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp only [pcong_iff_dvd_num]
  decide +kernel

end Zeta3.LucasV