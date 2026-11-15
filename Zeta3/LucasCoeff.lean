import Mathlib
import Zeta3.Apery

-- CLAIMED: Zeta3.LucasCoeff.lucas_aCoeff, Zeta3.LucasCoeff.lucas_aCoeff_of_lt, Zeta3.LucasCoeff.lucas_aCoeff_dvd, Zeta3.LucasCoeff.aCoeff_dvd_of_carry

/-!
# Lucas' congruence for the Apéry coefficients

`Zeta3.aCoeff n k = C(n,k) · C(n+k,k)` (ℕ-valued, from `Zeta3.Apery`).
For a prime `p`, `n = a*p + b`, `j = c*p + d` with digits `b, d < p`:

* `lucas_aCoeff`: if `b + d < p` then `aCoeff n j ≡ aCoeff a c * aCoeff b d [MOD p]`
  (the hypothesis `d ≤ b` of the written claim is not needed: if `d > b` both sides are
  `≡ 0`; `a`, `c` are arbitrary naturals);
* `lucas_aCoeff_dvd`: if `b < d` or `p ≤ b + d` then `p ∣ aCoeff n j`;
* `aCoeff_dvd_of_carry`: if `a, c < p` and `p ≤ a + c` then `p ∣ aCoeff a c`.

All three come from the one-step form of Lucas' theorem in Mathlib,
`Choose.choose_modEq_choose_mod_mul_choose_div_nat`.
-/

set_option autoImplicit false

namespace Zeta3.LucasCoeff
/-- The last base-`p` digit of `a*p + b` is `b` when `b < p`. -/
lemma digit_mod (a b : ℕ) {p : ℕ} (hb : b < p) : (a * p + b) % p = b := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- The quotient of `a*p + b` by `p` is `a` when `b < p`. -/
lemma digit_div (a b : ℕ) {p : ℕ} (hb : b < p) : (a * p + b) / p = a := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le b) hb
  rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hb, zero_add]

/-- Lucas' congruence for `aCoeff`, good case (no carry in `b + d`). -/
theorem lucas_aCoeff_of_lt {p : ℕ} (hp : p.Prime) (a b c d : ℕ) (hbd : b + d < p) :
    aCoeff (a * p + b) (c * p + d) ≡ aCoeff a c * aCoeff b d [MOD p] := by
  have := Fact.mk hp
  have hb : b < p := by omega
  have hd : d < p := by omega
  have h1 := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := a * p + b) (k := c * p + d) (p := p)
  have h2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := (a + c) * p + (b + d)) (k := c * p + d) (p := p)
  rw [digit_mod a b hb, digit_mod c d hd, digit_div a b hb, digit_div c d hd] at h1
  rw [digit_mod (a + c) (b + d) hbd, digit_mod c d hd, digit_div (a + c) (b + d) hbd,
    digit_div c d hd] at h2
  have e : a * p + b + (c * p + d) = (a + c) * p + (b + d) := by ring
  unfold aCoeff
  rw [e]
  calc (a * p + b).choose (c * p + d) * ((a + c) * p + (b + d)).choose (c * p + d)
      ≡ (b.choose d * a.choose c) * ((b + d).choose d * (a + c).choose c) [MOD p] :=
        Nat.ModEq.mul h1 h2
    _ = a.choose c * (a + c).choose c * (b.choose d * (b + d).choose d) := by ring

/-- Lucas' congruence for `aCoeff`, with the hypotheses of the written claim
(digits `a, b, c, d < p`, `d ≤ b`, `b + d < p`). -/
theorem lucas_aCoeff {p : ℕ} (hp : p.Prime) (a b c d : ℕ) (_ha : a < p) (_hb : b < p)
    (_hc : c < p) (_hd : d < p) (_hdb : d ≤ b) (hbd : b + d < p) :
    aCoeff (a * p + b) (c * p + d) ≡ aCoeff a c * aCoeff b d [MOD p] :=
  lucas_aCoeff_of_lt hp a b c d hbd

/-- The bad cases: a borrow (`b < d`) or a carry (`p ≤ b + d`) makes `p` divide `aCoeff`. -/
theorem lucas_aCoeff_dvd {p : ℕ} (hp : p.Prime) (a b c d : ℕ) (hb : b < p) (hd : d < p)
    (h : b < d ∨ p ≤ b + d) : p ∣ aCoeff (a * p + b) (c * p + d) := by
  have := Fact.mk hp
  unfold aCoeff
  rcases h with hlt | hle
  · have h1 := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := a * p + b) (k := c * p + d) (p := p)
    rw [digit_mod a b hb, digit_mod c d hd, Nat.choose_eq_zero_of_lt hlt, zero_mul] at h1
    exact Dvd.dvd.mul_right ((Nat.modEq_zero_iff_dvd).1 h1) _
  · set r := b + d - p with hr_def
    have hr : b + d = p + r := by omega
    have hrp : r < p := by omega
    have hrd : r < d := by omega
    have e : a * p + b + (c * p + d) = (a + c + 1) * p + r := by
      have : (a + c + 1) * p + r = a * p + c * p + (p + r) := by ring
      rw [this, ← hr]; ring
    have h2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := (a + c + 1) * p + r) (k := c * p + d) (p := p)
    rw [digit_mod (a + c + 1) r hrp, digit_mod c d hd, Nat.choose_eq_zero_of_lt hrd,
      zero_mul] at h2
    rw [e]
    exact Dvd.dvd.mul_left ((Nat.modEq_zero_iff_dvd).1 h2) _

/-- A carry in `a + c` (digits `a, c < p`) makes `p` divide `aCoeff a c`,
since `p ∣ C(a+c, c)`. -/
theorem aCoeff_dvd_of_carry {p : ℕ} (hp : p.Prime) (a c : ℕ) (ha : a < p) (hc : c < p)
    (h : p ≤ a + c) : p ∣ aCoeff a c := by
  have := Fact.mk hp
  unfold aCoeff
  set r := a + c - p with hr_def
  have e : a + c = 1 * p + r := by omega
  have hrp : r < p := by omega
  have hrc : r < c := by omega
  have h2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 1 * p + r) (k := c) (p := p)
  rw [digit_mod 1 r hrp, Nat.mod_eq_of_lt hc, Nat.choose_eq_zero_of_lt hrc, zero_mul] at h2
  rw [e]
  exact Dvd.dvd.mul_left ((Nat.modEq_zero_iff_dvd).1 h2) _

/-! Small exact values (p = 5, n = 1·5 + 2 = 7, j = 1·5 + 1 = 6):
`aCoeff 7 6 = 7 · 1716 = 12012 ≡ 2`, `aCoeff 1 1 · aCoeff 2 1 = 2 · 6 = 12 ≡ 2 (mod 5)`. -/
example : aCoeff 7 6 = 12012 := by decide
example : aCoeff 1 1 * aCoeff 2 1 = 12 := by decide
example : aCoeff (1 * 5 + 2) (1 * 5 + 1) ≡ aCoeff 1 1 * aCoeff 2 1 [MOD 5] :=
  lucas_aCoeff (by norm_num) 1 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
-- borrow: p = 5, n = 7 (b = 2), j = 3 (d = 3 > 2): aCoeff 7 3 = 35 · 120 = 4200
example : aCoeff 7 3 = 4200 := by decide
example : 5 ∣ aCoeff (1 * 5 + 2) (0 * 5 + 3) :=
  lucas_aCoeff_dvd (by norm_num) 1 2 0 3 (by norm_num) (by norm_num) (Or.inl (by norm_num))
-- carry: p = 5, a = 3, c = 4: aCoeff 3 4 = 0 (c > a), and a = 4, c = 3: aCoeff 4 3 = 4 · 35 = 140
example : aCoeff 4 3 = 140 := by decide
example : 5 ∣ aCoeff 4 3 :=
  aCoeff_dvd_of_carry (by norm_num) 4 3 (by norm_num) (by norm_num) (by norm_num)

end Zeta3.LucasCoeff