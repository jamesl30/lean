import Mathlib

-- CLAIMED: Zeta3.Harm.PInt, Zeta3.Harm.PCongZ, Zeta3.Harm.pint_intCast, Zeta3.Harm.pint_natCast, Zeta3.Harm.pint_zero, Zeta3.Harm.pint_one, Zeta3.Harm.pint_add, Zeta3.Harm.pint_neg, Zeta3.Harm.pint_sub, Zeta3.Harm.pint_mul, Zeta3.Harm.pint_pow, Zeta3.Harm.pint_sum, Zeta3.Harm.pint_prod, Zeta3.Harm.pint_one_div_nat, Zeta3.Harm.pint_one_div_pow, Zeta3.Harm.pcongZ_refl, Zeta3.Harm.pcongZ_symm, Zeta3.Harm.pcongZ_trans, Zeta3.Harm.pcongZ_add, Zeta3.Harm.pcongZ_sub, Zeta3.Harm.pcongZ_sum, Zeta3.Harm.pcongZ_mul_left, Zeta3.Harm.pcongZ_mul_right, Zeta3.Harm.pcongZ_mul, Zeta3.Harm.pint_of_pcongZ, Zeta3.Harm.pcongZ_natCast, Zeta3.Harm.pcongZ_of_eq_add, Zeta3.Harm.pcongZ_zero_of_pint, Zeta3.Harm.pcong_of_pcongZ, Zeta3.Harm.pcongZ_of_pcong, Zeta3.Harm.pcongZ_iff_pcong, Zeta3.Harm.harm_succ, Zeta3.Harm.harm_reduce, Zeta3.Harm.harm_reduce_pcongZ, Zeta3.Harm.pint_harm, Zeta3.Harm.pint_pow_mul_harm, Zeta3.Harm.pint_pow_harm, Zeta3.Harm.pint_pow_two_harm

/-!
# The ring `ℤ_(p)` inside `ℚ`, and the harmonic congruences

* `PInt p x` : `x ∈ ℤ_(p)`, i.e. `p` does not divide the reduced denominator of `x`.
* `PCongZ p x y` : `x ≡ y (mod p ℤ_(p))`, i.e. `x - y = p * z` with `z ∈ ℤ_(p)`.
* `PCong` (copied unchanged from `LucasV.lean`) and the equivalence `pcongZ_iff_pcong`.
* `harm s k = ∑_{i=1}^k 1/i^s` (copied unchanged from `LucasV.lean`) and
  - `harm_reduce`: `p^s H_m^{(s)} = H_{⌊m/p⌋}^{(s)} + p^s z` with `z ∈ ℤ_(p)` (all `s`, all `m`);
  - `pint_harm`: `m < p → H_m^{(s)} ∈ ℤ_(p)`;
  - `pint_pow_mul_harm`: `m < p^(k+1) → p^(k s) H_m^{(s)} ∈ ℤ_(p)` (so `k = 1, 2` give
    `pint_pow_harm`, `pint_pow_two_harm`).
-/

set_option autoImplicit false

namespace Zeta3.Harm
open Finset

/-! ## The toolkit -/

/-- `x ∈ ℤ_(p)`: the prime `p` does not divide the reduced denominator of `x`. -/
def PInt (p : ℕ) (x : ℚ) : Prop := ¬ p ∣ x.den

/-- `x ≡ y (mod p ℤ_(p))`. -/
def PCongZ (p : ℕ) (x y : ℚ) : Prop := ∃ z, PInt p z ∧ x - y = p * z

/-- `PCong p x y`: `x − y` lies in `p ℤ_(p)`, i.e. it is `0` or has positive `p`-adic valuation.
(Copied unchanged from `LucasV.lean`.) -/
def PCong (p : ℕ) (x y : ℚ) : Prop := x - y = 0 ∨ 0 < padicValRat p (x - y)

section toolkit

variable {p : ℕ}

theorem pint_intCast (hp : p.Prime) (n : ℤ) : PInt p (n : ℚ) := by
  unfold PInt; rw [Rat.den_intCast]; exact hp.not_dvd_one

theorem pint_natCast (hp : p.Prime) (n : ℕ) : PInt p (n : ℚ) := by
  have := pint_intCast hp (n : ℤ); simpa using this

theorem pint_zero (hp : p.Prime) : PInt p 0 := by simpa using pint_intCast hp 0

theorem pint_one (hp : p.Prime) : PInt p 1 := by simpa using pint_intCast hp 1

theorem pint_add (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp (h.trans (Rat.add_den_dvd x y)) with h1 | h1
  · exact hx h1
  · exact hy h1

theorem pint_neg {x : ℚ} (hx : PInt p x) : PInt p (-x) := by
  unfold PInt at *; rwa [Rat.neg_den]

theorem pint_sub (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x - y) := by
  rw [sub_eq_add_neg]; exact pint_add hp hx (pint_neg hy)

theorem pint_mul (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp (h.trans (Rat.mul_den_dvd x y)) with h1 | h1
  · exact hx h1
  · exact hy h1

theorem pint_pow (hp : p.Prime) {x : ℚ} (hx : PInt p x) (n : ℕ) : PInt p (x ^ n) := by
  induction n with
  | zero => simpa using pint_one hp
  | succ n ih => rw [pow_succ]; exact pint_mul hp ih hx

theorem pint_sum (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, PInt p (f i)) : PInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pint_zero hp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pint_add hp (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem pint_prod (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, PInt p (f i)) : PInt p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pint_one hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact pint_mul hp (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem pint_one_div_nat {k : ℕ} (hk : ¬ p ∣ k) : PInt p (1 / (k : ℚ)) := by
  unfold PInt
  rw [one_div, Rat.inv_natCast_den]
  split_ifs with h0
  · subst h0; exact absurd (dvd_zero p) hk
  · exact hk

theorem pint_one_div_pow (hp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k) (s : ℕ) :
    PInt p (1 / (k : ℚ) ^ s) := by
  rw [one_div, ← inv_pow, ← one_div]; exact pint_pow hp (pint_one_div_nat hk) s

theorem pcongZ_refl (hp : p.Prime) (x : ℚ) : PCongZ p x x :=
  ⟨0, pint_zero hp, by simp⟩

theorem pcongZ_symm {x y : ℚ} (h : PCongZ p x y) : PCongZ p y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, pint_neg hz, by linear_combination -e⟩

theorem pcongZ_trans (hp : p.Prime) {x y w : ℚ} (h1 : PCongZ p x y) (h2 : PCongZ p y w) :
    PCongZ p x w := by
  obtain ⟨z1, hz1, e1⟩ := h1
  obtain ⟨z2, hz2, e2⟩ := h2
  exact ⟨z1 + z2, pint_add hp hz1 hz2, by linear_combination e1 + e2⟩

theorem pcongZ_add (hp : p.Prime) {x y x' y' : ℚ} (h1 : PCongZ p x y) (h2 : PCongZ p x' y') :
    PCongZ p (x + x') (y + y') := by
  obtain ⟨z1, hz1, e1⟩ := h1
  obtain ⟨z2, hz2, e2⟩ := h2
  exact ⟨z1 + z2, pint_add hp hz1 hz2, by linear_combination e1 + e2⟩

theorem pcongZ_sub (hp : p.Prime) {x y x' y' : ℚ} (h1 : PCongZ p x y) (h2 : PCongZ p x' y') :
    PCongZ p (x - x') (y - y') := by
  obtain ⟨z1, hz1, e1⟩ := h1
  obtain ⟨z2, hz2, e2⟩ := h2
  exact ⟨z1 - z2, pint_sub hp hz1 hz2, by linear_combination e1 - e2⟩

theorem pcongZ_sum (hp : p.Prime) {ι : Type*} (s : Finset ι) (f g : ι → ℚ)
    (h : ∀ i ∈ s, PCongZ p (f i) (g i)) : PCongZ p (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pcongZ_refl hp 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact pcongZ_add hp (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem pcongZ_mul_left (hp : p.Prime) {x y w : ℚ} (hw : PInt p w) (h : PCongZ p x y) :
    PCongZ p (w * x) (w * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨w * z, pint_mul hp hw hz, by linear_combination w * e⟩

theorem pcongZ_mul_right (hp : p.Prime) {x y w : ℚ} (hw : PInt p w) (h : PCongZ p x y) :
    PCongZ p (x * w) (y * w) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨w * z, pint_mul hp hw hz, by linear_combination w * e⟩

/-- Product of two congruences; only `x` and `y'` need to be in `ℤ_(p)`. -/
theorem pcongZ_mul (hp : p.Prime) {x y x' y' : ℚ} (hx : PInt p x) (hy' : PInt p y')
    (h1 : PCongZ p x y) (h2 : PCongZ p x' y') : PCongZ p (x * x') (y * y') := by
  obtain ⟨z1, hz1, e1⟩ := h1
  obtain ⟨z2, hz2, e2⟩ := h2
  exact ⟨x * z2 + y' * z1, pint_add hp (pint_mul hp hx hz2) (pint_mul hp hy' hz1),
    by linear_combination x * e2 + y' * e1⟩

/-- `p ℤ_(p) ⊆ ℤ_(p)`: a number congruent to an element of `ℤ_(p)` is in `ℤ_(p)`. -/
theorem pint_of_pcongZ (hp : p.Prime) {x y : ℚ} (hy : PInt p y) (h : PCongZ p x y) :
    PInt p x := by
  obtain ⟨z, hz, e⟩ := h
  have : x = y + (p : ℚ) * z := by linear_combination e
  rw [this]; exact pint_add hp hy (pint_mul hp (pint_natCast hp p) hz)

theorem pcongZ_natCast (hp : p.Prime) {n m : ℕ} (h : n ≡ m [MOD p]) :
    PCongZ p (n : ℚ) (m : ℚ) := by
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.mp h)
  refine ⟨((-c : ℤ) : ℚ), pint_intCast hp _, ?_⟩
  have : ((m : ℤ) : ℚ) - ((n : ℤ) : ℚ) = (p : ℚ) * (c : ℚ) := by exact_mod_cast hc
  push_cast at this ⊢; linear_combination -this

theorem pcongZ_of_eq_add {x y z : ℚ} (hz : PInt p z) (e : x = y + p * z) : PCongZ p x y :=
  ⟨z, hz, by linear_combination e⟩

theorem pcongZ_zero_of_pint {z : ℚ} (hz : PInt p z) : PCongZ p ((p : ℚ) * z) 0 :=
  ⟨z, hz, by ring⟩

/-- Bridge to `PCong` of `LucasV.lean`. -/
theorem pcong_of_pcongZ (hp : p.Prime) {x y : ℚ} (h : PCongZ p x y) : PCong p x y := by
  have := Fact.mk hp
  obtain ⟨z, hz, e⟩ := h
  unfold PCong
  by_cases hz0 : z = 0
  · left; rw [e, hz0, mul_zero]
  · right
    rw [e, padicValRat.mul (by exact_mod_cast hp.ne_zero) hz0, padicValRat.self hp.one_lt]
    have h0 : padicValNat p z.den = 0 := padicValNat.eq_zero_of_not_dvd hz
    have : padicValRat p z = padicValInt p z.num - padicValNat p z.den := rfl
    omega

theorem pcongZ_of_pcong (hp : p.Prime) {x y : ℚ} (h : PCong p x y) : PCongZ p x y := by
  have := Fact.mk hp
  unfold PCong at h
  generalize hq : x - y = q at h
  have hnum : (p : ℤ) ∣ q.num := by
    rcases h with h | h
    · simp [h]
    · by_contra hn
      have h0 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hn
      have : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
      omega
  have hden : ¬ p ∣ q.den := by
    intro hd
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hnum
    have hc : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
    have h5 : p ∣ 1 := hc ▸ Nat.dvd_gcd h1 hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
  obtain ⟨c, hc⟩ := hnum
  refine ⟨(c : ℚ) * (1 / (q.den : ℚ)), pint_mul hp (pint_intCast hp c) (pint_one_div_nat hden), ?_⟩
  rw [hq]
  have hq' : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
  calc q = (q.num : ℚ) / (q.den : ℚ) := hq'.symm
    _ = _ := by rw [hc]; push_cast; ring

theorem pcongZ_iff_pcong (hp : p.Prime) (x y : ℚ) : PCongZ p x y ↔ PCong p x y :=
  ⟨pcong_of_pcongZ hp, pcongZ_of_pcong hp⟩

end toolkit

/-! ## Harmonic numbers -/

/-- `harm s k = H_k^{(s)} = ∑_{i=1}^{k} 1/i^s`. (Copied unchanged from `LucasV.lean`.) -/
def harm (s k : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 k, 1 / (i : ℚ) ^ s

theorem harm_succ (s m : ℕ) : harm s (m + 1) = harm s m + 1 / ((m + 1 : ℕ) : ℚ) ^ s := by
  unfold harm; rw [Finset.sum_Icc_succ_top (by omega)]

section harmonic

variable {p : ℕ}

/-- `p^s H_m^{(s)} = H_{⌊m/p⌋}^{(s)} + p^s z` with `z ∈ ℤ_(p)`: the multiples `p j` of `p` in
`1..m` contribute `p^s/(pj)^s = 1/j^s`, `j ≤ m/p`; the other terms have unit denominators. -/
theorem harm_reduce (hp : p.Prime) (s m : ℕ) :
    ∃ z, PInt p z ∧ (p : ℚ) ^ s * harm s m = harm s (m / p) + (p : ℚ) ^ s * z := by
  induction m with
  | zero => exact ⟨0, pint_zero hp, by simp [harm]⟩
  | succ m ih =>
    obtain ⟨z, hz, e⟩ := ih
    rw [Nat.succ_div]
    split_ifs with hd
    · obtain ⟨q, hq⟩ := hd
      have hq' : m / p + 1 = q := by
        have h1 := Nat.succ_div (a := m) (b := p)
        rw [if_pos (show p ∣ m + 1 from ⟨q, hq⟩), hq, Nat.mul_div_cancel_left q hp.pos] at h1
        exact h1.symm
      subst hq'
      refine ⟨z, hz, ?_⟩
      have hcast : ((m + 1 : ℕ) : ℚ) = (p : ℚ) * ((m / p + 1 : ℕ) : ℚ) := by exact_mod_cast hq
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hQ : ((m / p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [harm_succ s m, harm_succ s (m / p), mul_add ((p : ℚ) ^ s) (harm s m), e, hcast, mul_pow]
      have key : (p : ℚ) ^ s * (1 / ((p : ℚ) ^ s * ((m / p + 1 : ℕ) : ℚ) ^ s))
          = 1 / ((m / p + 1 : ℕ) : ℚ) ^ s := by
        field_simp
      rw [key]; ring
    · refine ⟨z + 1 / ((m + 1 : ℕ) : ℚ) ^ s, pint_add hp hz (pint_one_div_pow hp hd s), ?_⟩
      rw [add_zero, harm_succ s m, mul_add ((p : ℚ) ^ s) (harm s m), e]; ring

theorem harm_reduce_pcongZ (hp : p.Prime) {s : ℕ} (hs : 1 ≤ s) (m : ℕ) :
    PCongZ p ((p : ℚ) ^ s * harm s m) (harm s (m / p)) := by
  obtain ⟨z, hz, e⟩ := harm_reduce hp s m
  cases s with
  | zero => omega
  | succ t =>
    exact ⟨(p : ℚ) ^ t * z, pint_mul hp (pint_pow hp (pint_natCast hp p) t) hz,
      by linear_combination e⟩

theorem pint_harm (hp : p.Prime) {m : ℕ} (hm : m < p) (s : ℕ) : PInt p (harm s m) := by
  unfold harm
  refine pint_sum hp _ _ (fun i hi => pint_one_div_pow hp ?_ s)
  rw [Finset.mem_Icc] at hi
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- `m < p^(k+1) → p^(k s) H_m^{(s)} ∈ ℤ_(p)`. -/
theorem pint_pow_mul_harm (hp : p.Prime) (s k : ℕ) :
    ∀ m, m < p ^ (k + 1) → PInt p ((p : ℚ) ^ (k * s) * harm s m) := by
  induction k with
  | zero =>
    intro m hm
    rw [zero_mul, pow_zero, one_mul]
    exact pint_harm hp (by simpa using hm) s
  | succ k ih =>
    intro m hm
    obtain ⟨z, hz, e⟩ := harm_reduce hp s m
    have hlt : m / p < p ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul hp.pos, ← pow_succ]; exact hm
    have : (p : ℚ) ^ ((k + 1) * s) * harm s m
        = (p : ℚ) ^ (k * s) * harm s (m / p) + (p : ℚ) ^ ((k + 1) * s) * z := by
      rw [add_mul, one_mul, pow_add]; linear_combination (p : ℚ) ^ (k * s) * e
    rw [this]
    exact pint_add hp (ih _ hlt) (pint_mul hp (pint_pow hp (pint_natCast hp p) _) hz)

theorem pint_pow_harm (hp : p.Prime) (s : ℕ) {m : ℕ} (hm : m < p * p) :
    PInt p ((p : ℚ) ^ s * harm s m) := by
  have h := pint_pow_mul_harm hp s 1 m (by rw [show p ^ (1 + 1) = p * p by ring]; exact hm)
  rwa [one_mul] at h

theorem pint_pow_two_harm (hp : p.Prime) (s : ℕ) {m : ℕ} (hm : m < p * p * p) :
    PInt p ((p : ℚ) ^ (2 * s) * harm s m) :=
  pint_pow_mul_harm hp s 2 m (by rw [show p ^ (2 + 1) = p * p * p by ring]; exact hm)

end harmonic

/-! ## Small exact values -/

example : PInt 3 (1 / 2) := by unfold PInt; decide +kernel
example : ¬ PInt 3 (1 / 3) := by unfold PInt; decide +kernel
example : PInt 3 (7 / 10) := by unfold PInt; decide +kernel
example : ¬ PInt 2 (5 / 6) := by unfold PInt; decide +kernel
example : PCongZ 5 (6 / 5 * 5) 1 := ⟨1, pint_one (by norm_num), by norm_num⟩
example : PCongZ 3 (1 / 2) 2 := ⟨-1 / 2, by unfold PInt; decide +kernel, by norm_num⟩
example : ¬ PCongZ 3 1 2 := by
  rintro ⟨z, hz, e⟩
  have hz' : z = -1 / 3 := by push_cast at e; linarith
  subst hz'
  revert hz; unfold PInt; decide +kernel
example : PCong 3 4 1 := pcong_of_pcongZ (by norm_num) ⟨1, pint_one (by norm_num), by norm_num⟩
example : harm 2 3 = 49 / 36 := by decide +kernel
example : harm 1 4 = 25 / 12 := by decide +kernel
example : PInt 5 (harm 2 4) := by unfold PInt; decide +kernel
example : ¬ PInt 3 (harm 1 3) := by unfold PInt; decide +kernel
example : PCongZ 3 ((3 : ℚ) ^ 2 * harm 2 6) (harm 2 2) := by
  have h := harm_reduce_pcongZ (p := 3) (by norm_num) (s := 2) (by norm_num) 6
  norm_num at h ⊢; exact h
example : PInt 2 ((2 : ℚ) ^ 3 * harm 3 3) := by
  have h := pint_pow_harm (p := 2) (by norm_num) 3 (m := 3) (by norm_num)
  push_cast at h; exact h

end Zeta3.Harm