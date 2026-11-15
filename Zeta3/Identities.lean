import Zeta3.Rho

/-!
# Four more identities of the report, as identities of field elements

Over any field `K` (with `CharZero K` only where the text divides by `n + 1`), in the style of
`Zeta3.Rho` and `Zeta3.Row`: `ρ_n(t)` is `Zeta3.rho n t`, and since `x / 0 = 0` in Lean the poles
are excluded by explicit hypotheses ("away from the poles").

1. `sigma`, `sigma_succ`, `sigma_shift` — §11.6: `σ_m(t) = m!/(t(t+1)⋯(t+m))` and its two rules.
   Difference from the text: the shift rule `(t-1)σ_m(t-1) = (t+m)σ_m(t)` is stated for
   `t ≠ 1` and `t ≠ -m`.  Both are needed in Lean: at `t = 1` the left side is `0·σ_m(0) = 0` in
   Lean but the right side is `(m+1)σ_m(1) = 1`; at `t = -m` the right side is `0` and the left
   side is not.  (As rational functions both sides agree identically.)
2. `zeta2_row`, `zeta2_diag`, `zeta2_third` — §11.6, "Along a row", "Along the diagonal",
   "Second change".  Hypotheses: `zeta2_row`: `n ≥ 1`, `t ≠ -n, -(n+1), -m` (as `row_identity`);
   no hypothesis `t ≠ 1` is needed there, because `ρ_n(1) = 0`.  `zeta2_diag`: `t ≠ -(n+1)`, any
   `n ≥ 0`, `CharZero K` (the factor `4/(n+1)`).  `zeta2_third`: `t ≠ -(n+1)`.
   `S_2(t-1)` and `G_2(t-1)` are written out: `(t-1)σ_m(t-1)ρ_n(t)` and `(t-1-n)ρ_n(t)σ_n(t)`.
3. `certificate`, `certificate_s` — §11, "The certificate of the standard proof": for `n ≥ 1` and
   `t ≠ -n, -(n+1)`, with `s(t) = 4(2n+1)(-2t²+t+(2n+1)²)` written out, `H(t-1) = s(t)ρ_n(t)²` and
   `H(t) = s(t+1)ρ_n(t+1)²`; `certificate_s` is the polynomial identity for `s` (by `ring`).
4. `col_identity` — §11.4, (COL): `a = n+1`, `b = l+1` written out, `r = (b-a)(a²-ab+b²)`,
   `C(t) = (t-n)(t-l)ρ_n(t+1)ρ_l(t+1)`, `C(t-1) = (t-1-n)(t-1-l)ρ_n(t)ρ_l(t)`; for
   `t ≠ -(n+1), -(l+1)`.
5. `log2_identity` — §11.6, "Third change": for `n ≥ 1`, `t ≠ -n, -(n+1)`.
In every statement `ρ_{n-1}` is `rho (n - 1)` with natural subtraction, used only for `n ≥ 1`.
-/

set_option autoImplicit false

namespace Zeta3

/-! ## σ_m and its two rules -/

/-- `σ_m(t) = m! / (t(t+1)⋯(t+m))`. -/
noncomputable def sigma {K : Type*} [Field K] (m : ℕ) (t : K) : K :=
  (m.factorial : K) / (∏ j ∈ Finset.range (m + 1), (t + (j : K)))

/-- `σ_{m+1}(t) = σ_m(t)·(m+1)/(t+m+1)`, with no hypothesis. -/
theorem sigma_succ {K : Type*} [Field K] (m : ℕ) (t : K) :
    sigma (m + 1) t = sigma m t * ((m : K) + 1) / (t + (m : K) + 1) := by
  unfold sigma
  rw [Finset.prod_range_succ (fun j : ℕ => t + (j : K)) (m + 1), Nat.factorial_succ]
  simp only [div_eq_mul_inv, mul_inv]
  push_cast
  ring

/-- `(t-1)·σ_m(t-1) = (t+m)·σ_m(t)`, for `t ≠ 1` and `t ≠ -m`. -/
theorem sigma_shift {K : Type*} [Field K] (m : ℕ) (t : K) (h1 : t - 1 ≠ 0)
    (h2 : t + (m : K) ≠ 0) :
    (t - 1) * sigma m (t - 1) = (t + (m : K)) * sigma m t := by
  unfold sigma
  have eA : ∏ j ∈ Finset.range (m + 1), (t - 1 + (j : K))
      = (∏ j ∈ Finset.range m, (t + (j : K))) * (t - 1) := by
    rw [Finset.prod_range_succ']
    push_cast
    congr 1
    · exact Finset.prod_congr rfl (fun j _ => by ring)
    · ring
  have eB : ∏ j ∈ Finset.range (m + 1), (t + (j : K))
      = (∏ j ∈ Finset.range m, (t + (j : K))) * (t + (m : K)) :=
    Finset.prod_range_succ _ _
  rw [eA, eB]
  set P := ∏ j ∈ Finset.range m, (t + (j : K))
  by_cases hP : P = 0
  · simp [hP]
  field_simp

/-- The same rule one step later: `t·σ_m(t) = (t+m+1)·σ_m(t+1)`, for `t ≠ 0`, `t ≠ -(m+1)`. -/
theorem sigma_shift' {K : Type*} [Field K] (m : ℕ) (t : K) (h1 : t ≠ 0)
    (h2 : t + (m : K) + 1 ≠ 0) :
    t * sigma m t = (t + (m : K) + 1) * sigma m (t + 1) := by
  have h := sigma_shift m (t + 1) (by simpa using h1) (by intro h; apply h2; linear_combination h)
  rw [add_sub_cancel_right] at h
  linear_combination h

/-- `ρ_n(1) = 0` for `n ≥ 1`. -/
theorem rho_one {K : Type*} [Field K] (n : ℕ) (hn : 1 ≤ n) : rho n (1 : K) = 0 := by
  unfold rho
  rw [Finset.prod_eq_zero (i := 0) (by simp; omega) (by simp), zero_div]

/-! ## ζ(2): the row, the diagonal and the third identity (§11.6) -/

/-- (row) of §11.6, for `n ≥ 1`, any `m`, `t ≠ -n, -(n+1), -m`; here
`S_2(t) = tσ_m(t)ρ_n(t+1)` and `S_2(t-1) = (t-1)σ_m(t-1)ρ_n(t)`. -/
theorem zeta2_row {K : Type*} [Field K] (n m : ℕ) (hn : 1 ≤ n) (t : K)
    (h1 : t + (n : K) ≠ 0) (h2 : t + (n : K) + 1 ≠ 0) (h3 : t + (m : K) ≠ 0) :
    ((n : K) + 1) ^ 2 * rho (n + 1) t * sigma m t
        - (2 * (n : K) + 1) * (2 * (m : K) + 1) * rho n t * sigma m t
        - (n : K) ^ 2 * rho (n - 1) t * sigma m t
      = 2 * (2 * (n : K) + 1) *
          (t * sigma m t * rho n (t + 1) - (t - 1) * sigma m (t - 1) * rho n t) := by
  have hσ : (t - 1) * sigma m (t - 1) * rho n t = (t + (m : K)) * sigma m t * rho n t := by
    by_cases ht : t - 1 = 0
    · have : t = 1 := by linear_combination ht
      subst this
      rw [rho_one n hn]; ring
    · rw [sigma_shift m t ht h3]
  rw [hσ]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [rho_succ_shift k t, rho_succ (k + 1) t, rho_succ k t]
  push_cast at h1 h2 ⊢
  have h1' : (k : K) + 1 + t ≠ 0 := by intro h; apply h1; linear_combination h
  have h2' : (k : K) + 1 + 1 + t ≠ 0 := by intro h; apply h2; linear_combination h
  have h3' : t + (k : K) + 2 ≠ 0 := by intro h; apply h2; linear_combination h
  have h4' : t + (k : K) + 1 ≠ 0 := by intro h; apply h1; linear_combination h
  field_simp
  ring

/-- `(t-n)ρ_n(t+1)σ_n(t+1)·(t+n+1)² = t³ρ_n(t)σ_n(t)`, for `t ≠ -(n+1)`. -/
theorem G2_shift {K : Type*} [Field K] [CharZero K] (n : ℕ) (t : K)
    (h : t + (n : K) + 1 ≠ 0) :
    (t - n) * rho n (t + 1) * sigma n (t + 1) * (t + (n : K) + 1) ^ 2
      = t ^ 3 * rho n t * sigma n t := by
  have hb := rho_shift n t h
  by_cases ht : t = 0
  · subst ht
    have hn : (n : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    have : ((0 : K) - n) * rho n (0 + 1) = 0 := by
      have e : ((0 : K) - n) * rho n (0 + 1) * ((n : K) + 1) = 0 := by
        linear_combination -hb
      rcases mul_eq_zero.mp e with e | e
      · exact e
      · exact absurd e hn
    rw [this]; ring
  · have hs := sigma_shift' n t ht h
    linear_combination (-(t * sigma n t)) * hb -((t - n) * (t + n + 1) * rho n (t + 1)) * hs

/-- (diag) of §11.6, for any `n`, `t ≠ -(n+1)`; here `G_2(t) = (t-n)ρ_n(t+1)σ_n(t+1)` and
`G_2(t-1) = (t-1-n)ρ_n(t)σ_n(t)`. -/
theorem zeta2_diag {K : Type*} [Field K] [CharZero K] (n : ℕ) (t : K)
    (h : t + (n : K) + 1 ≠ 0) :
    2 * rho (n + 1) t * sigma (n + 1) t - rho n t * sigma n t
        - 5 * rho (n + 1) t * sigma n t
      = -(4 / ((n : K) + 1)) *
          ((t - n) * rho n (t + 1) * sigma n (t + 1) - (t - 1 - n) * rho n t * sigma n t) := by
  have hG := G2_shift n t h
  have hn : (n : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h' : (n : K) + 1 + t ≠ 0 := by intro e; apply h; linear_combination e
  have hG' : (t - n) * rho n (t + 1) * sigma n (t + 1)
      = t ^ 3 * rho n t * sigma n t / (t + (n : K) + 1) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 h)]; exact hG
  rw [hG', rho_succ n t, sigma_succ n t]
  field_simp
  ring

/-- The third identity of §11.6 ("Second change"): `(ρ_n + ρ_{n+1})σ_n = 2ρ_nσ_{n+1}`, for
`t ≠ -(n+1)`. -/
theorem zeta2_third {K : Type*} [Field K] (n : ℕ) (t : K) (h : t + (n : K) + 1 ≠ 0) :
    (rho n t + rho (n + 1) t) * sigma n t = 2 * rho n t * sigma (n + 1) t := by
  have h' : (n : K) + 1 + t ≠ 0 := by intro e; apply h; linear_combination e
  rw [rho_succ n t, sigma_succ n t]
  field_simp
  ring

/-! ## The certificate of the standard proof (§11) -/

/-- The two forms of `s(t)` in §11 agree (a polynomial identity). -/
theorem certificate_s {K : Type*} [Field K] (n : ℕ) (t : K) :
    4 * ((n : K) + 1) * ((n : K) + 1 - t) ^ 2 + 12 * (2 * (n : K) + 1) * ((n : K) + 1 - t) * (n + t)
        + 4 * (n : K) * (n + t) ^ 2
      = 4 * (2 * (n : K) + 1) * (-2 * t ^ 2 + t + (2 * (n : K) + 1) ^ 2) := by
  ring

/-- The certificate of §11: for `n ≥ 1` and `t ≠ -n, -(n+1)`,
`(n+1)³ρ_{n+1}² - b_nρ_n² + n³ρ_{n-1}² = H(t) - H(t-1)` with `H(t-1) = s(t)ρ_n(t)²`,
`H(t) = s(t+1)ρ_n(t+1)²`, `s(t) = 4(2n+1)(-2t²+t+(2n+1)²)`, `b_n = 34n³+51n²+27n+5`. -/
theorem certificate {K : Type*} [Field K] (n : ℕ) (hn : 1 ≤ n) (t : K)
    (h1 : t + (n : K) ≠ 0) (h2 : t + (n : K) + 1 ≠ 0) :
    ((n : K) + 1) ^ 3 * rho (n + 1) t ^ 2
        - (34 * (n : K) ^ 3 + 51 * (n : K) ^ 2 + 27 * (n : K) + 5) * rho n t ^ 2
        + (n : K) ^ 3 * rho (n - 1) t ^ 2
      = 4 * (2 * (n : K) + 1) * (-2 * (t + 1) ^ 2 + (t + 1) + (2 * (n : K) + 1) ^ 2)
            * rho n (t + 1) ^ 2
        - 4 * (2 * (n : K) + 1) * (-2 * t ^ 2 + t + (2 * (n : K) + 1) ^ 2) * rho n t ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [rho_succ_shift k t, rho_succ (k + 1) t, rho_succ k t]
  push_cast at h1 h2 ⊢
  have h1' : (k : K) + 1 + t ≠ 0 := by intro h; apply h1; linear_combination h
  have h2' : (k : K) + 1 + 1 + t ≠ 0 := by intro h; apply h2; linear_combination h
  have h3' : t + (k : K) + 2 ≠ 0 := by intro h; apply h2; linear_combination h
  have h4' : t + (k : K) + 1 ≠ 0 := by intro h; apply h1; linear_combination h
  field_simp
  ring

/-! ## (COL), §11.4 -/

/-- (COL): with `a = n+1`, `b = l+1`, `r = (b-a)(a²-ab+b²)`,
`C(t) = (t-n)(t-l)ρ_n(t+1)ρ_l(t+1)`: `b³ρ_nρ_{l+1} - a³ρ_{n+1}ρ_l - rρ_nρ_l = 2(a-b)[C(t)-C(t-1)]`,
for `t ≠ -(n+1), -(l+1)`. -/
theorem col_identity {K : Type*} [Field K] (n l : ℕ) (t : K)
    (h1 : t + (n : K) + 1 ≠ 0) (h2 : t + (l : K) + 1 ≠ 0) :
    ((l : K) + 1) ^ 3 * rho n t * rho (l + 1) t - ((n : K) + 1) ^ 3 * rho (n + 1) t * rho l t
        - (((l : K) + 1) - ((n : K) + 1)) *
            (((n : K) + 1) ^ 2 - ((n : K) + 1) * ((l : K) + 1) + ((l : K) + 1) ^ 2)
            * rho n t * rho l t
      = 2 * (((n : K) + 1) - ((l : K) + 1)) *
          ((t - n) * (t - l) * rho n (t + 1) * rho l (t + 1)
            - (t - 1 - n) * (t - 1 - l) * rho n t * rho l t) := by
  have hbn := rho_shift n t h1
  have hbl := rho_shift l t h2
  have h1' : (n : K) + 1 + t ≠ 0 := by intro e; apply h1; linear_combination e
  have h2' : (l : K) + 1 + t ≠ 0 := by intro e; apply h2; linear_combination e
  have en : (t - n) * rho n (t + 1) = t ^ 2 * rho n t / (t + (n : K) + 1) := by
    rw [eq_div_iff h1]; linear_combination -hbn
  have el : (t - l) * rho l (t + 1) = t ^ 2 * rho l t / (t + (l : K) + 1) := by
    rw [eq_div_iff h2]; linear_combination -hbl
  rw [show (t - n) * (t - l) * rho n (t + 1) * rho l (t + 1)
      = ((t - n) * rho n (t + 1)) * ((t - l) * rho l (t + 1)) by ring, en, el,
    rho_succ n t, rho_succ l t]
  field_simp
  ring

/-! ## log 2, §11.6 "Third change" -/

/-- For `n ≥ 1` and `t ≠ -n, -(n+1)`:
`(n+1)ρ_{n+1} - 3(2n+1)ρ_n + nρ_{n-1} = -2(2n+1)[ρ_n(t+1) + ρ_n(t)]`. -/
theorem log2_identity {K : Type*} [Field K] (n : ℕ) (hn : 1 ≤ n) (t : K)
    (h1 : t + (n : K) ≠ 0) (h2 : t + (n : K) + 1 ≠ 0) :
    ((n : K) + 1) * rho (n + 1) t - 3 * (2 * (n : K) + 1) * rho n t + (n : K) * rho (n - 1) t
      = -2 * (2 * (n : K) + 1) * (rho n (t + 1) + rho n t) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [rho_succ_shift k t, rho_succ (k + 1) t, rho_succ k t]
  push_cast at h1 h2 ⊢
  have h1' : (k : K) + 1 + t ≠ 0 := by intro h; apply h1; linear_combination h
  have h2' : (k : K) + 1 + 1 + t ≠ 0 := by intro h; apply h2; linear_combination h
  have h3' : t + (k : K) + 2 ≠ 0 := by intro h; apply h2; linear_combination h
  have h4' : t + (k : K) + 1 ≠ 0 := by intro h; apply h1; linear_combination h
  field_simp
  ring

-- CLAIMED: Zeta3.sigma_succ, Zeta3.sigma_shift, Zeta3.zeta2_row, Zeta3.zeta2_diag, Zeta3.zeta2_third
-- CLAIMED: Zeta3.certificate, Zeta3.certificate_s, Zeta3.col_identity, Zeta3.log2_identity

end Zeta3
