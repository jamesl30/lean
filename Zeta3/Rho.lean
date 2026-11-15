import Mathlib

/-!
# The rational functions `ρ_n` and the identities of §3 and §5.2

`ρ_n(t) = (1-t)(2-t)⋯(n-t) / (t(t+1)⋯(t+n))`, over any field `K`.  In Lean, `x / 0 = 0`, so the
definition makes sense for every `t`; the hypotheses of each theorem say exactly which values of
`t` are excluded.
-/

namespace Zeta3

/-- `ρ_n(t) = (1-t)(2-t)⋯(n-t) / (t(t+1)⋯(t+n))`. -/
noncomputable def rho {K : Type*} [Field K] (n : ℕ) (t : K) : K :=
  (∏ j ∈ Finset.range n, ((j : K) + 1 - t)) / (∏ j ∈ Finset.range (n + 1), (t + (j : K)))

/-- Rule (a): `ρ_{n+1}(t) = ρ_n(t)·(n+1-t)/(n+1+t)`.  No hypothesis is needed (with `x/0 = 0`
both sides vanish when `t = -(n+1)`). -/
theorem rho_succ {K : Type*} [Field K] (n : ℕ) (t : K) :
    rho (n + 1) t = rho n t * ((n : K) + 1 - t) / ((n : K) + 1 + t) := by
  unfold rho
  rw [Finset.prod_range_succ, Finset.prod_range_succ (fun j : ℕ => t + (j : K)) (n + 1)]
  simp only [div_eq_mul_inv, mul_inv]
  push_cast
  ring

/-- Numerator identity: `(n - t)·P_n(t+1) = -t·P_n(t)`. -/
private lemma num_shift {K : Type*} [Field K] (n : ℕ) (t : K) :
    ((n : K) - t) * (∏ j ∈ Finset.range n, ((j : K) + 1 - (t + 1)))
      = -t * ∏ j ∈ Finset.range n, ((j : K) + 1 - t) := by
  have h1 := Finset.prod_range_succ (fun j : ℕ => (j : K) - t) n
  have h2 := Finset.prod_range_succ' (fun j : ℕ => (j : K) - t) n
  have e1 : ∏ j ∈ Finset.range n, ((j : K) + 1 - (t + 1)) = ∏ j ∈ Finset.range n, ((j : K) - t) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  have e2 : ∏ j ∈ Finset.range n, ((j : K) + 1 - t) =
      ∏ j ∈ Finset.range n, (((j + 1 : ℕ) : K) - t) :=
    Finset.prod_congr rfl (fun j _ => by push_cast; ring)
  rw [e1, e2]
  simp only [Nat.cast_zero] at h2
  linear_combination h1.symm.trans h2

/-- Denominator identity: `t·Q_n(t+1) = (t+n+1)·Q_n(t)`. -/
private lemma den_shift {K : Type*} [Field K] (n : ℕ) (t : K) :
    t * (∏ j ∈ Finset.range (n + 1), (t + 1 + (j : K)))
      = (t + (n : K) + 1) * ∏ j ∈ Finset.range (n + 1), (t + (j : K)) := by
  have h1 := Finset.prod_range_succ (fun j : ℕ => t + (j : K)) (n + 1)
  have h2 := Finset.prod_range_succ' (fun j : ℕ => t + (j : K)) (n + 1)
  have e : ∏ j ∈ Finset.range (n + 1), (t + 1 + (j : K)) =
      ∏ j ∈ Finset.range (n + 1), (t + ((j + 1 : ℕ) : K)) :=
    Finset.prod_congr rfl (fun j _ => by push_cast; ring)
  rw [e]
  simp only [Nat.cast_zero, add_zero] at h2
  push_cast at h1
  linear_combination h2.symm.trans h1

/-- Rule (b): `t²·ρ_n(t) = (t-n)(t+n+1)·ρ_n(t+1)`, for `t ≠ -(n+1)`. -/
theorem rho_shift {K : Type*} [Field K] (n : ℕ) (t : K) (ht : t + (n : K) + 1 ≠ 0) :
    t ^ 2 * rho n t = (t - n) * (t + n + 1) * rho n (t + 1) := by
  unfold rho
  have hN := num_shift n t
  have hD := den_shift n t
  set P := ∏ j ∈ Finset.range n, ((j : K) + 1 - t)
  set P' := ∏ j ∈ Finset.range n, ((j : K) + 1 - (t + 1))
  set Q := ∏ j ∈ Finset.range (n + 1), (t + (j : K))
  set Q' := ∏ j ∈ Finset.range (n + 1), (t + 1 + (j : K))
  by_cases ht0 : t = 0
  · subst ht0
    simp only [zero_add, ne_eq] at *
    have : (n : K) * P' = 0 := by linear_combination hN
    have e : ((0 : K) - n) * (n + 1) * (P' / Q') = -((n : K) * P') * (n + 1) / Q' := by ring
    rw [e, this]
    simp
  by_cases hQ : Q = 0
  · have hQ' : Q' = 0 := by
      have : t * Q' = 0 := by rw [hD, hQ, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left ht0
    simp [hQ, hQ']
  have hQ' : Q' ≠ 0 := by
    intro h
    apply hQ
    have : (t + (n : K) + 1) * Q = 0 := by rw [← hD, h, mul_zero]
    exact (mul_eq_zero.mp this).resolve_left ht
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff hQ hQ']
  linear_combination (t * P) * hD + ((t + n + 1) * Q) * hN

/-- (SIX), with `G(t) - G(t-1) = (n-t)²ρ_n(t+1)² - (n+1-t)²ρ_n(t)²`, for `t ≠ -(n+1)`. -/
theorem six_identity {K : Type*} [Field K] [CharZero K] (n : ℕ) (t : K)
    (ht : t + (n : K) + 1 ≠ 0) :
    rho (n + 1) t ^ 2 + rho n t ^ 2 - 6 * rho (n + 1) t * rho n t
      = 4 / ((n : K) + 1) ^ 2 * (((n : K) - t) ^ 2 * rho n (t + 1) ^ 2
          - ((n : K) + 1 - t) ^ 2 * rho n t ^ 2) := by
  have hs := rho_shift n t ht
  have hβ : (n : K) + 1 + t ≠ 0 := by
    intro h; apply ht; linear_combination h
  have hn : (n : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hb : ((n : K) - t) * rho n (t + 1) = -(t ^ 2 * rho n t) / ((n : K) + 1 + t) := by
    rw [eq_div_iff hβ]
    linear_combination hs
  rw [show ((n : K) - t) ^ 2 * rho n (t + 1) ^ 2 = (((n : K) - t) * rho n (t + 1)) ^ 2 by ring,
    hb, rho_succ]
  field_simp
  ring

/-- `ρ_{k+1}(t+1) = -t²ρ_k(t)/((t+k+1)(t+k+2))`, with no hypothesis. -/
theorem rho_succ_shift {K : Type*} [Field K] (k : ℕ) (t : K) :
    rho (k + 1) (t + 1) = -(t ^ 2 * rho k t) / ((t + (k : K) + 1) * (t + (k : K) + 2)) := by
  unfold rho
  have hP : ∏ j ∈ Finset.range (k + 1), ((j : K) + 1 - (t + 1))
      = (∏ j ∈ Finset.range k, ((j : K) + 1 - t)) * (-t) := by
    rw [Finset.prod_range_succ']
    push_cast
    congr 1
    · exact Finset.prod_congr rfl (fun j _ => by ring)
    · ring
  have hD := den_shift (k + 1) t
  have hQ := Finset.prod_range_succ (fun j : ℕ => t + (j : K)) (k + 1)
  rw [hP]
  by_cases ht0 : t = 0
  · subst ht0; simp
  have hD' : (∏ j ∈ Finset.range (k + 1 + 1), (t + 1 + (j : K))) * t
      = (t + ((k + 1 : ℕ) : K) + 1) * ∏ j ∈ Finset.range (k + 1 + 1), (t + (j : K)) := by
    rw [mul_comm]; exact hD
  rw [← mul_div_mul_right _ _ ht0, hD', hQ]
  simp only [div_eq_mul_inv, mul_inv]
  push_cast
  field_simp
  ring

/-- Lemma 4, identity (5.3), for `n ≥ 1` and `t ≠ -n, -(n+1)`. -/
theorem lemma4 {K : Type*} [Field K] (n : ℕ) (hn : 1 ≤ n) (t : K)
    (h1 : t + (n : K) ≠ 0) (h2 : t + (n : K) + 1 ≠ 0) :
    ((n : K) + 1) ^ 3 * (rho (n + 1) t - rho n t) - (n : K) ^ 3 * (rho n t - rho (n - 1) t)
      = 2 * (2 * (n : K) + 1) * (t * (t - 1) * rho n t - t ^ 2 * rho n (t + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [rho_succ_shift k t, rho_succ (k + 1) t, rho_succ k t]
  push_cast at h1 h2 ⊢
  have h1' : (k : K) + 1 + t ≠ 0 := by intro h; apply h1; linear_combination h
  have h2' : (k : K) + 1 + 1 + t ≠ 0 := by intro h; apply h2; linear_combination h
  have h3 : t + (k : K) + 2 ≠ 0 := by intro h; apply h2; linear_combination h
  have h4 : t + (k : K) + 1 ≠ 0 := by intro h; apply h1; linear_combination h
  field_simp
  ring
