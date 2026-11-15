import Mathlib

/-!
# Row relation + column relation ⇒ diagonal relation; the commutation lemma

Purely algebraic statements about abstract tables `T : ℕ → ℕ → K` over a field of
characteristic 0 (written proofs: `zeta3/research/work/row2-commute/proof.md`, P2, P3, P4e).
No definitions are introduced. The hypotheses were checked numerically on the real tables
U₂(n,m) = Σₖ C(n,k)C(n+k,k)C(m,k) and U(n,m) = Σₖ C(n,k)C(n+k,k)C(m,k)C(m+k,k) for
0 ≤ n, m ≤ 5 (`work/row2-commute/lean/numcheck.py`).
-/

-- CLAIMED: Zeta3.RowCol.zeta2_diag_of_row_col, Zeta3.RowCol.mix_of_row_col, Zeta3.RowCol.commute_companion, Zeta3.RowCol.eq_companion_of_commute, Zeta3.RowCol.eq_half_of_commute

set_option autoImplicit false

namespace Zeta3.RowCol
/-- P2: the ζ(2) row relation and the column relation (COL₂) give the diagonal relation
`2 T(n+1,n+1) = T(n,n) + 5 T(n+1,n)` (5(n+1)² = [4(n+1)² − 1] + [(n+1)² + 1]). -/
theorem zeta2_diag_of_row_col {K : Type*} [Field K] [CharZero K] (T : ℕ → ℕ → K)
    (hrow : ∀ n m : ℕ, ((n : K) + 2) ^ 2 * T (n + 2) m
      = (2 * (n : K) + 3) * (2 * (m : K) + 1) * T (n + 1) m + ((n : K) + 1) ^ 2 * T n m)
    (hcol : ∀ n m : ℕ, 2 * ((m : K) + 1) ^ 2 * T n (m + 1)
      = ((n : K) + 1) ^ 2 * T (n + 1) m
        + (2 * ((m : K) + 1) ^ 2 - 2 * ((n : K) + 1) * ((m : K) + 1) + ((n : K) + 1) ^ 2)
          * T n m) :
    ∀ n : ℕ, 2 * T (n + 1) (n + 1) = T n n + 5 * T (n + 1) n := by
  intro n
  have h1 := hcol (n + 1) n
  have h2 := hrow n n
  push_cast at h1 h2
  have hne : ((n : K) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_add_one_ne_zero n)
  apply mul_left_cancel₀ hne
  linear_combination h1 + h2

/-- P3: Apéry's row relation (R) and the column relation (COL) give (MIX)
`T(n+1,n+1) + T(n,n) = 6 T(n+1,n)`, with no symmetry hypothesis on `T`. -/
theorem mix_of_row_col {K : Type*} [Field K] [CharZero K] (T : ℕ → ℕ → K)
    (hrow : ∀ n m : ℕ, ((n : K) + 2) ^ 3 * T (n + 2) m + ((n : K) + 1) ^ 3 * T n m
      = (((n : K) + 1) ^ 3 + ((n : K) + 2) ^ 3 + 2 * (m : K) * ((m : K) + 1) * (2 * (n : K) + 3))
        * T (n + 1) m)
    (hcol : ∀ n l : ℕ, ((l : K) + 1) ^ 3 * T n (l + 1)
      = ((n : K) + 1) ^ 3 * T (n + 1) l
        + (((l : K) + 1) - ((n : K) + 1))
          * (((n : K) + 1) ^ 2 - ((n : K) + 1) * ((l : K) + 1) + ((l : K) + 1) ^ 2) * T n l) :
    ∀ n : ℕ, T (n + 1) (n + 1) + T n n = 6 * T (n + 1) n := by
  intro n
  have h1 := hcol (n + 1) n
  have h2 := hrow n n
  push_cast at h1 h2
  have hne : ((n : K) + 1) ^ 3 ≠ 0 := pow_ne_zero 3 (Nat.cast_add_one_ne_zero n)
  apply mul_left_cancel₀ hne
  linear_combination h1 + h2

/-- P4e: a 2×2 matrix commutes with the companion matrix `!![0, 1; c, d]` iff it is
`p • 1 + q • !![0, 1; c, d]`, where `(p, q)` is its first row. -/
theorem commute_companion {K : Type*} [CommRing K] (c d : K) (M : Matrix (Fin 2) (Fin 2) K) :
    M * !![0, 1; c, d] = !![0, 1; c, d] * M ↔ M = M 0 0 • 1 + M 0 1 • !![0, 1; c, d] := by
  constructor
  · intro h
    have e : ∀ i j, (M * !![0, 1; c, d]) i j = (!![0, 1; c, d] * M) i j := fun i j => by rw [h]
    have h00 := e 0 0
    have h01 := e 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    ext i j
    fin_cases i <;> fin_cases j <;> (try simp) <;>
      first
      | linear_combination h00
      | linear_combination -h00
      | linear_combination h01
      | linear_combination -h01
  · intro h
    rw [h]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- A matrix with first row `(0, 1)` commuting with `!![0, 1; c, d]` is that matrix. -/
theorem eq_companion_of_commute {K : Type*} [CommRing K] (c d : K)
    (M : Matrix (Fin 2) (Fin 2) K) (h0 : M 0 0 = 0) (h1 : M 0 1 = 1)
    (hc : M * !![0, 1; c, d] = !![0, 1; c, d] * M) : M = !![0, 1; c, d] := by
  rw [(commute_companion c d M).1 hc, h0, h1]
  simp

/-- A matrix with first row `(1/2, 1/2)` commuting with `!![0, 1; 1, 4]` is
`!![1/2, 1/2; 1/2, 5/2]` (the ζ(2) column step on the diagonal). -/
theorem eq_half_of_commute {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 2) (Fin 2) K) (h0 : M 0 0 = 1 / 2) (h1 : M 0 1 = 1 / 2)
    (hc : M * !![0, 1; 1, 4] = !![0, 1; 1, 4] * M) :
    M = !![1 / 2, 1 / 2; 1 / 2, 5 / 2] := by
  rw [(commute_companion 1 4 M).1 hc, h0, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

end Zeta3.RowCol