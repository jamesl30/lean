import Zeta3.Rho

/-!
# The row identity (ROW) of §5.1

For `n ≥ 1`, `m ≥ 0`, with `M = m(m+1)` and `S(t) = t²ρ_m(t)ρ_n(t+1)`:

`(n+1)³(ρ_{n+1}ρ_m − ρ_nρ_m) − n³(ρ_nρ_m − ρ_{n−1}ρ_m) − 2M(2n+1)ρ_nρ_m = −2(2n+1)(S(t) − S(t−1))`,

as an identity of rational functions, where `S(t−1) = (t−1)²ρ_m(t−1)ρ_n(t)`.  In Lean `x / 0 = 0`,
so the poles are excluded by hypotheses: `t ≠ −n, −(n+1)` (as in `lemma4`) and `t ≠ −m`
(needed for rule (b) for `ρ_m` at `t − 1`; at `t = −m` the identity genuinely fails in Lean, since
`ρ_m(t)` is set to `0` while `ρ_m(t−1)` is not).
-/

namespace Zeta3

/-- (ROW), for `n ≥ 1`, any `m`, and `t ≠ −n, −(n+1), −m`. -/
theorem row_identity {K : Type*} [Field K] (n m : ℕ) (hn : 1 ≤ n) (t : K)
    (h1 : t + (n : K) ≠ 0) (h2 : t + (n : K) + 1 ≠ 0) (h3 : t + (m : K) ≠ 0) :
    ((n : K) + 1) ^ 3 * (rho (n + 1) t * rho m t - rho n t * rho m t)
        - (n : K) ^ 3 * (rho n t * rho m t - rho (n - 1) t * rho m t)
        - 2 * ((m : K) * ((m : K) + 1)) * (2 * (n : K) + 1) * (rho n t * rho m t)
      = -2 * (2 * (n : K) + 1) *
          (t ^ 2 * rho m t * rho n (t + 1) - (t - 1) ^ 2 * rho m (t - 1) * rho n t) := by
  have L := lemma4 n hn t h1 h2
  have R := rho_shift m (t - 1) (by intro h; apply h3; linear_combination h)
  rw [sub_add_cancel] at R
  linear_combination rho m t * L - 2 * (2 * (n : K) + 1) * rho n t * R

end Zeta3
