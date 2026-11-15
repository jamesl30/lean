import Mathlib
set_option autoImplicit false

/-!
# The necessity criterion for congruence schemes (Theorem `thm:kempner` of the report)

This file formalizes Definition `def:scheme` and Theorem `thm:kempner` (necessity) of the
problem-94 report.

* `R`-periodic functions (`IsPeriodic`), `B`-sparse functions (`IsSparse`) and schemes of degree
  at most `r` (`IsScheme`) follow Definition `def:scheme`. Functions on the positive integers
  are Mathlib's `ArithmeticFunction ℤ` (value `0` at `0`, which is never used), and `*` is
  Dirichlet convolution.
* `term_apply` is Step 1 of the proof (the core lemma): at a product `t` of `s` distinct primes,
  each `> B` and `≡ 1 (mod R)`, a term `P * u₁ * ⋯ * u_ℓ` takes the value
  `P(1) · ∏ⱼ uⱼ(1) · ℓ ^ s` (Lean's `0 ^ 0 = 1`).
* `kempner_general`, `kempner_b`, `kempner_a`, `kempner_c`, `kempner_c_order` are the theorem.
-/

namespace Mathathon.Kempner

open ArithmeticFunction Finset Polynomial
open scoped Nat ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

/-! ## Definitions (Definition `def:scheme`) -/

/-- `u` is `R`-periodic: for positive integers `m, n`, `m ≡ n (mod R)` implies `u m = u n`. -/
def IsPeriodic (R : ℕ) (u : ArithmeticFunction ℤ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m ≡ n [MOD R] → u m = u n

/-- `P` is `B`-sparse: if `P n ≠ 0`, every prime `p > B` dividing `n` divides it at least twice. -/
def IsSparse (B : ℕ) (P : ArithmeticFunction ℤ) : Prop :=
  ∀ n : ℕ, P n ≠ 0 → ∀ p : ℕ, p.Prime → B < p → p ∣ n → p ^ 2 ∣ n

/-- `G` is a scheme of degree at most `r` (with parameters `R`, `B`): a finite sum
`G = ∑ᵢ cᵢ (Pᵢ * uᵢ,₁ * ⋯ * uᵢ,ℓᵢ)` with integers `cᵢ`, `B`-sparse `Pᵢ`, `R`-periodic `uᵢ,ⱼ`
and `ℓᵢ ≤ r`, written pointwise: `G n = ∑ᵢ cᵢ · (Pᵢ * ∏ⱼ uᵢ,ⱼ)(n)`. Here `*` and `∏` are Dirichlet
convolution; for `ℓᵢ = 0` the empty product is the unit `1` of Dirichlet convolution, so the
term is `cᵢ · Pᵢ(n)`. -/
def IsScheme (R B r : ℕ) (G : ArithmeticFunction ℤ) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℤ) (P : Fin k → ArithmeticFunction ℤ) (ℓ : Fin k → ℕ)
    (u : (i : Fin k) → Fin (ℓ i) → ArithmeticFunction ℤ),
    (∀ i, ℓ i ≤ r) ∧ (∀ i, IsSparse B (P i)) ∧ (∀ i j, IsPeriodic R (u i j)) ∧
    ∀ n, G n = ∑ i, c i * (P i * ∏ j, u i j) n

/-- `S` is a finite set of primes, each `> B` and `≡ 1 (mod R)`. Its product `∏ q ∈ S, q`
is a product of `S.card` distinct such primes. -/
def GoodPrimes (R B : ℕ) (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, p.Prime ∧ B < p ∧ p ≡ 1 [MOD R]

/-- A sanity check that the definition is not vacuous: `ζ = δ * ζ` (the constant function `1`
on the positive integers) is a scheme of degree at most `1` with `R = 1`, `B = 0`. -/
example : IsScheme 1 0 1 (ζ : ArithmeticFunction ℤ) := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ _ => (ζ : ArithmeticFunction ℤ),
    fun _ => le_rfl, ?_, ?_, ?_⟩
  · intro _ n hn p hp _ hpn
    have h1 : n = 1 := by
      by_contra h
      exact hn (by simp [one_apply_ne h])
    subst h1
    exact absurd (Nat.le_of_dvd one_pos hpn) (not_le.2 hp.one_lt)
  · intro _ _ m n hm hn _
    simp [natCoe_apply, zeta_apply_ne hm.ne', zeta_apply_ne hn.ne']
  · intro n
    simp

/-! ## Step 1: the core lemma -/

section Stage1

variable {R B : ℕ}

/-- The constant multiple `n ↦ c · f(n)` (written out to avoid the several `•` instances on
`ArithmeticFunction`). -/
def cmul (c : ℤ) (f : ArithmeticFunction ℤ) : ArithmeticFunction ℤ := ⟨fun n => c * f n, by simp⟩

@[simp] lemma cmul_apply (c : ℤ) (f : ArithmeticFunction ℤ) (n : ℕ) : cmul c f n = c * f n := rfl

lemma cmul_mul_cmul (a b : ℤ) (f g : ArithmeticFunction ℤ) :
    cmul a f * cmul b g = cmul (a * b) (f * g) := by
  ext n
  simp only [cmul_apply, mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Two arithmetic functions agree on all divisors of `n`. -/
def EqOnDvd (n : ℕ) (f g : ArithmeticFunction ℤ) : Prop := ∀ d, d ∣ n → f d = g d

lemma EqOnDvd.mul {n : ℕ} {f f' g g' : ArithmeticFunction ℤ} (hf : EqOnDvd n f f')
    (hg : EqOnDvd n g g') : EqOnDvd n (f * g) (f' * g') := by
  intro d hd
  rw [mul_apply, mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h1 := Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  have h2 := Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  rw [hf _ (h1.trans hd), hg _ (h2.trans hd)]

lemma mem_of_prime_dvd_prod {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (h : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).1 hpq]

lemma not_mul_self_dvd_prod {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hpS : p ∈ S) :
    ¬ p * p ∣ ∏ q ∈ S, q := by
  rw [← Finset.mul_prod_erase S (fun q => q) hpS]
  intro h
  have h' := Nat.dvd_of_mul_dvd_mul_left (hS p hpS).pos h
  have := mem_of_prime_dvd_prod (fun q hq => hS q (Finset.mem_of_mem_erase hq)) (hS p hpS) h'
  simp at this

lemma squarefree_prod {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) : Squarefree (∏ q ∈ S, q) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp h
  exact not_mul_self_dvd_prod hS (mem_of_prime_dvd_prod hS hp ((Dvd.intro p rfl).trans h)) h

lemma prod_ne_zero' {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) : ∏ q ∈ S, q ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun q hq => (hS q hq).ne_zero

/-- Every divisor of a product of primes `≡ 1 (mod R)` is `≡ 1 (mod R)`. -/
lemma modEq_one_of_dvd_prod {S : Finset ℕ} (hS : GoodPrimes R B S) {d : ℕ}
    (hd : d ∣ ∏ q ∈ S, q) : d ≡ 1 [MOD R] := by
  have hS' : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact prod_ne_zero' hS' (Nat.eq_zero_of_zero_dvd hd)
  have key : ∀ l : List ℕ, (∀ p ∈ l, p ≡ 1 [MOD R]) → l.prod ≡ 1 [MOD R] := by
    intro l hl
    induction l with
    | nil => exact Nat.ModEq.refl 1
    | cons a l ih =>
      rw [List.prod_cons]
      have := (hl a (by simp)).mul (ih fun p hp => hl p (by simp [hp]))
      simpa using this
  rw [← Nat.prod_primeFactorsList hd0]
  apply key
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  have hpd := Nat.dvd_of_mem_primeFactorsList hp
  exact (hS p (mem_of_prime_dvd_prod hS' hpp (hpd.trans hd))).2.2

lemma zeta_pow_apply_prime (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    ((ζ : ArithmeticFunction ℤ) ^ ℓ) p = ℓ := by
  induction ℓ with
  | zero => simp [hp.ne_one]
  | succ ℓ ih =>
    have h1 : ((ζ : ArithmeticFunction ℤ) ^ ℓ) 1 = 1 :=
      (isMultiplicative_zeta.natCast.pow (k := ℓ)).map_one
    rw [pow_succ', coe_zeta_mul_apply, Nat.Prime.sum_divisors hp, ih, h1]
    push_cast
    ring

/-- `ζ ^ ℓ` (the `ℓ`-fold divisor function) at a product of `s` distinct primes is `ℓ ^ s`. -/
lemma zeta_pow_apply_prod (ℓ : ℕ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) :
    ((ζ : ArithmeticFunction ℤ) ^ ℓ) (∏ q ∈ S, q) = (ℓ : ℤ) ^ S.card := by
  rw [IsMultiplicative.map_prod_of_prime (isMultiplicative_zeta.natCast.pow (k := ℓ)) S hS,
    Finset.prod_congr rfl fun q hq => zeta_pow_apply_prime ℓ (hS q hq), Finset.prod_const]

/-- On the divisors of `t`, a product of periodic functions agrees with `(∏ⱼ uⱼ(1)) • ζ ^ ℓ`. -/
lemma prod_eqOnDvd {S : Finset ℕ} (hS : GoodPrimes R B S) {ι : Type*} (J : Finset ι)
    (u : ι → ArithmeticFunction ℤ) (hu : ∀ j ∈ J, IsPeriodic R (u j)) :
    EqOnDvd (∏ q ∈ S, q) (∏ j ∈ J, u j)
      (cmul (∏ j ∈ J, u j 1) ((ζ : ArithmeticFunction ℤ) ^ J.card)) := by
  classical
  have hS' : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  induction J using Finset.induction_on with
  | empty => intro d _; simp
  | insert j J hj ih =>
    have hone : EqOnDvd (∏ q ∈ S, q) (u j) (cmul (u j 1) (ζ : ArithmeticFunction ℤ)) := by
      intro d hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact prod_ne_zero' hS' (Nat.eq_zero_of_zero_dvd hd)
      rw [cmul_apply, natCoe_apply, zeta_apply_ne hd0, Nat.cast_one, mul_one]
      exact hu j (by simp) d 1 (Nat.pos_of_ne_zero hd0) one_pos (modEq_one_of_dvd_prod hS hd)
    have := hone.mul (ih fun j' hj' => hu j' (by simp [hj']))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj, pow_succ',
      ← cmul_mul_cmul]
    exact this

lemma sparse_eqOnDvd {S : Finset ℕ} (hS : GoodPrimes R B S) {P : ArithmeticFunction ℤ}
    (hP : IsSparse B P) : EqOnDvd (∏ q ∈ S, q) P (cmul (P 1) 1) := by
  have hS' : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  intro d hd
  by_cases h1 : d = 1
  · subst h1; simp
  · rw [cmul_apply, one_apply_ne h1, mul_zero]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hpS := mem_of_prime_dvd_prod hS' hp (hpd.trans hd)
    have h2 := hP d hne p hp (hS p hpS).2.1 hpd
    exact not_mul_self_dvd_prod hS' hpS (by rw [← sq]; exact h2.trans hd)

/-- **Step 1 (core lemma).** If `t = ∏ q ∈ S, q` is a product of `s = S.card` distinct primes,
each `> B` and `≡ 1 (mod R)`, `P` is `B`-sparse and `u₁, …, u_ℓ` are `R`-periodic, then
`(P * u₁ * ⋯ * u_ℓ)(t) = P(1) · ∏ⱼ uⱼ(1) · ℓ ^ s` (with `0 ^ 0 = 1`). -/
theorem term_apply {S : Finset ℕ} (hS : GoodPrimes R B S) {P : ArithmeticFunction ℤ}
    (hP : IsSparse B P) {ℓ : ℕ} (u : Fin ℓ → ArithmeticFunction ℤ)
    (hu : ∀ j, IsPeriodic R (u j)) :
    (P * ∏ j, u j) (∏ q ∈ S, q) = P 1 * (∏ j, u j 1) * (ℓ : ℤ) ^ S.card := by
  have hS' : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  have h := (sparse_eqOnDvd hS hP).mul (prod_eqOnDvd hS Finset.univ u (fun j _ => hu j))
  rw [h _ dvd_rfl, Finset.card_univ, Fintype.card_fin, cmul_mul_cmul, one_mul, cmul_apply,
    zeta_pow_apply_prod ℓ hS']

end Stage1

/-! ## Step 2 and the theorem -/

section Stage2

lemma sum_apply' {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℤ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ArithmeticFunction.add_apply, ih]

/-- A scheme of degree `≤ r`, evaluated at `t = ∏ q ∈ S, q`, is `∑ᵢ Cᵢ ℓᵢ ^ s` with `ℓᵢ ≤ r`
and integers `Cᵢ` independent of `S`. -/
lemma scheme_apply {R B r : ℕ} {G : ArithmeticFunction ℤ} (hG : IsScheme R B r G) :
    ∃ (k : ℕ) (C : Fin k → ℤ) (ℓ : Fin k → ℕ), (∀ i, ℓ i ≤ r) ∧
      ∀ S : Finset ℕ, GoodPrimes R B S →
        G (∏ q ∈ S, q) = ∑ i, C i * (ℓ i : ℤ) ^ S.card := by
  obtain ⟨k, c, P, ℓ, u, hℓ, hP, hu, hG⟩ := hG
  refine ⟨k, fun i => c i * (P i 1 * ∏ j, u i j 1), ℓ, hℓ, fun S hS => ?_⟩
  rw [hG]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term_apply hS (hP i) (u i) (hu i)]
  ring

/-- There are finite sets of primes `> B` and `≡ 1 (mod R)` of every size (Dirichlet's theorem
for the class `1`, Mathlib's `Nat.exists_prime_gt_modEq_one`). -/
lemma exists_goodPrimes {R : ℕ} (hR : 0 < R) (B s : ℕ) :
    ∃ S : Finset ℕ, S.card = s ∧ GoodPrimes R B S := by
  have hinf : {p : ℕ | p.Prime ∧ B < p ∧ p ≡ 1 [MOD R]}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    obtain ⟨p, hp, hlt, hmod⟩ := Nat.exists_prime_gt_modEq_one (max M B) hR.ne'
    have := hM ⟨hp, lt_of_le_of_lt (le_max_right _ _) hlt, hmod⟩
    exact absurd (lt_of_le_of_lt (le_max_left _ _) hlt) (not_lt.2 this)
  obtain ⟨S, hSsub, hcard⟩ := hinf.exists_subset_card_eq s
  exact ⟨S, hcard, fun p hp => hSsub hp⟩

/-- The polynomial `g(X) = X (X - 1) ⋯ (X - r)`. -/
noncomputable def g (r : ℕ) : ℤ[X] := ∏ i ∈ range (r + 1), (X - C (i : ℤ))

lemma g_eval (r : ℕ) (x : ℤ) : (g r).eval x = ∏ i ∈ range (r + 1), (x - i) := by
  simp [g, eval_prod]

lemma g_natDegree_lt (r : ℕ) : (g r).natDegree < r + 2 := by
  have h1 : (g r).natDegree ≤ ∑ i ∈ range (r + 1), (X - C (i : ℤ)).natDegree :=
    natDegree_prod_le (range (r + 1)) (fun i : ℕ => X - C (i : ℤ))
  have h2 : ∑ i ∈ range (r + 1), (X - C (i : ℤ)).natDegree = r + 1 := by
    rw [Finset.sum_congr rfl fun (i : ℕ) _ => natDegree_X_sub_C (R := ℤ) (i : ℤ)]
    simp
  omega

/-- `∑_{s ≤ r+1} αₛ x ^ s = x (x - 1) ⋯ (x - r)` where `αₛ` are the coefficients of `g`. -/
lemma g_eval_sum (r : ℕ) (x : ℤ) :
    ∑ s ∈ range (r + 2), (g r).coeff s * x ^ s = ∏ i ∈ range (r + 1), (x - i) := by
  rw [← g_eval, eval_eq_sum_range' (g_natDegree_lt r)]

lemma g_coeff_zero (r : ℕ) : (g r).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, g_eval]
  exact Finset.prod_eq_zero (Finset.mem_range.2 (Nat.succ_pos r)) (by simp)

lemma prod_range_neg_succ (n : ℕ) : ∏ i ∈ range n, ((0 : ℤ) - (i + 1 : ℕ)) = (-1) ^ n * n ! := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

lemma prod_range_neg_one_sub (n : ℕ) : ∏ i ∈ range n, ((-1 : ℤ) - i) = (-1) ^ n * n ! := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

lemma g_coeff_one (r : ℕ) : (g r).coeff 1 = (-1) ^ r * r ! := by
  have h : g r = X * ∏ i ∈ range r, (X - C ((i + 1 : ℕ) : ℤ)) := by
    rw [g, Finset.prod_range_succ']
    simp [mul_comm]
  rw [h, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_zero_eq_eval_zero, eval_prod]
  simpa using prod_range_neg_succ r

/-- **Step 2.** The combination `∑ₛ αₛ G(tₛ)` of a scheme of degree `≤ r` vanishes. -/
lemma scheme_combination {R B r : ℕ} {G : ArithmeticFunction ℤ} (hG : IsScheme R B r G)
    (S : ℕ → Finset ℕ) (hS : ∀ s, (S s).card = s ∧ GoodPrimes R B (S s)) :
    ∑ s ∈ range (r + 2), (g r).coeff s * G (∏ q ∈ S s, q) = 0 := by
  obtain ⟨k, Cc, ℓ, hℓ, hval⟩ := scheme_apply hG
  have h1 : ∀ s, G (∏ q ∈ S s, q) = ∑ i, Cc i * (ℓ i : ℤ) ^ s := fun s => by
    rw [hval _ (hS s).2, (hS s).1]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h2 : ∑ s ∈ range (r + 2), (g r).coeff s * (Cc i * (ℓ i : ℤ) ^ s)
      = Cc i * ∑ s ∈ range (r + 2), (g r).coeff s * (ℓ i : ℤ) ^ s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h2, g_eval_sum]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := ℓ i) ?_ (by simp))
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (hℓ i))

/-- **Theorem `thm:kempner`, general form of (b).** Let `G` be a scheme of degree `≤ r`
(parameters `R ≥ 1`, `B`). If `f(t) = a ^ s` for every product `t` of `s` distinct primes, each
`> B` and `≡ 1 (mod R)`, and `G(n) ≡ f(n) (mod m)` for all square-free `n`, then
`m ∣ a (a - 1) ⋯ (a - r)`. -/
theorem kempner_general {R B r : ℕ} (hR : 0 < R) {G : ArithmeticFunction ℤ}
    (hG : IsScheme R B r G) {f : ℕ → ℤ} {a m : ℤ}
    (hf : ∀ S : Finset ℕ, GoodPrimes R B S → f (∏ p ∈ S, p) = a ^ S.card)
    (hGf : ∀ n : ℕ, Squarefree n → G n ≡ f n [ZMOD m]) :
    m ∣ ∏ i ∈ range (r + 1), (a - i) := by
  choose S hS using fun s => exists_goodPrimes hR B s
  have hzero := scheme_combination hG S hS
  have htarget : ∑ s ∈ range (r + 2), (g r).coeff s * f (∏ q ∈ S s, q)
      = ∏ i ∈ range (r + 1), (a - i) := by
    rw [← g_eval_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hf _ (hS s).2, (hS s).1]
  have hdvd : m ∣ ∑ s ∈ range (r + 2),
      (g r).coeff s * (f (∏ q ∈ S s, q) - G (∏ q ∈ S s, q)) :=
    Finset.dvd_sum fun s _ => dvd_mul_of_dvd_right
      (hGf _ (squarefree_prod fun q hq => ((hS s).2 q hq).1)).dvd _
  simp_rw [mul_sub] at hdvd
  rwa [Finset.sum_sub_distrib, htarget, hzero, sub_zero] at hdvd

/-- **Theorem `thm:kempner` (b).** If `f` is integer-valued and multiplicative with `f(p) = a`
for all primes `p`, and `G(n) ≡ f(n) (mod m)` for all square-free `n`, then
`m ∣ a (a - 1) ⋯ (a - r)`. -/
theorem kempner_b {R B r : ℕ} (hR : 0 < R) {G : ArithmeticFunction ℤ}
    (hG : IsScheme R B r G) {f : ArithmeticFunction ℤ} (hfm : f.IsMultiplicative) {a m : ℤ}
    (hfp : ∀ p : ℕ, p.Prime → f p = a)
    (hGf : ∀ n : ℕ, Squarefree n → G n ≡ f n [ZMOD m]) :
    m ∣ ∏ i ∈ range (r + 1), (a - i) := by
  refine kempner_general hR hG (f := f) (fun S hS => ?_) hGf
  rw [IsMultiplicative.map_prod_of_prime hfm S fun q hq => (hS q hq).1,
    Finset.prod_congr rfl fun q hq => hfp q (hS q hq).1, Finset.prod_const]

/-- **Theorem `thm:kempner` (a).** If `G(n) ≡ μ(n) (mod m)` for all square-free `n`, then
`m ∣ (r + 1)!`. -/
theorem kempner_a {R B r : ℕ} (hR : 0 < R) {G : ArithmeticFunction ℤ}
    (hG : IsScheme R B r G) {m : ℤ}
    (hGμ : ∀ n : ℕ, Squarefree n → G n ≡ moebius n [ZMOD m]) :
    m ∣ ((r + 1)! : ℤ) := by
  have h := kempner_b hR hG isMultiplicative_moebius (a := -1)
    (fun p hp => moebius_apply_prime hp) hGμ
  rw [prod_range_neg_one_sub] at h
  exact ((isUnit_neg_one (α := ℤ)).pow (r + 1)).dvd_mul_left.1 h

lemma one_lt_prod {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (h : S.Nonempty) :
    1 < ∏ q ∈ S, q := by
  obtain ⟨p, hp⟩ := h
  exact lt_of_lt_of_le (hS p hp).one_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (prod_ne_zero' hS)) (Finset.dvd_prod_of_mem _ hp))

lemma prod_prime_iff {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) :
    (∏ q ∈ S, q).Prime ↔ S.card = 1 := by
  constructor
  · intro hpr
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : S = ∅ := Finset.card_eq_zero.1 (by omega)
      subst this
      exact Nat.not_prime_one (by simpa using hpr)
    · obtain ⟨p, hp⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      rw [← Finset.mul_prod_erase S (fun q => q) hp] at hpr
      refine Nat.not_prime_mul (hS p hp).ne_one ?_ hpr
      have := one_lt_prod (fun q hq => hS q (Finset.mem_of_mem_erase hq))
        (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hp]; omega))
      omega
  · intro h
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 h
    simpa using hS p (by simp)

/-- **Theorem `thm:kempner` (c).** If `G(n) ≡ c · 1_prime(n) (mod m')` for all square-free
`n > 1`, then `m' ∣ c · r!`. -/
theorem kempner_c {R B r : ℕ} (hR : 0 < R) {G : ArithmeticFunction ℤ}
    (hG : IsScheme R B r G) {c m' : ℤ}
    (hGc : ∀ n : ℕ, Squarefree n → 1 < n → G n ≡ c * (if n.Prime then 1 else 0) [ZMOD m']) :
    m' ∣ c * (r ! : ℤ) := by
  choose S hS using fun s => exists_goodPrimes hR B s
  have hS' : ∀ s, ∀ q ∈ S s, q.Prime := fun s q hq => ((hS s).2 q hq).1
  have hzero := scheme_combination hG S hS
  have hdvd : m' ∣ ∑ s ∈ range (r + 2),
      (g r).coeff s * (c * (if s = 1 then 1 else 0) - G (∏ q ∈ S s, q)) := by
    refine Finset.dvd_sum fun s _ => ?_
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [g_coeff_zero, zero_mul]; exact dvd_zero _
    · refine dvd_mul_of_dvd_right ?_ _
      have h1 : 1 < ∏ q ∈ S s, q :=
        one_lt_prod (hS' s) (Finset.card_pos.1 (by rw [(hS s).1]; exact hs))
      have h2 := (hGc _ (squarefree_prod (hS' s)) h1).dvd
      simp only [prod_prime_iff (hS' s), (hS s).1] at h2
      exact h2
  simp_rw [mul_sub] at hdvd
  rw [Finset.sum_sub_distrib, hzero, sub_zero] at hdvd
  have h3 : ∑ s ∈ range (r + 2), (g r).coeff s * (c * (if s = 1 then 1 else 0))
      = (g r).coeff 1 * c := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro s _ hs; simp [hs]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  rw [h3, g_coeff_one, mul_assoc, mul_comm _ c] at hdvd
  exact ((isUnit_neg_one (α := ℤ)).pow r).dvd_mul_left.1 hdvd

/-- **Theorem `thm:kempner` (c), second sentence.** If moreover `c` has additive order `m`
modulo `m'`, then `m ∣ r!`. -/
theorem kempner_c_order {R B r : ℕ} (hR : 0 < R) {G : ArithmeticFunction ℤ}
    (hG : IsScheme R B r G) {c : ℤ} {m m' : ℕ} (hord : addOrderOf (c : ZMod m') = m)
    (hGc : ∀ n : ℕ, Squarefree n → 1 < n →
      G n ≡ c * (if n.Prime then 1 else 0) [ZMOD (m' : ℤ)]) :
    m ∣ r ! := by
  have h := kempner_c hR hG hGc
  have h0 : ((c * (r ! : ℤ) : ℤ) : ZMod m') = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  rw [← hord]
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [nsmul_eq_mul]
  push_cast at h0
  rw [mul_comm]
  exact h0

end Stage2

/-! ## Stage 4: the integer identity behind the sufficiency direction

For integers `a` and `r ≥ 0` put `C_d = ∑_{j=d}^{r} (-1)^{j-d} C(j,d) C(a,j)` (`C(a,j)` is the
generalized binomial `Ring.choose a j`). Then for every `s ≥ 0`,
`a(a-1)⋯(a-r) ∣ a ^ s - ∑_{d=0}^{r} C_d d ^ s` (with `0 ^ 0 = 1`). Proof: `a ^ s = ∑_j S(s,j) (a)_j`
(Stirling numbers of the second kind, falling factorials), `∑_d (-1)^{j-d} C(j,d) d ^ s = j! S(s,j)`,
and `(a)_{r+1} ∣ (a)_j` for `j > r`. -/

section Stage4

/-- `a ^ s = ∑_{j ≤ s} S(s, j) · (a)_j` for every integer `a`, where `(a)_j = a (a-1) ⋯ (a-j+1)`
is `(descPochhammer ℤ j).eval a`. (Mathlib has the version for natural `a`.) -/
lemma pow_eq_sum_stirlingSecond (a : ℤ) (s : ℕ) :
    a ^ s = ∑ j ∈ range (s + 1), (Nat.stirlingSecond s j : ℤ) * (descPochhammer ℤ j).eval a := by
  set p : ℤ[X] := X ^ s - ∑ j ∈ range (s + 1), C (Nat.stirlingSecond s j : ℤ) * descPochhammer ℤ j
    with hp
  have hroot : ∀ n : ℕ, p.eval (n : ℤ) = 0 := by
    intro n
    simp only [hp, eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C,
      descPochhammer_eval_eq_descFactorial]
    rw [sub_eq_zero]
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n s
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact Set.infinite_of_injective_forall_mem (f := (Nat.cast : ℕ → ℤ)) Nat.cast_injective hroot
  have := congrArg (Polynomial.eval a) hp0
  simp only [hp, eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, eval_zero] at this
  exact sub_eq_zero.1 this

/-- `∑_{d ≤ j} (-1)^{j-d} C(j,d) d ^ s = j! · S(s, j)`. -/
lemma alt_sum_pow_eq (j s : ℕ) :
    ∑ d ∈ range (j + 1), (-1 : ℤ) ^ (j - d) * (j.choose d : ℤ) * (d : ℤ) ^ s
      = (j ! : ℤ) * Nat.stirlingSecond s j := by
  have h1 : ∀ d : ℕ, (d : ℤ) ^ s = ∑ k ∈ range (s + 1),
      (Nat.stirlingSecond s k : ℤ) * ((k ! : ℤ) * (d.choose k : ℤ)) := by
    intro d
    have := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial d s
    simp_rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    exact_mod_cast this
  have h2 : ∀ k : ℕ, ∑ d ∈ range (j + 1), (-1 : ℤ) ^ (j - d) * (j.choose d : ℤ) * (d.choose k : ℤ)
      = if j = k then 1 else 0 := by
    intro k
    rw [← fwdDiff_iter_choose_zero (R := ℤ) k j, fwdDiff_iter_eq_sum_shift]
    simp [smul_eq_mul]
  calc ∑ d ∈ range (j + 1), (-1 : ℤ) ^ (j - d) * (j.choose d : ℤ) * (d : ℤ) ^ s
      = ∑ d ∈ range (j + 1), ∑ k ∈ range (s + 1), (-1 : ℤ) ^ (j - d) * (j.choose d : ℤ) *
          ((Nat.stirlingSecond s k : ℤ) * ((k ! : ℤ) * (d.choose k : ℤ))) := by
        simp_rw [h1, Finset.mul_sum]
    _ = ∑ k ∈ range (s + 1), ((Nat.stirlingSecond s k : ℤ) * (k ! : ℤ)) *
          ∑ d ∈ range (j + 1), (-1 : ℤ) ^ (j - d) * (j.choose d : ℤ) * (d.choose k : ℤ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ = ∑ k ∈ range (s + 1), if j = k then (Nat.stirlingSecond s k : ℤ) * (k ! : ℤ) else 0 := by
        simp_rw [h2]
        simp
    _ = (j ! : ℤ) * Nat.stirlingSecond s j := by
        rw [Finset.sum_ite_eq]
        split_ifs with hj
        · ring
        · rw [Finset.mem_range, not_lt] at hj
          rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]
          simp

lemma choose_mul_factorial (a : ℤ) (j : ℕ) :
    Ring.choose a j * (j ! : ℤ) = (descPochhammer ℤ j).eval a := by
  rw [eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  ring

/-- The coefficient `C_d = ∑_{j=d}^{r} (-1)^{j-d} C(j,d) C(a,j)`, with the generalized binomial
`C(a,j) = Ring.choose a j = a (a-1) ⋯ (a-j+1) / j!`. -/
def coeffC (a : ℤ) (r d : ℕ) : ℤ :=
  ∑ j ∈ Icc d r, (-1) ^ (j - d) * (j.choose d : ℤ) * Ring.choose a j

/-- **Stage 4 (combinatorial core of the sufficiency direction).** For every integer `a` and all
`r, s ≥ 0`: `a (a-1) ⋯ (a-r) ∣ a ^ s - ∑_{d=0}^{r} C_d d ^ s` (Lean's `0 ^ 0 = 1`). -/
theorem prod_dvd_pow_sub_sum_coeffC (a : ℤ) (r s : ℕ) :
    ∏ i ∈ range (r + 1), (a - i) ∣ a ^ s - ∑ d ∈ range (r + 1), coeffC a r d * (d : ℤ) ^ s := by
  have hswap : ∑ d ∈ range (r + 1), coeffC a r d * (d : ℤ) ^ s
      = ∑ j ∈ range (r + 1), (Nat.stirlingSecond s j : ℤ) * (descPochhammer ℤ j).eval a := by
    calc ∑ d ∈ range (r + 1), coeffC a r d * (d : ℤ) ^ s
        = ∑ d ∈ range (r + 1), ∑ j ∈ Icc d r,
            Ring.choose a j * ((-1 : ℤ) ^ (j - d) * (j.choose d : ℤ) * (d : ℤ) ^ s) := by
          unfold coeffC
          simp_rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j ∈ range (r + 1), ∑ d ∈ range (j + 1),
            Ring.choose a j * ((-1 : ℤ) ^ (j - d) * (j.choose d : ℤ) * (d : ℤ) ^ s) := by
          apply Finset.sum_comm'
          intro d j
          simp only [Finset.mem_range, Finset.mem_Icc]
          omega
      _ = ∑ j ∈ range (r + 1), Ring.choose a j * ((j ! : ℤ) * Nat.stirlingSecond s j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, alt_sum_pow_eq]
      _ = ∑ j ∈ range (r + 1), (Nat.stirlingSecond s j : ℤ) * (descPochhammer ℤ j).eval a := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← choose_mul_factorial]
          ring
  have hfull : a ^ s
      = ∑ j ∈ range (r + 1 + s), (Nat.stirlingSecond s j : ℤ) * (descPochhammer ℤ j).eval a := by
    rw [pow_eq_sum_stirlingSecond]
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]
      simp
  rw [hswap, hfull, Finset.sum_range_add, add_sub_cancel_left]
  refine Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right ?_ _
  rw [← descPochhammer_eval_eq_prod_range, ← descPochhammer_mul (R := ℤ) (r + 1) x, eval_mul]
  exact dvd_mul_right _ _

/-- `φ_d(n) = d ^ ω(n)` if `n` is square-free and `0` otherwise (`ω` = number of distinct prime
factors). -/
def phi (d n : ℕ) : ℤ := if Squarefree n then (d : ℤ) ^ (ω n) else 0

/-- **Stage 4, pointwise statement for `μ`.** For every `n` (in particular every `n ≥ 1`),
`μ(n) ≡ ∑_{d=0}^{r} C_d φ_d(n) (mod (r+1)!)`, with `C_d` taken at `a = -1`. -/
theorem moebius_modEq_sum_phi (r n : ℕ) :
    moebius n ≡ ∑ d ∈ range (r + 1), coeffC (-1) r d * phi d n [ZMOD ((r + 1)! : ℤ)] := by
  unfold phi
  by_cases hn : Squarefree n
  · simp only [hn, ite_true]
    have h0 : n ≠ 0 := by
      rintro rfl
      exact not_squarefree_zero hn
    rw [moebius_apply_of_squarefree hn,
      ← (cardDistinctFactors_eq_cardFactors_iff_squarefree h0).2 hn]
    have h := prod_dvd_pow_sub_sum_coeffC (-1) r (ω n)
    rw [prod_range_neg_one_sub] at h
    have h' := ((isUnit_neg_one (α := ℤ)).pow (r + 1)).mul_left_dvd.1 h
    exact Int.modEq_iff_dvd.2 (dvd_sub_comm.1 h')
  · simp [hn, moebius_eq_zero_of_not_squarefree hn]

end Stage4

end Mathathon.Kempner
