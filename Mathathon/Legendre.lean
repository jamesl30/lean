import Mathlib
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Mathathon.Legendre

/-- indicator of `d ≠ 0` and all prime factors of `d` satisfy `Q` -/
def pfInd (Q : ℕ → Prop) [DecidablePred Q] : ArithmeticFunction ℤ :=
  ⟨fun d => if d ≠ 0 ∧ ∀ p ∈ d.primeFactors, Q p then 1 else 0, by simp⟩

lemma pfInd_apply (Q : ℕ → Prop) [DecidablePred Q] (d : ℕ) :
    pfInd Q d = if d ≠ 0 ∧ ∀ p ∈ d.primeFactors, Q p then 1 else 0 := rfl

lemma pfInd_mult (Q : ℕ → Prop) [DecidablePred Q] : IsMultiplicative (pfInd Q) := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [pfInd_apply], ?_⟩
  intro m n hm hn _
  rw [pfInd_apply, pfInd_apply, pfInd_apply, Nat.primeFactors_mul hm hn]
  simp only [Finset.forall_mem_union]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  split_ifs <;> simp_all

lemma smooth_mu_zeta (z : ℕ) :
    (pmul μ (pfInd (· ≤ z))) * (ζ : ArithmeticFunction ℤ) = pfInd (z < ·) := by
  have hG := (isMultiplicative_moebius.pmul (pfInd_mult (· ≤ z))).mul
    (isMultiplicative_zeta.natCast (R := ℤ))
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hG _ (pfInd_mult _)]
  intro p i hp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero, hG.map_one, (pfInd_mult _).map_one]
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sum_range_succ']
  simp [pmul_apply, moebius_apply_prime_pow hp, pfInd_apply, hp.ne_zero,
    Nat.primeFactors_prime_pow hi.ne' hp]
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (fun h => absurd (mem_range.2 hi) h)]
  simp only [zero_add, pow_one, hp.primeFactors, Finset.mem_singleton, forall_eq,
    hp.ne_zero, not_false_eq_true, true_and, ite_true]
  split_ifs <;> omega

lemma smooth_moebius_sum (z n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ z), (μ d : ℤ)
      = if ∀ p ∈ n.primeFactors, z < p then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) (smooth_mu_zeta z)
  simp only [coe_mul_zeta_apply, pmul_apply, pfInd_apply] at h
  have hn0 : n ≠ 0 := by omega
  simp only [ne_eq, hn0, not_false_eq_true, true_and] at h
  rw [← h, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  by_cases hq : ∀ p ∈ d.primeFactors, p ≤ z
  · rw [if_pos hq, if_pos ⟨hd0, hq⟩]; simp
  · rw [if_neg hq, if_neg (fun h' => hq h'.2)]; simp

theorem legendre_convolution (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ Nat.sqrt N), (μ d : ℤ)
      = (Nat.primeCounting N : ℤ) - (Nat.primeCounting (Nat.sqrt N) : ℤ) + 1 := by
  rw [Finset.sum_congr rfl (fun n hn => smooth_moebius_sum _ n (mem_Icc.1 hn).1), Finset.sum_boole]
  set z := Nat.sqrt N with hz
  have hzN : z ≤ N := Nat.sqrt_le_self N
  have hset : (Icc 1 N).filter (fun n => ∀ p ∈ n.primeFactors, z < p)
      = insert 1 ((Ioc z N).filter Nat.Prime) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_insert, mem_Ioc]
    constructor
    · rintro ⟨⟨h1n, hnN⟩, hP⟩
      by_cases hn1 : n = 1
      · exact Or.inl hn1
      right
      by_cases hp : n.Prime
      · exact ⟨⟨hP n (by simp [hp.primeFactors]), hnN⟩, hp⟩
      · exfalso
        have hsq := Nat.minFac_sq_le_self (by omega) hp
        have hle : n.minFac ≤ z := Nat.le_sqrt'.2 (le_trans hsq hnN)
        have hmem : n.minFac ∈ n.primeFactors :=
          Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn1, Nat.minFac_dvd n, by omega⟩
        have := hP _ hmem
        omega
    · rintro (rfl | ⟨⟨hzn, hnN⟩, hp⟩)
      · simp; omega
      · refine ⟨⟨hp.one_lt.le, hnN⟩, ?_⟩
        intro q hq
        rw [hp.primeFactors, Finset.mem_singleton] at hq
        omega
  have h1 : 1 ∉ (Ioc z N).filter Nat.Prime := by simp [Nat.not_prime_one]
  rw [hset, Finset.card_insert_of_notMem h1]
  have hpc : ∀ m, Nat.primeCounting m = ((range (m + 1)).filter Nat.Prime).card := by
    intro m
    rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow]
  have hsplit : (range (N + 1)).filter Nat.Prime
      = (range (z + 1)).filter Nat.Prime ∪ (Ioc z N).filter Nat.Prime := by
    rw [← Finset.filter_union]
    congr 1
    ext m; simp only [mem_range, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint ((range (z + 1)).filter Nat.Prime) ((Ioc z N).filter Nat.Prime) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [mem_range, mem_Ioc] at h1 h2
    omega
  rw [hpc N, hpc z, hsplit, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

end Mathathon.Legendre
