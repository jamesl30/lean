import Mathlib
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace Mathathon.Rows

lemma d3_apply (m : ℕ) (hm : m ≠ 0) :
    (((ζ * ζ * ζ : ArithmeticFunction ℕ) m : ℕ) : ℂ)
      = ∑ x ∈ m.divisorsAntidiagonal, ∑ _y ∈ x.1.divisorsAntidiagonal, (1 : ℂ) := by
  rw [mul_apply]
  push_cast
  apply sum_congr rfl
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have h1 : x.1 ≠ 0 := fun h => hm (by rw [← hx.1, h, zero_mul])
  have h2 : x.2 ≠ 0 := fun h => hm (by rw [← hx.1, h, mul_zero])
  rw [mul_apply]
  push_cast
  rw [zeta_apply_ne h2, Nat.cast_one, mul_one]
  apply sum_congr rfl
  intro y hy
  rw [Nat.mem_divisorsAntidiagonal] at hy
  have h3 : y.1 ≠ 0 := fun h => h1 (by rw [← hy.1, h, zero_mul])
  have h4 : y.2 ≠ 0 := fun h => h1 (by rw [← hy.1, h, mul_zero])
  rw [zeta_apply_ne h3, zeta_apply_ne h4]; simp

lemma aux (a b c M : ℕ) (h : a * b * c ≤ M) (h0 : a * b * c ≠ 0) :
    1 ≤ a ∧ a ≤ M ∧ 1 ≤ b ∧ b ≤ M ∧ 1 ≤ c ∧ c ≤ M := by
  have hp : 0 < a * b * c := Nat.pos_of_ne_zero h0
  have ha : a ≤ a * b * c := Nat.le_of_dvd hp ⟨b * c, by ring⟩
  have hb : b ≤ a * b * c := Nat.le_of_dvd hp ⟨a * c, by ring⟩
  have hc : c ≤ a * b * c := Nat.le_of_dvd hp ⟨a * b, by ring⟩
  simp only [mul_ne_zero_iff] at h0
  omega

theorem d3_sum_ordered (M : ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 M, (((ζ * ζ * ζ : ArithmeticFunction ℕ) m : ℕ) : ℂ) * F m =
    ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 M,
      if a * b * c ≤ M then F (a * b * c) else 0 := by
  have hL : ∑ m ∈ Finset.Icc 1 M, (((ζ * ζ * ζ : ArithmeticFunction ℕ) m : ℕ) : ℂ) * F m
      = ∑ m ∈ Finset.Icc 1 M, ∑ x ∈ m.divisorsAntidiagonal, ∑ _y ∈ x.1.divisorsAntidiagonal, F m := by
    apply sum_congr rfl
    intro m hm
    rw [d3_apply m (by simp at hm; omega), sum_mul]
    simp
  have hR : (∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 M,
      if a * b * c ≤ M then F (a * b * c) else 0)
      = ∑ t ∈ ((Icc 1 M ×ˢ Icc 1 M) ×ˢ Icc 1 M).filter (fun t => t.1.1 * t.1.2 * t.2 ≤ M),
          F (t.1.1 * t.1.2 * t.2) := by
    rw [sum_filter, sum_product, sum_product]
  rw [hL, hR, Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun t => ((t.2.1, t.2.2), t.1.2.2))
    (fun t => (⟨⟨t.1.1 * t.1.2 * t.2, (t.1.1 * t.1.2, t.2)⟩, (t.1.1, t.1.2)⟩ :
      Σ _ : (Σ _ : ℕ, ℕ × ℕ), ℕ × ℕ))
  · rintro ⟨⟨m, x1, x2⟩, y1, y2⟩ h
    simp only [mem_sigma, mem_Icc,
      Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨⟨⟨_, hmM⟩, hx, hm0⟩, hy, _⟩ := h
    subst hy; subst hx
    have := aux y1 y2 x2 M hmM hm0
    simp only [mem_filter, mem_product, mem_Icc]
    refine ⟨?_, hmM⟩
    omega
  · rintro ⟨⟨a, b⟩, c⟩ h
    simp only [mem_filter, mem_product, mem_Icc] at h
    obtain ⟨h, hM⟩ := h
    have ha1 : 1 ≤ a := by omega
    have hb1 : 1 ≤ b := by omega
    have hc1 : 1 ≤ c := by omega
    have hab : a * b ≠ 0 := mul_ne_zero (by omega) (by omega)
    have habc : a * b * c ≠ 0 := mul_ne_zero hab (by omega)
    simp only [mem_sigma, mem_Icc,
      Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨⟨Nat.pos_of_ne_zero habc, hM⟩, trivial, habc⟩, trivial, hab⟩
  · rintro ⟨⟨m, x1, x2⟩, y1, y2⟩ h
    simp only [mem_sigma, mem_Icc,
      Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨⟨_, hx, _⟩, hy, _⟩ := h
    subst hy; subst hx
    rfl
  · rintro ⟨⟨a, b⟩, c⟩ _
    rfl
  · rintro ⟨⟨m, x1, x2⟩, y1, y2⟩ h
    simp only [mem_sigma, mem_Icc,
      Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨⟨_, hx, _⟩, hy, _⟩ := h
    subst hy; subst hx
    rfl

section Sorted

variable (I : Finset ℕ)

lemma perm_bac (H : ℕ → ℕ → ℕ → ℂ) :
    ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H b a c = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a b c :=
  Finset.sum_comm

lemma perm_acb (H : ℕ → ℕ → ℕ → ℂ) :
    ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a c b = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a b c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma perm_bca (H : ℕ → ℕ → ℕ → ℂ) :
    ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H b c a = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a b c := by
  rw [perm_bac I (fun x y z => H x z y), perm_acb I H]

lemma perm_cab (H : ℕ → ℕ → ℕ → ℂ) :
    ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H c a b = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a b c := by
  rw [perm_acb I (fun x y z => H y x z), perm_bac I H]

lemma perm_cba (H : ℕ → ℕ → ℕ → ℂ) :
    ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H c b a = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a b c := by
  rw [perm_bca I (fun x y z => H y x z), perm_bac I H]

end Sorted

/-- weight of a triple if sorted, else 0 -/
def wt (a b c : ℕ) : ℕ :=
  if a ≤ b ∧ b ≤ c then (if a = b ∧ b = c then 1 else if a = b ∨ b = c then 3 else 6) else 0

lemma wt_sum (a b c : ℕ) :
    wt a b c + wt b a c + wt a c b + wt c b a + wt b c a + wt c a b = 6 := by
  rcases lt_trichotomy a b with h1 | h1 | h1 <;>
  rcases lt_trichotomy b c with h2 | h2 | h2 <;>
  rcases lt_trichotomy a c with h3 | h3 | h3 <;>
  first
    | omega
    | (simp (disch := omega) only [wt, if_pos, if_neg])

theorem sum_sorted_triples (M : ℕ) (G : ℕ → ℕ → ℕ → ℂ)
    (hsw : ∀ a b c, G a b c = G b a c) (hcy : ∀ a b c, G a b c = G b c a) :
    ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 M, G a b c =
    ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc a M, ∑ c ∈ Finset.Icc b M,
      ((if a = b ∧ b = c then 1 else if a = b ∨ b = c then 3 else 6 : ℕ) : ℂ) * G a b c := by
  set I := Finset.Icc 1 M
  set H : ℕ → ℕ → ℕ → ℂ := fun a b c => (wt a b c : ℂ) * G a b c with hH
  have hA : (∑ a ∈ I, ∑ b ∈ Finset.Icc a M, ∑ c ∈ Finset.Icc b M,
      ((if a = b ∧ b = c then 1 else if a = b ∨ b = c then 3 else 6 : ℕ) : ℂ) * G a b c)
      = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a b c := by
    apply Finset.sum_congr rfl
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.1 ha).1
    calc _ = ∑ b ∈ Finset.Icc a M, ∑ c ∈ I, H a b c := by
          apply Finset.sum_congr rfl
          intro b hb
          have hb1 : a ≤ b := (Finset.mem_Icc.1 hb).1
          calc _ = ∑ c ∈ Finset.Icc b M, H a b c := by
                apply Finset.sum_congr rfl
                intro c hc
                have hc1 : b ≤ c := (Finset.mem_Icc.1 hc).1
                show _ = (wt a b c : ℂ) * G a b c
                rw [wt, if_pos (show a ≤ b ∧ b ≤ c from ⟨hb1, hc1⟩)]
            _ = _ := by
                apply Finset.sum_subset
                · intro c hc; simp only [I, Finset.mem_Icc] at hc ⊢; omega
                · intro c hc hc'
                  simp only [I, Finset.mem_Icc] at hc hc'
                  simp only [hH, wt]
                  rw [if_neg (by omega)]; simp
      _ = _ := by
          apply Finset.sum_subset
          · intro b hb; simp only [I, Finset.mem_Icc] at hb ⊢; omega
          · intro b hb hb'
            simp only [I, Finset.mem_Icc] at hb hb'
            apply Finset.sum_eq_zero
            intro c _
            simp only [hH, wt]
            rw [if_neg (by omega)]; simp
  rw [hA]
  have hB : (6 : ℂ) * ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, G a b c
      = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I,
          (H a b c + H b a c + H a c b + H c b a + H b c a + H c a b) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    have e1 : G b a c = G a b c := (hsw a b c).symm
    have e2 : G a c b = G a b c := by rw [hcy a c b, ← hsw b c a, ← hcy a b c]
    have e3 : G c b a = G a b c := by rw [hsw c b a, ← hcy a b c]
    have e4 : G b c a = G a b c := (hcy a b c).symm
    have e5 : G c a b = G a b c := by rw [← hcy b c a, ← hcy a b c]
    simp only [hH, e1, e2, e3, e4, e5]
    have hw := wt_sum a b c
    have hw' : ((wt a b c + wt b a c + wt a c b + wt c b a + wt b c a + wt c a b : ℕ) : ℂ) = 6 := by
      rw [hw]; norm_num
    push_cast at hw'
    rw [← hw']; ring
  have hC : ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I,
          (H a b c + H b a c + H a c b + H c b a + H b c a + H c a b)
      = 6 * ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, H a b c := by
    simp only [Finset.sum_add_distrib]
    rw [perm_bac I H, perm_acb I H, perm_cba I H, perm_bca I H, perm_cab I H]
    ring
  have := hB.trans hC
  exact mul_left_cancel₀ (by norm_num : (6 : ℂ) ≠ 0) this

open scoped ArithmeticFunction.zeta in
theorem rows_decomp (M : ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 M, (((ζ * ζ * ζ : ArithmeticFunction ℕ) m : ℕ) : ℂ) * F m =
    ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc a M, ∑ c ∈ Finset.Icc b M,
      if a * b * c ≤ M then
        ((if a = b ∧ b = c then 1 else if a = b ∨ b = c then 3 else 6 : ℕ) : ℂ) * F (a * b * c)
      else 0 := by
  rw [d3_sum_ordered, sum_sorted_triples M (fun a b c => if a * b * c ≤ M then F (a * b * c) else 0)]
  · simp only [mul_ite, mul_zero]
  · intro a b c; simp only [show b * a * c = a * b * c by ring]
  · intro a b c; simp only [show b * c * a = a * b * c by ring]

end Mathathon.Rows
