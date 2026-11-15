import Mathlib
import Zeta3.TableU
import Zeta3.Zeta2Rec

/-!
# (DAVID) and (DAVID-2): the integer halves of O. David's ζ(3) and ζ(2) matrix fields (§11.5, §11.6)

Part 1 (ζ(3), report §11.5) is described here; Part 2 (ζ(2), §11.6) has its own header further down.

Report: `zeta3/report/report.tex`, §11.5, paragraph "(DAVID) The table is David's, for all n, m".

Definitions (over ℚ, `Matrix (Fin 2) (Fin 2) ℚ`, rows listed in order):
* `davidA x y = x³ + (x+1)³ + 2y(y−1)(2x+1)`;
* `davidMX x y = !![0, 1; −(x+1)⁶, davidA x y]`, `davidMY k = !![k³, 1; 0, k³]`;
* `davidPi n y = M_Y(1) ⋯ M_Y(y−1) · M_X(0,y) M_X(1,y) ⋯ M_X(n−1,y)` (left to right), built as
  `List.prod` of `List.map` over `List.range` (an empty product is the identity matrix);
* `davidQ n y = davidPi n y 1 1` (second row, second column, 0-indexed), `davidP n y = davidPi n y 0 1`.

Claimed theorems:
* `davidPi_succ`: `Π(n+1,y) = Π(n,y) · M_X(n,y)` (the product is what the text says).
* `david_col_rec`: for every row `i` (so for both `P` and `Q`) and `n ≥ 1`, the second column satisfies
  `g(n+1) = a(n,y)·g(n) − n⁶·g(n−1)` — derived from the matrix product, not assumed.
* `davidPiY_eq`: `M_Y(1)⋯M_Y(m) = !![(m!)³, (m!)³·H_m^{(3)}; 0, (m!)³]` with `H_m^{(3)} = Σ_{k=1}^m 1/k³`
  (the matrix `A` of the text).
* `tableU_zero_left_q`, `tableU_one_left_q`: `U(0,m) = 1`, `U(1,m) = 1 + 2m(m+1)`.
* `davidQ_zero`, `davidQ_one`: `Q(0,m+1) = (m!)³`, `Q(1,m+1) = (m!)³(1 + 2m(m+1))`.
* `david_Q`: **for all n, m: `Q(n,m+1) = (n!·m!)³ · U(n,m)`**.

Differences from the text (nothing else is changed):
* Only the `Q` entry is identified with the table. The `P` entry (`P(n,m+1) = (n! m!)³ V(n,m)`) is not
  formalised: `V` and the ζ(3)-linear forms `Z` are not in Lean. What is proved about `P` is only what
  the matrix product gives: its recursion (`david_col_rec` at `i = 0`) and its start
  `P(0,m+1) = (m!)³ H_m^{(3)}` (`davidPiY_eq`, `davidP_zero`).
* The matrices are taken over ℚ with natural-number arguments `x, y, k` (cast to ℚ); David's field is
  stated for the integer points used in the text, which is all the text uses.
* The recursion (R) for `U` is `Zeta3.tableU_row` (proved there by a telescoping certificate, not by
  the partial-fraction argument of the text).
* `n − 1` is natural subtraction with `n ≥ 1`.
-/

set_option autoImplicit false

namespace Zeta3

open Matrix

/-- `a(x,y) = x³ + (x+1)³ + 2y(y−1)(2x+1)`. -/
def davidA (x y : ℚ) : ℚ := x ^ 3 + (x + 1) ^ 3 + 2 * y * (y - 1) * (2 * x + 1)

/-- `M_X(x,y) = !![0, 1; −(x+1)⁶, a(x,y)]`. -/
def davidMX (x y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 1; -((x : ℚ) + 1) ^ 6, davidA x y]

/-- `M_Y(0,k) = !![k³, 1; 0, k³]`. -/
def davidMY (k : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(k : ℚ) ^ 3, 1; 0, (k : ℚ) ^ 3]

/-- `M_Y(0,1) ⋯ M_Y(0,y−1)` (identity for `y ≤ 1`). -/
def davidPiY (y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((List.range (y - 1)).map (fun k => davidMY (k + 1))).prod

/-- `M_X(0,y) M_X(1,y) ⋯ M_X(n−1,y)` (identity for `n = 0`). -/
def davidPiX (n y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((List.range n).map (fun x => davidMX x y)).prod

/-- `Π(n,y) = M_Y(0,1)⋯M_Y(0,y−1) · M_X(0,y)⋯M_X(n−1,y)`. -/
def davidPi (n y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := davidPiY y * davidPiX n y

/-- `Q(n,y)`: second row, second column of `Π(n,y)`. -/
def davidQ (n y : ℕ) : ℚ := davidPi n y 1 1

/-- `P(n,y)`: first row, second column of `Π(n,y)`. -/
def davidP (n y : ℕ) : ℚ := davidPi n y 0 1

theorem davidPiX_succ (n y : ℕ) : davidPiX (n + 1) y = davidPiX n y * davidMX n y := by
  simp [davidPiX, List.range_succ, List.prod_append]

/-- One more factor on the right. -/
theorem davidPi_succ (n y : ℕ) : davidPi (n + 1) y = davidPi n y * davidMX n y := by
  rw [davidPi, davidPi, davidPiX_succ, Matrix.mul_assoc]

theorem davidPi_succ_col0 (n y : ℕ) (i : Fin 2) :
    davidPi (n + 1) y i 0 = -((n : ℚ) + 1) ^ 6 * davidPi n y i 1 := by
  rw [davidPi_succ]
  simp [Matrix.mul_apply, Fin.sum_univ_two, davidMX]
  ring

theorem davidPi_succ_col1 (n y : ℕ) (i : Fin 2) :
    davidPi (n + 1) y i 1 = davidPi n y i 0 + davidA n y * davidPi n y i 1 := by
  rw [davidPi_succ]
  simp [Matrix.mul_apply, Fin.sum_univ_two, davidMX]
  ring

/-- The second columns `g_n` (both entries, row `i`) satisfy `g(n+1) = a(n,y) g(n) − n⁶ g(n−1)`,
`n ≥ 1`, as a consequence of the matrix product. -/
theorem david_col_rec (n y : ℕ) (hn : 1 ≤ n) (i : Fin 2) :
    davidPi (n + 1) y i 1 = davidA n y * davidPi n y i 1 - (n : ℚ) ^ 6 * davidPi (n - 1) y i 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  rw [davidPi_succ_col1, davidPi_succ_col0, Nat.add_sub_cancel]
  push_cast
  ring

/-- The `Q` entry: `Q(n+1,y) = a(n,y) Q(n,y) − n⁶ Q(n−1,y)` for `n ≥ 1`. -/
theorem davidQ_rec (n y : ℕ) (hn : 1 ≤ n) :
    davidQ (n + 1) y = davidA n y * davidQ n y - (n : ℚ) ^ 6 * davidQ (n - 1) y :=
  david_col_rec n y hn 1

/-- The product of the `M_Y`: `A = (m!)³ · !![1, H_m^{(3)}; 0, 1]`. -/
theorem davidPiY_eq (m : ℕ) :
    davidPiY (m + 1) = !![(m.factorial : ℚ) ^ 3,
        (m.factorial : ℚ) ^ 3 * ∑ k ∈ Finset.range m, 1 / ((k : ℚ) + 1) ^ 3;
        0, (m.factorial : ℚ) ^ 3] := by
  induction m with
  | zero => simp [davidPiY, Matrix.one_fin_two]
  | succ m ih =>
    have h : davidPiY (m + 1 + 1) = davidPiY (m + 1) * davidMY (m + 1) := by
      simp [davidPiY, List.range_succ, List.prod_append]
    rw [h, ih]
    have hk : ((m : ℚ) + 1) ^ 3 ≠ 0 := by positivity
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, davidMY, Nat.factorial_succ,
        Finset.sum_range_succ] <;> field_simp <;> ring

theorem davidQ_zero (m : ℕ) : davidQ 0 (m + 1) = (m.factorial : ℚ) ^ 3 := by
  simp [davidQ, davidPi, davidPiX, davidPiY_eq]

theorem davidP_zero (m : ℕ) :
    davidP 0 (m + 1) = (m.factorial : ℚ) ^ 3 * ∑ k ∈ Finset.range m, 1 / ((k : ℚ) + 1) ^ 3 := by
  simp [davidP, davidPi, davidPiX, davidPiY_eq]

theorem davidQ_one (m : ℕ) :
    davidQ 1 (m + 1) = (m.factorial : ℚ) ^ 3 * (1 + 2 * (m : ℚ) * ((m : ℚ) + 1)) := by
  unfold davidQ
  rw [davidPi_succ_col1]
  simp [davidPi, davidPiX, davidPiY_eq, davidA]
  ring

theorem tableU_zero_left_q (m : ℕ) : tableU 0 m = 1 := by
  simp [tableU, aCoeff]

theorem tableU_one_left_q (m : ℕ) : (tableU 1 m : ℚ) = 1 + 2 * (m : ℚ) * ((m : ℚ) + 1) := by
  rw [tableU_cast_eq 1 m 2 (by omega)]
  simp [Finset.sum_range_succ, aCoeff]
  ring

/-- **(DAVID), the `Q` entry**: for all `n, m`, `Q(n,m+1) = (n!·m!)³ · U(n,m)`. -/
theorem david_Q (n m : ℕ) :
    davidQ n (m + 1) = ((n.factorial : ℚ) * (m.factorial : ℚ)) ^ 3 * (tableU n m : ℚ) := by
  have key : ∀ n : ℕ,
      davidQ n (m + 1) = ((n.factorial : ℚ) * (m.factorial : ℚ)) ^ 3 * (tableU n m : ℚ) ∧
      davidQ (n + 1) (m + 1)
        = (((n + 1).factorial : ℚ) * (m.factorial : ℚ)) ^ 3 * (tableU (n + 1) m : ℚ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [davidQ_zero, tableU_zero_left_q]; simp
      · rw [davidQ_one, tableU_one_left_q]; simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨h0, h1⟩ := ih
      have hr := davidQ_rec (n + 1) (m + 1) (by omega)
      have hrow := tableU_row (n + 1) m (by omega)
      rw [Nat.add_sub_cancel] at hr hrow
      rw [hr, h0, h1]
      rw [show n + 1 + 1 = n + 2 from rfl] at hrow ⊢
      rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
      unfold davidA
      push_cast at hrow ⊢
      linear_combination
        (-((n : ℚ) + 1) ^ 3 * (n.factorial : ℚ) ^ 3 * (m.factorial : ℚ) ^ 3) * hrow
  exact (key n).1

-- CLAIMED: Zeta3.davidPi_succ, Zeta3.david_col_rec, Zeta3.davidQ_rec, Zeta3.davidPiY_eq
-- CLAIMED: Zeta3.davidQ_zero, Zeta3.davidP_zero, Zeta3.davidQ_one
-- CLAIMED: Zeta3.david_Q

/-!
## Part 2. (DAVID-2): the integers U₂ are the integer half of O. David's ζ(2) matrix field (report §11.6)

Report: `zeta3/report/report.tex`, §11.6, paragraph "(DAVID-2) The table is David's ζ(2) field".

All names in this part end in `2`.

Definitions (over ℚ, `Matrix (Fin 2) (Fin 2) ℚ`, rows listed in order):
* `davidA2 x y = (2x+1)(2y−1)`;
* `davidMX2 x y = !![0, 1; (x+1)⁴, davidA2 x y]`, `davidMY2 k = !![2k², 1; 0, 2k²]`;
* `davidPi2 n y = M_Y(1) ⋯ M_Y(y−1) · M_X(0,y) M_X(1,y) ⋯ M_X(n−1,y)` (left to right), built as
  `List.prod` of `List.map` over `List.range` (an empty product is the identity matrix);
* `davidQ2 n y = davidPi2 n y 1 1` (second row, second column, 0-indexed),
  `davidP2 n y = davidPi2 n y 0 1`.

Claimed theorems:
* `davidPi2_succ`: `Π(n+1,y) = Π(n,y) · M_X(n,y)`.
* `david2_col_rec`: for every row `i` (so for both `P` and `Q`) and `n ≥ 1`, the second column satisfies
  `g(n+1) = (2n+1)(2y−1)·g(n) + n⁴·g(n−1)` — derived from the matrix product.
* `davidPiY2_eq`: `M_Y(1)⋯M_Y(m) = ω_m · !![1, ½H_m^{(2)}; 0, 1]`, `ω_m = (m!)²2^m`,
  `H_m^{(2)} = Σ_{k=1}^m 1/k²` (written as `ω_m · Σ_{k=1}^m 1/(2k²)`).
* `U2_zero_left`, `U2_one_left`: `U₂(0,m) = 1`, `U₂(1,m) = 2m+1`.
* `davidQ2_zero`, `davidQ2_one`: `Q(0,m+1) = ω_m`, `Q(1,m+1) = ω_m(2m+1)`.
* `david_Q_zeta2`: **for all n, m: `Q(n,m+1) = (n!)²(m!)²2^m · U₂(n,m)`**.

Differences from the text (nothing else is changed):
* Only the `Q` entry is identified with `U₂`. The `P` entry (`P(n,m+1) = (n!)²ω_m·½V₂(n,m)`) is not
  formalised: `V₂` and the ζ(2)-linear forms `Z₂` are not in Lean. What is proved about `P` is its
  recursion (`david2_col_rec` at `i = 0`) and its start `P(0,m+1) = ω_m·½H_m^{(2)}` (`davidP2_zero`).
* The matrices are those the text gives (its derivation from David's Example 19 and Theorem 23 is not
  formalised); they are taken over ℚ with natural-number arguments, cast to ℚ.
* The row relation for `U₂` is `Zeta3.U2_row` (proved there by a telescoping certificate, not by the
  partial-fraction argument of the text). `n − 1` is natural subtraction with `n ≥ 1`.
-/

/-- `(2x+1)(2y−1)`. -/
def davidA2 (x y : ℚ) : ℚ := (2 * x + 1) * (2 * y - 1)

/-- `M_X(x,y) = !![0, 1; (x+1)⁴, (2x+1)(2y−1)]`. -/
def davidMX2 (x y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 1; ((x : ℚ) + 1) ^ 4, davidA2 x y]

/-- `M_Y(0,k) = !![2k², 1; 0, 2k²]`. -/
def davidMY2 (k : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2 * (k : ℚ) ^ 2, 1; 0, 2 * (k : ℚ) ^ 2]

/-- `M_Y(0,1) ⋯ M_Y(0,y−1)` (identity for `y ≤ 1`). -/
def davidPiY2 (y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((List.range (y - 1)).map (fun k => davidMY2 (k + 1))).prod

/-- `M_X(0,y) M_X(1,y) ⋯ M_X(n−1,y)` (identity for `n = 0`). -/
def davidPiX2 (n y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  ((List.range n).map (fun x => davidMX2 x y)).prod

/-- `Π(n,y) = M_Y(0,1)⋯M_Y(0,y−1) · M_X(0,y)⋯M_X(n−1,y)`. -/
def davidPi2 (n y : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := davidPiY2 y * davidPiX2 n y

/-- `Q(n,y)`: second row, second column of `Π(n,y)`. -/
def davidQ2 (n y : ℕ) : ℚ := davidPi2 n y 1 1

/-- `P(n,y)`: first row, second column of `Π(n,y)`. -/
def davidP2 (n y : ℕ) : ℚ := davidPi2 n y 0 1

theorem davidPiX2_succ (n y : ℕ) : davidPiX2 (n + 1) y = davidPiX2 n y * davidMX2 n y := by
  simp [davidPiX2, List.range_succ, List.prod_append]

/-- One more factor on the right. -/
theorem davidPi2_succ (n y : ℕ) : davidPi2 (n + 1) y = davidPi2 n y * davidMX2 n y := by
  rw [davidPi2, davidPi2, davidPiX2_succ, Matrix.mul_assoc]

theorem davidPi2_succ_col0 (n y : ℕ) (i : Fin 2) :
    davidPi2 (n + 1) y i 0 = ((n : ℚ) + 1) ^ 4 * davidPi2 n y i 1 := by
  rw [davidPi2_succ]
  simp [Matrix.mul_apply, Fin.sum_univ_two, davidMX2]
  ring

theorem davidPi2_succ_col1 (n y : ℕ) (i : Fin 2) :
    davidPi2 (n + 1) y i 1 = davidPi2 n y i 0 + davidA2 n y * davidPi2 n y i 1 := by
  rw [davidPi2_succ]
  simp [Matrix.mul_apply, Fin.sum_univ_two, davidMX2]
  ring

/-- The second columns (row `i`) satisfy `g(n+1) = (2n+1)(2y−1) g(n) + n⁴ g(n−1)`, `n ≥ 1`. -/
theorem david2_col_rec (n y : ℕ) (hn : 1 ≤ n) (i : Fin 2) :
    davidPi2 (n + 1) y i 1
      = davidA2 n y * davidPi2 n y i 1 + (n : ℚ) ^ 4 * davidPi2 (n - 1) y i 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  rw [davidPi2_succ_col1, davidPi2_succ_col0, Nat.add_sub_cancel]
  push_cast
  ring

/-- The `Q` entry: `Q(n+1,y) = (2n+1)(2y−1) Q(n,y) + n⁴ Q(n−1,y)` for `n ≥ 1`. -/
theorem davidQ2_rec (n y : ℕ) (hn : 1 ≤ n) :
    davidQ2 (n + 1) y = davidA2 n y * davidQ2 n y + (n : ℚ) ^ 4 * davidQ2 (n - 1) y :=
  david2_col_rec n y hn 1

/-- The product of the `M_Y`: `A = ω_m · !![1, ½H_m^{(2)}; 0, 1]`, `ω_m = (m!)²2^m`. -/
theorem davidPiY2_eq (m : ℕ) :
    davidPiY2 (m + 1) = !![(m.factorial : ℚ) ^ 2 * 2 ^ m,
        (m.factorial : ℚ) ^ 2 * 2 ^ m * ∑ k ∈ Finset.range m, 1 / (2 * ((k : ℚ) + 1) ^ 2);
        0, (m.factorial : ℚ) ^ 2 * 2 ^ m] := by
  induction m with
  | zero => simp [davidPiY2, Matrix.one_fin_two]
  | succ m ih =>
    have h : davidPiY2 (m + 1 + 1) = davidPiY2 (m + 1) * davidMY2 (m + 1) := by
      simp [davidPiY2, List.range_succ, List.prod_append]
    rw [h, ih]
    have hk : ((m : ℚ) + 1) ^ 2 ≠ 0 := by positivity
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, davidMY2, Nat.factorial_succ,
        Finset.sum_range_succ, pow_succ] <;> field_simp <;> ring

theorem davidQ2_zero (m : ℕ) : davidQ2 0 (m + 1) = (m.factorial : ℚ) ^ 2 * 2 ^ m := by
  simp [davidQ2, davidPi2, davidPiX2, davidPiY2_eq]

theorem davidP2_zero (m : ℕ) :
    davidP2 0 (m + 1)
      = (m.factorial : ℚ) ^ 2 * 2 ^ m * ∑ k ∈ Finset.range m, 1 / (2 * ((k : ℚ) + 1) ^ 2) := by
  simp [davidP2, davidPi2, davidPiX2, davidPiY2_eq]

theorem davidQ2_one (m : ℕ) :
    davidQ2 1 (m + 1) = (m.factorial : ℚ) ^ 2 * 2 ^ m * (2 * (m : ℚ) + 1) := by
  unfold davidQ2
  rw [davidPi2_succ_col1]
  simp [davidPi2, davidPiX2, davidPiY2_eq, davidA2]
  ring

theorem U2_zero_left (m : ℕ) : U2 0 m = 1 := by
  simp [U2, aCoeff]

theorem U2_one_left (m : ℕ) : (U2 1 m : ℚ) = 2 * (m : ℚ) + 1 := by
  rw [U2_cast_eq 1 m 2 (by omega)]
  simp [Finset.sum_range_succ, aCoeff]
  ring

/-- **(DAVID-2), the `Q` entry**: for all `n, m`, `Q(n,m+1) = (n!)²(m!)²2^m · U₂(n,m)`. -/
theorem david_Q_zeta2 (n m : ℕ) :
    davidQ2 n (m + 1)
      = (n.factorial : ℚ) ^ 2 * (m.factorial : ℚ) ^ 2 * 2 ^ m * (U2 n m : ℚ) := by
  have key : ∀ n : ℕ,
      davidQ2 n (m + 1)
          = (n.factorial : ℚ) ^ 2 * (m.factorial : ℚ) ^ 2 * 2 ^ m * (U2 n m : ℚ) ∧
      davidQ2 (n + 1) (m + 1)
          = ((n + 1).factorial : ℚ) ^ 2 * (m.factorial : ℚ) ^ 2 * 2 ^ m * (U2 (n + 1) m : ℚ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [davidQ2_zero, U2_zero_left]; simp
      · rw [davidQ2_one, U2_one_left]; simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨h0, h1⟩ := ih
      have hr := davidQ2_rec (n + 1) (m + 1) (by omega)
      have hrow := U2_row (n + 1) m (by omega)
      rw [Nat.add_sub_cancel] at hr hrow
      rw [hr, h0, h1]
      rw [show n + 1 + 1 = n + 2 from rfl] at hrow ⊢
      rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
      unfold davidA2
      push_cast at hrow ⊢
      linear_combination
        (-((n : ℚ) + 1) ^ 2 * (n.factorial : ℚ) ^ 2 * (m.factorial : ℚ) ^ 2 * 2 ^ m) * hrow
  exact (key n).1

-- CLAIMED: Zeta3.davidPi2_succ, Zeta3.david2_col_rec, Zeta3.davidQ2_rec, Zeta3.davidPiY2_eq
-- CLAIMED: Zeta3.davidQ2_zero, Zeta3.davidP2_zero, Zeta3.davidQ2_one
-- CLAIMED: Zeta3.U2_zero_left, Zeta3.U2_one_left, Zeta3.david_Q_zeta2

end Zeta3
