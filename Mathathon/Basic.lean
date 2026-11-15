import Mathlib

/-! Smoke test for the pinned toolchain (Lean v4.35.0, Mathlib v4.35.0). -/

namespace Mathathon

theorem smoke (n : ℕ) : n + 0 = n := by simp

end Mathathon
