import SingleCoordinate.Numerical
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! An explicit real-valued form of the lower bound. -/

namespace SingleCoordinate

private theorem ninths_to_quarters {d s : ℕ} (dim : 8 ≤ d)
    (h : (d/4)^9 ≤ (18*s)^4) : (d : ℝ) ^ (9/4 : ℝ) / 2304 ≤ (s : ℝ) := by
  have hd : d ≤ 8*(d/4) := by omega
  have hn : d^9 ≤ (2304*s)^4 := calc
    d^9 ≤ (8*(d/4))^9 := Nat.pow_le_pow_left hd 9
    _ = 8^9 * (d/4)^9 := mul_pow _ _ _
    _ ≤ 8^9 * (18*s)^4 := Nat.mul_le_mul_left _ h
    _ = (8^9 * 18^4) * s^4 := by rw [mul_pow, mul_assoc]
    _ ≤ 2304^4 * s^4 := Nat.mul_le_mul_right _ (by decide)
    _ = (2304*s)^4 := (mul_pow _ _ _).symm
  have hr : (d : ℝ)^(9 : ℕ) ≤ (2304 * (s : ℝ))^(4 : ℕ) := by exact_mod_cast hn
  have he : ((d : ℝ) ^ (9/4 : ℝ)) ^ (4 : ℕ) = (d : ℝ)^(9 : ℕ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d)]
    norm_num
    exact Real.rpow_natCast _ 9
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2304), mul_comm (s : ℝ)]
  exact le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity) (he ▸ hr)

/-- For every dimension d = n+1 ≥ 8, computing just this one coordinate
on every invertible input requires at least d^(9/4)/2304 arithmetic gates. -/
theorem single_coordinate_nine_fourths {K : Type*} [Field K] [Infinite K] {rank : ℕ → ℕ}
    (andrews : AndrewsBound K rank) (matrixRank : MatrixRankBound rank)
    {n s : ℕ} (dim : 8 ≤ n+1) (p : Program RatOp (MatrixInput K (n+1)) s)
    (out : Ref (MatrixInput K (n+1)) s) (correct : SolvesFirst p out) :
    ((n+1 : ℕ) : ℝ) ^ (9/4 : ℝ) / 2304 ≤ (s : ℝ) :=
  ninths_to_quarters dim (concrete_program_lower andrews matrixRank dim p out correct)

end SingleCoordinate
