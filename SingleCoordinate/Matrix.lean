import SingleCoordinate.Specialize
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! The generic determinant and its top-left cofactor have no nonunit common divisor.
A divisor of the cofactor is independent of the first row. Substituting each unit row
in the determinant makes the same divisor divide every cofactor of that row.
The cofactor omitting column j is independent of column j. -/

namespace SingleCoordinate
open MvPolynomial

abbrev MatrixVars (d : ℕ) := Fin d × Fin d
abbrev MatrixPoly (K : Type*) [Field K] (d : ℕ) := MvPolynomial (MatrixVars d) K
noncomputable abbrev generic (K : Type*) [Field K] (d : ℕ) :=
  Matrix.mvPolynomialX (Fin d) (Fin d) K

noncomputable def detPoly (K : Type*) [Field K] (d : ℕ) : MatrixPoly K d :=
  (generic K d).det

noncomputable def cofactor (K : Type*) [Field K] {n : ℕ} (j : Fin (n+1)) :
    MatrixPoly K (n+1) := (generic K (n+1)).adjugate j 0

section
variable {K : Type*} [Field K] {n : ℕ}

private def minorIndex (j : Fin (n+1)) (v : MatrixVars n) : MatrixVars (n+1) :=
  (v.1.succ, j.succAbove v.2)

private theorem minorIndex_inj (j : Fin (n+1)) : Function.Injective (minorIndex j) := by
  rintro ⟨i,k⟩ ⟨i',k'⟩ h
  exact Prod.ext (Fin.succ_injective _ (congrArg Prod.fst h))
    (Fin.succAbove_right_injective (congrArg Prod.snd h))

private theorem cofactor_expansion (j : Fin (n+1)) :
    cofactor K j = (-1) ^ (j : ℕ) * rename (minorIndex j) (detPoly K n) := by
  classical
  rw [cofactor, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, zero_add]
  congr 1
  unfold detPoly
  rw [AlgHom.map_det]
  congr 1
  ext i k
  simp [minorIndex, Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]

theorem cofactor_ne_zero (j : Fin (n+1)) : cofactor K j ≠ 0 := by
  have nd : detPoly K n ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin n) K
  rw [cofactor_expansion]
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  intro e
  exact nd (rename_injective _ (minorIndex_inj j) (e.trans (map_zero _).symm))

/-- A substitution fixing the variables of this minor fixes its cofactor along the line. -/
private theorem line_cofactor (j : Fin (n+1)) (v : MatrixVars (n+1) → MatrixPoly K (n+1))
    (fix : ∀ u, v (minorIndex j u) = X (minorIndex j u)) :
    Subst.line v (cofactor K j) = Polynomial.C (cofactor K j) := by
  rw [cofactor_expansion, map_mul, map_mul, map_pow, map_neg, map_one, map_pow, map_neg, map_one]
  congr 1
  let r := (rename (R := K) (minorIndex j)).toRingHom
  have h : (Subst.line v).comp r = Polynomial.C.comp r := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [r, Subst.line]
    · intro i; simpa [r] using Subst.line_X_fixed v (minorIndex j i) (fix i)
  exact DFunLike.congr_fun h (detPoly K n)

private noncomputable def rowValues (j : Fin (n+1)) (u : MatrixVars (n+1)) :
    MatrixPoly K (n+1) :=
  if u.1 = 0 then (Pi.single j 1 : Fin (n+1) → MatrixPoly K (n+1)) u.2 else X u

private theorem row_det (j : Fin (n+1)) :
    Subst.atValues (rowValues (K := K) j) (detPoly K (n+1)) = cofactor K j := by
  classical
  rw [detPoly, RingHom.map_det, cofactor, Matrix.adjugate_apply]
  congr 1
  ext i k
  by_cases hi : i = 0
  · subst i; simp [rowValues, RingHom.mapMatrix_apply, Matrix.map_apply]
  · simp [rowValues, hi, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne]

theorem det_cofactor_relPrime : IsRelPrime (detPoly K (n+1)) (cofactor K (0 : Fin (n+1))) := by
  classical
  intro p pd pc
  have cols (j : Fin (n+1)) : p ∣ cofactor K j := by
    have pf := Subst.fixedFactor pc (cofactor_ne_zero _) (rowValues j)
      (line_cofactor _ _ (fun u => by simp [rowValues, minorIndex]))
    have hh := map_dvd (Subst.atValues (rowValues j)) pd
    rwa [pf, row_det] at hh
  have fixedCols (j : Fin (n+1)) : Subst.eraseGroups Prod.snd {j} p = p := by
    apply Subst.fixedFactor (cols j) (cofactor_ne_zero _)
    apply line_cofactor
    intro u
    simp [minorIndex, Fin.succAbove_ne]
  have cp := Subst.constant_of_erase Prod.snd p fixedCols
  have pne : p ≠ 0 := by
    intro hp
    exact cofactor_ne_zero (K := K) 0 (zero_dvd_iff.mp (hp ▸ pc))
  have cne : constantCoeff p ≠ 0 := by
    intro hc
    exact pne (cp.trans (by rw [hc, map_zero]))
  exact cp ▸ (isUnit_iff_ne_zero.mpr cne).map (C : K →+* MatrixPoly K (n+1))

end
end SingleCoordinate
