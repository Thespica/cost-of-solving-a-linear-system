import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A divisor of a nonzero polynomial fixed along an affine line is fixed at
both endpoints. This avoids importing an irreducibility theorem for the generic determinant. -/

namespace SingleCoordinate
open MvPolynomial

namespace Subst

variable {σ K : Type*} [Field K]
abbrev P (σ K : Type*) [Field K] := MvPolynomial σ K

noncomputable def atValues (v : σ → P σ K) : P σ K →+* P σ K :=
  eval₂Hom C v

noncomputable def line (v : σ → P σ K) : P σ K →+* Polynomial (P σ K) :=
  eval₂Hom (Polynomial.C.comp C) fun i =>
    Polynomial.C (v i) + Polynomial.X * Polynomial.C ((X i : P σ K) - v i)

@[simp] theorem atValues_X (v : σ → P σ K) (i : σ) :
    atValues v (X i) = v i := eval₂Hom_X' _ _ _
@[simp] theorem atValues_C (v : σ → P σ K) (c : K) :
    atValues v (C c) = C c := by simp [atValues]

theorem line_X_fixed (v : σ → P σ K) (i : σ) (h : v i = X i) :
    line v (X i) = Polynomial.C (X i) := by simp [line, h]

private theorem evalLineZero (v : σ → P σ K) (p : P σ K) :
    (line v p).eval 0 = atValues v p := by
  have eqn : (Polynomial.evalRingHom (0 : P σ K)).comp (line v) = atValues v := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [line, atValues]
    · intro i; simp [line, atValues]
  exact DFunLike.congr_fun eqn p

private theorem evalLineOne (v : σ → P σ K) (p : P σ K) :
    (line v p).eval 1 = p := by
  have eqn : (Polynomial.evalRingHom (1 : P σ K)).comp (line v) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun eqn p

theorem fixedFactor {p h : P σ K} (divides : p ∣ h) (hne : h ≠ 0)
    (v : σ → P σ K) (fixed : line v h = Polynomial.C h) : atValues v p = p := by
  have dvdC : line v p ∣ Polynomial.C h := fixed ▸ map_dvd (line v) divides
  have deg := Polynomial.natDegree_le_of_dvd dvdC (Polynomial.C_ne_zero.mpr hne)
  have const := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (by simpa using deg))
  calc
    atValues v p = (line v p).eval 0 := (evalLineZero v p).symm
    _ = (line v p).eval 1 := by rw [const]; simp
    _ = p := evalLineOne v p

noncomputable def eraseGroups {ι : Type*} [DecidableEq ι] (group : σ → ι) (s : Finset ι) :
    P σ K →+* P σ K := atValues fun i => if group i ∈ s then 0 else X i

theorem constant_of_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (group : σ → ι) (p : P σ K) (h : ∀ j, eraseGroups group {j} p = p) :
    p = C (constantCoeff p) := by
  classical
  have allSets (s : Finset ι) : eraseGroups group s p = p := by
    induction s using Finset.induction_on with
    | empty =>
      have he : eraseGroups (K := K) group ∅ = RingHom.id _ := by
        apply MvPolynomial.ringHom_ext <;> intro x <;> simp [eraseGroups]
      rw [he]; rfl
    | @insert a s ha ih =>
      have he : eraseGroups (K := K) group (insert a s) =
          (eraseGroups group s).comp (eraseGroups group {a}) := by
        apply MvPolynomial.ringHom_ext
        · intro c; simp [eraseGroups]
        · intro i
          by_cases hi : group i = a <;> simp [eraseGroups, hi]
      rw [he, RingHom.comp_apply, h, ih]
  have he : eraseGroups (K := K) group Finset.univ =
      (C : K →+* P σ K).comp constantCoeff := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp [eraseGroups]
  exact (allSets Finset.univ).symm.trans (DFunLike.congr_fun he p)

end Subst
end SingleCoordinate
