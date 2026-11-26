import SingleCoordinate.Programs
import SingleCoordinate.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp

/-! The two literature inputs are explicit hypotheses of the main theorem.
The conclusion is a finite-dimensional inequality in natural numbers. -/

namespace SingleCoordinate
open MvPolynomial
open scoped Matrix

abbrev RF (K : Type*) [Field K] (d : ℕ) := FractionRing (MatrixPoly K d)

abbrev MatrixInput (K : Type*) (d : ℕ) := K ⊕ MatrixVars d

noncomputable def polynomialInput (K : Type*) [Field K] (d : ℕ) :
    MatrixInput K d → MatrixPoly K d := Sum.elim C X

def inputs (K : Type*) [Field K] (d : ℕ) : Set (MatrixPoly K d) :=
  Set.range (polynomialInput K d)

noncomputable def rationalInput (K : Type*) [Field K] (d : ℕ) :
    MatrixInput K d → RF K d := algebraMap _ _ ∘ polynomialInput K d

theorem range_rationalInput (K : Type*) [Field K] (d : ℕ) :
    Set.range (rationalInput K d) = algebraMap _ (RF K d) '' inputs K d :=
  Set.range_comp _ _

noncomputable def matrixOverFractions (K : Type*) [Field K] (d : ℕ) :
    Matrix (Fin d) (Fin d) (RF K d) :=
  (algebraMap (MatrixPoly K d) (RF K d)).mapMatrix (generic K d)

/-- The first coordinate of the solution with the fixed first unit vector as right-hand side. -/
noncomputable def firstCoordinate (K : Type*) [Field K] (n : ℕ) : RF K (n+1) :=
  ((matrixOverFractions K (n+1))⁻¹ *ᵥ Pi.single 0 1) 0

private theorem det_map_ne (K : Type*) [Field K] (d : ℕ) :
    algebraMap (MatrixPoly K d) (RF K d) (detPoly K d) ≠ 0 :=
  fun e => Matrix.det_mvPolynomialX_ne_zero (Fin d) K
    (IsFractionRing.injective (MatrixPoly K d) (RF K d) (e.trans (map_zero _).symm))

theorem matrixOverFractions_det_ne (K : Type*) [Field K] (d : ℕ) :
    (matrixOverFractions K d).det ≠ 0 := by
  rw [matrixOverFractions, ← RingHom.map_det]
  exact det_map_ne K d

theorem firstCoordinate_formula (K : Type*) [Field K] (n : ℕ) :
    firstCoordinate K n =
      algebraMap _ (RF K (n+1)) (cofactor K (0 : Fin (n+1))) /
      algebraMap _ (RF K (n+1)) (detPoly K (n+1)) := by
  classical
  rw [firstCoordinate, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, matrixOverFractions,
    ← RingHom.map_det, ← RingHom.map_adjugate, div_eq_mul_inv, mul_comm]
  rfl

/-- Correctness for the ordinary equation, without prescribing an elimination procedure. -/
theorem firstCoordinate_of_solution {K : Type*} [Field K] {n : ℕ}
    (x : Fin (n+1) → RF K (n+1)) (h : matrixOverFractions K (n+1) *ᵥ x = Pi.single 0 1) :
    x 0 = firstCoordinate K n := by
  let A := matrixOverFractions K (n+1)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (matrixOverFractions_det_ne K _)
  change x 0 = (A⁻¹ *ᵥ Pi.single 0 1) 0
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- Specialization of Andrews, Theorem 3.4, to the principal determinant ideal.
Here rank k denotes the border rank of square matrix multiplication of side k.
The exact division-free polynomial program supplies an upper bound on its border cost. -/
def AndrewsBound (K : Type*) [Field K] (rank : ℕ → ℕ) : Prop :=
  ∀ (d : ℕ) {r : ℕ} (p : Program PolyOp (MatrixInput K d) r) (out : Ref (MatrixInput K d) r),
    let q := p.value PolyOp.eval (polynomialInput K d) out
    4 ≤ d → q ≠ 0 → detPoly K d ∣ q → rank (d / 4) ≤ 6 * p.cost PolyOp.weight

/-- The pointwise matrix multiplication border-rank bound, raised to the fourth power. -/
def MatrixRankBound (rank : ℕ → ℕ) : Prop := ∀ k, 2 ≤ k → k^9 ≤ (rank k)^4

/-- Before applying any external lower bound, extract an actual division-free circuit
for a nonzero determinant multiple. The source cost counts every scalar operation. -/
theorem extractDenominator {K : Type*} [Field K] {n s : ℕ} {S : Set (RF K (n+1))}
    (run : RatRun (algebraMap _ (RF K (n+1)) '' inputs K (n+1)) S s)
    (out : firstCoordinate K n ∈ S) :
    ∃ T m q, PolyRun (inputs K (n+1)) T m ∧ m ≤ 3*s ∧
      q ∈ T ∧ q ≠ 0 ∧ detPoly K (n+1) ∣ q := by
  have hone : (1 : MatrixPoly K (n+1)) ∈ inputs K (n+1) :=
    ⟨Sum.inl (1 : K), map_one _⟩
  obtain ⟨T, m, gr, bound, reps⟩ := clearDivisions hone run
  obtain ⟨p, _, q, hq, qne, eqn⟩ := reps _ out
  refine ⟨T, m, q, gr, bound, hq, qne, ?_⟩
  rw [firstCoordinate_formula] at eqn
  let f := algebraMap (MatrixPoly K (n+1)) (RF K (n+1))
  have inj : Function.Injective f := IsFractionRing.injective _ _
  have hd : f (detPoly K (n+1)) ≠ 0 := det_map_ne K (n+1)
  change f p = f (cofactor K (0 : Fin (n+1))) / f (detPoly K (n+1)) * f q at eqn
  have cross : p * detPoly K (n+1) = q * cofactor K (0 : Fin (n+1)) := by
    apply inj
    rw [map_mul, map_mul, eqn]
    field_simp
    ring
  have hdiv : detPoly K (n+1) ∣ q * cofactor K (0 : Fin (n+1)) :=
    cross ▸ dvd_mul_left _ _
  exact (det_cofactor_relPrime (K := K) (n := n)).dvd_of_dvd_mul_right hdiv

theorem singleCoordinate_lower {K : Type*} [Field K] {rank : ℕ → ℕ}
    (andrews : AndrewsBound K rank) (matrixRank : MatrixRankBound rank)
    {n s : ℕ} (dim : 8 ≤ n+1) {S : Set (RF K (n+1))}
    (run : RatRun (algebraMap _ (RF K (n+1)) '' inputs K (n+1)) S s)
    (out : firstCoordinate K n ∈ S) :
    ((n+1)/4)^9 ≤ (18*s)^4 := by
  obtain ⟨T, m, q, gr, hm, hq, qne, dvd⟩ := extractDenominator run out
  obtain ⟨r, p, cost, regs⟩ := program_of_polyRun (polynomialInput K (n+1)) gr
  obtain ⟨o, val⟩ := regs q hq
  have a := andrews (n+1) p o (by omega) (by simpa only [val] using qne)
    (by simpa only [val] using dvd)
  rw [cost] at a
  exact (matrixRank _ (by omega)).trans (Nat.pow_le_pow_left (by omega) 4)

theorem singleCoordinate_dimension_lower {K : Type*} [Field K] {rank : ℕ → ℕ}
    (andrews : AndrewsBound K rank) (matrixRank : MatrixRankBound rank)
    {n s : ℕ} (dim : 8 ≤ n+1) {S : Set (RF K (n+1))}
    (run : RatRun (algebraMap _ (RF K (n+1)) '' inputs K (n+1)) S s)
    (out : firstCoordinate K n ∈ S) :
    (n+1)^9 ≤ 8^9 * (18*s)^4 := by
  have sharp := singleCoordinate_lower andrews matrixRank dim run out
  have hdim : n+1 ≤ 8*((n+1)/4) := by omega
  calc
    (n+1)^9 ≤ (8*((n+1)/4))^9 := Nat.pow_le_pow_left hdim 9
    _ = 8^9 * ((n+1)/4)^9 := mul_pow _ _ _
    _ ≤ 8^9 * (18*s)^4 := Nat.mul_le_mul_left _ sharp

/-- A lower bound for literal straight-line code with bounded register addresses.
The number s is the number of all four-arithmetic gates in the input program. -/
theorem program_lower {K : Type*} [Field K] {rank : ℕ → ℕ}
    (andrews : AndrewsBound K rank) (matrixRank : MatrixRankBound rank)
    {n s : ℕ} (dim : 8 ≤ n+1) (program : Program RatOp (MatrixInput K (n+1)) s)
    (out : Ref (MatrixInput K (n+1)) s) (legal : program.legal (rationalInput K (n+1)))
    (correct : program.value RatOp.eval (rationalInput K (n+1)) out = firstCoordinate K n) :
    ((n+1)/4)^9 ≤ (18*s)^4 := by
  obtain ⟨S, run, available⟩ := program.toRatRun (rationalInput K (n+1)) legal
  rw [range_rationalInput] at run
  exact singleCoordinate_lower andrews matrixRank dim run (correct ▸ available out)

end SingleCoordinate
