import SingleCoordinate.LowerBound
import SingleCoordinate.SpecializationOfProgram
import Mathlib.Algebra.MvPolynomial.Funext

/-! A program correct on every invertible input over an infinite field
computes the same rational function at the generic matrix. -/

namespace SingleCoordinate
open MvPolynomial
open scoped Matrix

noncomputable def evalAt {K : Type*} [Field K] {d : ℕ} (A : Matrix (Fin d) (Fin d) K) :
    MatrixPoly K d →+* K := eval fun i => A i.1 i.2

theorem eval_detPoly {K : Type*} [Field K] {d : ℕ} (A : Matrix (Fin d) (Fin d) K) :
    evalAt A (detPoly K d) = A.det := by
  rw [detPoly, RingHom.map_det]
  exact congrArg Matrix.det (Matrix.mvPolynomialX_mapMatrix_eval A)

theorem eval_cofactor {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (j : Fin (n+1)) :
    evalAt A (cofactor K j) = A.adjugate j 0 := by
  let f := evalAt A
  have h : f.mapMatrix (generic K (n+1)) = A := Matrix.mvPolynomialX_mapMatrix_eval A
  have ad := f.map_adjugate (generic K (n+1))
  rw [h] at ad
  exact congrArg (fun M => M j 0) ad

theorem numeric_coordinate {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    (A⁻¹ *ᵥ Pi.single 0 1) 0 = A.adjugate 0 0 / A.det := by
  rw [Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.inv_def, Matrix.smul_apply,
    Ring.inverse_eq_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The only promise on concrete inputs is that A is invertible. -/
def SolvesFirst {K : Type*} [Field K] {n s : ℕ}
    (p : Program RatOp (MatrixInput K (n+1)) s) (out : Ref (MatrixInput K (n+1)) s) : Prop :=
  ∀ A : Matrix (Fin (n+1)) (Fin (n+1)) K, A.det ≠ 0 →
    let inp := evalAt A ∘ polynomialInput K (n+1)
    p.legal inp ∧ p.value RatOp.eval inp out = (A⁻¹ *ᵥ Pi.single 0 1) 0

/-- Equality on invertible matrices forces equality of the cleared polynomials.
At singular inputs the extra determinant factor makes the identity automatic. -/
private theorem cross_of_points {K : Type*} [Field K] [Infinite K] {n s : ℕ}
    (p : Program RatOp (MatrixInput K (n+1)) s) (out : Ref (MatrixInput K (n+1)) s)
    (h : SolvesFirst p out) :
    let pq := p.pairValue (polynomialInput K (n+1)) out
    pq.1 * detPoly K (n+1) = pq.2 * cofactor K (0 : Fin (n+1)) := by
  let pq := p.pairValue (polynomialInput K (n+1)) out
  let D := detPoly K (n+1)
  let Δ := cofactor K (0 : Fin (n+1))
  change pq.1 * D = pq.2 * Δ
  have identity : (pq.1 * D - pq.2 * Δ) * D = 0 := by
    apply MvPolynomial.funext
    intro v
    let A : Matrix (Fin (n+1)) (Fin (n+1)) K := fun i j => v (i,j)
    change evalAt A ((pq.1 * D - pq.2 * Δ) * D) = evalAt A 0
    simp only [map_zero, map_mul, map_sub, D, Δ, eval_detPoly, eval_cofactor]
    by_cases singular : A.det = 0
    · simp [singular]
    obtain ⟨legal, cout⟩ := h A singular
    have agreement := p.pair_agrees (polynomialInput K (n+1)) (evalAt A) legal out
    have ep : evalAt A pq.1 = A.adjugate 0 0 / A.det * evalAt A pq.2 := by
      rw [← numeric_coordinate, ← cout]
      exact agreement.2
    rw [ep]
    field_simp
    ring
  have nd : D ≠ 0 := Matrix.det_mvPolynomialX_ne_zero _ _
  exact sub_eq_zero.mp ((mul_eq_zero.mp identity).resolve_right nd)

theorem generic_of_concrete {K : Type*} [Field K] [Infinite K] {n s : ℕ}
    (p : Program RatOp (MatrixInput K (n+1)) s) (out : Ref (MatrixInput K (n+1)) s)
    (h : SolvesFirst p out) :
    p.legal (rationalInput K (n+1)) ∧
      p.value RatOp.eval (rationalInput K (n+1)) out = firstCoordinate K n := by
  let I : Matrix (Fin (n+1)) (Fin (n+1)) K := 1
  have ni : I.det ≠ 0 := by simp [I]
  let g := algebraMap (MatrixPoly K (n+1)) (RF K (n+1))
  have inj : Function.Injective g := IsFractionRing.injective _ _
  have legal := p.legal_of_injective_map (polynomialInput K (n+1)) (evalAt I) g inj (h I ni).1
  refine ⟨legal, ?_⟩
  let pq := p.pairValue (polynomialInput K (n+1)) out
  have w := p.pair_agrees (polynomialInput K (n+1)) g legal out
  have val : p.value RatOp.eval (rationalInput K (n+1)) out = g pq.1 / g pq.2 :=
    (eq_div_iff w.1).mpr w.2.symm
  rw [val, firstCoordinate_formula]
  have hd : g (detPoly K (n+1)) ≠ 0 :=
    fun e => Matrix.det_mvPolynomialX_ne_zero _ _ (inj (e.trans (map_zero g).symm))
  apply (div_eq_div_iff w.1 hd).mpr
  have hpoly : pq.1 * detPoly K (n+1) = pq.2 * cofactor K (0 : Fin (n+1)) :=
    cross_of_points p out h
  calc
    g pq.1 * g (detPoly K (n+1)) = g (pq.1 * detPoly K (n+1)) := (map_mul g _ _).symm
    _ = g (pq.2 * cofactor K (0 : Fin (n+1))) := congrArg g hpoly
    _ = g pq.2 * g (cofactor K (0 : Fin (n+1))) := map_mul g _ _
    _ = _ := mul_comm _ _

/-- Finite-size lower bound for a fixed exact program correct on every invertible
matrix over an infinite field, including when the input field is just the rationals. -/
theorem concrete_program_lower {K : Type*} [Field K] [Infinite K] {rank : ℕ → ℕ}
    (andrews : AndrewsBound K rank) (matrixRank : MatrixRankBound rank)
    {n s : ℕ} (dim : 8 ≤ n+1) (p : Program RatOp (MatrixInput K (n+1)) s)
    (out : Ref (MatrixInput K (n+1)) s) (correct : SolvesFirst p out) :
    ((n+1)/4)^9 ≤ (18*s)^4 := by
  obtain ⟨legal, formal⟩ := generic_of_concrete p out correct
  exact program_lower andrews matrixRank dim p out legal formal

end SingleCoordinate
