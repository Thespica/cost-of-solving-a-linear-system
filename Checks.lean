import SingleCoordinate
import Lean.Util.CollectAxioms

open SingleCoordinate

/- A concrete four-gate program computing d / (a*d - b*c).
   Executing it exercises old-register references and the nonzero divisor condition. -/
private def solveTwo : Program RatOp (Fin 4) 4 :=
  let ad := Program.nil.step RatOp.mul (.input 0) (.input 3)
  let bc := ad.step .mul (.input 1) (.input 2)
  let delta := bc.step .sub (.reg (Fin.succ 0)) (.reg 0)
  delta.step .div (.input 3) (.reg 0)

private def four (a b c d : ℚ) : Fin 4 → ℚ := ![a,b,c,d]

#eval solveTwo.value RatOp.eval (four 2 1 1 3) (.reg 0)
#guard solveTwo.value RatOp.eval (four 2 1 1 3) (.reg 0) == (3/5 : ℚ)
#guard solveTwo.value RatOp.eval (four 0 1 1 0) (.reg 0) == 0
example : solveTwo.legal (four 2 1 1 3) := by
  simp [solveTwo, Program.legal, Program.value, Program.registers, RatOp.eval, Ref.read, four]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, Fin.cases_succ, Fin.cases_zero]
  norm_num
example : ¬ solveTwo.legal (four 1 2 2 4) := by
  simp [solveTwo, Program.legal, Program.value, Program.registers, RatOp.eval, Ref.read, four]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, Fin.cases_succ, Fin.cases_zero]
  norm_num

#print axioms SingleCoordinate.clearDivisions
#print axioms SingleCoordinate.det_cofactor_relPrime
#print axioms SingleCoordinate.extractDenominator
#print axioms SingleCoordinate.concrete_program_lower
#print axioms SingleCoordinate.single_coordinate_nine_fourths

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for thm in #[``SingleCoordinate.clearDivisions, ``SingleCoordinate.det_cofactor_relPrime,
      ``SingleCoordinate.extractDenominator, ``SingleCoordinate.concrete_program_lower, ``SingleCoordinate.single_coordinate_nine_fourths] do
    for ax in ← Lean.collectAxioms thm do
      unless allowed.contains ax do
        throwError "{thm} uses unexpected axiom {ax}"
