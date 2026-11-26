import SingleCoordinate.Programs
import Mathlib.Tactic.FieldSimp

/-! Relate evaluation at a concrete point to evaluation in a field of rational functions.
For this purpose, the same program can also be evaluated on pairs in a polynomial ring. -/

namespace SingleCoordinate

namespace RatOp

def pair {R : Type*} [CommRing R] : RatOp → R × R → R × R → R × R
  | .add, (p,q), (r,t) => (p*t + r*q, q*t)
  | .sub, (p,q), (r,t) => (p*t - r*q, q*t)
  | .mul, (p,q), (r,t) => (p*r, q*t)
  | .div, (p,q), (r,t) => (p*t, q*r)

end RatOp

namespace Program

variable {I R F : Type*} [CommRing R] [Field F]

def agrees (f : R →+* F) (p : R × R) (v : F) : Prop :=
  f p.2 ≠ 0 ∧ f p.1 = v * f p.2

private theorem agrees_gate (op : RatOp) (f : R →+* F) {P Q : R × R} {a b : F}
    (ha : agrees f P a) (hb : agrees f Q b) (valid : op = .div → b ≠ 0) :
    agrees f (op.pair P Q) (op.eval a b) := by
  obtain ⟨p,q⟩ := P
  obtain ⟨r,t⟩ := Q
  obtain ⟨qn, pa⟩ := ha
  obtain ⟨tn, rb⟩ := hb
  change f q ≠ 0 at qn
  change f t ≠ 0 at tn
  change f p = a * f q at pa
  change f r = b * f t at rb
  cases op with
  | add =>
    exact ⟨by simpa [RatOp.pair] using mul_ne_zero qn tn, by
      simp only [RatOp.pair, RatOp.eval, map_add, map_mul, pa, rb]; ring⟩
  | sub =>
    exact ⟨by simpa [RatOp.pair] using mul_ne_zero qn tn, by
      simp only [RatOp.pair, RatOp.eval, map_sub, map_mul, pa, rb]; ring⟩
  | mul =>
    exact ⟨by simpa [RatOp.pair] using mul_ne_zero qn tn, by
      simp only [RatOp.pair, RatOp.eval, map_mul, pa, rb]; ring⟩
  | div =>
    have bn := valid rfl
    have rn : f r ≠ 0 := rb ▸ mul_ne_zero bn tn
    exact ⟨by simpa [RatOp.pair] using mul_ne_zero qn rn, by
      simp only [RatOp.pair, RatOp.eval, map_mul, pa, rb]; field_simp; ring⟩

def pairValue {r : ℕ} (p : Program RatOp I r) (input : I → R) (o : Ref I r) : R × R :=
  p.value RatOp.pair (fun i => (input i, 1)) o

theorem pair_agrees {r : ℕ} (p : Program RatOp I r) (input : I → R) (f : R →+* F)
    (h : p.legal (f ∘ input)) (o : Ref I r) :
    agrees f (p.pairValue input o) (p.value RatOp.eval (f ∘ input) o) := by
  induction p with
  | nil =>
    cases o with
    | reg j => exact Fin.elim0 j
    | input i => exact ⟨by simp [pairValue], by simp [pairValue]⟩
  | @step t prev op a b ih =>
    cases o with
    | input i => exact ⟨by simp [pairValue], by simp [pairValue]⟩
    | reg j =>
      refine Fin.cases ?_ (fun k => ?_) j
      · exact agrees_gate op f (ih h.1 a) (ih h.1 b) h.2
      · exact ih h.1 (.reg k)

/-- If a division is legal at one specialization, its symbolic divisor cannot be identically zero. -/
theorem legal_of_injective_map {G : Type*} [Field G] {r : ℕ}
    (p : Program RatOp I r) (input : I → R) (f : R →+* F)
    (g : R →+* G) (inj : Function.Injective g) (legalAt : p.legal (f ∘ input)) :
    p.legal (g ∘ input) := by
  induction p with
  | nil => trivial
  | @step t prev op a b ih =>
    have genericLegal := ih legalAt.1
    refine ⟨genericLegal, ?_⟩
    intro hd hz
    have h₁ := prev.pair_agrees input f legalAt.1 b
    have h₂ := prev.pair_agrees input g genericLegal b
    have ng : g (prev.pairValue input b).1 = 0 := by rw [h₂.2, hz, zero_mul]
    have nr : (prev.pairValue input b).1 = 0 := inj (ng.trans (map_zero g).symm)
    have nf : f (prev.pairValue input b).1 ≠ 0 := h₁.2 ▸ mul_ne_zero (legalAt.2 hd) h₁.1
    exact nf (nr ▸ map_zero f)

end Program
end SingleCoordinate
