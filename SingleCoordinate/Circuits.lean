import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Ring

/-! Straight-line computations over a field and over a polynomial ring.
A state contains exactly the values available so far, including the inputs.
Every gate may reuse any previous value. -/

namespace SingleCoordinate

inductive RatOp | add | sub | mul | div

def RatOp.eval {F : Type*} [Field F] : RatOp → F → F → F
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

inductive RatRun {F : Type*} [Field F] (inputs : Set F) : Set F → ℕ → Prop
  | start : RatRun inputs inputs 0
  | step {S : Set F} {s : ℕ} (prev : RatRun inputs S s) (op : RatOp)
      {a b : F} (ha : a ∈ S) (hb : b ∈ S) (valid : op = .div → b ≠ 0) :
      RatRun inputs (insert (op.eval a b) S) (s + 1)

/-- Division-free circuits charge one per multiplication, with free addition and subtraction. -/
inductive PolyRun {R : Type*} [CommRing R] (inputs : Set R) : Set R → ℕ → Prop
  | start : PolyRun inputs inputs 0
  | mul {S : Set R} {c : ℕ} (prev : PolyRun inputs S c) {a b : R}
      (ha : a ∈ S) (hb : b ∈ S) : PolyRun inputs (insert (a * b) S) (c + 1)
  | add {S : Set R} {c : ℕ} (prev : PolyRun inputs S c) {a b : R}
      (ha : a ∈ S) (hb : b ∈ S) : PolyRun inputs (insert (a + b) S) c
  | sub {S : Set R} {c : ℕ} (prev : PolyRun inputs S c) {a b : R}
      (ha : a ∈ S) (hb : b ∈ S) : PolyRun inputs (insert (a - b) S) c

section Clearing

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

/-- Two available registers give an unreduced fraction with a nonzero denominator. -/
def Represents (S : Set R) (v : F) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, q ≠ 0 ∧ algebraMap R F p = v * algebraMap R F q

omit [IsDomain R] [IsFractionRing R F] in
private theorem rep_mono {S T : Set R} {v : F} (h : S ⊆ T) (hv : Represents S v) :
    Represents T v := by
  obtain ⟨p, hp, q, hq, hn, e⟩ := hv
  exact ⟨p, h hp, q, h hq, hn, e⟩

omit [IsFractionRing R F] in
private theorem addPair {I S : Set R} {c : ℕ} (run : PolyRun I S c)
    {a b : F} (ha : Represents S a) (hb : Represents S b) (subtract : Bool) :
    ∃ T, PolyRun I T (c + 3) ∧ S ⊆ T ∧
      Represents T (if subtract then a - b else a + b) := by
  obtain ⟨p, hp, q, hq, qne, pa⟩ := ha
  obtain ⟨r, hr, t, ht, tne, rb⟩ := hb
  have g₁ := run.mul hp ht
  have g₂ := g₁.mul (a := r) (b := q) (by simp [hr]) (by simp [hq])
  have g₃ := g₂.mul (a := q) (b := t) (by simp [hq]) (by simp [ht])
  cases subtract with
  | false =>
    have g := g₃.add (a := p*t) (b := r*q) (by simp) (by simp)
    refine ⟨_, g, fun x hx => by simp [hx], p*t+r*q, by simp, q*t, by simp,
      mul_ne_zero qne tne, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte, map_add, map_mul, pa, rb]
    ring
  | true =>
    have g := g₃.sub (a := p*t) (b := r*q) (by simp) (by simp)
    refine ⟨_, g, fun x hx => by simp [hx], p*t-r*q, by simp, q*t, by simp,
      mul_ne_zero qne tne, ?_⟩
    simp only [↓reduceIte, map_sub, map_mul, pa, rb]
    ring

omit [IsFractionRing R F] in
private theorem mulPair {I S : Set R} {c : ℕ} (run : PolyRun I S c)
    {a b : F} (ha : Represents S a) (hb : Represents S b) :
    ∃ T, PolyRun I T (c + 2) ∧ S ⊆ T ∧ Represents T (a * b) := by
  obtain ⟨p, hp, q, hq, qne, pa⟩ := ha
  obtain ⟨r, hr, t, ht, tne, rb⟩ := hb
  have g₁ := run.mul hp hr
  have g₂ := g₁.mul (a := q) (b := t) (by simp [hq]) (by simp [ht])
  refine ⟨_, g₂, fun x hx => by simp [hx], p*r, by simp, q*t, by simp,
    mul_ne_zero qne tne, ?_⟩
  simp only [map_mul, pa, rb]
  ring

omit [IsDomain R] in
private theorem invPair {S : Set R} {v : F} (hv : Represents S v) (hne : v ≠ 0) :
    Represents S v⁻¹ := by
  obtain ⟨p, hp, q, hq, qne, eqn⟩ := hv
  have qmap : algebraMap R F q ≠ 0 := fun h =>
    qne (IsFractionRing.injective R F (h.trans (map_zero _).symm))
  have pne : p ≠ 0 := by
    intro h
    rw [h, map_zero] at eqn
    exact mul_ne_zero hne qmap eqn.symm
  refine ⟨q, hq, p, hp, pne, ?_⟩
  rw [eqn, inv_mul_cancel_left₀ hne]

/-- Clear all divisions without losing sharing. The bound counts all source gates. -/
theorem clearDivisions {I : Set R} (one_mem : (1 : R) ∈ I)
    {S : Set F} {s : ℕ} (run : RatRun (algebraMap R F '' I) S s) :
    ∃ T c, PolyRun I T c ∧ c ≤ 3*s ∧ ∀ v ∈ S, Represents T v := by
  induction run with
  | start =>
    refine ⟨I, 0, .start, by omega, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hp, 1, one_mem, one_ne_zero, by simp⟩
  | @step S s prev op a b ha hb valid ih =>
    obtain ⟨T, c, poly, bound, rep⟩ := ih
    suffices h : ∃ U d, PolyRun I U d ∧ d ≤ c+3 ∧ T ⊆ U ∧
        Represents U (op.eval a b) by
      obtain ⟨U, d, gu, hd, subT, fresh⟩ := h
      refine ⟨U, d, gu, by omega, ?_⟩
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | old
      · exact fresh
      · exact rep_mono subT (rep v old)
    cases op with
    | add =>
      obtain ⟨U, g, h, e⟩ := addPair poly (rep a ha) (rep b hb) false
      exact ⟨U, _, g, le_rfl, h, e⟩
    | sub =>
      obtain ⟨U, g, h, e⟩ := addPair poly (rep a ha) (rep b hb) true
      exact ⟨U, _, g, le_rfl, h, e⟩
    | mul =>
      obtain ⟨U, g, h, e⟩ := mulPair poly (rep a ha) (rep b hb)
      exact ⟨U, _, g, by omega, h, e⟩
    | div =>
      obtain ⟨U, g, h, e⟩ := mulPair poly (rep a ha) (invPair (rep b hb) (valid rfl))
      exact ⟨U, _, g, by omega, h, by simpa [RatOp.eval, div_eq_mul_inv] using e⟩

end Clearing
end SingleCoordinate
