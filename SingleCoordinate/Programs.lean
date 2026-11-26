import SingleCoordinate.Circuits

/-! Syntax for finite straight-line programs. A register reference is bounded
by the number of earlier gates. Register zero always holds the newest result. -/

namespace SingleCoordinate

inductive Ref (I : Type*) (r : ℕ)
  | input (i : I)
  | reg (j : Fin r)

def Ref.read {I V : Type*} {r : ℕ} (a : Ref I r) (input : I → V) (reg : Fin r → V) : V :=
  match a with | .input i => input i | .reg j => reg j

def Ref.weaken {I : Type*} {r : ℕ} : Ref I r → Ref I (r+1)
  | .input i => .input i
  | .reg j => .reg j.succ

inductive Program (O I : Type*) : ℕ → Type _
  | nil : Program O I 0
  | step {r : ℕ} (prev : Program O I r) (op : O) (left right : Ref I r) : Program O I (r+1)

namespace Program

variable {O I V : Type*} {r : ℕ}

def registers (ev : O → V → V → V) (input : I → V) :
    {r : ℕ} → Program O I r → Fin r → V
  | _, .nil => Fin.elim0
  | _, .step prev op a b =>
    let regs := prev.registers ev input
    Fin.cases (ev op (a.read input regs) (b.read input regs)) regs

def value (ev : O → V → V → V) (input : I → V) (p : Program O I r) (out : Ref I r) : V :=
  out.read input (p.registers ev input)

@[simp] theorem value_input (ev : O → V → V → V) (input : I → V)
    (p : Program O I r) (i : I) : value ev input p (.input i) = input i := rfl

@[simp] theorem value_new (ev : O → V → V → V) (input : I → V) (p : Program O I r)
    (op : O) (a b : Ref I r) :
    value ev input (p.step op a b) (.reg 0) = ev op (value ev input p a) (value ev input p b) := rfl

@[simp] theorem value_old (ev : O → V → V → V) (input : I → V) (p : Program O I r)
    (op : O) (a b z : Ref I r) :
    value ev input (p.step op a b) z.weaken = value ev input p z := by cases z <;> rfl

def cost (weight : O → ℕ) : {r : ℕ} → Program O I r → ℕ
  | _, .nil => 0
  | _, .step prev op _ _ => prev.cost weight + weight op

/-- All divisions must have nonzero divisors at this input. -/
def legal {F : Type*} [Field F] (input : I → F) : {r : ℕ} → Program RatOp I r → Prop
  | _, .nil => True
  | _, .step prev op _ b =>
    prev.legal input ∧ (op = .div → prev.value RatOp.eval input b ≠ 0)

theorem toRatRun {F : Type*} [Field F] (input : I → F)
    (p : Program RatOp I r) (h : p.legal input) :
    ∃ S, RatRun (Set.range input) S r ∧ ∀ a, p.value RatOp.eval input a ∈ S := by
  induction p with
  | nil =>
    refine ⟨_, .start, ?_⟩
    intro a
    cases a with
    | input i => exact Set.mem_range_self i
    | reg j => exact Fin.elim0 j
  | @step t prev op a b ih =>
    obtain ⟨S, run, hr⟩ := ih h.1
    refine ⟨_, run.step op (hr a) (hr b) h.2, ?_⟩
    intro z
    cases z with
    | input i => exact Set.mem_insert_of_mem _ (hr (.input i))
    | reg j =>
      refine Fin.cases ?_ (fun k => ?_) j
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (hr (.reg k))

end Program

inductive PolyOp | add | sub | mul

def PolyOp.eval {R : Type*} [CommRing R] : PolyOp → R → R → R
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

def PolyOp.weight : PolyOp → ℕ | .add | .sub => 0 | .mul => 1

/-- A semantic derivation of a polynomial register gives literal division-free code
with the same multiplication count. References preserve shared subexpressions. -/
theorem program_of_polyRun {I R : Type*} [CommRing R] (input : I → R)
    {S : Set R} {c : ℕ} (run : PolyRun (Set.range input) S c) :
    ∃ (r : ℕ) (p : Program PolyOp I r), p.cost PolyOp.weight = c ∧
      ∀ y ∈ S, ∃ a, p.value PolyOp.eval input a = y := by
  have extend {T : Set R} {m t : ℕ} (p : Program PolyOp I t)
      (cost : p.cost PolyOp.weight = m)
      (vars : ∀ y ∈ T, ∃ a, p.value PolyOp.eval input a = y)
      (op : PolyOp) {u v : R} (hu : u ∈ T) (hv : v ∈ T) :
      ∃ (r : ℕ) (q : Program PolyOp I r), q.cost PolyOp.weight = m+op.weight ∧
        ∀ y ∈ insert (op.eval u v) T, ∃ a, q.value PolyOp.eval input a = y := by
    obtain ⟨a, ea⟩ := vars u hu
    obtain ⟨b, eb⟩ := vars v hv
    refine ⟨_, p.step op a b, by simp [Program.cost, cost], ?_⟩
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | old
    · exact ⟨.reg 0, by simp [ea, eb]⟩
    · obtain ⟨z, hz⟩ := vars y old
      exact ⟨z.weaken, by simpa using hz⟩
  induction run with
  | start =>
    refine ⟨0, .nil, rfl, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact ⟨.input i, rfl⟩
  | mul _ ha hb ih =>
    obtain ⟨t, p, c, h⟩ := ih
    exact extend p c h .mul ha hb
  | add _ ha hb ih =>
    obtain ⟨t, p, c, h⟩ := ih
    exact extend p c h .add ha hb
  | sub _ ha hb ih =>
    obtain ⟨t, p, c, h⟩ := ih
    exact extend p c h .sub ha hb

end SingleCoordinate
