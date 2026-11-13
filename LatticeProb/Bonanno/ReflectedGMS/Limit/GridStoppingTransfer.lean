/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GridStoppingTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Process.Stopping

/-! Transfer discrete stopping indices to their actual deterministic grid
times. This connects discrete greedy oscillation stops with the existing
nonnegative-real-time optional-stopping estimates. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A discrete stopping index gives a genuine continuous-time stopping time
whenever its information is available by the corresponding grid time. -/
theorem isStoppingTime_deterministicGrid
    {F : Filtration ℝ≥0 m} {G : Filtration ℕ m}
    (a : ℕ → ℝ≥0) (hGF : ∀ i, G i ≤ F (a i))
    {σ : Ω → ℕ}
    (hσ : IsStoppingTime G (fun ω => (σ ω : WithTop ℕ))) :
    IsStoppingTime F (fun ω => (a (σ ω) : WithTop ℝ≥0)) := by
  intro t
  simp only [WithTop.coe_le_coe]
  have heq : {ω | a (σ ω) ≤ t} = ⋃ i, ⋃ (_ : a i ≤ t), {ω | σ ω = i} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨σ ω, h, rfl⟩
    · rintro ⟨i, hi, hσi⟩
      simpa only [hσi] using hi
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro hi
  have hσi : MeasurableSet[G i] {ω | σ ω = i} := by
    have hi := hσ.measurableSet_eq i
    change MeasurableSet[G i] {ω | (σ ω : WithTop ℕ) = (i : WithTop ℕ)} at hi
    simpa using hi
  exact F.mono hi _ (hGF i _ hσi)

end ReflectedGMS.MartingaleLimit
