/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5CircuitMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitInput

 



set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.QPos

private theorem measurableSet_above_on_path (n : ℕ) (u : ℝ)
    (p : List (DGFFSite n)) :
    MeasurableSet {h : EuclideanSpace ℝ (DGFFSite n) |
      ∀ z ∈ p, -u ≤ h z} := by
  induction p with
  | nil => simp
  | cons z p ih =>
      have hmeas : Measurable
          (fun h : EuclideanSpace ℝ (DGFFSite n) => h z) := by
        exact (PiLp.continuous_apply (p := 2)
          (β := fun _ : DGFFSite n => ℝ) z).measurable
      have hcoord : MeasurableSet
          {h : EuclideanSpace ℝ (DGFFSite n) | -u ≤ h z} :=
        measurableSet_le measurable_const hmeas
      have heq : {h : EuclideanSpace ℝ (DGFFSite n) |
          ∀ w ∈ z :: p, -u ≤ h w} =
          {h | -u ≤ h z} ∩ {h | ∀ w ∈ p, -u ≤ h w} := by
        ext h
        simp
      rw [heq]
      exact hcoord.inter ih

theorem measurableSet_dgffCircuitEvent (n : ℕ) (u : ℝ) :
    MeasurableSet {h : EuclideanSpace ℝ (DGFFSite n) |
      ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧
        ∀ z ∈ p, -u ≤ h z} := by
  have heq : {h : EuclideanSpace ℝ (DGFFSite n) |
      ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧
        ∀ z ∈ p, -u ≤ h z} =
      ⋃ p : List (DGFFSite n),
        {h | IsDGFFAroundPath n p ∧ ∀ z ∈ p, -u ≤ h z} := by
    ext h
    simp
  rw [heq]
  apply MeasurableSet.iUnion
  intro p
  by_cases hp : IsDGFFAroundPath n p
  · simpa [hp] using measurableSet_above_on_path n u p
  · simp [hp]

end SupercriticalLQGUniqueness.B2.QPos
