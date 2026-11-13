/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.VisitBoundQuantum at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimedObservables
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalQuantumCurveBorel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters

/-! The frozen Lebesgue-time visit bound passes to the quantum-time curve. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.MoTInput

theorem finite_quantum_visits_of_reparam
    {cL c : ℝ → ℂ} (φ : ℝ ≃o ℝ)
    (hc : ∀ t, c t = cL (φ t)) {z : ℂ}
    (hfinite : (cL ⁻¹' {z}).Finite) :
    (c ⁻¹' {z}).Finite := by
  have hset : c ⁻¹' {z} = φ ⁻¹' (cL ⁻¹' {z}) := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, hc]
  rw [hset]
  exact hfinite.preimage φ.injective.injOn

/-- Simultaneously at every point, the area-parametrized bundle curve has
finitely many visits, hence its primed observables are genuine maxima. -/
theorem ae_bundle_finite_quantum_visits
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ((η ω) ⁻¹' {z}).Finite := by
  obtain ⟨k, hk⟩ := D.visitBound
  filter_upwards [D.areaParam, hk] with ω hparam hvisit z
  obtain ⟨φ, -, hφ⟩ := hparam.1
  exact finite_quantum_visits_of_reparam φ hφ
    (Set.finite_of_encard_le_coe (hvisit z))

end MatedCRTHarmonic.GMS4c

