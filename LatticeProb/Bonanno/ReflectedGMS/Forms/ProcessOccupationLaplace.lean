/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ProcessOccupationLaplace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.TransitionRightContinuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Tonelli's theorem for actual reflected-process discounted vertex occupation.
The existing jointly measurable version agrees with the original process at
every time on one event of full probability. No joint measurability assumption
is added to the reflected-walk contract. -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16

universe u
variable {V Ω : Type u} [MeasurableSpace Ω]

/-- The discounted time an actual path spends at a given vertex. -/
noncomputable def discountedVertexOccupation
    (X : ℝ≥0 → Ω → Option V) (alpha : ℝ) (y : V) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ioi 0, {s : ℝ | X (Real.toNNReal s) ω = some y}.indicator
    (fun s => ENNReal.ofReal (Real.exp (-alpha * s))) t

private theorem lintegral_discountedVertexOccupation_jointlyMeasurable
    {P : Measure Ω} [SFinite P] {X : ℝ≥0 → Ω → Option V}
    (hX : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) (alpha : ℝ) (y : V) :
    (∫⁻ ω, discountedVertexOccupation X alpha y ω ∂P) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-alpha * t)) *
        P {ω | X (Real.toNNReal t) ω = some y} := by
  classical
  let F : Ω → ℝ → ℝ≥0∞ := fun ω t =>
    {s : ℝ | X (Real.toNNReal s) ω = some y}.indicator
      (fun s => ENNReal.ofReal (Real.exp (-alpha * s))) t
  have hF : Measurable (Function.uncurry F) := by
    change Measurable ({p : Ω × ℝ | X (Real.toNNReal p.2) p.1 = some y}.indicator
      (fun p => ENNReal.ofReal (Real.exp (-alpha * p.2))))
    apply Measurable.indicator
    · fun_prop
    · exact measurable_swap_toNNReal hX (measurableSet_option {some y})
  change (∫⁻ ω, ∫⁻ t : ℝ in Ioi 0, F ω t ∂volume ∂P) = _
  rw [lintegral_lintegral_swap hF.aemeasurable]
  apply lintegral_congr
  intro t
  change (∫⁻ ω, {ω | X (Real.toNNReal t) ω = some y}.indicator
    (fun _ => ENNReal.ofReal (Real.exp (-alpha * t))) ω ∂P) = _
  exact lintegral_indicator_const
    ((hX.comp (measurable_const.prodMk measurable_id)) (measurableSet_option {some y})) _

end ReflectedGMS
