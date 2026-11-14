/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.StoppedCurveMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-!
# Measurability of stopped polygonal curves

For a finite discrete state space, an interpolation of fixed duration factors
through the finite prefix of that length. The measurable exit time selects
among these countably many measurable interpolations. This includes the
duration-zero convention at infinite exit time and uses no exit estimate.
-/

open scoped BigOperators unitInterval
open MeasureTheory

namespace BouRabeeGwynne

/-- Interpolation through step `m` only uses the vertices with indices at most `m`. -/
lemma polygonalCurve_congr_prefix {d : ℕ} {V : Type*} (pos : V → Euc d)
    {ω ω' : ℕ → V} {m : ℕ} (h : ∀ k ≤ m, ω k = ω' k) :
    polygonalCurve pos ω m = polygonalCurve pos ω' m := by
  apply ContinuousMap.ext
  intro t
  change pos (ω 0) + _ = pos (ω' 0) + _
  rw [h 0 (Nat.zero_le m)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k < m := Finset.mem_range.mp hk
  rw [h k (Nat.le_of_lt hkm), h (k + 1) hkm]

variable {d : ℕ} {V : Type*} [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-- A fixed-duration curve class is a measurable function of the discrete path. -/
lemma measurable_curveProjection_polygonalCurve (pos : V → Euc d) (m : ℕ) :
    Measurable (fun ω : ℕ → V => CurveSpace.project (polygonalCurve pos ω m)) := by
  let pathPrefix : (ℕ → V) → (Fin (m + 1) → V) := fun ω i => ω i.val
  let extend : (Fin (m + 1) → V) → ℕ → V :=
    fun p k => p ⟨min k m, Nat.lt_succ_of_le (Nat.min_le_right k m)⟩
  have hp : Measurable pathPrefix := measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
  have hg : Measurable (fun p : Fin (m + 1) → V =>
      CurveSpace.project (polygonalCurve pos (extend p) m)) := measurable_of_finite _
  have heq : (fun ω : ℕ → V => CurveSpace.project (polygonalCurve pos ω m)) =
      (fun p : Fin (m + 1) → V =>
        CurveSpace.project (polygonalCurve pos (extend p) m)) ∘ pathPrefix := by
    funext ω
    congr 1
    apply polygonalCurve_congr_prefix
    intro k hk
    simp [pathPrefix, extend, Nat.min_eq_left hk]
  rw [heq]
  exact hg.comp hp

/-- The canonical discrete first exit is measurable also on never-exiting paths. -/
lemma measurable_discreteExitTime (A : Set V) :
    Measurable (FiniteConductanceNetwork.exitTime A) :=
  (FiniteConductanceNetwork.exitTime_isStoppingTime A).measurable'

/-- The duration used by the total stopped interpolation is measurable. -/
lemma measurable_stoppedPolygonalDuration (A : Set V) :
    Measurable (fun ω : ℕ → V =>
      (FiniteConductanceNetwork.exitTime A ω).untopD 0) :=
  (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp
    (measurable_discreteExitTime A)

/-- Actual stopped polygonal interpolation into the Fréchet curve space is
measurable. No almost-sure finite-exit hypothesis is required. -/
lemma measurable_stoppedPolygonalCurve (pos : V → Euc d) (A : Set V) :
    Measurable (stoppedPolygonalCurve pos A) := by
  have hf : Measurable (fun p : (ℕ → V) × ℕ =>
      CurveSpace.project (polygonalCurve pos p.1 p.2)) :=
    measurable_from_prod_countable_left (measurable_curveProjection_polygonalCurve pos)
  exact hf.comp (measurable_id.prodMk (measurable_stoppedPolygonalDuration A))

lemma aemeasurable_stoppedPolygonalCurve (pos : V → Euc d) (A : Set V)
    (μ : Measure (ℕ → V)) : AEMeasurable (stoppedPolygonalCurve pos A) μ :=
  (measurable_stoppedPolygonalCurve pos A).aemeasurable

/-- The measurable stopped-curve pushforward of a probability law is a probability law. -/
lemma stoppedPolygonalCurve_map_isProbabilityMeasure (pos : V → Euc d) (A : Set V)
    (μ : Measure (ℕ → V)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.map (stoppedPolygonalCurve pos A)) :=
  (Measure.isProbabilityMeasure_map_iff
    (aemeasurable_stoppedPolygonalCurve pos A μ)).mpr inferInstance

end BouRabeeGwynne
