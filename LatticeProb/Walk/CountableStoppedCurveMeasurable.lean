/- The prefix measurability argument is adapted from Leonardo Bonanno,
   lean-formalizations, BouRabeeGwynne.StoppedCurveMeasurable, commit 31e74833. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveMeasurable

/-! # Stopped polygonal curves on countable vertex spaces -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

open BouRabeeGwynne

variable {d : ℕ} {V : Type*} [Countable V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-- A fixed-length polygonal curve depends measurably on a countable vertex path. -/
theorem measurable_polygonalCurve_projection_countable (pos : V → Euc d) (m : ℕ) :
    Measurable (fun ω : ℕ → V => CurveSpace.project (polygonalCurve pos ω m)) := by
  let pathPrefix : (ℕ → V) → (Fin (m + 1) → V) := fun ω i => ω i.val
  let extend : (Fin (m + 1) → V) → ℕ → V :=
    fun p k => p ⟨min k m, Nat.lt_succ_of_le (Nat.min_le_right k m)⟩
  have hp : Measurable pathPrefix := measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
  have hg : Measurable (fun p : Fin (m + 1) → V =>
      CurveSpace.project (polygonalCurve pos (extend p) m)) := measurable_of_countable _
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

/-- The stopped polygonal curve is measurable, including on paths that never exit. -/
theorem measurable_stoppedPolygonalCurve_countable (pos : V → Euc d) (A : Set V) :
    Measurable (stoppedPolygonalCurve pos A) := by
  have ht : Measurable (FiniteConductanceNetwork.exitTime A) := by
    apply (FiniteConductanceNetwork.coordinateProcess_adapted.isStoppingTime_hittingAfter
      (Set.to_countable Aᶜ).measurableSet).measurable'
  have hd : Measurable (fun ω : ℕ → V =>
      (FiniteConductanceNetwork.exitTime A ω).untopD 0) :=
    (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp ht
  have hf : Measurable (fun p : (ℕ → V) × ℕ =>
      CurveSpace.project (polygonalCurve pos p.1 p.2)) :=
    measurable_from_prod_countable_left (measurable_polygonalCurve_projection_countable pos)
  exact hf.comp (measurable_id.prodMk hd)

end LatticeProb
