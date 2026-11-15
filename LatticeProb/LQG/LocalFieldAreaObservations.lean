import LatticeProb.LQG.LocalConeAreaIndependence
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2

/-! # Joint observations of a local field and area -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open LQGMetric

namespace LatticeProb.LQG

/-- Joint independence of a field and measure on a region passes to all
fixed open subregions simultaneously, while retaining the auxiliary path. -/
theorem indepFun_restricted_field_area_family
    {Ω ι A W : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace W]
    {P : Measure Ω} {U : Opens ℂ} (V : ι → Opens ℂ) (hVU : ∀ i, V i ≤ U)
    {X : Ω → DistC} {μ : Ω → Measure ℂ} {Y : Ω → W} {Z : Ω → A}
    (hind : IndepFun (fun ω => ((restrictTo U (X ω), (μ ω).restrict U), Y ω)) Z P) :
    IndepFun (fun ω => ((fun i => (restrictTo (V i) (X ω), (μ ω).restrict (V i))), Y ω)) Z P := by
  let G : (DistOn U × Measure ℂ) × W → ((i : ι) → DistOn (V i) × Measure ℂ) × W :=
    fun p => ((fun i => (CONF.resUW U (V i) p.1.1, p.1.2.restrict (V i))), p.2)
  have hG : Measurable G := by
    apply Measurable.prodMk _ measurable_snd
    apply measurable_pi_iff.mpr
    intro i
    have hm : Measurable (fun p : (DistOn U × Measure ℂ) × W =>
        p.1.2.restrict (V i : Set ℂ)) :=
      (measurable_measure_restrict (V i : Set ℂ) (V i).2.measurableSet).comp
        (measurable_snd.comp measurable_fst)
    exact ((CONF.measurable_resUW U (V i)).comp (measurable_fst.comp measurable_fst)).prodMk hm
  have h := hind.comp hG measurable_id
  have heq : (fun ω => G ((restrictTo U (X ω), (μ ω).restrict U), Y ω)) =
      (fun ω => ((fun i => (restrictTo (V i) (X ω), (μ ω).restrict (V i))), Y ω)) := by
    funext ω
    dsimp only [G]
    congr 1
    funext i
    congr 1
    · exact CONF.resUW_restrictTo (hVU i) (X ω)
    · exact Measure.restrict_restrict_of_subset (hVU i)
  change IndepFun (fun ω => G ((restrictTo U (X ω), (μ ω).restrict U), Y ω)) Z P at h
  rw [heq] at h
  exact h

end LatticeProb.LQG
