/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenMeasurable
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_measure_lfppDOn_open_eq
    {Ω Ω₂ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂}
    {Y : ℂ → Ω → ℝ} {Y₂ : ℂ → Ω₂ → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x))
    (hY₂c : ∀ ω, Continuous fun x => Y₂ x ω)
    (hY₂m : ∀ x, Measurable (Y₂ x))
    (hlaw : P.map (fun ω => (Y · ω)) = P₂.map (fun ω => (Y₂ · ω)))
    (ξ : ℝ) (U : Set ℂ) (hU : IsOpen U) (z w : ℂ)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | lfppDOn ξ (fun x => Y x ω) U z w ∈ S} =
      P₂ {ω | lfppDOn ξ (fun x => Y₂ x ω) U z w ∈ S} := by
  have hgm : Measurable fun f : C(ℂ, ℝ) =>
      lfppDOn ξ (fun x => f x) U z w :=
    pt_dist_measurable_lfppDOn_open ξ U hU z w
      (fun f => f.continuous) (fun x => ContinuousMap.measurable_eval x)
  have hE : MeasurableSet[
      MeasurableSpace.comap (fun f : C(ℂ, ℝ) => (f : ℂ → ℝ))
        MeasurableSpace.pi]
      {f : C(ℂ, ℝ) | lfppDOn ξ (fun x => f x) U z w ∈ S} := by
    rw [← measurableSpace_continuousMap_eq_comap]
    exact hgm hS
  obtain ⟨T, hT, hTE⟩ := hE
  have key : ∀ g : ℂ → ℝ, Continuous g →
      (lfppDOn ξ g U z w ∈ S ↔ g ∈ T) := by
    intro g hg
    have := congrArg
      (fun E => (⟨g, hg⟩ : C(ℂ, ℝ)) ∈ E) hTE
    simp only [mem_preimage, ContinuousMap.coe_mk, mem_ofPred_eq,
      eq_iff_iff] at this
    exact this.symm
  have h1 :
      {ω | lfppDOn ξ (fun x => Y x ω) U z w ∈ S} =
        (fun ω => (Y · ω)) ⁻¹' T := by
    ext ω
    exact key _ (hYc ω)
  have h2 :
      {ω | lfppDOn ξ (fun x => Y₂ x ω) U z w ∈ S} =
        (fun ω => (Y₂ · ω)) ⁻¹' T := by
    ext ω
    exact key _ (hY₂c ω)
  rw [h1, h2,
    ← Measure.map_apply (measurable_pi_iff.2 hYm) hT,
    ← Measure.map_apply (measurable_pi_iff.2 hY₂m) hT, hlaw]

end SupercriticalLQGUniqueness.B2.DG20Pt
