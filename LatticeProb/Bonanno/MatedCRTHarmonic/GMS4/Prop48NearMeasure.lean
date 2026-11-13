/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48NearMeasure at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48

/-!
# Near-pair geometry for [18] Proposition 4.8

The spatial part of (4.34) bounds the area of pairs of test points within a
fixed distance by the test-domain area times the area of one planar ball.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4

/-- The geometric Fubini bound behind [18] (4.34). -/
theorem prop48_nearPair_volume_le (D : Set ℂ) (hD : MeasurableSet D)
    (r : ℝ) :
    (volume.prod volume) {p : ℂ × ℂ | p.1 ∈ D ∧ p.2 ∈ D ∧ dist p.1 p.2 ≤ r} ≤
      volume D * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ D ∧ p.2 ∈ D ∧ dist p.1 p.2 ≤ r}
  have hS : MeasurableSet S := by
    have h1 : MeasurableSet {p : ℂ × ℂ | p.1 ∈ D} := hD.preimage measurable_fst
    have h2 : MeasurableSet {p : ℂ × ℂ | p.2 ∈ D} := hD.preimage measurable_snd
    have h3 : MeasurableSet {p : ℂ × ℂ | dist p.1 p.2 ≤ r} :=
      measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
    simpa only [S, Set.ofPred_and] using h1.inter (h2.inter h3)
  have hsection : ∀ z : ℂ, volume (Prod.mk z ⁻¹' S) ≤
      D.indicator (fun _ => ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) z := by
    intro z
    by_cases hz : z ∈ D
    · simp only [Set.indicator_of_mem hz]
      have hsubset : Prod.mk z ⁻¹' S ⊆ closedBall z r := by
        intro w hw
        simpa only [mem_closedBall, dist_comm] using hw.2.2
      calc
        volume (Prod.mk z ⁻¹' S) ≤ volume (closedBall z r) := measure_mono hsubset
        _ = ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal) := Complex.volume_closedBall z r
    · have hempty : Prod.mk z ⁻¹' S = ∅ := by
        ext w
        simp [S, hz]
      simp [Set.indicator_of_notMem hz, hempty]
  change (volume.prod volume) S ≤ _
  rw [Measure.prod_apply hS]
  calc
    (∫⁻ z, volume (Prod.mk z ⁻¹' S) ∂volume) ≤
        ∫⁻ z, D.indicator (fun _ => ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) z ∂volume :=
      lintegral_mono hsection
    _ = volume D * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) := by
      rw [lintegral_indicator_const hD, mul_comm]

end MatedCRTHarmonic.GMS4

