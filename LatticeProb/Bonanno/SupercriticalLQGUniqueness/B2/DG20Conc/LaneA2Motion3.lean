/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Motion3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Scale3

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneA2_mrectLen_motion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W)
    (m K : ℕ) (u : Circle) (c : ℂ) (a b : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) K u c a b ∈ S} =
      P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) K 1 0 a b ∈ S} := by
  have he (X : Set ℂ) : T20B.mot K u c '' X =
      (fun x => (u : ℂ) * x + c) '' (T20B.mot K 1 0 '' X) := by
    simp only [T20B.mot_image, Set.image_image]
    congr 1
    funext x
    simp
  have hcompact : IsCompact (T20B.mot K 1 0 '' (rectAB a b).toSet) :=
    (rectAB a b).isCompact_toSet.image (by
      change Continuous (fun x : ℂ => (1 : ℂ) * ((((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) + 0)
      fun_prop)
  have h := measure_crossLenIn_phiMN_motion (ξ := ξ) hW (Nat.zero_le m) u c
    (K := T20B.mot K 1 0 '' (rectAB a b).toSet)
    (A := T20B.mot K 1 0 '' (rectAB a b).side₁)
    (B := T20B.mot K 1 0 '' (rectAB a b).side₂)
    hcompact (S := {v : ℝ≥0∞ | v.toReal ∈ S}) (ENNReal.measurable_toReal hS)
  rw [← he, ← he, ← he] at h
  simpa only [T20B.mrectLen, Set.mem_ofPred_eq] using h

 

theorem laneA2_mrectLen_canonical (ξ : ℝ) (f : ℂ → ℝ) (a b : ℝ) :
    T20B.mrectLen ξ f 3 1 0 a b =
      (rectLen ξ f (rectAB ((1 / 8) * a) ((1 / 8) * b))).toReal := by
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ 3 := by positivity
  unfold T20B.mrectLen
  rw [T20B.mot_image, T20B.mot_image, T20B.mot_image]
  simp only [Circle.coe_one, one_mul, add_zero]
  rw [image_mul_rectAB_toSet hr, image_mul_rectAB_side₁ hr,
    image_mul_rectAB_side₂ hr]
  norm_num [rectLen]

 

theorem laneA2_mrectLen_law_three
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W)
    (m : ℕ) (u : Circle) (c : ℂ) (a b : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 u c a b ∈ S} =
      P {ω | lenObs ξ (phiMN W P 0 m)
        (rectAB ((1 / 8) * a) ((1 / 8) * b)) ω ∈ S} := by
  rw [laneA2_mrectLen_motion hW m 3 u c a b hS]
  simp only [laneA2_mrectLen_canonical, lenObs]

end SupercriticalLQGUniqueness.B2.DG20Conc
