/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4BadMax at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTripleHolder
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondIndepMoment
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiBlock
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundMeas
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BMom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConditionalHolder
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelAeMono
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1MaxLogMoment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConcaveMoment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPowerRate
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMain
import Mathlib.MeasureTheory.Integral.MeanInequalities

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

private theorem laneA4_two_holder : (2 : ℝ).HolderConjugate 2 := by
  exact Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

 

theorem laneA4_bad_max_conditional_holder
    {Ω ι : Type*} [MeasurableSpace Ω]
    (κ : Measure Ω) (s : Finset ι) (hs : s.Nonempty)
    (E : Set Ω) (hE : MeasurableSet E)
    (Y : ι → Ω → ℝ≥0∞)
    (hY : ∀ i ∈ s, AEMeasurable (Y i) κ) :
    s.sup' hs (fun i => ∫⁻ x, (Eᶜ).indicator (Y i) x ∂κ) ≤
      (κ Eᶜ) ^ (1 / 2 : ℝ) *
        (s.sup' hs (fun i => ∫⁻ x, Y i x ^ (2 : ℝ) ∂κ)) ^
          (1 / 2 : ℝ) := by
  classical
  apply Finset.sup'_le
  intro i hi
  have hInd : AEMeasurable ((Eᶜ).indicator (fun _ : Ω => (1 : ℝ≥0∞))) κ :=
    Measurable.aemeasurable ((measurable_const.indicator hE.compl))
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq κ
    laneA4_two_holder hInd (hY i hi)
  have hpoint :
      (fun x => (Eᶜ).indicator (fun _ : Ω => (1 : ℝ≥0∞)) x * Y i x) =
        (Eᶜ).indicator (Y i) := by
    funext x
    by_cases hx : x ∈ Eᶜ <;> simp [hx]
  simp only [Pi.mul_apply] at hCS
  rw [hpoint] at hCS
  have hpower :
      (fun x => ((Eᶜ).indicator (fun _ : Ω => (1 : ℝ≥0∞)) x) ^
        (2 : ℝ)) = (Eᶜ).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Eᶜ <;> simp [hx]
  rw [hpower] at hCS
  have hone : (∫⁻ x, (Eᶜ).indicator
      (fun _ : Ω => (1 : ℝ≥0∞)) x ∂κ) = κ Eᶜ :=
    lintegral_indicator_one hE.compl
  rw [hone] at hCS
  exact hCS.trans (by
    gcongr
    exact Finset.le_sup' (s := s)
      (f := fun j => ∫⁻ x, Y j x ^ (2 : ℝ) ∂κ) hi)

 


theorem laneA4_bad_max_L2_of_conditional_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q M B : Ω → ℝ≥0∞)
    (hq : AEMeasurable q P) (hM : AEMeasurable M P)
    (hq1 : ∀ ω, q ω ≤ 1)
    (hpoint : ∀ ω, B ω ^ (2 : ℝ) ≤ q ω * M ω)
    {δ H : ℝ≥0∞}
    (hprob : (∫⁻ ω, q ω ∂P) ≤ δ)
    (hC2 : (∫⁻ ω, M ω ^ (2 : ℝ) ∂P) ≤ H) :
    (∫⁻ ω, B ω ^ (2 : ℝ) ∂P) ≤
      δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) := by
  have hqSq (ω : Ω) : q ω ^ (2 : ℝ) ≤ q ω := by
    rw [ENNReal.rpow_two, pow_two]
    calc
      q ω * q ω ≤ q ω * 1 := by gcongr; exact hq1 ω
      _ = q ω := mul_one _
  have hq2 : (∫⁻ ω, q ω ^ (2 : ℝ) ∂P) ≤ δ :=
    (lintegral_mono hqSq).trans hprob
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq P
    laneA4_two_holder hq hM
  calc
    (∫⁻ ω, B ω ^ (2 : ℝ) ∂P) ≤
        ∫⁻ ω, q ω * M ω ∂P := lintegral_mono hpoint
    _ ≤ (∫⁻ ω, q ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, M ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
        simpa only [Pi.mul_apply] using hholder
    _ ≤ δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) := by gcongr

end SupercriticalLQGUniqueness.B2.DG20Conc
