/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4BadKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4BadProbability

 








set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA4_bad_kernel_max_square_le
    {Ω ι : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) (s : Finset ι) (hs : s.Nonempty)
    (E : Set Ω) (hE : MeasurableSet E)
    (Y : ι → Ω → ℝ≥0∞)
    (hY : ∀ i ∈ s, Measurable (Y i))
    {δ H : ℝ≥0∞} (hbad : P Eᶜ ≤ δ)
    (hsecond :
      (∫⁻ ω, (s.sup' hs (fun i =>
        ∫⁻ x, Y i x ^ (2 : ℝ) ∂(condExpKernel P m ω))) ^
          (2 : ℝ) ∂P) ≤ H) :
    (∫⁻ ω, (s.sup' hs (fun i =>
      ∫⁻ x, (Eᶜ).indicator (Y i) x
        ∂(condExpKernel P m ω))) ^ (2 : ℝ) ∂P) ≤
      δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) := by
  let κ := condExpKernel P m
  let q : Ω → ℝ≥0∞ := fun ω => (κ ω) Eᶜ
  let M : Ω → ℝ≥0∞ := fun ω => s.sup' hs
    (fun i => ∫⁻ x, Y i x ^ (2 : ℝ) ∂(κ ω))
  let B : Ω → ℝ≥0∞ := fun ω => s.sup' hs
    (fun i => ∫⁻ x, (Eᶜ).indicator (Y i) x ∂(κ ω))
  obtain ⟨hqm, hq1, hqmean⟩ :=
    laneA4_conditional_bad_probability P hm E hE
  have hMm : Measurable M := by
    have hf : Measurable (s.sup' hs (fun i ω =>
        ∫⁻ x, Y i x ^ (2 : ℝ) ∂(κ ω))) := by
      apply Finset.measurable_sup' hs
      intro i hi
      exact ((hY i hi).pow_const (2 : ℝ)).lintegral_kernel.mono hm le_rfl
    have heq : (s.sup' hs (fun i ω =>
        ∫⁻ x, Y i x ^ (2 : ℝ) ∂(κ ω))) = M := by
      funext ω
      simp only [Finset.sup'_apply, M]
    exact heq ▸ hf
  have hpoint (ω : Ω) : B ω ^ (2 : ℝ) ≤ q ω * M ω := by
    have hholder := laneA4_bad_max_conditional_holder
      (κ ω) s hs E hE Y
      (fun i hi => (hY i hi).aemeasurable)
    have hsq := ENNReal.rpow_le_rpow hholder
      (by norm_num : (0 : ℝ) ≤ 2)
    have hpow :
        ((q ω) ^ (1 / 2 : ℝ) * (M ω) ^ (1 / 2 : ℝ)) ^
            (2 : ℝ) = q ω * M ω := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num
    exact hsq.trans_eq hpow
  exact laneA4_bad_max_L2_of_conditional_moments P q M B
    hqm.aemeasurable hMm.aemeasurable hq1 hpoint
    (hqmean.trans_le hbad) hsecond

end SupercriticalLQGUniqueness.B2.DG20Conc
