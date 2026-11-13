/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.GradientSup at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.OpenAnnulusFamily




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

def gradientSup (f : ℂ → ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖fderiv ℝ f z‖) '' gradientBox)

private theorem gradientBox_compact : IsCompact gradientBox :=
  isCompact_Icc.reProdIm isCompact_Icc

private theorem gradientBox_nonempty : gradientBox.Nonempty := by
  refine ⟨0, ?_⟩
  simp [gradientBox, Complex.mem_reProdIm]

theorem gradientSup_bound (f : ℂ → ℝ)
    (hfc : ContinuousOn (fun z => fderiv ℝ f z) gradientBox) :
    ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ gradientSup f := by
  intro z hz
  exact le_csSup (gradientBox_compact.bddAbove_image hfc.norm)
    (Set.mem_image_of_mem _ hz)

theorem gradientSup_nonneg (f : ℂ → ℝ)
    (hfc : ContinuousOn (fun z => fderiv ℝ f z) gradientBox) :
    0 ≤ gradientSup f := by
  obtain ⟨z, hz⟩ := gradientBox_nonempty
  exact (norm_nonneg _).trans (gradientSup_bound f hfc z hz)

end SupercriticalLQGUniqueness.Exponent.InwardMap
