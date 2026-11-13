/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaApprox
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond

/-! The selected dyadic GMC vague limit is determined by the field on a thickening. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.CellScaling MatedCRTHarmonic.MoTPort QuantumZipper

theorem vagueLimitC_restrict_eq_of_localField_eq
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ)
    {h h' : DistC} (hlocal : restrictTo (thickOpen V δ) h =
      restrictTo (thickOpen V δ) h')
    {μ μ' : Measure ℂ}
    (hμ : IsVagueLimitC (lqgAreaApprox γ h) μ)
    (hμ' : IsVagueLimitC (lqgAreaApprox γ h') μ') :
    μ.restrict V = μ'.restrict V := by
  have hlim : IsVagueLimitOn V (areaApproxC γ h) (μ.restrict V) :=
    AtomlessUncond.isVagueLimitOn_restrict V.isOpen (subset_univ _)
      (LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hμ)
  have hlim' : IsVagueLimitOn V (areaApproxC γ h') (μ'.restrict V) :=
    AtomlessUncond.isVagueLimitOn_restrict V.isOpen (subset_univ _)
      (LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hμ')
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt hδ
  have happrox : ∀ k, K ≤ k →
      (areaApproxC γ h k).restrict V = (areaApproxC γ h' k).restrict V := by
    intro k hk
    have hsmall : dyadicScale k < δ := by
      rw [LQGCone.dyadicScale_eq_radius]
      exact hK k hk
    rw [← LQGCone.lqgAreaApprox_eq_areaApproxC,
      ← LQGCone.lqgAreaApprox_eq_areaApproxC,
      ← localAreaApprox_restrictTo γ V δ h k hsmall,
      ← localAreaApprox_restrictTo γ V δ h' k hsmall, hlocal]
  have hlim₀ : IsVagueLimitOn V (areaApproxC γ h') (μ.restrict V) := by
    refine ⟨hlim.1, hlim.2.1, ?_⟩
    intro f hf hfc hfV
    have hevent : (fun k => ∫ z, f z ∂(areaApproxC γ h k)) =ᶠ[atTop]
        (fun k => ∫ z, f z ∂(areaApproxC γ h' k)) := by
      filter_upwards [eventually_ge_atTop K] with k hk
      have hf0 : ∀ z ∉ (V : Set ℂ), f z = 0 :=
        fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hfV h)
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := areaApproxC γ h k) hf0,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := areaApproxC γ h' k) hf0,
        happrox k hk]
    exact (hlim.2.2 f hf hfc hfV).congr' hevent
  exact isVagueLimitOn_unique V.isOpen hlim₀ hlim'

/-- On the locus where both dyadic GMC limits exist, the selected area measure on `V`
depends only on the field restricted to the `δ`-thickening of `V`. -/
theorem lqgArea_restrict_eq_of_localField_eq
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ)
    {h h' : DistC} (hlocal : restrictTo (thickOpen V δ) h =
      restrictTo (thickOpen V δ) h')
    (hex : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ)
    (hex' : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h') μ) :
    (lqgArea γ h).restrict V = (lqgArea γ h').restrict V := by
  apply vagueLimitC_restrict_eq_of_localField_eq γ V hδ hlocal
  · have hv := ConeArea.isVagueLimitOn_qAreaC
      (γ := γ) (h := h) ⟨hex.choose, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hex.choose_spec⟩
    rw [LQGCone.lqgArea_eq_qAreaC]
    exact LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr hv
  · have hv := ConeArea.isVagueLimitOn_qAreaC
      (γ := γ) (h := h') ⟨hex'.choose, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hex'.choose_spec⟩
    rw [LQGCone.lqgArea_eq_qAreaC]
    exact LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr hv

end MatedCRTHarmonic.GMS4c

