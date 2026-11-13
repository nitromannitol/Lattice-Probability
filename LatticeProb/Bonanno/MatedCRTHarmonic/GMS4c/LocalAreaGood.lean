/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaGood at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaSelectionCorrect
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaFinite

/-! The cone GMC samples satisfy the local dyadic selector's good-sample condition. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric QuantumZipper MatedCRTHarmonic.CellScaling MatedCRTHarmonic.MoTPort

private theorem integrable_of_measure_tsupport_lt_top
    {μ : Measure ℂ} {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hμ : μ (tsupport f) < ⊤) :
    Integrable f μ := by
  letI : IsFiniteMeasure (μ.restrict (tsupport f)) := by
    rw [isFiniteMeasure_iff]
    simpa using hμ
  have hint : Integrable f (μ.restrict (tsupport f)) :=
    hf.integrable_of_hasCompactSupport hfc
  exact (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport f)).mp hint

theorem localDyadicGood_of_vague_continuity_finiteness
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (h : DistC)
    (hex : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ)
    (hcont : ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ) h) (dyadicScale k) w) z)
    (hfin : ∀ᶠ k : ℕ in atTop,
      lqgAreaApprox γ h k (closure V) < ⊤) :
    LocalDyadicGood γ V δ (restrictTo (thickOpen V δ) h) := by
  have hv : IsVagueLimitC (lqgAreaApprox γ h) (lqgArea γ h) := by
    have hs := ConeArea.isVagueLimitOn_qAreaC
      (γ := γ) (h := h)
        ⟨hex.choose, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hex.choose_spec⟩
    rw [LQGCone.lqgArea_eq_qAreaC]
    exact LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr hs
  refine ⟨⟨(lqgArea γ h).restrict V,
    isVagueLimitOn_localAreaApproxDy_of_ae_continuous γ V hδ h hcont hex,
    ?_⟩, ?_⟩
  · exact lt_of_le_of_lt
      ((lqgArea γ h).restrict_apply_le V V |>.trans (measure_mono subset_closure))
      (hv.1 _ hVb.isCompact_closure)
  · intro f hf hfc hfV
    obtain ⟨K, hK⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt hδ
    filter_upwards [hfin, hcont, eventually_ge_atTop K]
      with k hk hc hkK
    apply integrable_of_measure_tsupport_lt_top hf hfc
    rw [localAreaApproxDy_eq_localAreaApprox_of_ae_continuous γ V δ _ k hc,
      localAreaApprox_restrictTo γ V δ h k]
    · exact ((lqgAreaApprox γ h k).restrict_apply_le V (tsupport f)).trans_lt
        ((measure_mono (hfV.trans subset_closure)).trans_lt hk)
    · rw [LQGCone.dyadicScale_eq_radius]
      exact hK k hkK

end MatedCRTHarmonic.GMS4c

