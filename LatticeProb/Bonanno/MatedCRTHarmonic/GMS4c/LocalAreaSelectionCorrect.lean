/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaSelectionCorrect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaSelection
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaLimit

/-! Identification of the Borel local GMC selector on regular samples. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.CellScaling MatedCRTHarmonic.MoTPort QuantumZipper

/-- Vague convergence does not change if the approximating measures agree
from some index onward. -/
theorem isVagueLimitOn_of_eventuallyEq
    {V : Set ℂ} {a b : ℕ → Measure ℂ} {μ : Measure ℂ}
    (heq : a =ᶠ[atTop] b) (ha : IsVagueLimitOn V a μ) :
    IsVagueLimitOn V b μ := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro f hf hfc hfV
  apply (ha.2.2 f hf hfc hfV).congr'
  filter_upwards [heq] with k hk
  exact congrArg (fun ν : Measure ℂ => ∫ z, f z ∂ν) hk

theorem isVagueLimitOn_localAreaApproxDy_of_ae_continuous
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ)
    (h : DistC)
    (hcont : ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ) h) (dyadicScale k) w) z)
    (hex : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ) :
    IsVagueLimitOn V (localAreaApproxDy γ V δ
      (restrictTo (thickOpen V δ) h)) ((lqgArea γ h).restrict V) := by
  have hv : IsVagueLimitC (lqgAreaApprox γ h) (lqgArea γ h) := by
    have hs := ConeArea.isVagueLimitOn_qAreaC
      (γ := γ) (h := h)
        ⟨hex.choose, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hex.choose_spec⟩
    rw [LQGCone.lqgArea_eq_qAreaC]
    exact LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr hs
  have hraw : IsVagueLimitOn V (areaApproxC γ h) ((lqgArea γ h).restrict V) :=
    AtomlessUncond.isVagueLimitOn_restrict V.isOpen (subset_univ _)
      (LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hv)
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt hδ
  have heq : (fun k => localAreaApproxDy γ V δ
      (restrictTo (thickOpen V δ) h) k) =ᶠ[atTop]
      (fun k => (areaApproxC γ h k).restrict V) := by
    filter_upwards [eventually_ge_atTop K, hcont] with k hk hc
    rw [localAreaApproxDy_eq_localAreaApprox_of_ae_continuous
      γ V δ _ k hc, localAreaApprox_restrictTo γ V δ h k]
    · exact congrArg (fun μ : Measure ℂ => μ.restrict V)
        (LQGCone.lqgAreaApprox_eq_areaApproxC γ h k)
    · rw [LQGCone.dyadicScale_eq_radius]
      exact hK k hk
  have hlim : IsVagueLimitOn V (fun k => (areaApproxC γ h k).restrict V)
      ((lqgArea γ h).restrict V) := by
    refine ⟨hraw.1, hraw.2.1, ?_⟩
    intro f hf hfc hfV
    have hf0 : ∀ z ∉ (V : Set ℂ), f z = 0 :=
      fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hfV h)
    have hInt : (fun k => ∫ z, f z ∂(areaApproxC γ h k).restrict V) =
        fun k => ∫ z, f z ∂areaApproxC γ h k := by
      funext k
      exact setIntegral_eq_integral_of_forall_compl_eq_zero hf0
    rw [hInt]
    exact hraw.2.2 f hf hfc hfV
  exact isVagueLimitOn_of_eventuallyEq heq.symm hlim

/-- If the dyadic local approximants agree with the raw ones almost
everywhere at each scale, their selected limit is the actual GMC area
restricted to `V`. -/
theorem localAreaVagueSelection_eq_lqgArea_of_ae_continuous
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ)
    (h : DistC) (hgood : LocalDyadicGood γ V δ (restrictTo (thickOpen V δ) h))
    (hcont : ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ) h) (dyadicScale k) w) z)
    (hex : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ) :
    localAreaVagueSelection γ V δ (restrictTo (thickOpen V δ) h) =
      (lqgArea γ h).restrict V := by
  have hv : IsVagueLimitC (lqgAreaApprox γ h) (lqgArea γ h) := by
    have hs := ConeArea.isVagueLimitOn_qAreaC
      (γ := γ) (h := h)
        ⟨hex.choose, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hex.choose_spec⟩
    rw [LQGCone.lqgArea_eq_qAreaC]
    exact LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr hs
  have hraw : IsVagueLimitOn V (areaApproxC γ h) ((lqgArea γ h).restrict V) :=
    AtomlessUncond.isVagueLimitOn_restrict V.isOpen (subset_univ _)
      (LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hv)
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt hδ
  have heq : (fun k => localAreaApproxDy γ V δ
      (restrictTo (thickOpen V δ) h) k) =ᶠ[atTop]
      (fun k => (areaApproxC γ h k).restrict V) := by
    filter_upwards [eventually_ge_atTop K, hcont] with k hk hc
    rw [localAreaApproxDy_eq_localAreaApprox_of_ae_continuous
      γ V δ _ k hc, localAreaApprox_restrictTo γ V δ h k]
    · exact congrArg (fun μ : Measure ℂ => μ.restrict V)
        (LQGCone.lqgAreaApprox_eq_areaApproxC γ h k)
    · rw [LQGCone.dyadicScale_eq_radius]
      exact hK k hk
  have hlim : IsVagueLimitOn V (fun k => (areaApproxC γ h k).restrict V)
      ((lqgArea γ h).restrict V) := by
    refine ⟨hraw.1, hraw.2.1, ?_⟩
    intro f hf hfc hfV
    have hf0 : ∀ z ∉ (V : Set ℂ), f z = 0 :=
      fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hfV h)
    have hInt : (fun k => ∫ z, f z ∂(areaApproxC γ h k).restrict V) =
        fun k => ∫ z, f z ∂areaApproxC γ h k := by
      funext k
      exact setIntegral_eq_integral_of_forall_compl_eq_zero hf0
    rw [hInt]
    exact hraw.2.2 f hf hfc hfV
  exact isVagueLimitOn_unique V.isOpen
    (isVagueLimitOn_of_eventuallyEq heq (localAreaVagueSelection_spec hgood).1) hlim

end MatedCRTHarmonic.GMS4c

