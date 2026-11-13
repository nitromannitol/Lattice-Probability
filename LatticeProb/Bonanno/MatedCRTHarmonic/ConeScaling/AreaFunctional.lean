/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.AreaFunctional at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas

/-!
# A measurable version of `h ↦ μ_h(U)` for open bounded `U`

`CellScaling.lqgArea γ h` is the vague limit of the dyadic approximations `lqgAreaApprox γ h k`
, chosen by `Classical.choose` (junk `0` if no limit exists), so `h ↦ lqgArea γ h U` is not
obviously measurable on `DistC`. For an open bounded `U` we define the measurable functional

  `areaOpenFun γ U h = ⨆ₙ limsup_k ofReal (∫ ψ_{U,n} d(lqgAreaApprox γ h k))`

(`ψ_{U,n}` QuantumZipper's continuous bumps increasing to `1_U`), and show that it equals
`lqgArea γ h U` whenever the vague limit exists (`areaOpenFun_eq_lqgArea`). This is the deterministic
form of the ported MoT `ConeMeas.aemeasurable_qAreaC_open` (same bumps, QuantumZipper's
`LQGMeas.measure_open_eq_iSup`). Used to push the field law of DMS Prop 4.13(i) forward to the area of
the unit disk.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.ConeScaling

open LQGMetric MatedCRTHarmonic.CellScaling QuantumZipper

/-- The measurable area functional of an open bounded set. -/
def areaOpenFun (γ : ℝ) (U : Set ℂ) (h : DistC) : ℝ≥0∞ :=
  ⨆ n : ℕ, limsup (fun k => ENNReal.ofReal (∫ z, LQGMeas.openBump U n z ∂lqgAreaApprox γ h k))
    atTop

theorem measurable_areaOpenFun (γ : ℝ) (U : Set ℂ) : Measurable (areaOpenFun γ U) := by
  refine Measurable.iSup fun n => Measurable.limsup fun k => ?_
  have e : (fun h : DistC => ∫ z, LQGMeas.openBump U n z ∂lqgAreaApprox γ h k) =
      fun h => ∫ z, LQGMeas.openBump U n z ∂MoTPort.areaApproxC γ h k := by
    funext h; rw [LQGCone.lqgAreaApprox_eq_areaApproxC]
  have hm := ENNReal.measurable_ofReal.comp (MoTPort.ConeMeas.measurable_integral_areaApproxC γ k
    (LQGMeas.continuous_openBump U n) (LQGMeas.openBump_nonneg U n))
  rw [← e] at hm
  exact hm

/-- If `lqgArea γ h` is a genuine vague limit, the measurable functional computes its mass of `U`. -/
theorem areaOpenFun_eq_lqgArea {γ : ℝ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {h : DistC} (hv : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ) :
    areaOpenFun γ U h = lqgArea γ h U := by
  have hlim : IsVagueLimitC (lqgAreaApprox γ h) (lqgArea γ h) := by
    unfold lqgArea
    rw [dite_eq_left hv]
    exact Classical.choose_spec hv
  have hUc : Uᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : ℂ)
    refine ⟨((|R| + 1 : ℝ) : ℂ), fun hmem => ?_⟩
    have := hR hmem
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  have : IsFiniteMeasureOnCompacts (lqgArea γ h) := ⟨fun K hK => hlim.1 K hK⟩
  rw [LQGMeas.measure_open_eq_iSup _ hU hUc, areaOpenFun]
  congr 1
  funext n
  have hconv := hlim.2 _ (LQGMeas.continuous_openBump U n)
    (LQGMeas.hasCompactSupport_openBump hUb n)
  have hconv' : Tendsto (fun k => ENNReal.ofReal
      (∫ z, LQGMeas.openBump U n z ∂lqgAreaApprox γ h k)) atTop
      (𝓝 (ENNReal.ofReal (∫ z, LQGMeas.openBump U n z ∂lqgArea γ h))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hconv
  rw [hconv'.limsup_eq]
  exact ofReal_integral_eq_lintegral_ofReal
    ((LQGMeas.continuous_openBump U n).integrable_of_hasCompactSupport
      (LQGMeas.hasCompactSupport_openBump hUb n))
    (ae_of_all _ fun z => LQGMeas.openBump_nonneg U n z)

/-- A nonzero `lqgArea` is a genuine vague limit (the junk value is `0`). -/
theorem exists_isVagueLimitC_of_lqgArea_ne_zero {γ : ℝ} {h : DistC} {U : Set ℂ}
    (hU : lqgArea γ h U ≠ 0) : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ := by
  by_contra hv
  apply hU
  unfold lqgArea
  rw [dite_eq_right hv]
  rfl

end MatedCRTHarmonic.ConeScaling
