import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.LQG.LQGMeasure

/-!
# Local vague limits of circle-average approximations of the LQG measure

Vague convergence on an open set `U` (`QuantumZipper.IsVagueLimitOn U`) only sees the
approximating measures through their restrictions to `U`. We record three consequences.

* `LatticeProb.LQG.isVagueLimitOn_congr_restrict`: approximations with the same restrictions to
  `U` have the same vague limits on `U`.
* `LatticeProb.LQG.isVagueLimitOn_withDensity_of_areaApprox`: on an open subset of the upper
  half-plane, the half-plane approximations `areaApprox γ x k` of the `γ`-LQG measure may be
  replaced by the Lebesgue measure with density `2^{-kγ²/2} e^{γ x_{2^{-k}}(z)}` on all of `ℂ`;
  `LatticeProb.LQG.ae_isVagueLimitOn_withDensity_avgReg_wnField` is the almost sure statement for
  the white-noise zero-boundary Gaussian free field of the unit square (Ding-Zeitouni-Zhang).
* `LatticeProb.LQG.IsLQGLimit.isVagueLimitOn_restrict`: a vague limit on `ℂ` of the
  approximations `ε^{γ²/2} e^{γ h_ε(z)} dz` along the dyadic scales restricts to a vague limit on
  every open set.
-/

open MeasureTheory Filter Topology Set

namespace LQGMetric

open QuantumZipper GMCIdent3 GMCIdent WhiteNoise

/-- The dyadic scale `2^{-k}` is the radius `2^{-k}` of the circle-average process. -/
theorem _root_.LatticeProb.LQG.dyadicScale_eq_radius (k : ℕ) :
    LatticeProb.LQG.dyadicScale k = QuantumZipper.radius k := rfl

/-- Approximating sequences with the same restrictions to a set `U` have the same vague limits
on `U`. -/
theorem _root_.LatticeProb.LQG.isVagueLimitOn_congr_restrict {U : Set ℂ}
    {μs νs : ℕ → Measure ℂ} {μ : Measure ℂ} (hμν : ∀ k, (μs k).restrict U = (νs k).restrict U)
    (h : IsVagueLimitOn U μs μ) : IsVagueLimitOn U νs μ := by
  refine ⟨h.1, h.2.1, fun f hf hfc hfU => ?_⟩
  have e : ∀ ν : Measure ℂ, ∫ z, f z ∂(ν.restrict U) = ∫ z, f z ∂ν := fun ν =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      image_eq_zero_of_notMem_tsupport fun h' => hz (hfU h')
  refine (h.2.2 f hf hfc hfU).congr fun k => ?_
  rw [← e (μs k), hμν k, e]

/-- On a measurable subset `U` of the upper half-plane, the half-plane approximation
`areaApprox γ x k` of the `γ`-LQG measure coincides with the Lebesgue measure with density
`2^{-kγ²/2} e^{γ x_{2^{-k}}(z)}`. -/
theorem _root_.LatticeProb.LQG.areaApprox_restrict_eq {U : Set ℂ} (hU : MeasurableSet U)
    (hUH : U ⊆ QuantumZipper.H) (γ : ℝ) (x : FieldSample) (k : ℕ) :
    (areaApprox γ x k).restrict U =
      (volume.withDensity fun z =>
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k z))).restrict U := by
  rw [areaApprox, restrict_withDensity hU, restrict_withDensity hU, Measure.restrict_restrict hU,
    inter_eq_left.mpr hUH]

/-- A vague limit on an open subset `U` of the upper half-plane of the half-plane approximations
`areaApprox γ x k` is also the vague limit on `U` of the Lebesgue measures with densities
`2^{-kγ²/2} e^{γ x_{2^{-k}}(z)}`. -/
theorem _root_.LatticeProb.LQG.isVagueLimitOn_withDensity_of_areaApprox {U : Set ℂ}
    (hU : MeasurableSet U) (hUH : U ⊆ QuantumZipper.H) {γ : ℝ} {x : FieldSample}
    {μ : Measure ℂ} (h : IsVagueLimitOn U (areaApprox γ x) μ) :
    IsVagueLimitOn U (fun k => volume.withDensity fun z =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k z))) μ :=
  LatticeProb.LQG.isVagueLimitOn_congr_restrict
    (fun k => LatticeProb.LQG.areaApprox_restrict_eq hU hUH γ x k) h

/-- **Ding-Zeitouni-Zhang, white-noise form.** For the white-noise zero-boundary Gaussian free
field of the open unit square and `0 < γ < 2`, almost surely the Lebesgue measures with densities
`2^{-kγ²/2} e^{γ h_{2^{-k}}(z)}` converge vaguely on the open unit square to the `γ`-LQG measure
of the field there. -/
theorem _root_.LatticeProb.LQG.ae_isVagueLimitOn_withDensity_avgReg_wnField
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ} [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', IsVagueLimitOn openSquare (fun k => volume.withDensity fun z =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (wnField W ω) k z)))
      (qAreaMeasureOn γ (wnField W ω) openSquare) := by
  filter_upwards [ae_isVagueLimitOn_wn hX hW hγ hγ2] with ω hω
  exact LatticeProb.LQG.isVagueLimitOn_withDensity_of_areaApprox isOpen_openSquare.measurableSet
    openSquare_subset_H hω

/-- A vague limit on `ℂ` of the approximations `ε^{γ²/2} e^{γ h_ε(z)} dz` along the dyadic scales
restricts to a vague limit on every open set `U`. -/
theorem _root_.LatticeProb.LQG.IsLQGLimit.isVagueLimitOn_restrict {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {m : Measure ℂ} (h : LatticeProb.LQG.IsLQGLimit γ hε m) {U : Set ℂ} (hU : IsOpen U) :
    IsVagueLimitOn U (fun k => LatticeProb.LQG.lqgApprox γ hε (LatticeProb.LQG.dyadicScale k))
      (m.restrict U) :=
  haveI := h.isLocallyFiniteMeasure
  MatedCRTHarmonic.GMCFacts.isVagueLimitOn_restrict hU (fun _ hK => hK.measure_lt_top)
    h.tendsto_integral

end LQGMetric
