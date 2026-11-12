/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4Vague at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Final
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueOpenExist

/-!
# A.s. vague convergence of the white-noise approximations (P2-GMCID4, item 4a)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 656–665): "the sequence (eq-03172018-a) almost surely
weakly converges … the limit is precisely `M_γ`". With
`wnMeas W γ n ω = CR^{γ²/2} e^{γ h̃_{2^{-n}} − γ²/2 Var h̃_{2^{-n}}} dz` (the measure of
`GMCIdent.wnGMC`), **`ae_isVagueLimitOn_wnMeas`**: a.s. `wnMeas W γ n ω → M_γ` vaguely on `𝕍`,
for the white-noise field. From `ae_tendsto_wnGMC_wnField` on the countable family
`sqCut n · g` (`g ∈ denseF`), a.s. finiteness of the masses of compact sets
(`integrable_wnDens_wn`), QZ `VagueOpen.exists_isVagueLimitOn_of_cutoff` (existence of a vague
limit from countably many test functions) and `VagueOpen.eq_of_integral_cutoff_eq` (uniqueness).
Since vague convergence holds for all test functions on one full-measure set, it applies to
random test functions pathwise (this is used for the factorization `M_γ = e^{γh̃_δ} M̃_{γ,δ}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent4

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

/-- the density `CR^{γ²/2} e^{γ h̃_{2^{-n}}(z) − γ²/2 Var h̃_{2^{-n}}(z)}` of the white-noise
approximation -/
def wnDens (W : WNSpace → Ω' → ℝ) (γ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω') : ℝ :=
  wnWeight γ n z * Real.exp (γ * tildeVer W n z ω)

omit [MeasurableSpace Ω'] in
lemma wnDens_nonneg (γ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω') : 0 ≤ wnDens W γ n z ω :=
  mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

lemma measurable_wnDens (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) (ω : Ω') :
    Measurable fun z => wnDens W γ n z ω :=
  (measurable_wnWeight hW γ n).mul (Real.measurable_exp.comp
    (((measurable_tildeVer' hW n).comp (measurable_id.prodMk measurable_const)).const_mul γ))

/-- the white-noise approximation of the LQG measure (DZZ (eq-03172018-a)) -/
def wnMeas (W : WNSpace → Ω' → ℝ) (γ : ℝ) (n : ℕ) (ω : Ω') : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (wnDens W γ n z ω)

lemma integral_wnMeas (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) (f : ℂ → ℝ) (ω : Ω') :
    ∫ z, f z ∂(wnMeas W γ n ω) = wnGMC W γ n f ω := by
  unfold wnMeas wnGMC
  have hm : Measurable fun z => (wnDens W γ n z ω).toNNReal :=
    (measurable_wnDens hW γ n ω).real_toNNReal
  change ∫ z, f z ∂(volume.withDensity fun z => ((wnDens W γ n z ω).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (wnDens_nonneg γ n z ω)]
  rw [mul_comm]; rfl

/-- a.s. the approximations are finite on the squares `sqIn s` -/
lemma ae_wnMeas_sqIn_lt_top (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W)
    (γ : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) : ∀ᵐ ω ∂P', wnMeas W γ n ω (sqIn s) < ∞ := by
  have hP := hW.isProbabilityMeasure
  have hSm : MeasurableSet (sqIn s) := (isClosed_sqIn s).measurableSet
  filter_upwards [(integrable_wnDens_wn hX hW γ n hs).prod_right_ae] with ω h
  rw [wnMeas, withDensity_apply _ hSm]
  have h' := h.hasFiniteIntegral
  unfold HasFiniteIntegral at h'
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun z => ?_)) h'
  rw [Real.enorm_eq_ofReal_abs]
  exact congrArg ENNReal.ofReal (abs_of_nonneg (wnDens_nonneg γ n z ω)).symm

lemma exists_sqCut_eq_one {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare) :
    ∃ n, ∀ z ∈ K, sqCut n z = 1 := by
  obtain ⟨s, hs, hKs⟩ := exists_sqIn_of_isCompact hK hKU
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / s)
  refine ⟨n, fun z hz => sqCut_eq_one ?_⟩
  obtain ⟨a, b, c, d⟩ := hKs hz
  have : 2 / ((n : ℝ) + 2) ≤ s := by
    rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hs] at hn; nlinarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **a.s. vague convergence of the white-noise approximations to `M_γ`** (DZZ l. 656–665) -/
theorem ae_isVagueLimitOn_wnMeas [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', IsVagueLimitOn openSquare (fun n => wnMeas W γ n ω)
      (qAreaMeasureOn γ (wnField W ω) openSquare) := by
  have : Countable denseF := denseF_countable.to_subtype
  have htest : ∀ (m : ℕ) (g : denseF), Continuous (fun z => sqCut m z * g.1 z) ∧
      HasCompactSupport (fun z => sqCut m z * g.1 z) ∧
      tsupport (fun z => sqCut m z * g.1 z) ⊆ openSquare := fun m g =>
    ⟨(continuous_sqCut m).mul (denseF_dense.1 g.1 g.2).1,
      (hasCompactSupport_sqCut m).mul_right,
      (tsupport_mul_subset_left).trans (tsupport_sqCut_subset_openSquare m)⟩
  have hconv : ∀ᵐ ω ∂P', ∀ (m : ℕ) (g : denseF),
      Tendsto (fun n => wnGMC W γ n (fun z => sqCut m z * g.1 z) ω) atTop
        (𝓝 (∫ z, sqCut m z * g.1 z ∂(qAreaMeasureOn γ (wnField W ω) openSquare))) :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun g =>
      ae_tendsto_wnGMC_wnField hX hW hγ hγ2 (htest m g).1 (htest m g).2.1 (htest m g).2.2
  have hfin : ∀ᵐ ω ∂P', ∀ m n : ℕ, wnMeas W γ n ω (sqIn (1 / ((m : ℝ) + 1))) < ∞ :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun n =>
      ae_wnMeas_sqIn_lt_top hX hW γ n (by positivity)
  filter_upwards [hconv, hfin, ae_isVagueLimitOn_wn hX hW hγ hγ2] with ω hc hf hM
  have hfin' : ∀ K, IsCompact K → K ⊆ openSquare → ∀ᶠ k in atTop, wnMeas W γ k ω K < ∞ := by
    intro K hK hKU
    obtain ⟨s, hs, hKs⟩ := exists_sqIn_of_isCompact hK hKU
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / s)
    have hsub : K ⊆ sqIn (1 / ((m : ℝ) + 1)) := hKs.trans fun z ⟨a, b, c, d⟩ => by
      have : 1 / ((m : ℝ) + 1) ≤ s := by
        rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hs] at hm; nlinarith
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    exact Eventually.of_forall fun k => (measure_mono hsub).trans_lt (hf m k)
  have hc' : ∀ m, ∀ g ∈ denseF, Tendsto (fun k => ∫ z, sqCut m z * g z ∂(wnMeas W γ k ω)) atTop
      (𝓝 (∫ z, sqCut m z * g z ∂(qAreaMeasureOn γ (wnField W ω) openSquare))) := by
    intro m g hg
    simp_rw [integral_wnMeas hW]
    exact hc m ⟨g, hg⟩
  obtain ⟨μ, hμ⟩ := VagueOpen.exists_isVagueLimitOn_of_cutoff isOpen_openSquare openSquare_subset_H
    continuous_sqCut sqCut_nonneg sqCut_le_one tsupport_sqCut_subset_openSquare
    (fun K hK hKU => exists_sqCut_eq_one hK hKU) denseF_dense hfin' fun m g hg => ⟨_, hc' m g hg⟩
  have he : μ = qAreaMeasureOn γ (wnField W ω) openSquare := by
    refine VagueOpen.eq_of_integral_cutoff_eq isOpen_openSquare openSquare_subset_H
      continuous_sqCut sqCut_nonneg sqCut_le_one tsupport_sqCut_subset_openSquare
      (fun K hK hKU => exists_sqCut_eq_one hK hKU) denseF_dense hμ.1 hM.1 hμ.2.1 hM.2.1
      fun m g hg => ?_
    have h1 := hμ.2.2 _ (htest m ⟨g, hg⟩).1 (htest m ⟨g, hg⟩).2.1 (htest m ⟨g, hg⟩).2.2
    exact tendsto_nhds_unique h1 (hc' m g hg)
  rw [← he]
  exact hμ

end GMCIdent4
end LQGMetric
