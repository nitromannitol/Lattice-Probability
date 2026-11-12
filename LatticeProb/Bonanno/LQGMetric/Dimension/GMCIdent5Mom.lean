/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent5Mom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Ind
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMass
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FiniteArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments

/-!
# First moment of `M̃_{γ,δ}` and the moment bound (eq-LQG-positive-moment) for `0 < p ≤ 1`
(P2-GMCID5, item 2, part)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 684–688): for `B ⊆ 𝕍` a square or a ball of
diameter `ξ`, `E (ξ^{-2} M̃_{γ,δ}(B))^p ≤ C_{γ,p}` for `0 < p < 4/γ²` and `δ ≤ ξ`
(eq-LQG-positive-moment). Here, for `δ = 2^{-m}`:

* `lintegral_fineDens` : `E[e^{γ h̃^δ_ε(z) − γ²/2 Var h̃^δ_ε(z)}] = 1`;
* **`lintegral_tildeM_le`** : `E M̃_{γ,δ}(U) ≤ Leb(U)` for every open `U ⊆ 𝕍`
  (Fatou along the band approximations, tested against `ramp U n · sqCut n ↑ 1_U`, as in
  QZ `FinArea.rpow_le_liminf_of_isVagueLimitOn`; the first-moment computation of Rhodes–Vargas
  arXiv:1305.6221 §2 and Berestycki arXiv:1506.09113 §2);
* **`lintegral_tildeM_rpow_le`** : (eq-LQG-positive-moment) for `0 < p ≤ 1` with
  `C_{γ,p} = π^p`, for every open `U ⊆ 𝕍` contained in a closed ball of radius `ξ` (in particular
  open squares and balls of diameter `ξ`), any `δ = 2^{-m}` (Jensen). The range
  `1 < p < 4/γ²` and the negative moments are not done here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent5

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 GMCIdent4

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

/-- **the band density has mean one** -/
lemma lintegral_fineDens (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal (fineDens W γ m n z ω) ∂P' = 1 := by
  set κ := wndKernelL2 openSquare (Ioo (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ m) ^ 2)) z
  have hV : Var[tildeH W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) z; P'] = Real.pi * ‖κ‖ ^ 2 :=
    variance_sqrtPi_wn hW κ
  have he : (fun ω => fineDens W γ m n z ω) =ᵐ[P'] fun ω =>
      Real.exp (-(γ ^ 2 / 2 * (Real.pi * ‖κ‖ ^ 2))) *
        Real.exp ((γ * Real.sqrt Real.pi) * W κ ω) := by
    filter_upwards [bandDens_eq_fineDens_ae hW γ hmn z, bandDens_ae_eq hW γ hmn z] with ω h1 h2
    rw [← h1, h2, hV, ← Real.exp_add]
    simp only [tildeH, DZZ.wnField]
    congr 1; ring
  have hint : Integrable (fun ω => Real.exp (-(γ ^ 2 / 2 * (Real.pi * ‖κ‖ ^ 2))) *
      Real.exp ((γ * Real.sqrt Real.pi) * W κ ω)) P' :=
    (integrable_exp_wn hW _ κ).const_mul _
  have he' : (fun ω => ENNReal.ofReal (fineDens W γ m n z ω)) =ᵐ[P'] fun ω =>
      ENNReal.ofReal (Real.exp (-(γ ^ 2 / 2 * (Real.pi * ‖κ‖ ^ 2))) *
        Real.exp ((γ * Real.sqrt Real.pi) * W κ ω)) := he.mono fun ω h => congrArg ENNReal.ofReal h
  rw [lintegral_congr_ae he', ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun ω => by positivity), integral_const_mul, integral_exp_wn hW,
    ← Real.exp_add]
  have : -(γ ^ 2 / 2 * (Real.pi * ‖κ‖ ^ 2)) + (γ * Real.sqrt Real.pi) ^ 2 / 2 * ‖κ‖ ^ 2 = 0 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring
  rw [this, Real.exp_zero, ENNReal.ofReal_one]

/-- the test functions `ramp U n · sqCut n ↑ 1_U` -/
def cutRamp (U : Set ℂ) (n : ℕ) (z : ℂ) : ℝ := FinArea.ramp U n z * sqCut n z

lemma continuous_cutRamp (U : Set ℂ) (n : ℕ) : Continuous (cutRamp U n) :=
  (FinArea.continuous_ramp U n).mul (continuous_sqCut n)

lemma hasCompactSupport_cutRamp (U : Set ℂ) (n : ℕ) : HasCompactSupport (cutRamp U n) :=
  (hasCompactSupport_sqCut n).mul_left

lemma tsupport_cutRamp (U : Set ℂ) (n : ℕ) : tsupport (cutRamp U n) ⊆ openSquare :=
  (tsupport_mul_subset_right (f := FinArea.ramp U n)).trans (tsupport_sqCut_subset_openSquare n)

lemma cutRamp_nonneg (U : Set ℂ) (n : ℕ) (z : ℂ) : 0 ≤ cutRamp U n z :=
  mul_nonneg (FinArea.ramp_nonneg U n z) (sqCut_nonneg n z)

lemma cutRamp_le_one (U : Set ℂ) (n : ℕ) (z : ℂ) : cutRamp U n z ≤ 1 :=
  mul_le_one₀ (FinArea.ramp_le_one U n z) (sqCut_nonneg n z) (sqCut_le_one n z)

lemma cutRamp_mono (U : Set ℂ) (z : ℂ) : Monotone fun n => cutRamp U n z := fun _ _ h =>
  mul_le_mul (FinArea.ramp_mono U z h) (sqCut_mono z h) (sqCut_nonneg _ z)
    (FinArea.ramp_nonneg U _ z)

lemma iSup_cutRamp {U : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ openSquare) (z : ℂ) :
    ⨆ n, ENNReal.ofReal (cutRamp U n z) = U.indicator 1 z := by
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz, Pi.one_apply]
    have hne : Uᶜ.Nonempty := ⟨0, fun h0 => by
      have := hUV h0
      simp [openSquare] at this⟩
    obtain ⟨a, ha⟩ := FinArea.exists_ramp_eq_one hU hne hz
    obtain ⟨b, hb⟩ := exists_sqCut_eq_one isCompact_singleton (singleton_subset_iff.2 (hUV hz))
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_one.2 (cutRamp_le_one U n z))
      (le_iSup_of_le (max a b) ?_)
    have h1 : FinArea.ramp U (max a b) z = 1 := le_antisymm (FinArea.ramp_le_one U _ z)
      (ha ▸ FinArea.ramp_mono U z (le_max_left a b))
    have h2 : sqCut (max a b) z = 1 := le_antisymm (sqCut_le_one _ z)
      ((hb z rfl) ▸ sqCut_mono z (le_max_right a b))
    rw [cutRamp, h1, h2, mul_one, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]
    refine le_antisymm (iSup_le fun n => ?_) zero_le
    rw [cutRamp, FinArea.ramp_eq_zero n hz, zero_mul, ENNReal.ofReal_zero]

lemma lintegral_cutRamp_le (U : Set ℂ) (n : ℕ) (μ : Measure ℂ) (hU : MeasurableSet U) :
    ∫⁻ z, ENNReal.ofReal (cutRamp U n z) ∂μ ≤ μ U := by
  rw [← lintegral_indicator_one hU]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz, Pi.one_apply]; exact ENNReal.ofReal_le_one.2 (cutRamp_le_one U n z)
  · rw [indicator_of_notMem hz, cutRamp, FinArea.ramp_eq_zero n hz, zero_mul, ENNReal.ofReal_zero]

omit [MeasurableSpace Ω'] in
lemma fineDens_nonneg (γ : ℝ) (m n : ℕ) (z : ℂ) (ω : Ω') : 0 ≤ fineDens W γ m n z ω := by
  unfold fineDens wnWeight; positivity

attribute [local irreducible] fineDens in
lemma measurable_fineDens' (hW : IsWhiteNoise P' W) (γ : ℝ) (m n : ℕ) :
    Measurable fun p : ℂ × Ω' => fineDens W γ m n p.1 p.2 :=
  (measurable_fineDens hW γ m n).mono (sup_le_sup le_rfl
    (MeasurableSpace.comap_mono (wnSigma_le hW _))) le_rfl

/-- `g ∈ C_c(𝕍)`, `0 ≤ g ≤ 1`, is `M̃`-integrable when `M̃` is finite on compacts of `𝕍` -/
lemma integrable_of_le_one {μ : Measure ℂ} (hμ : ∀ K, IsCompact K → K ⊆ openSquare → μ K < ⊤)
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ openSquare)
    (hg1 : ∀ z, ‖g z‖ ≤ 1) : Integrable g μ := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt ?_ (hμ _ hgc hgU)
  rw [← lintegral_indicator_one (isClosed_tsupport g).measurableSet]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ tsupport g
  · rw [indicator_of_mem hz, Pi.one_apply, ← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 (hg1 z)
  · rw [image_eq_zero_of_notMem_tsupport hz, enorm_zero]; exact zero_le

end GMCIdent5
end LQGMetric
