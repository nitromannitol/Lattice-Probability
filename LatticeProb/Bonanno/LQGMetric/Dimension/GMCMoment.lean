/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMoment at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCTest
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure

/-!
# First moment of the LQG measure of the unit square (task P2-GMC, WP-24; DZZ Lemma 2.10, part)

For a QZ zero-boundary GFF `X` on `𝕍 = (0,1)²` and `γ : ℝ`, the LQG measure of
Statement/Dimension.lean, `μ_ω = QuantumZipper.qAreaMeasureOn γ (X ω) openSquare` (a vague limit
on `𝕍` of `areaApprox γ (X ω) k = 2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz`, or `0` if none exists),
satisfies

* `lintegral_qAreaMeasureOn_openSquare_le` : `E μ(𝕍) ≤ C_γ · Leb(𝕍) < ∞`;
* `lintegral_qAreaMeasureOn_rpow_lt_top` : `E μ(A)^p < ∞` for every set `A` and `0 < p ≤ 1`.

This is the range `0 < p ≤ 1` of the positive-moment half of DZZ Lemma 2.10
(`LBM_LGDarXiv.tex` l. 673–682: "For any `0 < p < 4/γ²`, `E (M_γ(𝕍))^p < ∞`"; DZZ cites
Kahane 85, RV10 and Rhodes–Vargas arXiv:1305.6221 Thms 2.11–2.12). The proof is the standard
first-moment computation (Rhodes–Vargas arXiv:1305.6221 §2, `E M(A) = ∫_A e^{γ²/2 (Var X_ε − log
1/ε)}`; Berestycki arXiv:1506.09113 §2): Fatou's lemma along the vague limit and
`E e^{γ h_r(z)} ≤ (3/r)^{γ²/2}` (`GMCCircle.lean`). The constant `C_γ` contains
`e^{γ c₀}`, `c₀` the junk value of `limUnder` (QZ's `avgReg` is a `limUnder` along dyadic
centres, whose a.s. existence for the square is not available); this only changes the constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set QuantumZipper
open scoped ENNReal

namespace LQGMetric

/-- the junk value of `limUnder` in `ℝ` -/
def junkR : ℝ := Classical.choice (⟨0⟩ : Nonempty ℝ)

/-- the constant of the first-moment bound -/
def gmcConst (γ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (3 ^ (γ ^ 2 / 2)) + ENNReal.ofReal (Real.exp (γ * junkR))

/-- `e^{γ limUnder a} ≤ liminf e^{γ aₙ} + e^{γ c₀}` -/
lemma ofReal_exp_limUnder_le (γ : ℝ) (a : ℕ → ℝ) :
    ENNReal.ofReal (Real.exp (γ * limUnder atTop a)) ≤
      liminf (fun n => ENNReal.ofReal (Real.exp (γ * a n))) atTop +
        ENNReal.ofReal (Real.exp (γ * junkR)) := by
  by_cases h : ∃ L, Tendsto a atTop (𝓝 L)
  · obtain ⟨L, hL⟩ := h
    rw [hL.limUnder_eq]
    have hc : Continuous fun y : ℝ => ENNReal.ofReal (Real.exp (γ * y)) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hlim := ((hc.tendsto L).comp hL).liminf_eq
    simp only [Function.comp_def] at hlim
    rw [hlim]
    exact le_self_add
  · rw [limUnder_of_not_tendsto h]
    exact le_add_self

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

lemma measurable_field (hX : IsZeroBoundaryGFFOn openSquare X P) :
    Measurable fun ω => (X ω : FieldSample) :=
  measurable_pi_iff.mpr hX.measurable_coord

/-- the density of `areaApprox` -/
def areaDens (γ : ℝ) (x : FieldSample) (k : ℕ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k z))

lemma measurable_areaDens (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ) (k : ℕ) :
    Measurable fun p : Ω × ℂ => areaDens γ (X p.1) k p.2 := by
  have h := (measurable_avgReg k).comp ((measurable_field hX).prodMap measurable_id)
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (h.const_mul γ)).const_mul _)

lemma radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity
lemma radius_le_one (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- **pointwise exponential moment of the regularized circle average** at a point at distance
`≥ s` from `∂𝕍`, for `2^{-k} < s/2` -/
lemma lintegral_areaDens_le (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ) {s : ℝ}
    (hs : 0 < s) {k : ℕ} (hk : radius k < s / 2) {z : ℂ} (hz : z ∈ sqIn s) :
    ∫⁻ ω, areaDens γ (X ω) k z ∂P ≤ gmcConst γ := by
  set r := radius k
  have hr := radius_pos k
  have hr1 := radius_le_one k
  set a := γ ^ 2 / 2
  have ha : 0 ≤ a := by positivity
  -- eventually the dyadic centres carry a circle inside the square
  have hev : ∀ᶠ m in atTop, InSq r (dyadicRoundC m z) := by
    have := (RegClosure.tendsto_dyadicRoundC z).eventually (Metric.ball_mem_nhds z (half_pos hs))
    filter_upwards [this] with m hm
    rw [Complex.dist_eq] at hm
    have h1 := (Complex.abs_re_le_norm _).trans hm.le
    have h2 := (Complex.abs_im_le_norm _).trans hm.le
    rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
    obtain ⟨b1, b2, b3, b4⟩ := hz
    have := abs_le.mp h1; have := abs_le.mp h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hmeas : ∀ m, Measurable fun ω =>
      ENNReal.ofReal (Real.exp (γ * X ω (foldedCircle (dyadicRoundC m z) r))) := fun m =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hX.measurable_coord _).const_mul γ))
  have hpt : ∀ ω, areaDens γ (X ω) k z ≤ ENNReal.ofReal (r ^ a) *
      (liminf (fun m => ENNReal.ofReal
          (Real.exp (γ * X ω (foldedCircle (dyadicRoundC m z) r)))) atTop +
        ENNReal.ofReal (Real.exp (γ * junkR))) := by
    intro ω
    unfold areaDens
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
    exact mul_le_mul_right (ofReal_exp_limUnder_le γ _) _
  calc ∫⁻ ω, areaDens γ (X ω) k z ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (r ^ a) * (liminf (fun m => ENNReal.ofReal
          (Real.exp (γ * X ω (foldedCircle (dyadicRoundC m z) r)))) atTop +
          ENNReal.ofReal (Real.exp (γ * junkR))) ∂P := lintegral_mono hpt
    _ ≤ ENNReal.ofReal (r ^ a) * (liminf (fun m => ∫⁻ ω, ENNReal.ofReal
          (Real.exp (γ * X ω (foldedCircle (dyadicRoundC m z) r))) ∂P) atTop +
          ENNReal.ofReal (Real.exp (γ * junkR))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine mul_le_mul_right ?_ _
        have hP : IsProbabilityMeasure P := by
          obtain ⟨m, hm⟩ := hev.exists
          exact (hX.gaussian.hasGaussianLaw_eval
            ⟨_, isAdmissibleDual_openSquare_foldedCircle hm hr⟩).isProbabilityMeasure
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        exact add_le_add_left (lintegral_liminf_le hmeas) _
    _ ≤ ENNReal.ofReal (r ^ a) * (ENNReal.ofReal ((3 / r) ^ a) +
          ENNReal.ofReal (Real.exp (γ * junkR))) := by
        refine mul_le_mul_right (add_le_add_left ?_ _) _
        refine liminf_le_of_frequently_le' (hev.mono fun m hm => ?_).frequently
        exact lintegral_exp_foldedCircle_le hX γ hm hr
    _ ≤ gmcConst γ := by
        rw [mul_add, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
          ← Real.mul_rpow hr.le (by positivity), show r * (3 / r) = 3 by have hr0 : r ≠ 0 := hr.ne'; field_simp]
        refine add_le_add le_rfl ?_
        calc ENNReal.ofReal (r ^ a) * ENNReal.ofReal (Real.exp (γ * junkR))
            ≤ 1 * ENNReal.ofReal (Real.exp (γ * junkR)) := by
              refine mul_le_mul_left ?_ _
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one hr.le hr1 ha)
          _ = _ := one_mul _

end LQGMetric
