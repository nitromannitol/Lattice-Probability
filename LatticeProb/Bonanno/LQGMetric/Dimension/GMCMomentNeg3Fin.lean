/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg3Fin at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Sq

/-!
# DZZ Lemma 2.10, negative moments: `E μ_h(B(x,ρ))^p < ∞` for `p < 0` (P2-NEGMOM2, step 4)

`lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg`: for the LQG measure `μ_h` of the zero-boundary
GFF on `𝕍 = (0,1)²`, `0 < γ < 2`, a ball `B(x,ρ) ⊆ 𝕍` and `p < 0`, `E μ_h(B(x,ρ))^p < ∞`
(DZZ Lemma 2.10, `LBM_LGDarXiv.tex` l. 673–682; Molchan 1996, Robert–Vargas arXiv:0807.1036
Prop. 3.6, Berestycki–Powell arXiv:2404.16642 Theorem `T:negmom`).

Passage to the limit (BP proof of Theorem `T:negmom`, `GMCproperties.tex` l. 1719–1745, "by
Fatou"): the square `Q = z₀ + 2^{-m}[0,1)²` centred at `x` with `2^{-m} ≤ ρ/8`, a continuous
`f` with `1_Q ≤ f ≤ 1_{B(x,ρ/2)}`; vague convergence gives
`μ(B) ≥ ∫ f dμ = lim_k ∫ f d areaApprox_k ≥ limsup_k areaApprox_k(Q)`, hence
`μ(B)^p ≤ liminf_k areaApprox_{m+k}(Q)^p`, and Fatou with the uniform bound
`exists_lintegral_areaApprox_sqQ_rpow_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset Topology
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

namespace Neg3

/-- a ball inside `𝕍` stays `ρ` away from the sides -/
lemma ball_sub_sqIn {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hB : ball x ρ ⊆ openSquare) :
    closedBall x (ρ / 2) ⊆ sqIn (ρ / 2) := by
  have hx : x ∈ openSquare := hB (mem_ball_self hρ)
  have key : ∀ y : ℂ, ‖y - x‖ < ρ → y ∈ openSquare := fun y hy => hB (by rwa [mem_ball, dist_eq_norm])
  have a1 : ρ ≤ x.re := by
    by_contra h; push Not at h
    have := (key ⟨0, x.im⟩ (by
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp [abs_of_pos hx.1]; linarith)).1
    simp at this
  have a2 : x.re ≤ 1 - ρ := by
    by_contra h; push Not at h
    have := (key ⟨1, x.im⟩ (by
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp [abs_of_pos (show 0 < 1 - x.re by linarith [hx.2.1])]; linarith)).2.1
    simp at this
  have a3 : ρ ≤ x.im := by
    by_contra h; push Not at h
    have := (key ⟨x.re, 0⟩ (by
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp [abs_of_pos hx.2.2.1]; linarith)).2.2.1
    simp at this
  have a4 : x.im ≤ 1 - ρ := by
    by_contra h; push Not at h
    have := (key ⟨x.re, 1⟩ (by
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp [abs_of_pos (show 0 < 1 - x.im by linarith [hx.2.2.2])]; linarith)).2.2.2
    simp at this
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 := (Complex.abs_re_le_norm (z - x)).trans hz
  have h2 := (Complex.abs_im_le_norm (z - x)).trans hz
  rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
  have := abs_le.1 h1; have := abs_le.1 h2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- the plateau test function: `1` on `B(x,ρ/4)`, `0` off `B(x,ρ/2)` -/
def plat (x : ℂ) (ρ : ℝ) (z : ℂ) : ℝ := min 1 (max 0 ((ρ / 2 - ‖z - x‖) * (4 / ρ)))

lemma continuous_plat (x : ℂ) (ρ : ℝ) : Continuous (plat x ρ) := by unfold plat; fun_prop

lemma plat_nonneg (x : ℂ) (ρ : ℝ) (z : ℂ) : 0 ≤ plat x ρ z :=
  le_min zero_le_one (le_max_left _ _)

lemma plat_le_one (x : ℂ) (ρ : ℝ) (z : ℂ) : plat x ρ z ≤ 1 := min_le_left _ _

lemma plat_eq_zero {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : ρ / 2 ≤ ‖z - x‖) :
    plat x ρ z = 0 := by
  unfold plat
  rw [max_eq_left (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)),
    min_eq_right zero_le_one]

lemma plat_eq_one {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : ‖z - x‖ ≤ ρ / 4) :
    plat x ρ z = 1 := by
  unfold plat
  have : 1 ≤ (ρ / 2 - ‖z - x‖) * (4 / ρ) := by
    rw [← sub_nonneg]
    have e : (ρ / 2 - ‖z - x‖) * (4 / ρ) - 1 = (ρ / 4 - ‖z - x‖) * (4 / ρ) := by
      field_simp; ring
    rw [e]; exact mul_nonneg (by linarith) (by positivity)
  rw [max_eq_right (by linarith), min_eq_left this]

lemma tsupport_plat {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) : tsupport (plat x ρ) ⊆ closedBall x (ρ / 2) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_eq_norm]
  by_contra h; push Not at h
  exact hz (plat_eq_zero hρ h.le)

end Neg3

end DGMC

open DGMC DGMC.Neg3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- **DZZ Lemma 2.10, negative moments** (`Statement`-level form for balls): for `0 < γ < 2`, a
ball `B(x,ρ) ⊆ 𝕍` and `p < 0`, `E μ_h(B(x,ρ))^p < ∞`. -/
theorem lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ p : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hB : Metric.ball x ρ ⊆ openSquare) (hp : p < 0) :
    ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ^ p ∂P < ⊤ := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  -- the square
  obtain ⟨m, hm⟩ := exists_radius_le (show 0 < ρ / 2 by positivity)
  have hma : 4 * radius m ≤ ρ / 2 := hm m le_rfl
  set a := radius m
  have ha : 0 < a := radius_pos m
  set c : ℂ := ⟨1 / 2, 1 / 2⟩
  set z₀ : ℂ := x - a • c
  set K := closedBall x (ρ / 2)
  have hKU : K ⊆ openSquare := (closedBall_subset_ball (by linarith)).trans hB
  have hdist : ∀ w ∈ unitSq, ‖(z₀ + a • w) - x‖ ≤ a := fun w ⟨w1, w2, w3, w4⟩ => by
    have e : (z₀ + a • w) - x = a • (w - c) := by simp only [z₀, smul_sub]; abel
    rw [e, norm_smul, Real.norm_of_nonneg ha.le]
    refine mul_le_of_le_one_right ha.le ((Complex.norm_le_abs_re_add_abs_im _).trans ?_)
    simp only [Complex.sub_re, Complex.sub_im, c]
    have h1 : |w.re - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : |w.im - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hQ : ∀ w ∈ unitSq, closedBall (z₀ + a • w) (2 * a) ⊆ K := fun w hw =>
    closedBall_subset_closedBall' (by rw [dist_eq_norm]; linarith [hdist w hw])
  obtain ⟨C, hC, hCk⟩ := exists_lintegral_areaApprox_sqQ_rpow_le (P := P) hX hγ hγ2 hp hKU
    (convex_closedBall _ _) (isCompact_closedBall _ _) hQ
  -- finiteness of the approximations on `K`
  obtain ⟨n, hn⟩ := exists_nat_ge (2 / ρ)
  set T := sqIn (1 / ((n : ℝ) + 2))
  have hKT : K ⊆ T := (ball_sub_sqIn hρ hB).trans fun z ⟨z1, z2, z3, z4⟩ => by
    have : 1 / ((n : ℝ) + 2) ≤ ρ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hρ] at hn
      nlinarith
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨k₁, hk₁⟩ := exists_radius_le (show 0 < 1 / ((n : ℝ) + 2) by positivity)
  have hfin : ∀ᵐ ω ∂P, ∀ k, k₁ ≤ k → areaApprox γ (X ω) k T < ⊤ := by
    rw [ae_all_iff]; intro k
    by_cases hk : k₁ ≤ k
    · filter_upwards [ae_areaApprox_sqIn_lt_top hX γ n k (by
        have := hk₁ k hk; have := radius_pos k; linarith)] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hk
  -- the pointwise bound
  set f := plat x ρ
  have hfc : Continuous f := continuous_plat x ρ
  have hfts : tsupport f ⊆ K := tsupport_plat hρ
  have hfcs : HasCompactSupport f := (isCompact_closedBall x (ρ / 2)).of_isClosed_subset
    (isClosed_tsupport _) hfts
  have hfK : ∀ z, z ∉ K → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport
    fun h => hz (hfts h)
  have hQf : ∀ z ∈ sqQ z₀ m, f z = 1 := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := eq_of_mem_sqQ hz
    exact plat_eq_one hρ ((hdist w (cell0_subset_unitSq hw)).trans (by linarith))
  set g : ℕ → Ω → ℝ≥0∞ := fun k ω => areaApprox γ (X ω) (m + k) (sqQ z₀ m) ^ p
  have hgm : ∀ k, Measurable (g k) := fun k =>
    ((Measure.measurable_coe (measurableSet_sqQ z₀ m)).comp
      ((measurable_areaApprox γ _).comp (measurable_field hX))).pow_const p
  have hpt : ∀ᵐ ω ∂P, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ^ p ≤
      liminf (fun k => g k ω) atTop := by
    filter_upwards [ae_isVagueLimitOn_qAreaMeasureOn_openSquare hX hγ hγ2, hfin] with ω hv hω
    set μ := qAreaMeasureOn γ (X ω) openSquare
    have hT := hv.2.2 f hfc hfcs (hfts.trans hKU)
    set L := ENNReal.ofReal (∫ z, f z ∂μ)
    have h1 : L ≤ μ (ball x ρ) := by
      refine (ofReal_integral_le_lintegral (μ := μ) (plat_nonneg x ρ)).trans ?_
      rw [← lintegral_indicator_one measurableSet_ball]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ ball x ρ
      · rw [indicator_of_mem hz, Pi.one_apply, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (plat_le_one x ρ z)
      · have : z ∉ K := fun h => hz (closedBall_subset_ball (by linarith) h)
        rw [show plat x ρ z = 0 from hfK z this, ENNReal.ofReal_zero]; exact zero_le
    have hlim : Tendsto (fun k => ENNReal.ofReal (∫ z, f z ∂(areaApprox γ (X ω) (m + k))) ^ p)
        atTop (𝓝 (L ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp ((ENNReal.continuous_ofReal.tendsto _).comp
        (hT.comp (tendsto_atTop_mono (fun k => Nat.le_add_left k m) tendsto_id)))
    have hle : ∀ᶠ k in atTop, ENNReal.ofReal (∫ z, f z ∂(areaApprox γ (X ω) (m + k))) ^ p ≤
        g k ω := by
      filter_upwards [eventually_ge_atTop k₁] with k hk
      refine ennrpow_anti hp.le ?_
      have hfinK : areaApprox γ (X ω) (m + k) K < ⊤ :=
        (measure_mono hKT).trans_lt (hω (m + k) (by omega))
      have hint : Integrable f (areaApprox γ (X ω) (m + k)) := by
        have hg : Integrable (K.indicator fun _ => (1 : ℝ)) (areaApprox γ (X ω) (m + k)) :=
          (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
            (integrableOn_const hfinK.ne)
        refine hg.mono' hfc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (plat_nonneg x ρ z)]
          exact plat_le_one x ρ z
        · rw [hfK z hz, indicator_of_notMem hz, norm_zero]
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (plat_nonneg x ρ)),
        ← lintegral_indicator_one (measurableSet_sqQ z₀ m)]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ sqQ z₀ m
      · rw [indicator_of_mem hz, Pi.one_apply, hQf z hz, ENNReal.ofReal_one]
      · rw [indicator_of_notMem hz]; exact zero_le
    calc μ (ball x ρ) ^ p ≤ L ^ p := ennrpow_anti hp.le h1
      _ = liminf (fun k => ENNReal.ofReal (∫ z, f z ∂(areaApprox γ (X ω) (m + k))) ^ p) atTop :=
          hlim.liminf_eq.symm
      _ ≤ liminf (fun k => g k ω) atTop := liminf_le_liminf hle
  calc ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ^ p ∂P
      ≤ ∫⁻ ω, liminf (fun k => g k ω) atTop ∂P := lintegral_mono_ae hpt
    _ ≤ liminf (fun k => ∫⁻ ω, g k ω ∂P) atTop := lintegral_liminf_le hgm
    _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hCk)
    _ < ⊤ := hC

end LQGMetric
