/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Loc3 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_le_eLpNorm_of_exponent_le no longer takes the measurability argument; eLpNorm_one_eq_lintegral_enorm takes it. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Loc2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1C2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of `μ_{ĥ^tr}` (P2-DGLOC, part 3): local versions of the circle averages of `ĥ^tr`

DG:950 (3.4) with `t = 0`: `ĥ^tr = √π ∫_0^1 ∫ p_{B_{1/10}(·)}(s/2; ·, w) W(dw, ds)`. The kernel of
the circle average `ĥ^tr(σ_{z,r})` is carried by `(0,1] × (B̄(z,r) + B(0,1/10))`; so for
`B̄(z,r) ⊆ U` the circle average is measurable for the white noise on
`trLocReg U = (0,1) × B_{1/10}(U)` (`supportedIn_trMeasKerL2_circle`; `{1} × ℂ` is null).

`exists_trCircVer_loc`: a version `V k` of `z ↦ ĥ^tr(σ_{z,2^{-k}})` on `dSet U k` which is
`Borel ⊗ σ(W|_{trLocReg U})`-measurable: the limit of the values at dyadic points along a
subsequence chosen by the uniform `L²`-continuity of the kernels on a compact (part 2) and
first-moment Borel–Cantelli (`GMCIdent.ae_tendsto_of_summable`); as `GMCIdent.dyVer`.
Own elementary glue.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent QuantumZipper

/-- the region of the white noise seen by `ĥ^tr` around `U` (unit frame) -/
def trLocReg (U : Set ℂ) : Set (ℝ × ℂ) := Ioo 0 1 ×ˢ thickening (1 / 10) U

lemma measurableSet_trLocReg (U : Set ℂ) : MeasurableSet (trLocReg U) :=
  measurableSet_Ioo.prod isOpen_thickening.measurableSet

/-- **the kernel of `ĥ^tr(σ_{z,r})` lives in `trLocReg U`** when `B̄(z,r) ⊆ U` (DG:950) -/
lemma supportedIn_trMeasKerL2_circle {U : Set ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ U) : SupportedIn (trLocReg U) (trMeasKerL2 (circleUnif z r)) := by
  have hm := memLp_trMeasKer_circleUnif z hr
  have h1 : volume {p : ℝ × ℂ | p.1 = 1} = 0 := by
    have e : {p : ℝ × ℂ | p.1 = 1} = ({1} : Set ℝ) ×ˢ (univ : Set ℂ) := by ext p; simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]; simp
  unfold SupportedIn
  simp only [trMeasKerL2, dite_eq_left_of_eq_true (eq_true hm)]
  filter_upwards [ae_restrict_of_ae hm.coeFn_toLp, ae_restrict_mem (measurableSet_trLocReg U).compl,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h1)] with p hp hpS hp1
  rw [hp]
  unfold trMeasKer
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) 1
  · have hw : p.2 ∉ thickening (1 / 10) U := fun hw =>
      hpS ⟨⟨ht.1, lt_of_le_of_ne ht.2 hp1⟩, hw⟩
    refine integral_eq_zero_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (circleUnif_compl_closedBall hr z)] with x hx
    have hxU : x ∈ U := hB (not_not.1 hx)
    simp only [trKer, wndKernel, Pi.zero_apply]
    rw [indicator_of_mem ht]
    exact killedHeat_eq_zero_of_not_mem_right isOpen_ball
      (Real.toNNReal_pos.2 (by linarith [ht.1])).ne' x
      (fun h => hw (ball_subset_thickening hxU _ h))
  · refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
    simp only [trKer, wndKernel, Pi.zero_apply]
    rw [indicator_of_notMem ht]

/-- the limit of a field along the dyadic points of a subsequence of levels -/
def subVer {Ω : Type*} (F : ℂ → Ω → ℝ) (φ : ℕ → ℕ) (z : ℂ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => F (dyadicRoundC (φ n) z) ω

theorem measurable_subVer {Ω : Type*} {m : MeasurableSpace Ω} {F : ℂ → Ω → ℝ}
    (hF : ∀ z, Measurable[m] (F z)) (φ : ℕ → ℕ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω _ m] fun p : ℂ × Ω => subVer F φ p.1 p.2 := by
  let _ : MeasurableSpace Ω := m
  unfold subVer
  exact (StronglyMeasurable.limUnder
    (fun n => (measurable_eval_dyadicRoundC hF (φ n)).stronglyMeasurable)).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `E|√π W f − √π W g| ≤ √π ‖f − g‖` -/
lemma lintegral_abs_wn_sub_le (hW : IsWhiteNoise P W) (f g : WNSpace) :
    ∫⁻ ω, ENNReal.ofReal |Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω| ∂P ≤
      ENNReal.ofReal (Real.sqrt Real.pi * ‖f - g‖) := by
  have := hW.isProbabilityMeasure
  have hsm : AEStronglyMeasurable (W f - W g) P :=
    ((hW.measurable f).sub (hW.measurable g)).aestronglyMeasurable
  have h12 := eLpNorm_le_eLpNorm_of_exponent_le (f := W f - W g) (μ := P) (p := 1) (q := 2) (by norm_num)
  rw [eLpNorm_wn_sub hW, eLpNorm_one_eq_lintegral_enorm hsm] at h12
  have e : ∀ ω, ENNReal.ofReal |Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω| =
      ENNReal.ofReal (Real.sqrt Real.pi) * ‖(W f - W g) ω‖ₑ := by
    intro ω
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.ofReal_mul (Real.sqrt_nonneg _), Pi.sub_apply, Real.enorm_eq_ofReal_abs]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact mul_le_mul_right h12 _

/-- **a local jointly measurable version of the circle averages of `ĥ^tr`** on `dSet U k`:
`Borel ⊗ σ(W|_{trLocReg U})`-measurable -/
theorem exists_trCircVer_loc (hW : IsWhiteNoise P W) {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (k : ℕ) :
    ∃ V : ℂ → Ω → ℝ,
      Measurable[@Prod.instMeasurableSpace ℂ Ω _ (wnSigma W (trLocReg U))]
        (fun p : ℂ × Ω => V p.1 p.2) ∧
      ∀ z ∈ dSet U k, V z =ᵐ[P] dgTr W z ((2 : ℝ)⁻¹ ^ k) := by
  set r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by positivity
  set f : ℂ → WNSpace := fun z => trMeasKerL2 (circleUnif z r)
  have hfc : Continuous f := continuous_trMeasKerL2_circle hr
  set A : Set ℂ := {z | r < infDist z Uᶜ}
  have hAB : ∀ z ∈ A, closedBall z r ⊆ U := by
    intro z hz w hw
    by_contra hwU
    have h1 := infDist_le_dist_of_mem (x := z) (show w ∈ Uᶜ from hwU)
    have h2 : dist z w ≤ r := by rw [dist_comm]; exact mem_closedBall.1 hw
    have h3 : r < infDist z Uᶜ := hz
    linarith
  classical
  set F : ℂ → Ω → ℝ := fun z ω => if z ∈ A then dgTr W z r ω else 0
  have hFm : ∀ z, Measurable[wnSigma W (trLocReg U)] (F z) := by
    intro z
    by_cases hz : z ∈ A
    · simp only [F, hz, ite_true]
      exact (measurable_wnSigma (supportedIn_trMeasKerL2_circle hr (hAB z hz))).const_mul _
    · simp only [F, hz, ite_false]
      exact measurable_const
  -- uniform continuity of the kernels on a compact neighbourhood of `U`
  set C : Set ℂ := cthickening 2 (closure U)
  have hC : IsCompact C := hUb.isCompact_closure.cthickening
  have huc := (hC.uniformContinuousOn_of_continuous hfc.continuousOn)
  rw [Metric.uniformContinuousOn_iff] at huc
  have hφ : ∀ n : ℕ, ∃ j : ℕ, n ≤ j ∧ ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ 2 * (1 / 2 ^ j) →
      dist (f x) (f y) < (2 : ℝ)⁻¹ ^ n := by
    intro n
    obtain ⟨δ, hδ, hδf⟩ := huc _ (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n)
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (half_pos hδ) (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨max n j, le_max_left _ _, fun x hx y hy hxy => hδf x hx y hy ?_⟩
    have h1 : (2 : ℝ)⁻¹ ^ max n j ≤ (2 : ℝ)⁻¹ ^ j :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    have h2 : 2 * (1 / 2 ^ max n j) = 2 * (2 : ℝ)⁻¹ ^ max n j := by rw [one_div, inv_pow]
    linarith
  choose φ hφn hφf using hφ
  refine ⟨subVer F φ, measurable_subVer hFm φ, fun z hz => ?_⟩
  have hz2 : 2 * r < infDist z Uᶜ := hz
  have hzA : z ∈ A := show r < infDist z Uᶜ by linarith
  have hzU : z ∈ U := hAB z hzA (mem_closedBall_self hr.le)
  -- the dyadic points are eventually in `A`, and always in `C`
  have hdC : ∀ j, dyadicRoundC j z ∈ C := fun j => by
    refine mem_cthickening_of_dist_le _ z 2 _ (subset_closure hzU) ?_
    rw [dist_eq_norm]
    refine (CircleCont.norm_dyadicRoundC_sub_le j z).trans ?_
    have : (1 : ℝ) / 2 ^ j ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  have hzC : z ∈ C := self_subset_cthickening _ (subset_closure hzU)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (1 / 2 ^ N) < r := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hr) (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨N, by rw [one_div, ← inv_pow]; linarith⟩
  have hdA : ∀ n, N ≤ n → dyadicRoundC (φ n) z ∈ A := by
    intro n hn
    have hd := CircleCont.norm_dyadicRoundC_sub_le (φ n) z
    have hmono : 2 * (1 / (2 : ℝ) ^ φ n) ≤ 2 * (1 / 2 ^ N) := by
      gcongr
      · norm_num
      · exact hn.trans (hφn n)
    have hL := infDist_le_infDist_add_dist (s := Uᶜ) (x := z) (y := dyadicRoundC (φ n) z)
    rw [dist_eq_norm, norm_sub_rev] at hL
    show r < infDist (dyadicRoundC (φ n) z) Uᶜ
    linarith
  have hFz : F z = dgTr W z r := by funext ω; simp only [F, hzA, ite_true]
  -- first-moment Borel–Cantelli along the shifted subsequence
  have hsum : ∑' n, ∫⁻ ω, ENNReal.ofReal |F (dyadicRoundC (φ (n + N)) z) ω - F z ω| ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_left
        (Real.sqrt Real.pi)).toNNReal) (ENNReal.tsum_le_tsum fun n => ?_)
    have hdn := hdA (n + N) (Nat.le_add_left N n)
    simp only [F, hdn, hzA, ite_true, dgTr]
    refine (lintegral_abs_wn_sub_le hW _ _).trans ?_
    rw [ENNReal.ofNNReal_toNNReal]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    have h := hφf (n + N) _ (hdC _) z hzC (by
      rw [dist_eq_norm]; exact CircleCont.norm_dyadicRoundC_sub_le _ z)
    rw [dist_eq_norm] at h
    refine h.le.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right n N))
  have hFae : ∀ w, AEMeasurable (F w) P := fun w =>
    ((hFm w).mono (wnSigma_le hW _) le_rfl).aemeasurable
  filter_upwards [ae_tendsto_of_summable (fun n => hFae _) (hFae z) hsum] with ω hω
  rw [← hFz]
  exact ((tendsto_add_atTop_iff_nat N).1 hω).limUnder_eq

end DG
end LQGMetric
