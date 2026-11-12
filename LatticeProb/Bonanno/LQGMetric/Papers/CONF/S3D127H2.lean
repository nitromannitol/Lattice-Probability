/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127H2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127H1

/-!
# (L3) The white-noise zero-boundary GFF on a bounded open `U`: antiderivative field and
stochastic Fubini (packet P-127H)

For a bounded open `U` and a white noise `W`:

* `exists_continuous_uRectField`: a continuous version `Y` of `x ↦ √π W(K_U(1_U 1_{[0,x]}))`
  (copy of `DGo.ZB.exists_continuous_zbRectField`, the square kernel replaced by
  `uKerL2 U (Ioi 0)`; Kolmogorov–Čentsov `GFFExist.exists_continuous_modification_of_gauss`);
* `integral_d12_mul_uKer_rho`: `∫ ∂_re∂_im φ(x) K_U(ρ_x)(s, w) dx = K_U(φ 1_U)(s, w)` pointwise
  (copy of `DGo.ZB.integral_d12_mul_zbKerFun_rho`);
* `ae_integral_d12_mul_zbU`: `∫ ∂_re∂_im φ Y = W(√π K_U(φ 1_U))` a.s. (copy of
  `DGo.ZB.ae_integral_d12_mul_zb`, through the generic `DGo.ZB.ae_integral_d12_mul_eq_gen`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ GFFExist DGo.ZB

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma hasLaw_uRect_sub (hW : IsWhiteNoise P W) (x x' : ℂ) :
    HasLaw (fun ω => W (uRectL2 U x) ω - W (uRectL2 U x') ω)
      (gaussianReal 0 (‖uRectL2 U x - uRectL2 U x'‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw ![uRectL2 U x, uRectL2 U x'] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    ← sub_eq_add_neg] at h
  refine h.congr ?_
  exact Eventually.of_forall fun ω => by ring

lemma measurable_uKer_rho (hU : IsOpen U) :
    Measurable fun p : ℂ × (ℝ × ℂ) => uKer U (Ioi 0) (rhoU U p.1) p.2 := by
  have h1 : Measurable fun z : (ℂ × (ℝ × ℂ)) × ℂ => rhoU U z.1.1 z.2 := by
    have e : (fun z : (ℂ × (ℝ × ℂ)) × ℂ => rhoU U z.1.1 z.2) =
        {z : (ℂ × (ℝ × ℂ)) × ℂ | z.2 ∈ U}.indicator (fun z => rectInd z.1.1 z.2) := by
      funext z; by_cases h : z.2 ∈ U <;> simp [rhoU, indicator, h]
    rw [e]
    exact (measurable_rectInd₂.comp ((measurable_fst.comp measurable_fst).prodMk
      measurable_snd)).indicator (measurable_snd hU.measurableSet)
  have hm : Measurable fun z : (ℂ × (ℝ × ℂ)) × ℂ =>
      rhoU U z.1.1 z.2 * wndKernel U (Ioi 0) z.2 z.1.2 :=
    h1.mul (measurable_wndKernel_comp hU measurableSet_Ioi measurable_snd
      (measurable_snd.comp measurable_fst))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))).measurable

/-- **Kernel identity**: `∫ ∂_re∂_im φ(x) K_U(ρ_x) dx = K_U(φ 1_U)` pointwise. -/
theorem integral_d12_mul_uKer_rho (hU : IsOpen U) (hUR : U ⊆ Metric.ball c R) (φ : TestC)
    (q : ℝ × ℂ) :
    ∫ x, d12 φ x * uKer U (Ioi 0) (rhoU U x) q = uKer U (Ioi 0) (U.indicator φ) q := by
  unfold uKer
  by_cases hq : 0 < q.1
  swap
  · have h0 : ∀ y, wndKernel U (Ioi 0) y q = 0 := fun y => by
      simp [wndKernel, show q.1 ∉ Ioi (0 : ℝ) from hq]
    simp only [h0, mul_zero, integral_zero]
  set p : ℂ → ℝ := fun y' => wndKernel U (Ioi 0) y' q with hp
  have hpm : Measurable p := measurable_wndKernel_comp hU measurableSet_Ioi measurable_id
    measurable_const
  have hpb : ∀ y', |p y'| ≤ (Real.pi * q.1)⁻¹ := fun y' => by
    rw [abs_of_nonneg (wndKernel_nonneg _ _ _ _)]
    exact GMCIdent.wndKernel_le U (Ioi 0) y' q hq
  set F : ℂ × ℂ → ℝ := fun z => d12 φ z.1 * (rhoU U z.1 z.2 * p z.2) with hF
  have hm2 : Measurable fun z : ℂ × ℂ => rhoU U z.1 z.2 := by
    have e : (fun z : ℂ × ℂ => rhoU U z.1 z.2) =
        {z : ℂ × ℂ | z.2 ∈ U}.indicator (fun z => rectInd z.1 z.2) := by
      funext z; by_cases h : z.2 ∈ U <;> simp [rhoU, indicator, h]
    rw [e]
    exact measurable_rectInd₂.indicator (measurable_snd hU.measurableSet)
  have hFm : Measurable F :=
    ((d12 φ).continuous.measurable.comp measurable_fst).mul (hm2.mul (hpm.comp measurable_snd))
  have hvol : volume U ≠ ∞ := ((measure_mono hUR).trans_lt measure_ball_lt_top).ne
  have hci : Integrable (U.indicator fun _ : ℂ => (Real.pi * q.1)⁻¹) :=
    (integrableOn_const hvol).integrable_indicator hU.measurableSet
  have hFi : Integrable F (volume.prod volume) := by
    refine ((GFFInv.integrable_test (d12 φ)).norm.mul_prod hci).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    simp only [hF, norm_mul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    by_cases hz : z.2 ∈ U
    · rw [indicator_of_mem hz, rhoU, indicator_of_mem hz]
      have h1 := (rectInd_bddSupp z.1).bdd z.2
      have h2 := hpb z.2
      have := abs_nonneg (p z.2)
      calc |rectInd z.1 z.2| * |p z.2| ≤ 1 * (Real.pi * q.1)⁻¹ :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [indicator_of_notMem hz, rhoU, indicator_of_notMem hz]; simp
  have e1 : ∀ x, d12 φ x * ∫ y', rhoU U x y' * p y' = ∫ y', F (x, y') := fun x => by
    rw [← integral_const_mul]
  refine (integral_congr_ae (Eventually.of_forall e1)).trans ?_
  rw [integral_integral_swap (f := fun x y' => F (x, y')) hFi]
  congr 1; funext y'
  simp only [hF]
  by_cases hy : y' ∈ U
  · simp only [rhoU, indicator_of_mem hy]
    have e2 : (fun x => d12 φ x * (rectInd x y' * p y')) =
        fun x => (d12 φ x * rectInd x y') * p y' := by funext x; ring
    rw [e2, integral_mul_const, integral_d12_mul_rectInd]
  · simp only [rhoU, indicator_of_notMem hy, zero_mul, mul_zero, integral_zero]

/-- the deterministic half: `∫ ∂_re∂_im φ(x) ⟪√π K_U ρ_x, G⟫ dx = ⟪√π K_U(φ 1_U), G⟫` -/
theorem integral_d12_mul_inner_uRect (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (φ : TestC) (G : WNSpace) :
    ∫ x, d12 φ x * ⟪uRectL2 U x, G⟫ =
      ⟪Real.sqrt Real.pi • uKerL2 U (Ioi 0) (U.indicator φ), G⟫ := by
  obtain ⟨C, hC⟩ := testC_abs_le φ
  obtain ⟨m1, b1, i1⟩ := indicator_props hU φ hC
  have hmem : ∀ x, MemLp (uKer U (Ioi 0) (rhoU U x)) 2 volume := fun x =>
    memLp_uKer hU hR hUR measurableSet_Ioi subset_rfl (measurable_rhoU hU x) (abs_rhoU_le x)
      (integrable_rhoU hU x)
  have hφm := memLp_uKer hU hR hUR measurableSet_Ioi subset_rfl m1 b1 i1
  simp only [uRectL2, real_inner_smul_left, inner_uKerL2_eq (hmem _), inner_uKerL2_eq hφm]
  have e : ∀ x, d12 φ x * (Real.sqrt Real.pi * ∫ q, uKer U (Ioi 0) (rhoU U x) q * G q) =
      Real.sqrt Real.pi * (d12 φ x * ∫ q, uKer U (Ioi 0) (rhoU U x) q * G q) := fun x => by ring
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  exact integral_d12_mul_inner_gen φ (fun x => uKer U (Ioi 0) (rhoU U x))
    (measurable_uKer_rho hU) hmem (integral_sq_uKer_rhoU_le hU hR hUR) _
    (integral_d12_mul_uKer_rho hU hUR φ) G

/-- **Stochastic Fubini for the zero-boundary GFF on `U`**:
`∫ ∂_re∂_im φ Y = W(√π K_U(φ 1_U))` a.s. -/
theorem ae_integral_d12_mul_zbU (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hW : IsWhiteNoise P W) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (uRectL2 U x)) (φ : TestC) :
    (fun ω => ∫ x, d12 φ x * Y x ω) =ᵐ[P]
      W (Real.sqrt Real.pi • uKerL2 U (Ioi 0) (U.indicator φ)) := by
  have hRb : ∀ x, ‖uRectL2 U x‖ ^ 2 ≤ Real.pi * rectBnd₁ U R := by
    intro x
    rw [uRectL2, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt Real.pi_pos.le]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    rw [sq_norm_uKerL2_eq (memLp_uKer hU hR hUR measurableSet_Ioi subset_rfl
      (measurable_rhoU hU x) (abs_rhoU_le x) (integrable_rhoU hU x))]
    exact integral_sq_uKer_rhoU_le hU hR hUR x
  exact ae_integral_d12_mul_eq_gen hW hRb hYc hYm hYW φ
    (integral_d12_mul_inner_uRect hU hR hUR φ)

end LQGMetric.CONF.ZBM
