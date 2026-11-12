/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127H1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108R2
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBSFub

/-!
# (L3) The white-noise zero-boundary GFF on a bounded open `U`: kernel bounds (packet P-127H)

CONF (arXiv:1905.00381, `confluence-final.tex`) C:722–724: `(h^U, φ) = √π W(K_U(φ 1_U))`
(`zbProcU`, S3D108R2). To realise it as a random distribution we follow
`DGo.ZB.exists_zbDist` (the case `U = (a, a+L)²`, task P2-DGZB), which follows the whole-plane
construction `GFFExist` (D109): the antiderivative field `F(x) = √π W(K_U(1_U 1_{[0,x]}))`.

This file generalises the square-specific inputs of `DGo/ZBField` and `DGo/ZBSFub` to a bounded
open `U`, with DDDF's square kernel `zbKerL2 a L` replaced by `uKerL2 U (Ioi 0)` (S3D108R1):

* `lintegral_triple_le`: the quantitative form of `lintegral_triple_lt_top` (same proof);
* `integral_sq_uKer_le`: `∫ (K_U ρ)² ≤ (N · (C · 1 + M ∫_1^∞ R²/(π s²)))` for `|ρ| ≤ C`,
  `∫|ρ| ≤ M, N` (replaces `DGo.ZB.sq_norm_zbKerL2_le`);
* `rhoU U x = 1_U 1_{[0,x]}`, `uRectL2 U x = √π K_U(ρ_x)`, `sq_norm_uRectL2_sub_le` (the
  Lipschitz bound of the increment variance; replaces `DGo.ZB.sq_norm_zbRectL2_sub_le`);
* `integral_d12_mul_uKer_rho`, `integral_d12_mul_inner_uRect` (copies of
  `DGo.ZB.integral_d12_mul_zbKerFun_rho`, `integral_d12_mul_inner_zbRect`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ GFFExist

variable {U : Set ℂ} {I : Set ℝ} {c : ℂ} {R : ℝ}

/-- the tail time integral `∫_1^∞ R²/(π s²) ds` -/
def tailT (R : ℝ) : ℝ≥0∞ := ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R ^ 2 / Real.pi * s ^ (-2 : ℝ))

/-- the constant of the kernel bound -/
def uBnd (C : ℝ) (M : ℝ≥0∞) (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal C * volume (Ioc (0 : ℝ) 1) + M * tailT R

set_option maxHeartbeats 1000000 in
/-- **the triple integral bound** (quantitative form of `lintegral_triple_lt_top`, same proof) -/
theorem lintegral_triple_le (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {g h : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hh : Measurable h) {C : ℝ} (hhC : ∀ z, h z ≤ ENNReal.ofReal C) :
    ∫⁻ x : (ℝ × ℂ) × (ℂ × ℂ), g x.2.1 * h x.2.2 * (ENNReal.ofReal (wndKernel U I x.2.1 x.1) *
      ENNReal.ofReal (wndKernel U I x.2.2 x.1)) ≤ (∫⁻ z, g z) * uBnd C (∫⁻ z, h z) R := by
  have hm : Measurable fun x : (ℝ × ℂ) × (ℂ × ℂ) => g x.2.1 * h x.2.2 *
      (ENNReal.ofReal (wndKernel U I x.2.1 x.1) * ENNReal.ofReal (wndKernel U I x.2.2 x.1)) :=
    ((hg.comp (measurable_fst.comp measurable_snd)).mul
      (hh.comp (measurable_snd.comp measurable_snd))).mul
      ((measurable_wndKernel_comp hU hI (measurable_fst.comp measurable_snd)
        measurable_fst).ennreal_ofReal.mul (measurable_wndKernel_comp hU hI
        (measurable_snd.comp measurable_snd) measurable_fst).ennreal_ofReal)
  rw [Measure.volume_eq_prod (α := ℝ × ℂ) (β := ℂ × ℂ),
    lintegral_prod_symm _ hm.aemeasurable]
  have hkm : Measurable fun q : ℂ × ℂ =>
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal q.1 q.2) :=
    measurable_lintegral_time hU measurable_fst measurable_snd
  calc ∫⁻ q : ℂ × ℂ, ∫⁻ p : ℝ × ℂ, g q.1 * h q.2 * (ENNReal.ofReal (wndKernel U I q.1 p) *
        ENNReal.ofReal (wndKernel U I q.2 p))
      ≤ ∫⁻ q : ℂ × ℂ, g q.1 * h q.2 *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal q.1 q.2) := by
        refine lintegral_mono fun q => ?_
        refine (lintegral_const_mul (g q.1 * h q.2)
          ((measurable_wndKernel hU hI q.1).ennreal_ofReal.mul
          (measurable_wndKernel hU hI q.2).ennreal_ofReal)).trans_le ?_
        gcongr; exact lintegral_wnd_mul_le hU hI hI0 q.1 q.2
    _ = ∫⁻ y, g y * ∫⁻ y', h y' *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal y y') := by
        rw [Measure.volume_eq_prod (α := ℂ) (β := ℂ),
          lintegral_prod (f := fun q : ℂ × ℂ => g q.1 * h q.2 *
            ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal q.1 q.2))
            (((hg.comp measurable_fst).mul (hh.comp measurable_snd)).mul hkm).aemeasurable]
        refine lintegral_congr fun y => ?_
        have hy : Measurable fun y' : ℂ => h y' *
            ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal y y') :=
          hh.mul (measurable_lintegral_time hU measurable_const measurable_id)
        rw [← lintegral_const_mul (g y) hy]
        exact lintegral_congr fun y' => by ring
    _ = ∫⁻ y, g y * ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y', h y' *
          ENNReal.ofReal (killedHeat U s.toNNReal y y') := by
        refine lintegral_congr fun y => ?_
        congr 1
        have hk : Measurable fun x : ℂ × ℝ =>
            h x.1 * ENNReal.ofReal (killedHeat U x.2.toNNReal y x.1) :=
          (hh.comp measurable_fst).mul (measurable_killedHeat_comp hU measurable_snd
            measurable_const measurable_fst).ennreal_ofReal
        have e : ∀ y', h y' * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal y y') =
            ∫⁻ s in Ioi (0 : ℝ), h y' * ENNReal.ofReal (killedHeat U s.toNNReal y y') := fun y' =>
          (lintegral_const_mul _ (measurable_killedHeat_comp hU measurable_id
            measurable_const measurable_const).ennreal_ofReal).symm
        simp_rw [e]
        exact lintegral_lintegral_swap hk.aemeasurable
    _ ≤ ∫⁻ y, g y * uBnd C (∫⁻ z, h z) R :=
        lintegral_mono fun y => by gcongr; exact lintegral_time_weight_le hU hR hUR hh hhC y
    _ = (∫⁻ z, g z) * uBnd C (∫⁻ z, h z) R := lintegral_mul_const _ hg

lemma uBnd_ne_top (C : ℝ) {M : ℝ≥0∞} (hM : M ≠ ∞) (R : ℝ) : uBnd C M R ≠ ∞ :=
  (tBnd_lt_top C hM R).ne

/-- **kernel bound** (replaces `DGo.ZB.sq_norm_zbKerL2_le`): for `|ρ| ≤ C` and
`∫ |ρ| ≤ M, N`, `∫ (K_U ρ)² ≤ N · uBnd C M R` -/
theorem lintegral_sq_uKer_le (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) {M N : ℝ≥0∞} (hM : ∫⁻ z, ‖ρ z‖ₑ ≤ M) (hN : ∫⁻ z, ‖ρ z‖ₑ ≤ N) :
    ∫⁻ p, ‖uKer U I ρ p ^ 2‖ₑ ≤ N * uBnd C M R := by
  have hg : Measurable fun y => ‖ρ y‖ₑ := hρ.enorm
  calc ∫⁻ p, ‖uKer U I ρ p ^ 2‖ₑ
      ≤ ∫⁻ p, (∫⁻ y, ‖ρ y‖ₑ * ENNReal.ofReal (wndKernel U I y p)) *
          ∫⁻ y, ‖ρ y‖ₑ * ENNReal.ofReal (wndKernel U I y p) := by
        refine lintegral_mono fun p => ?_
        rw [enorm_pow, pow_two]
        exact mul_le_mul' (enorm_uKer_le ρ p) (enorm_uKer_le ρ p)
    _ = ∫⁻ x : (ℝ × ℂ) × (ℂ × ℂ), ‖ρ x.2.1‖ₑ * ‖ρ x.2.2‖ₑ *
          (ENNReal.ofReal (wndKernel U I x.2.1 x.1) *
            ENNReal.ofReal (wndKernel U I x.2.2 x.1)) := by
        rw [Measure.volume_eq_prod (α := ℝ × ℂ) (β := ℂ × ℂ), lintegral_prod
          (f := fun x : (ℝ × ℂ) × (ℂ × ℂ) => ‖ρ x.2.1‖ₑ * ‖ρ x.2.2‖ₑ *
            (ENNReal.ofReal (wndKernel U I x.2.1 x.1) * ENNReal.ofReal (wndKernel U I x.2.2 x.1)))
          (((hg.comp (measurable_fst.comp measurable_snd)).mul
            (hg.comp (measurable_snd.comp measurable_snd))).mul
            ((measurable_wndKernel_comp hU hI (measurable_fst.comp measurable_snd)
              measurable_fst).ennreal_ofReal.mul (measurable_wndKernel_comp hU hI
              (measurable_snd.comp measurable_snd) measurable_fst).ennreal_ofReal)).aemeasurable]
        refine lintegral_congr fun p => ?_
        have hA : Measurable fun y => ‖ρ y‖ₑ * ENNReal.ofReal (wndKernel U I y p) :=
          hg.mul (measurable_wndKernel_comp hU hI measurable_id measurable_const).ennreal_ofReal
        rw [Measure.volume_eq_prod (α := ℂ) (β := ℂ), ← lintegral_prod_mul hA.aemeasurable
          hA.aemeasurable]
        exact lintegral_congr fun q => by simp only; ring
    _ ≤ (∫⁻ z, ‖ρ z‖ₑ) * uBnd C (∫⁻ z, ‖ρ z‖ₑ) R :=
        lintegral_triple_le hU hR hUR hI hI0 hg hg (enorm_le_ofReal hC)
    _ ≤ N * uBnd C M R := by
        unfold uBnd
        gcongr

lemma inner_uKerL2_eq {ρ : ℂ → ℝ} (h : MemLp (uKer U I ρ) 2 volume) (G : WNSpace) :
    ⟪uKerL2 U I ρ, G⟫ = ∫ q, uKer U I ρ q * G q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_uKerL2 h] with q h1
  rw [h1, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

lemma integral_sq_uKer_le (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) {M N : ℝ≥0∞} (hM : ∫⁻ z, ‖ρ z‖ₑ ≤ M) (hN : ∫⁻ z, ‖ρ z‖ₑ ≤ N)
    (hMt : M ≠ ∞) (hNt : N ≠ ∞) :
    ∫ q, uKer U I ρ q ^ 2 ≤ (N * uBnd C M R).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun q => sq_nonneg _)
    ((measurable_uKer hU hI hρ).pow_const 2).aestronglyMeasurable]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hNt (uBnd_ne_top C hMt R)) ?_
  refine le_trans (le_of_eq (lintegral_congr fun q => ?_))
    (lintegral_sq_uKer_le hU hR hUR hI hI0 hρ hC hM hN)
  rw [Real.enorm_of_nonneg (sq_nonneg _)]

lemma sq_norm_uKerL2_eq {ρ : ℂ → ℝ} (h : MemLp (uKer U I ρ) 2 volume) :
    ‖uKerL2 U I ρ‖ ^ 2 = ∫ q, uKer U I ρ q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_uKerL2_eq h]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_uKerL2 h] with q h1
  rw [h1, sq]

/-! ### Differences of densities -/

lemma uKer_sub (hU : IsOpen U) (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {ρ σ : ℂ → ℝ}
    (hρi : Integrable ρ) (hσi : Integrable σ) : uKer U I (ρ - σ) = uKer U I ρ - uKer U I σ := by
  funext p
  simp only [uKer, Pi.sub_apply]
  rw [← integral_sub (integrable_mul_wnd hU hI hI0 hρi p) (integrable_mul_wnd hU hI hI0 hσi p)]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

lemma uKerL2_sub (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {ρ σ : ℂ → ℝ} (hρ : Measurable ρ)
    (hσ : Measurable σ) {C : ℝ} (hρC : ∀ z, |ρ z| ≤ C) (hσC : ∀ z, |σ z| ≤ C)
    (hρi : Integrable ρ) (hσi : Integrable σ) :
    uKerL2 U I (ρ - σ) = uKerL2 U I ρ - uKerL2 U I σ := by
  have h₁ := memLp_uKer hU hR hUR hI hI0 hρ hρC hρi
  have h₂ := memLp_uKer hU hR hUR hI hI0 hσ hσC hσi
  have h₀ := memLp_uKer hU hR hUR hI hI0 (hρ.sub hσ) (C := C + C)
    (fun z => (abs_sub _ _).trans (add_le_add (hρC z) (hσC z))) (hρi.sub hσi)
  rw [uKerL2, uKerL2, uKerL2, dite_eq_left_of_eq_true (eq_true h₀),
    dite_eq_left_of_eq_true (eq_true h₁), dite_eq_left_of_eq_true (eq_true h₂),
    ← MemLp.toLp_sub]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p => by
    rw [uKer_sub hU hI hI0 hρi hσi])

/-! ### The rectangle densities `ρ_x = 1_U 1_{[0,x]}` -/

/-- `ρ_x = 1_U · rectInd x` -/
def rhoU (U : Set ℂ) (x : ℂ) : ℂ → ℝ := U.indicator (rectInd x)

lemma measurable_rhoU (hU : IsOpen U) (x : ℂ) : Measurable (rhoU U x) :=
  (measurable_rectInd x).indicator hU.measurableSet

lemma abs_rhoU_le (x z : ℂ) : |rhoU U x z| ≤ 1 := by
  unfold rhoU
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz]; exact (rectInd_bddSupp x).bdd z
  · rw [indicator_of_notMem hz, abs_zero]; exact zero_le_one

lemma integrable_rhoU (hU : IsOpen U) (x : ℂ) : Integrable (rhoU U x) :=
  (rectInd_bddSupp x).integrable.indicator hU.measurableSet

lemma lintegral_enorm_le_vol (hU : IsOpen U) {ρ : ℂ → ℝ} {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    (h0 : ∀ z ∉ U, ρ z = 0) : ∫⁻ z, ‖ρ z‖ₑ ≤ ENNReal.ofReal C * volume U := by
  rw [← lintegral_indicator_const hU.measurableSet]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz]; exact enorm_le_ofReal hC z
  · rw [indicator_of_notMem hz, h0 z hz, enorm_zero]

lemma rhoU_zero (x : ℂ) : ∀ z ∉ U, rhoU U x z = 0 := fun _ hz => indicator_of_notMem hz _

lemma lintegral_enorm_rhoU_sub_le {x x' : ℂ} {A : ℝ} (h2 : |x.im| ≤ A) (h3 : |x'.re| ≤ A) :
    ∫⁻ z, ‖(rhoU U x - rhoU U x') z‖ₑ ≤ ENNReal.ofReal (4 * A * ‖x - x'‖) := by
  have hi := (rectInd_bddSupp x).integrable.sub (rectInd_bddSupp x').integrable
  calc ∫⁻ z, ‖(rhoU U x - rhoU U x') z‖ₑ ≤ ∫⁻ z, ‖(rectInd x - rectInd x') z‖ₑ := by
        refine lintegral_mono fun z => ?_
        simp only [rhoU, Pi.sub_apply]
        by_cases hz : z ∈ U
        · rw [indicator_of_mem hz, indicator_of_mem hz]
        · rw [indicator_of_notMem hz, indicator_of_notMem hz, sub_zero, enorm_zero]
          exact bot_le
    _ = ENNReal.ofReal (∫ z, |rectInd x z - rectInd x' z|) := by
        rw [ofReal_integral_eq_lintegral_ofReal (f := fun z => |rectInd x z - rectInd x' z|)
          hi.abs (ae_of_all _ fun _ => abs_nonneg _)]
        exact lintegral_congr fun z => by rw [Real.enorm_eq_ofReal_abs]; rfl
    _ ≤ _ := ENNReal.ofReal_le_ofReal (integral_abs_rectInd_sub_le h2 h3)

/-- the white-noise kernel of the antiderivative field: `√π K_U ρ_x` -/
def uRectL2 (U : Set ℂ) (x : ℂ) : WNSpace :=
  Real.sqrt Real.pi • uKerL2 U (Ioi 0) (rhoU U x)

/-- the constant of the increment bound -/
def rectBnd (U : Set ℂ) (R : ℝ) : ℝ := (uBnd 2 (ENNReal.ofReal 2 * volume U) R).toReal

lemma sq_norm_uRectL2_sub_le (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {x x' : ℂ} {A : ℝ} (hA : 0 ≤ A) (h2 : |x.im| ≤ A) (h3 : |x'.re| ≤ A) :
    ‖uRectL2 U x - uRectL2 U x'‖ ^ 2 ≤ Real.pi * rectBnd U R * (4 * A) * ‖x - x'‖ := by
  have hvol : volume U ≠ ∞ :=
    ((measure_mono hUR).trans_lt measure_ball_lt_top).ne
  have hMt : ENNReal.ofReal 2 * volume U ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol
  have hm := (measurable_rhoU hU x).sub (measurable_rhoU (U := U) hU x')
  have hC : ∀ z, |(rhoU U x - rhoU U x') z| ≤ 2 := fun z =>
    (abs_sub _ _).trans (by linarith [abs_rhoU_le (U := U) x z, abs_rhoU_le (U := U) x' z])
  have h0 : ∀ z ∉ U, (rhoU U x - rhoU U x') z = 0 := fun z hz => by
    simp [rhoU_zero x z hz, rhoU_zero x' z hz]
  rw [uRectL2, uRectL2, ← smul_sub, ← uKerL2_sub hU hR hUR measurableSet_Ioi subset_rfl
    (measurable_rhoU hU x) (measurable_rhoU hU x') (abs_rhoU_le x) (abs_rhoU_le x')
    (integrable_rhoU hU x) (integrable_rhoU hU x'), norm_smul, mul_pow,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt Real.pi_pos.le, mul_assoc,
    mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  have hmem := memLp_uKer hU hR hUR measurableSet_Ioi subset_rfl hm hC
    ((integrable_rhoU hU x).sub (integrable_rhoU hU x'))
  rw [sq_norm_uKerL2_eq hmem]
  refine (integral_sq_uKer_le hU hR hUR measurableSet_Ioi subset_rfl hm hC
    (lintegral_enorm_le_vol hU hC h0) (lintegral_enorm_rhoU_sub_le h2 h3) hMt
    ENNReal.ofReal_ne_top).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), rectBnd]
  ring

lemma rectBnd_nonneg (U : Set ℂ) (R : ℝ) : 0 ≤ rectBnd U R := ENNReal.toReal_nonneg

/-- the uniform bound `‖√π K_U ρ_x‖² ≤ π · rectBnd₁` -/
def rectBnd₁ (U : Set ℂ) (R : ℝ) : ℝ :=
  (ENNReal.ofReal 1 * volume U * uBnd 1 (ENNReal.ofReal 1 * volume U) R).toReal

lemma integral_sq_uKer_rhoU_le (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (x : ℂ) : ∫ q, uKer U (Ioi 0) (rhoU U x) q ^ 2 ≤ rectBnd₁ U R := by
  have hvol : volume U ≠ ∞ :=
    ((measure_mono hUR).trans_lt measure_ball_lt_top).ne
  have hMt : ENNReal.ofReal 1 * volume U ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol
  have hb := lintegral_enorm_le_vol hU (abs_rhoU_le (U := U) x) (rhoU_zero x)
  exact integral_sq_uKer_le hU hR hUR measurableSet_Ioi subset_rfl (measurable_rhoU hU x)
    (abs_rhoU_le x) hb hb hMt hMt

end LQGMetric.CONF.ZBM
