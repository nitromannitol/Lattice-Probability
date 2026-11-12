/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.ZBSFub at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBField
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBSFubG

/-!
# Stochastic Fubini for the white-noise zero-boundary GFF on a square (task P2-DGZB)

For the continuous version `Y` of `x ↦ √π W(zbKer ρ_x)` (`exists_continuous_zbRectField`,
`ρ_x = 1_D 1_{[0,x]}`):

  `∫ ∂_re∂_im φ(x) Y(x) dx = h^D(φ 1_D) = √π W(zbKer(φ 1_D))` a.s. (`ae_integral_d12_mul_zb`).

Deterministic half `integral_d12_mul_zbKerFun_rho`: pointwise in `(s, y)`,
`∫ ∂_re∂_im φ(x) zbKer(ρ_x)(s, y) dx = zbKer(φ 1_D)(s, y)` (Fubini over `(x, y')` and
`GFFExist.integral_d12_mul_rectInd`), as `GFFExist.integral_d12_mul_kerFun` for the whole plane.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace ZB

open WhiteNoise HeatSq DDDF.P29WN GFFExist HeatDir

variable {a L : ℝ}

lemma measurable_indicator_rectInd₂ (a L : ℝ) :
    Measurable fun p : ℂ × ℂ => (sqOpen a L).indicator (rectInd p.1) p.2 := by
  have e : (fun p : ℂ × ℂ => (sqOpen a L).indicator (rectInd p.1) p.2) =
      {p : ℂ × ℂ | p.2 ∈ sqOpen a L}.indicator (fun p => rectInd p.1 p.2) := by
    funext p; by_cases h : p.2 ∈ sqOpen a L <;> simp [indicator, h]
  rw [e]
  exact measurable_rectInd₂.indicator (measurable_snd (measurableSet_sqOpen a L))

lemma measurable_zbKerFun_rho (hL : 0 < L) :
    Measurable fun p : ℂ × (ℝ × ℂ) => zbKerFun a L (rhoX a L p.1).1 p.2 := by
  have hF : StronglyMeasurable (Function.uncurry fun (p : ℂ × (ℝ × ℂ)) (y' : ℂ) =>
      (sqOpen a L).indicator (rectInd p.1) y' *
        (if 0 < p.2.1 / 2 then sqDirKernel a L (p.2.1 / 2) y' p.2.2 else 0)) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((measurable_indicator_rectInd₂ a L).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (measurable_sqDirKernel_joint (a := a) hL
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).div_const 2) measurable_snd
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hG := (hF.integral_prod_right (ν := (volume : Measure ℂ))).measurable
  have e : (fun p : ℂ × (ℝ × ℂ) => zbKerFun a L (rhoX a L p.1).1 p.2) =
      {p : ℂ × (ℝ × ℂ) | p.2 ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L}.indicator (fun p =>
        ∫ y', (sqOpen a L).indicator (rectInd p.1) y' *
          (if 0 < p.2.1 / 2 then sqDirKernel a L (p.2.1 / 2) y' p.2.2 else 0)) := by
    funext p
    unfold zbKerFun
    by_cases hq : p.2 ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
    · have h2 : 0 < p.2.1 / 2 := half_pos hq.1
      simp only [indicator_of_mem hq, mem_setOf_eq, if_pos h2]
      rw [indicator_of_mem (show p ∈ {p : ℂ × (ℝ × ℂ) | p.2 ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L}
        from hq)]
      congr 1; funext y'; rw [if_pos h2]; rfl
    · simp only [indicator_of_notMem hq]
      rw [indicator_of_notMem (show p ∉ {p : ℂ × (ℝ × ℂ) | p.2 ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L}
        from hq)]
  rw [e]
  exact hG.indicator (measurable_snd ((measurableSet_Ioi).prod (measurableSet_sqOpen a L)))

/-- `y ↦ |p^D_r(y, y')|` is integrable on `D` -/
lemma integrableOn_sqDirKernel (hL : 0 < L) {r : ℝ} (hr : 0 < r) (y : ℂ) :
    IntegrableOn (fun y' => sqDirKernel a L r y' y) (sqOpen a L) := by
  have e : (fun y' => sqDirKernel a L r y' y) = fun y' => sqDirKernel a L r y y' := by
    funext y'; exact sqDirKernel_symm hr hL y' y
  rw [e]
  refine ⟨(measurable_sqDirKernel_right' hr hL y).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  simp_rw [Real.enorm_eq_ofReal_abs]
  exact (lintegral_abs_sqDirKernel_le hr hL y).trans_lt (by norm_num)

/-- **Kernel identity**: `∫ ∂_re∂_im φ(x) zbKer(ρ_x) dx = zbKer(φ 1_D)` pointwise. -/
theorem integral_d12_mul_zbKerFun_rho (hL : 0 < L) (φ : TestC) (q : ℝ × ℂ) :
    ∫ x, d12 φ x * zbKerFun a L (rhoX a L x).1 q =
      zbKerFun a L ((sqOpen a L).indicator φ) q := by
  unfold zbKerFun
  by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
  swap
  · simp only [indicator_of_notMem hq, mul_zero, integral_zero]
  simp only [indicator_of_mem hq]
  have hs : 0 < q.1 / 2 := half_pos hq.1
  set p : ℂ → ℝ := fun y' => sqDirKernel a L (q.1 / 2) y' q.2 with hp
  have hpm : Measurable p := by
    have e : p = fun y' => sqDirKernel a L (q.1 / 2) q.2 y' := by
      funext y'; exact sqDirKernel_symm hs hL y' q.2
    rw [e]; exact measurable_sqDirKernel_right' hs hL q.2
  set F : ℂ × ℂ → ℝ := fun z => d12 φ z.1 * ((sqOpen a L).indicator (rectInd z.1) z.2 * p z.2)
    with hF
  have hFm : Measurable F :=
    ((d12 φ).continuous.measurable.comp measurable_fst).mul
      ((measurable_indicator_rectInd₂ a L).mul (hpm.comp measurable_snd))
  have hpi := ((integrableOn_sqDirKernel (a := a) hL hs q.2).integrable_indicator
    (measurableSet_sqOpen a L)).norm
  have hFi : Integrable F (volume.prod volume) := by
    refine ((GFFInv.integrable_test (d12 φ)).norm.mul_prod hpi).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    simp only [hF, norm_mul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    by_cases hz : z.2 ∈ sqOpen a L
    · rw [indicator_of_mem hz, indicator_of_mem hz]
      exact mul_le_of_le_one_left (abs_nonneg _) ((rectInd_bddSupp z.1).bdd z.2)
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]; simp
  have e1 : ∀ x, d12 φ x * ∫ y', (rhoX a L x).1 y' * p y' = ∫ y', F (x, y') := fun x => by
    rw [← integral_const_mul]; rfl
  refine (integral_congr_ae (Eventually.of_forall e1)).trans ?_
  rw [integral_integral_swap (f := fun x y' => F (x, y')) hFi]
  congr 1; funext y'
  simp only [hF]
  by_cases hy : y' ∈ sqOpen a L
  · simp only [indicator_of_mem hy]
    have e2 : (fun x => d12 φ x * (rectInd x y' * p y')) =
        fun x => (d12 φ x * rectInd x y') * p y' := by funext x; ring
    rw [e2, integral_mul_const, integral_d12_mul_rectInd]
  · simp only [indicator_of_notMem hy, zero_mul, mul_zero, integral_zero]

lemma integral_sq_zbKerFun_rho_le (hL : 0 < L) (x : ℂ) :
    ∫ q, zbKerFun a L (rhoX a L x).1 q ^ 2 ≤ zbBnd L 1 * L ^ 2 := by
  have h := sq_norm_zbKerL2_le hL (rhoX a L x) (abs_rhoX_le x)
  rw [← real_inner_self_eq_norm_sq, L2.inner_def] at h
  have e : ∫ q, ⟪(zbKerL2 a L hL (rhoX a L x) : ℝ × ℂ → ℝ) q,
      (zbKerL2 a L hL (rhoX a L x) : ℝ × ℂ → ℝ) q⟫ = ∫ q, zbKerFun a L (rhoX a L x).1 q ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_zbKerFun_bdd hL (rhoX a L x)).coeFn_toLp] with q h1
    simp only [zbKerL2, h1, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [e] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hint : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (sqOpen a L) :=
      integrableOn_const (volume_sqOpen_ne_top a L)
    calc ∫ z, |(rhoX a L x).1 z| ≤ ∫ z, (sqOpen a L).indicator (fun _ => (1 : ℝ)) z := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hint.integrable_indicator (measurableSet_sqOpen a L))
            (Eventually.of_forall fun z => ?_)
          show |(sqOpen a L).indicator (rectInd x) z| ≤ _
          by_cases hz : z ∈ sqOpen a L
          · rw [indicator_of_mem hz, indicator_of_mem hz]; exact (rectInd_bddSupp x).bdd z
          · rw [indicator_of_notMem hz, indicator_of_notMem hz, abs_zero]
      _ = L ^ 2 := by
          rw [integral_indicator (measurableSet_sqOpen a L), setIntegral_const, smul_eq_mul,
            mul_one, measureReal_def, volume_sqOpen a L hL.le, ENNReal.toReal_ofReal (sq_nonneg _)]
  · unfold zbBnd
    refine setIntegral_nonneg measurableSet_Ioi fun s _ => ?_
    unfold zbProf
    exact add_nonneg (indicator_nonneg (fun _ _ => by norm_num) _) (by positivity)

lemma inner_zbKerL2_eq (hL : 0 < L) (ρ : BddOn (sqOpen a L)) (G : WNSpace) :
    ⟪zbKerL2 a L hL ρ, G⟫ = ∫ q, zbKerFun a L ρ.1 q * G q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_zbKerFun_bdd hL ρ).coeFn_toLp] with q h1
  rw [zbKerL2, h1, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

/-- the deterministic half: `∫ ∂_re∂_im φ(x) ⟪√π zbKer ρ_x, G⟫ dx = ⟪√π zbKer(φ 1_D), G⟫` -/
theorem integral_d12_mul_inner_zbRect (hL : 0 < L) (φ : TestC) (G : WNSpace) :
    ∫ x, d12 φ x * ⟪zbRectL2 a L hL x, G⟫ =
      ⟪Real.sqrt π • zbKerL2 a L hL (extZeroTest (sqOpens a L) φ), G⟫ := by
  simp only [zbRectL2, real_inner_smul_left, inner_zbKerL2_eq]
  have e : ∀ x, d12 φ x * (Real.sqrt π * ∫ q, zbKerFun a L (rhoX a L x).1 q * G q) =
      Real.sqrt π * (d12 φ x * ∫ q, zbKerFun a L (rhoX a L x).1 q * G q) := fun x => by ring
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  refine Eq.trans ?_ (inner_zbKerL2_eq hL (extZeroTest (sqOpens a L) φ) G).symm
  exact integral_d12_mul_inner_gen φ (fun x => zbKerFun a L (rhoX a L x).1)
    (measurable_zbKerFun_rho hL) (fun x => memLp_zbKerFun_bdd hL (rhoX a L x))
    (integral_sq_zbKerFun_rho_le hL) _ (integral_d12_mul_zbKerFun_rho hL φ) G

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Stochastic Fubini for the zero-boundary GFF**: `∫ ∂_re∂_im φ Y = h^D(φ 1_D)` a.s. -/
theorem ae_integral_d12_mul_zb (hL : 0 < L) (hW : IsWhiteNoise P W) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (zbRectL2 a L hL x)) (φ : TestC) :
    (fun ω => ∫ x, d12 φ x * Y x ω) =ᵐ[P] zbXSq a L hL W (extZeroTest (sqOpens a L) φ) := by
  have hRb : ∀ x, ‖zbRectL2 a L hL x‖ ^ 2 ≤ π * (zbBnd L 1 * L ^ 2) := by
    intro x
    rw [zbRectL2, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt Real.pi_pos.le]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    have h := integral_sq_zbKerFun_rho_le (a := a) hL x
    rw [← real_inner_self_eq_norm_sq, inner_zbKerL2_eq]
    refine le_trans (le_of_eq ?_) h
    refine integral_congr_ae ?_
    filter_upwards [(memLp_zbKerFun_bdd hL (rhoX a L x)).coeFn_toLp] with q h1
    rw [zbKerL2, h1, sq]
  exact ae_integral_d12_mul_eq_gen hW hRb hYc hYm hYW φ (integral_d12_mul_inner_zbRect hL φ)

end ZB
end DGo
end LQGMetric
