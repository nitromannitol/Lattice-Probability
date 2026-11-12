/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.ZBField at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirCoupling
import LatticeProb.Bonanno.LQGMetric.Field.ExistField
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub2

/-!
# The antiderivative field of the white-noise zero-boundary GFF on a square (task P2-DGZB)

DDDF's white-noise zero-boundary GFF `h^D(ρ) = √π W(zbKer ρ)` on `D = (a, a+L)²`
(`DGo.HeatDir.zbXSq`, DD:1514) is made a random distribution exactly as the whole-plane GFF was
(`Field/ExistField`, `Field/ExistGFF`, D109): the antiderivative field
`F(x) = h^D(1_D 1_{[0,x]})` (`rhoX x = 1_D · rectInd x`) has increments
`Var(F(x) − F(x')) = π‖zbKer(ρ_x − ρ_{x'})‖² ≤ C_A ‖x − x'‖` (`sq_norm_zbKerL2_le`: the kernel
bound `‖zbKer ρ‖² ≤ B ∫|ρ|` from DDDF's heat bounds `abs_integral_mul_sqDirKernel_le(_exp)`,
plus `integral_abs_rectInd_sub_le`), hence a continuous modification
(`exists_continuous_modification_of_gauss`, Kolmogorov–Čentsov).

Adapted from `GFFExist.exists_continuous_rectField` (the whole-plane kernel `kerFun` replaced by
DDDF's `zbKerFun`). Own elementary proof (as `Field/ExistField`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real
open scoped RealInnerProductSpace NNReal

namespace LQGMetric
namespace DGo
namespace ZB

open WhiteNoise HeatSq DDDF.P29WN GFFExist HeatDir

variable {a L : ℝ}

lemma integrable_bddOn (ρ : BddOn (sqOpen a L)) : Integrable ρ.1 := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
  have e : ρ.1 = (sqOpen a L).indicator ρ.1 := by
    funext z; by_cases hz : z ∈ sqOpen a L
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, h0 z hz]
  rw [e, integrable_indicator_iff (measurableSet_sqOpen a L)]
  refine Measure.integrableOn_of_bounded (M := C) (volume_sqOpen_ne_top a L)
    hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]; exact hC z

/-- the time profile bounding `|∫ ρ p^D_s ρ|` -/
def zbProf (L C : ℝ) (s : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => 4 * C) s +
    C * L ^ 2 * (decayConst L 1 ^ 2 * Real.exp (-(2 * rateC L) * s))

/-- the constant `B` of `‖zbKer ρ‖² ≤ B ∫ |ρ|` -/
def zbBnd (L C : ℝ) : ℝ := ∫ s in Ioi 0, zbProf L C s

lemma integrableOn_zbProf (hL : 0 < L) (C : ℝ) : IntegrableOn (zbProf L C) (Ioi 0) := by
  have hc0 : 0 < 2 * rateC L := by unfold rateC; positivity
  refine Integrable.add ?_ ?_
  · refine (IntegrableOn.integrable_indicator ?_ measurableSet_Ioc).integrableOn
    exact integrableOn_const (by simp)
  · exact ((exp_neg_integrableOn_Ioi 0 hc0).const_mul _).const_mul _

/-- **Kernel bound**: `‖zbKer ρ‖² ≤ B_{L,C} ∫ |ρ|` for `|ρ| ≤ C`. -/
theorem sq_norm_zbKerL2_le (hL : 0 < L) (ρ : BddOn (sqOpen a L)) {C : ℝ}
    (hC : ∀ z, |ρ.1 z| ≤ C) :
    ‖zbKerL2 a L hL ρ‖ ^ 2 ≤ zbBnd L C * ∫ z, |ρ.1 z| := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h0 := ρ.2.2.2
  have hρi := integrable_bddOn ρ
  rw [← real_inner_self_eq_norm_sq, inner_zbKerL2, zbBnd, ← integral_mul_const]
  refine (Real.le_norm_self _).trans (norm_integral_le_of_norm_le
    ((integrableOn_zbProf hL C).mul_const _) ((ae_restrict_mem measurableSet_Ioi).mono
      fun s (hs : 0 < s) => ?_))
  have hb : ∀ y', |∫ y'', sqDirKernel a L s y' y'' * ρ.1 y''| ≤ zbProf L C s := by
    intro y'
    have e : ∫ y'', sqDirKernel a L s y' y'' * ρ.1 y'' =
        ∫ y'', ρ.1 y'' * sqDirKernel a L s y'' y' := by
      congr 1; funext y''; rw [sqDirKernel_symm hs hL, mul_comm]
    rw [e]
    have hK : 0 ≤ C * L ^ 2 * (decayConst L 1 ^ 2 * Real.exp (-(2 * rateC L) * s)) := by
      positivity
    rcases le_or_gt s 1 with h1 | h1
    · have := abs_integral_mul_sqDirKernel_le hL hC h0 hs y'
      rw [zbProf, indicator_of_mem (show s ∈ Ioc (0 : ℝ) 1 from ⟨hs, h1⟩)]
      linarith
    · have := abs_integral_mul_sqDirKernel_le_exp hL hC h0 h1.le y'
      rw [zbProf, indicator_of_notMem (show s ∉ Ioc (0 : ℝ) 1 from fun h => by
        linarith [h.2])]
      linarith
  have e2 : (fun y' => ∫ y'', ρ.1 y' * sqDirKernel a L s y' y'' * ρ.1 y'') =
      fun y' => ρ.1 y' * ∫ y'', sqDirKernel a L s y' y'' * ρ.1 y'' := by
    funext y'; rw [← integral_const_mul]; congr 1; funext y''; ring
  rw [e2, mul_comm, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hρi.abs.mul_const (zbProf L C s))
    (Eventually.of_forall fun y' => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hb y') (abs_nonneg _)

/-- `y' ↦ ρ(y') p^D_r(y', y)` is integrable for bounded measurable `ρ` vanishing off `D` -/
lemma integrable_mul_sqDirKernel (hL : 0 < L) {ρ : ℂ → ℝ} (hm : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) {r : ℝ} (hr : 0 < r) (y : ℂ) :
    Integrable fun y' => ρ y' * sqDirKernel a L r y' y := by
  have hpi : IntegrableOn (fun y' => sqDirKernel a L r y y') (sqOpen a L) := by
    refine ⟨(measurable_sqDirKernel_right' hr hL y).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact (lintegral_abs_sqDirKernel_le hr hL y).trans_lt (by norm_num)
  have hpi' := (hpi.integrable_indicator (measurableSet_sqOpen a L)).norm.const_mul C
  refine hpi'.mono' ?_ (Eventually.of_forall fun y' => ?_)
  · have hpm : Measurable fun y' => sqDirKernel a L r y' y := by
      have e : (fun y' => sqDirKernel a L r y' y) = fun y' => sqDirKernel a L r y y' := by
        funext y'; exact sqDirKernel_symm hr hL y' y
      rw [e]; exact measurable_sqDirKernel_right' hr hL y
    exact (hm.mul hpm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : y' ∈ sqOpen a L
    · rw [indicator_of_mem hy, Real.norm_eq_abs, sqDirKernel_symm hr hL]
      exact mul_le_mul_of_nonneg_right (hC y') (abs_nonneg _)
    · rw [h0 y' hy, abs_zero, zero_mul, indicator_of_notMem hy, norm_zero, mul_zero]

/-- `ρ − σ` in `BddOn D` -/
def bddSub (ρ σ : BddOn (sqOpen a L)) : BddOn (sqOpen a L) :=
  ⟨fun z => ρ.1 z - σ.1 z, ρ.2.1.sub σ.2.1,
    by
      obtain ⟨C, hC⟩ := ρ.2.2.1
      obtain ⟨C', hC'⟩ := σ.2.2.1
      exact ⟨C + C', fun z => (abs_sub _ _).trans (add_le_add (hC z) (hC' z))⟩,
    fun z hz => by simp only [ρ.2.2.2 z hz, σ.2.2.2 z hz, sub_zero]⟩

lemma zbKerFun_bddSub (hL : 0 < L) (ρ σ : BddOn (sqOpen a L)) (q : ℝ × ℂ) :
    zbKerFun a L (bddSub ρ σ).1 q = zbKerFun a L ρ.1 q - zbKerFun a L σ.1 q := by
  unfold zbKerFun
  by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
  · simp only [indicator_of_mem hq]
    obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
    obtain ⟨hm', ⟨C', hC'⟩, h0'⟩ := σ.2
    have hs : 0 < q.1 / 2 := half_pos hq.1
    rw [← integral_sub (integrable_mul_sqDirKernel hL hm hC h0 hs q.2)
      (integrable_mul_sqDirKernel hL hm' hC' h0' hs q.2)]
    congr 1; funext y'; simp only [bddSub]; ring
  · simp only [indicator_of_notMem hq, sub_zero]

lemma zbKerL2_bddSub (hL : 0 < L) (ρ σ : BddOn (sqOpen a L)) :
    zbKerL2 a L hL (bddSub ρ σ) = zbKerL2 a L hL ρ - zbKerL2 a L hL σ := by
  refine Lp.ext ?_
  filter_upwards [(memLp_zbKerFun_bdd hL (bddSub ρ σ)).coeFn_toLp,
    Lp.coeFn_sub (zbKerL2 a L hL ρ) (zbKerL2 a L hL σ),
    (memLp_zbKerFun_bdd hL ρ).coeFn_toLp, (memLp_zbKerFun_bdd hL σ).coeFn_toLp]
    with q h1 h2 h3 h4
  rw [zbKerL2, h1, h2, Pi.sub_apply, zbKerL2, zbKerL2, h3, h4, zbKerFun_bddSub hL]

/-! ### The rectangle densities `ρ_x = 1_D 1_{[0,x]}` -/

/-- `ρ_x = 1_D · rectInd x` -/
def rhoX (a L : ℝ) (x : ℂ) : BddOn (sqOpen a L) :=
  ⟨(sqOpen a L).indicator (rectInd x),
    (measurable_rectInd x).indicator (measurableSet_sqOpen a L),
    ⟨1, fun z => by
      by_cases hz : z ∈ sqOpen a L
      · rw [indicator_of_mem hz]; exact (rectInd_bddSupp x).bdd z
      · rw [indicator_of_notMem hz, abs_zero]; exact zero_le_one⟩,
    fun _ hz => indicator_of_notMem hz _⟩

lemma abs_rhoX_le (x z : ℂ) : |(rhoX a L x).1 z| ≤ 1 := by
  obtain ⟨_, ⟨C, hC⟩, _⟩ := (rhoX a L x).2
  show |(sqOpen a L).indicator (rectInd x) z| ≤ 1
  by_cases hz : z ∈ sqOpen a L
  · rw [indicator_of_mem hz]; exact (rectInd_bddSupp x).bdd z
  · rw [indicator_of_notMem hz, abs_zero]; exact zero_le_one

lemma integral_abs_rhoX_sub_le {x x' : ℂ} {A : ℝ} (h2 : |x.im| ≤ A) (h3 : |x'.re| ≤ A) :
    ∫ z, |(bddSub (rhoX a L x) (rhoX a L x')).1 z| ≤ 4 * A * ‖x - x'‖ := by
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    (((rectInd_bddSupp x).integrable.sub (rectInd_bddSupp x').integrable)).abs
    (Eventually.of_forall fun z => ?_)) (integral_abs_rectInd_sub_le h2 h3)
  show |(sqOpen a L).indicator (rectInd x) z - (sqOpen a L).indicator (rectInd x') z| ≤ _
  by_cases hz : z ∈ sqOpen a L
  · rw [indicator_of_mem hz, indicator_of_mem hz]; rfl
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, sub_zero, abs_zero]; exact abs_nonneg _

lemma abs_bddSub_rhoX_le (x x' z : ℂ) : |(bddSub (rhoX a L x) (rhoX a L x')).1 z| ≤ 2 := by
  have h1 := abs_rhoX_le (a := a) (L := L) x z
  have h2 := abs_rhoX_le (a := a) (L := L) x' z
  exact (abs_sub _ _).trans (by linarith)

/-- the white-noise kernel of the antiderivative field: `√π zbKer ρ_x` -/
def zbRectL2 (a L : ℝ) (hL : 0 < L) (x : ℂ) : WNSpace :=
  Real.sqrt π • zbKerL2 a L hL (rhoX a L x)

lemma sq_norm_zbRectL2_sub_le (hL : 0 < L) {x x' : ℂ} {A : ℝ} (h2 : |x.im| ≤ A)
    (h3 : |x'.re| ≤ A) :
    ‖zbRectL2 a L hL x - zbRectL2 a L hL x'‖ ^ 2 ≤ π * zbBnd L 2 * (4 * A) * ‖x - x'‖ := by
  rw [zbRectL2, zbRectL2, ← smul_sub, ← zbKerL2_bddSub, norm_smul, mul_pow,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt Real.pi_pos.le, mul_assoc,
    mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  have hB : 0 ≤ zbBnd L 2 := by
    unfold zbBnd
    refine setIntegral_nonneg measurableSet_Ioi fun s _ => ?_
    unfold zbProf
    exact add_nonneg (indicator_nonneg (fun _ _ => by norm_num) _) (by positivity)
  refine (sq_norm_zbKerL2_le hL _ (abs_bddSub_rhoX_le x x')).trans ?_
  calc zbBnd L 2 * ∫ z, |(bddSub (rhoX a L x) (rhoX a L x')).1 z|
      ≤ zbBnd L 2 * (4 * A * ‖x - x'‖) :=
        mul_le_mul_of_nonneg_left (integral_abs_rhoX_sub_le h2 h3) hB
    _ = _ := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma hasLaw_zbRect_sub (hL : 0 < L) (hW : IsWhiteNoise P W) (x x' : ℂ) :
    HasLaw (fun ω => W (zbRectL2 a L hL x) ω - W (zbRectL2 a L hL x') ω)
      (gaussianReal 0 (‖zbRectL2 a L hL x - zbRectL2 a L hL x'‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw ![zbRectL2 a L hL x, zbRectL2 a L hL x'] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    ← sub_eq_add_neg] at h
  refine h.congr ?_
  exact Eventually.of_forall fun ω => by ring

/-- **Continuous version of the zero-boundary antiderivative field** `x ↦ h^D(1_D 1_{[0,x]})`. -/
theorem exists_continuous_zbRectField (hL : 0 < L) (hW : IsWhiteNoise P W) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] W (zbRectL2 a L hL x) := by
  have hB : 0 ≤ zbBnd L 2 := by
    unfold zbBnd
    refine setIntegral_nonneg measurableSet_Ioi fun s _ => ?_
    unfold zbProf
    exact add_nonneg (indicator_nonneg (fun _ _ => by norm_num) _) (by positivity)
  refine exists_continuous_modification_of_gauss (fun x => hW.measurable _)
    (fun x x' => (‖zbRectL2 a L hL x - zbRectL2 a L hL x'‖ ^ 2).toNNReal)
    (hasLaw_zbRect_sub hL hW)
    (fun A => ⟨π * zbBnd L 2 * (4 * |A|), by positivity, fun x x' h0 h1 h2 h3 => ?_⟩)
  have hA : 0 ≤ A := (abs_nonneg _).trans h0
  rw [Real.coe_toNNReal', max_le_iff, abs_of_nonneg hA]
  exact ⟨sq_norm_zbRectL2_sub_le hL h1 h2, by positivity⟩

end ZB
end DGo
end LQGMetric
