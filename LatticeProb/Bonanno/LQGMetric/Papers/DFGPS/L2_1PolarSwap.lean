/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1PolarSwap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarCont
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: radial truncations about `z`

`g*_ε(z)` is defined (GM (1.2), `heatMollify`) as `lim_n ⟨g, p_s(z,·) χ_n⟩` with cutoffs `χ_n`
centred at `0`; the polar formula of DFGPS T:715–722 needs test functions radial about `z`. Here:

* `radCut n`: a smooth radial cutoff, `1` on `B̄_{n+1}(0)`, `0` off `B_{n+2}(0)` (from mathlib's
  radial bump base `ContDiffBumpBase.ofInnerProductSpace`);
* `radTrunc s z n = p_s(z,·) ρ_n(· − z)` (radial about `z`);
* `ae_tendsto_heatTrunc_sub_radTrunc`: for a whole-plane GFF, a.s.
  `⟨g, p_s(z,·)χ_n⟩ − ⟨g, p_s(z,·)ρ_n(· − z)⟩ → 0` — the difference is `≤ K e^{−n}` and supported in
  `B_{n+3+‖z‖}`, so `IsWholePlaneGFF.ae_summable_abs_of_decay` (Field/HeatMollifyPoint) applies
  after a shift of the index. Own elementary argument (the paper works with `h*_ε(z)` directly).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

open LFPP

lemma radCut_R (n : ℕ) : 1 < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
  rw [one_lt_div (by positivity)]; linarith

/-- smooth radial cutoff: `1` on `B̄_{n+1}(0)`, `0` off `B_{n+2}(0)` -/
def radCut (n : ℕ) (y : ℂ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun (((n : ℝ) + 2) / ((n : ℝ) + 1))
    (((n : ℝ) + 1)⁻¹ • y)

lemma contDiff_radCut (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radCut n) := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun y : ℂ => ((((n : ℝ) + 2) / ((n : ℝ) + 1)), ((n : ℝ) + 1)⁻¹ • y) :=
    contDiff_const.prodMk (contDiff_id.const_smul _)
  exact ((ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hf
    fun _ => ⟨radCut_R n, mem_univ _⟩).of_le le_rfl

lemma radCut_mem_Icc (n : ℕ) (y : ℂ) : radCut n y ∈ Icc (0 : ℝ) 1 :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _

lemma norm_radCut_arg (n : ℕ) (y : ℂ) : ‖((n : ℝ) + 1)⁻¹ • y‖ = ‖y‖ / ((n : ℝ) + 1) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_eq_div]

lemma radCut_eq_one (n : ℕ) {y : ℂ} (hy : ‖y‖ ≤ (n : ℝ) + 1) : radCut n y = 1 := by
  refine (ContDiffBumpBase.ofInnerProductSpace ℂ).eq_one _ (radCut_R n) _ ?_
  rw [norm_radCut_arg, div_le_one (by positivity)]
  exact hy

lemma radCut_eq_zero (n : ℕ) {y : ℂ} (hy : (n : ℝ) + 2 ≤ ‖y‖) : radCut n y = 0 := by
  have hs := (ContDiffBumpBase.ofInnerProductSpace ℂ).support _ (radCut_R n)
  by_contra hne
  have hm : ((n : ℝ) + 1)⁻¹ • y ∈ Function.support
      ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun (((n : ℝ) + 2) / ((n : ℝ) + 1))) := hne
  rw [hs, mem_ball_zero_iff, norm_radCut_arg, div_lt_div_iff_of_pos_right (by positivity)] at hm
  linarith

lemma radCut_radial (n : ℕ) (y : ℂ) : radCut n y = radCut n (‖y‖ : ℂ) := by
  simp only [radCut, ContDiffBumpBase.ofInnerProductSpace, norm_smul, Complex.norm_real,
    norm_norm]

attribute [irreducible] radCut

/-- `w ↦ p_s(z,w) ρ_n(w − z)`, radial about `z` -/
def radTrunc (s : ℝ) (z : ℂ) (n : ℕ) : TestC where
  toFun := fun w => heatKernel s z w * radCut n (w - z)
  contDiff' := (contDiff_heatKernel_left s z).mul
    ((contDiff_radCut n).comp (contDiff_id.sub contDiff_const))
  hasCompactSupport' := HasCompactSupport.intro (isCompact_closedBall z ((n : ℝ) + 2))
    fun w hw => by
      rw [mem_closedBall, not_le, dist_eq_norm] at hw
      simp only [radCut_eq_zero n hw.le, mul_zero]
  tsupport_subset' := subset_univ _

lemma radTrunc_apply (s : ℝ) (z : ℂ) (n : ℕ) (w : ℂ) :
    radTrunc s z n w = heatKernel s z w * radCut n (w - z) := rfl

lemma abs_heatTrunc_sub_radTrunc_le (s : ℝ) (hs : 0 < s) (z : ℂ) (n : ℕ) (w : ℂ) :
    |heatTrunc s z n w - radTrunc s z n w| ≤
      (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + 2 * ‖z‖) * Real.exp (-(n : ℝ)) := by
  rw [heatTrunc_apply, radTrunc_apply, ← mul_sub]
  have hp := heatKernel_nonneg s hs.le z w
  have hwz : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := norm_sub_norm_le w z
  by_cases hw : ‖w‖ ≤ (n : ℝ) + 1 - ‖z‖
  · have h1 : (cutoff n : ℂ → ℝ) w = 1 := (cutoff n).one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right]; show ‖w‖ ≤ (n : ℝ) + 1; linarith [norm_nonneg z])
    have h2 : radCut n (w - z) = 1 := radCut_eq_one n (by
      linarith [norm_sub_le w z])
    rw [h1, h2, sub_self, mul_zero, abs_zero]; positivity
  push Not at hw
  have hc : |(cutoff n : ℂ → ℝ) w - radCut n (w - z)| ≤ 1 := by
    have := (cutoff n).nonneg (x := w); have := (cutoff n).le_one (x := w)
    have := radCut_mem_Icc n (w - z)
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  rw [abs_mul, abs_of_nonneg hp]
  refine (mul_le_of_le_one_right hp hc).trans ?_
  unfold heatKernel
  rw [mul_assoc _ (Real.exp (s / 2 + 2 * ‖z‖))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (2 * Real.pi * s)⁻¹)
  refine (exp_neg_sq_div_le s _ hs).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le w z
  linarith

lemma heatTrunc_sub_radTrunc_eq_zero (s : ℝ) (z : ℂ) (n : ℕ) (w : ℂ)
    (hw : (n : ℝ) + 2 + ‖z‖ ≤ ‖w‖) : heatTrunc s z n w - radTrunc s z n w = 0 := by
  have hwz : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := norm_sub_norm_le w z
  rw [heatTrunc_eq_zero s z n w (by linarith [norm_nonneg z]), radTrunc_apply,
    radCut_eq_zero n (by linarith), mul_zero, sub_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → DistC}

/-- **Swapping the cutoffs**: a.s. `⟨g, p_s(z,·)χ_n⟩ − ⟨g, p_s(z,·)ρ_n(· − z)⟩ → 0`. -/
theorem ae_tendsto_heatTrunc_sub_radTrunc (hg : IsWholePlaneGFF g P) {s : ℝ} (hs : 0 < s)
    (z : ℂ) : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => g ω (heatTrunc s z n) - g ω (radTrunc s z n))
      atTop (𝓝 0) := by
  classical
  set c : ℕ := ⌈‖z‖⌉₊
  have hc : ‖z‖ ≤ c := Nat.le_ceil _
  set φ : ℕ → TestC := fun k =>
    if c ≤ k then heatTrunc s z (k - c) - radTrunc s z (k - c) else 0
  set K0 := (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + 2 * ‖z‖)
  have hK : 0 ≤ K0 * Real.exp c := by positivity
  have hb : ∀ (k : ℕ) (w : ℂ), |φ k w| ≤ K0 * Real.exp c * Real.exp (-(k : ℝ)) := by
    intro k w
    by_cases hk : c ≤ k
    · simp only [φ, if_pos hk]
      refine (abs_heatTrunc_sub_radTrunc_le s hs z (k - c) w).trans (le_of_eq ?_)
      show K0 * Real.exp (-((k - c : ℕ) : ℝ)) = _
      rw [Nat.cast_sub hk, mul_assoc K0, ← Real.exp_add]
      congr 2; ring
    · simp only [φ, if_neg hk]
      show |(0 : ℝ)| ≤ _
      rw [abs_zero]; positivity
  have hsupp : ∀ (k : ℕ) (w : ℂ), (k : ℝ) + 3 ≤ ‖w‖ → φ k w = 0 := by
    intro k w hw
    by_cases hk : c ≤ k
    · simp only [φ, if_pos hk]
      refine heatTrunc_sub_radTrunc_eq_zero s z (k - c) w ?_
      rw [Nat.cast_sub hk]; linarith
    · simp only [φ, if_neg hk]; rfl
  filter_upwards [hg.ae_summable_abs_of_decay φ hK hb hsupp] with ω hω
  have h0 : Tendsto (fun k => |g ω (φ k)|) atTop (𝓝 0) := hω.tendsto_atTop_zero
  have h1 : Tendsto (fun k => g ω (φ k)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 h0
  have h2 := (tendsto_add_atTop_iff_nat c).2 h1
  refine h2.congr fun n => ?_
  simp only [φ, if_pos (Nat.le_add_left c n), Nat.add_sub_cancel, map_sub]

end LQGMetric.DFGPS
