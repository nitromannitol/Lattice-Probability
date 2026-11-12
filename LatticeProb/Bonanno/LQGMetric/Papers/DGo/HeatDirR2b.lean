/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR2b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR2a
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirGreen

/-!
# DGo (3.10): `max_v Var Δ_δ(v) = O_{𝒰,ε}(1)` on a square (task P2-HEAT2, packet R2)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, proof of Prop 3.3, (3.10) (DGo:618–700),
for `𝒰 = D = (a, a+L)²`: **`dgo_var_bound`**

  `∀ ε > 0, ∃ σ², ∀ δ ∈ (0, ε/4), ∀ v, B̄_ε(v) ⊆ D → ‖√π (K^D_{δ,v} − k_{δ,1,v})‖² ≤ σ²`,

where `K^D_{δ,v} = dirCircKernel a L δ v` (the kernel of `ĥ^D_δ(v)`) and `k_{δ,1,v} =
phiKernelL2 δ 1 v` (the kernel of `η_δ(v)`), i.e. `Var(ĥ^D_δ(v) − η_δ(v)) ≤ σ²` for every white noise.

As in DGo, the difference is split by time (pointwise, `abs_dirCircFun_sub_phiKernel_le`):
* `G_{v;1}` (`s ≥ 1`) and the part of `G_{v;3}` inside `D`: bounded by `K e^{−cs} 1_D(z)`
  (`DDDF.P29WN.abs_sqDirKernel_le_exp` for `s ≥ 2`; `|p^D_s − p_s| ≤ M₀` for `s ≤ 1`,
  `HeatSq.abs_sqDirKernel_sub_le`, at margin `ε/2`). This replaces DGo's Brownian-bridge bounds
  for `G_{v;1}` and `G_{v;3}` by the image-series estimates (proposed DEVIATIONS HEAT2-2);
* `G_{v;2}` (`s < δ²`): `lintegral_freeCircFun_sq_le`;
* `G_{v;4}`: `lintegral_g4Fun_sq_le`;
* the part of `G_{v;3}` outside `D` (`η`'s kernel at `|z − v| > ε`): `lintegral_g6Fun_sq_le`.
The near-miss `HeatDir.abs_dirCircFun_le` (P2-HEAT1, bound with a margin depending on `δ`) is
adapted here with the uniform margin `ε/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set Function Metric
open scoped ENNReal Interval

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq

variable {a L δ ε : ℝ} {v : ℂ}

/-- the off-domain part of `η`'s kernel: `1_{(0,1]}(s) 1_{|z−v|>ε} p_{s/2}(v, z)` -/
def g6Fun (ε : ℝ) (v : ℂ) (q : ℝ × ℂ) : ℝ :=
  (Ioc 0 1 ×ˢ (closedBall v ε)ᶜ).indicator (fun q => heatKernel (q.1 / 2) v q.2) q

lemma measurable_g6Fun : Measurable (g6Fun ε v) :=
  (WhiteNoise.measurable_heatKernel_half v).indicator
    (measurableSet_Ioc.prod measurableSet_closedBall.compl)

lemma heatKernel_half_le {s : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) {z : ℂ} (hr : ε ≤ ‖v - z‖) :
    heatKernel (s / 2) v z ≤ 2 * Real.exp (-ε ^ 2 / (2 * s)) * heatKernel s v z := by
  unfold heatKernel
  have key : -‖v - z‖ ^ 2 / (2 * (s / 2)) ≤ -ε ^ 2 / (2 * s) + -‖v - z‖ ^ 2 / (2 * s) := by
    rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ε, mul_le_mul hr hr hε (norm_nonneg _)]
  have h1 := Real.exp_le_exp.2 key
  rw [Real.exp_add] at h1
  have e : (2 * π * (s / 2))⁻¹ = 2 * (2 * π * s)⁻¹ := by field_simp
  rw [e]
  have hp : 0 ≤ (2 * π * s)⁻¹ := by positivity
  nlinarith [Real.exp_pos (-ε ^ 2 / (2 * s))]

/-- **the off-domain part** (part of `G_{v;3}`, DGo:670–682): `∫∫ g₆² ≤ (π ε²)⁻¹`. -/
theorem lintegral_g6Fun_sq_le (hε : 0 < ε) (v : ℂ) :
    ∫⁻ q, ENNReal.ofReal (g6Fun ε v q ^ 2) ≤ ENNReal.ofReal ((π * ε ^ 2)⁻¹) := by
  set F : ℝ × ℂ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (4 * q.1 / ε ^ 2) * ENNReal.ofReal (heatKernel q.1 v q.2 * heatKernel q.1 v q.2)
  have hF : Measurable F := by
    have : Measurable fun q : ℝ × ℂ => heatKernel q.1 v q.2 := by unfold heatKernel; fun_prop
    exact (ENNReal.measurable_ofReal.comp ((measurable_fst.const_mul 4).div_const _)).mul
      (ENNReal.measurable_ofReal.comp (this.mul this))
  have hpt : ∀ q, ENNReal.ofReal (g6Fun ε v q ^ 2) ≤ (Ioc 0 1 ×ˢ (univ : Set ℂ)).indicator F q := by
    intro q
    by_cases hq : q ∈ Ioc (0 : ℝ) 1 ×ˢ (closedBall v ε)ᶜ
    · have hs : 0 < q.1 := hq.1.1
      have hr : ε ≤ ‖v - q.2‖ := by
        have := hq.2; simp only [mem_compl_iff, mem_closedBall, not_le, dist_eq_norm] at this
        rw [norm_sub_rev]; exact this.le
      rw [indicator_of_mem (show q ∈ Ioc (0 : ℝ) 1 ×ˢ (univ : Set ℂ) from ⟨hq.1, trivial⟩)]
      simp only [F, g6Fun, indicator_of_mem hq]
      rw [← ENNReal.ofReal_mul (by have := hq.1.1; positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := heatKernel_half_le hs hε.le hr
      have h0 := heatKernel_nonneg (q.1 / 2) (by linarith) v q.2
      have hp0 := heatKernel_nonneg q.1 hs.le v q.2
      have hexp : Real.exp (-ε ^ 2 / (2 * q.1)) ^ 2 ≤ q.1 / ε ^ 2 := by
        rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-ε ^ 2 / (2 * q.1)) = -(ε ^ 2 / q.1) by
          push_cast; field_simp, Real.exp_neg]
        have hu : 0 < ε ^ 2 / q.1 := by positivity
        have := Real.add_one_le_exp (ε ^ 2 / q.1)
        rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : ε ^ 2 / q.1 ≤ Real.exp (ε ^ 2 / q.1) := by linarith
        rw [div_le_iff₀ hs] at this
        nlinarith
      calc heatKernel (q.1 / 2) v q.2 ^ 2
          ≤ (2 * Real.exp (-ε ^ 2 / (2 * q.1)) * heatKernel q.1 v q.2) ^ 2 :=
            pow_le_pow_left₀ h0 h1 2
        _ = 4 * Real.exp (-ε ^ 2 / (2 * q.1)) ^ 2 * (heatKernel q.1 v q.2 * heatKernel q.1 v q.2) := by
            ring
        _ ≤ 4 * (q.1 / ε ^ 2) * (heatKernel q.1 v q.2 * heatKernel q.1 v q.2) := by
            gcongr
        _ = _ := by ring
    · simp only [g6Fun, indicator_of_notMem hq]; simp
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ), Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hF.aemeasurable]
  have hin : ∀ s ∈ Ioc (0 : ℝ) 1, ∫⁻ z, F (s, z) = ENNReal.ofReal ((π * ε ^ 2)⁻¹) := by
    intro s hs
    simp only [F]
    have hm : Measurable fun z : ℂ => heatKernel s v z := by unfold heatKernel; fun_prop
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal
        (WhiteNoise.integrable_heatKernel_mul_heatKernel s hs.1 v v)
        (Filter.Eventually.of_forall fun z => mul_nonneg (heatKernel_nonneg _ hs.1.le _ _)
          (heatKernel_nonneg _ hs.1.le _ _)),
      WhiteNoise.integral_heatKernel_mul_heatKernel s hs.1, ← ENNReal.ofReal_mul (by
        have := hs.1; positivity)]
    congr 1
    unfold heatKernel
    simp only [sub_self, norm_zero]
    have := hs.1
    field_simp
    norm_num
  rw [setLIntegral_congr_fun measurableSet_Ioc hin, setLIntegral_const, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_one, mul_one]

/-- `|p^D_s(x, z) − p_s(x, z)| ≤ M₀` for `0 < s ≤ 1`, `x` at margin `d`, `z ∈ D` (adapted from
`abs_sqDirKernel_le_heat_add`) -/
lemma abs_sqDirKernel_sub_heat_le (hL : 0 < L) {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hs1 : s ≤ 1)
    {x z : ℂ} (hxre : x.re ∈ Icc (a + d) (a + L - d)) (hxim : x.im ∈ Icc (a + d) (a + L - d))
    (hz : z ∈ sqOpen a L) :
    |sqDirKernel a L s x z - heatKernel s x z| ≤ smallConst d L := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have h := abs_sqDirKernel_sub_le (a := a) hs hs1 hd hL (y' := z) (y := x) ⟨h1.le, h2.le⟩
    ⟨h3.le, h4.le⟩ hxre hxim
  rw [← sqDirKernel_symm hs hL, heatKernel_symm] at h
  have hK : 0 ≤ 4 * imgConst d L + 4 * imgConst d L ^ 2 := by
    have := imgConst_nonneg d L; positivity
  have hd' : heatKernel s (d : ℂ) 0 ≤ 2 * (π * d ^ 2)⁻¹ :=
    (heatKernel_d_le_exp hs hd).trans (by
      have : Real.exp (-(d ^ 2 / 4) / s) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 ≤ d ^ 2 / 4 / s := by positivity
        rw [neg_div]; linarith)
      have : 0 ≤ 2 * (π * d ^ 2)⁻¹ := by positivity
      nlinarith)
  exact h.trans (mul_le_mul_of_nonneg_left hd' hK)

/-- the uniform margin: `B̄_ε(v) ⊆ D`, `δ < ε/4` put `∂B_δ(v)` at margin `ε/2` -/
lemma circle_margin (hB : closedBall v ε ⊆ sqOpen a L) (hδ : 0 < δ) (hδε : δ < ε / 4) (θ : ℝ) :
    (circleMap v δ θ).re ∈ Icc (a + ε / 2) (a + L - ε / 2) ∧
      (circleMap v δ θ).im ∈ Icc (a + ε / 2) (a + L - ε / 2) := by
  have hε : 0 ≤ ε := by linarith
  have mem : ∀ w : ℂ, ‖w‖ = ε → v + w ∈ sqOpen a L := fun w hw =>
    hB (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hw])
  have p1 := mem ε (by simp [abs_of_nonneg hε])
  have p2 := mem (-ε) (by simp [abs_of_nonneg hε])
  have p3 := mem (ε * Complex.I) (by simp [abs_of_nonneg hε])
  have p4 := mem (-(ε * Complex.I)) (by simp [abs_of_nonneg hε])
  simp only [sqOpen, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] at p1 p2 p3 p4
  have hd : ‖circleMap v δ θ - v‖ = δ := by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hδ]
  have hre := Complex.abs_re_le_norm (circleMap v δ θ - v)
  have him := Complex.abs_im_le_norm (circleMap v δ θ - v)
  rw [hd, Complex.sub_re] at hre
  rw [hd, Complex.sub_im] at him
  have := abs_le.1 hre
  have := abs_le.1 him
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

end HeatDir
end DGo
end LQGMetric
