/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDir at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirFree
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29WN

/-!
# DGo (3.1): the Dirichlet circle kernel `dirCircKernel` on a square (task P2-HEAT1, packet R0)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, (3.1) (DGo:491–494):
`ĥ^𝒰_δ(v) = √π ∫_{𝒰 × ℝ₊} (2π)⁻¹ ∫_0^{2π} p^𝒰(s/2; v + δe^{iθ}, w) dθ W(dw, ds)`.
For `𝒰 = D = (a, a+L)²` (`HeatSq.sqOpen a L`) with `p^D = HeatSq.sqDirKernel a L` (image series):

* `integrableOn_sqDirKernel_Ioi_one` — large-time decay: `∫_1^∞ |p^D_s(x,y)| ds < ∞`
  (from `DDDF.P29WN.abs_sqDirKernel_le_exp`, `|p^D_s| ≤ K e^{−2cs}`, `s ≥ 1`).
  Chapman–Kolmogorov for `sqDirKernel` is `HeatSq.integral_sqDirKernel_mul` (already proved, from
  the 1-d image-series CK `HeatSq.integral_intervalDirKernel_mul`).
* `dirCircFun a L δ v` — `(s, z) ↦ 1_{s>0} 1_D(z) (2π)⁻¹ ∫_0^{2π} p^D_{s/2}(v + δe^{iθ}, z) dθ`.
* `memLp_dirCircFun` — it is in `L²(ℝ × ℂ)` when `δ > 0` and `closedBall v δ ⊆ D`.
* `dirCircKernel a L δ v : WNSpace` — its `L²` class (junk `0` outside these hypotheses, as for
  `phiKernelL2`).

Proof of `memLp_dirCircFun`: for `s ≤ 2`, `|p^D_{s/2} − p_{s/2}| ≤ M` on the circle (margin `d` of
the compact circle in `D`, `HeatSq.abs_sqDirKernel_sub_le`), so the kernel is dominated by the
circle-averaged free kernel (`HeatDir.memLp_freeCircFun`) plus a constant; for `s > 2`,
`|p^D_{s/2}| ≤ K e^{−cs}`. Own elementary arrangement (proposed DEVIATIONS HEAT1-1).
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

variable {a L δ : ℝ} {v : ℂ}

/-- DGo's circle-averaged Dirichlet kernel on the square, as a function on `ℝ × ℂ`:
`(s, z) ↦ 1_{s>0} 1_D(z) (2π)⁻¹ ∫_0^{2π} p^D_{s/2}(v + δe^{iθ}, z) dθ` (DGo (3.1)). -/
def dirCircFun (a L δ : ℝ) (v : ℂ) (q : ℝ × ℂ) : ℝ :=
  (Ioi 0 ×ˢ sqOpen a L).indicator (fun q => (2 * π)⁻¹ *
    ∫ θ in (0 : ℝ)..2 * π, sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2) q

lemma measurable_dirCircFun (hL : 0 < L) : Measurable (dirCircFun a L δ v) := by
  have hF : StronglyMeasurable (uncurry fun (q : ℝ × ℂ) (θ : ℝ) =>
      if 0 < q.1 / 2 then sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2 else 0) :=
    (DDDF.P29WN.measurable_sqDirKernel_joint (a := a) hL
      ((measurable_fst.comp measurable_fst).div_const 2)
      ((continuous_circleMap v δ).measurable.comp measurable_snd)
      (measurable_snd.comp measurable_fst)).stronglyMeasurable
  have hG := (hF.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * π)))).measurable
  have e : dirCircFun a L δ v = (Ioi 0 ×ˢ sqOpen a L).indicator (fun q : ℝ × ℂ => (2 * π)⁻¹ *
      ∫ θ in Ioc 0 (2 * π),
        if 0 < q.1 / 2 then sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2 else 0) := by
    funext q
    unfold dirCircFun
    by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
    · have h2 : 0 < q.1 / 2 := half_pos hq.1
      simp only [indicator_of_mem hq, if_pos h2,
        intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    · simp only [indicator_of_notMem hq]
  rw [e]
  exact (hG.const_mul _).indicator ((measurableSet_Ioi).prod (measurableSet_sqOpen a L))

/-- the `L²` function `1_{s>0} K e^{−cs} 1_D(z)` -/
lemma memLp_expInd {c : ℝ} (hc : 0 < c) (K : ℝ) (a L : ℝ) :
    MemLp (fun q : ℝ × ℂ => (Ioi 0).indicator (fun s => K * Real.exp (-c * s)) q.1 *
      (sqOpen a L).indicator (fun _ => (1 : ℝ)) q.2) 2 (volume : Measure (ℝ × ℂ)) := by
  have hm : Measurable fun q : ℝ × ℂ => (Ioi 0).indicator (fun s => K * Real.exp (-c * s)) q.1 *
      (sqOpen a L).indicator (fun _ => (1 : ℝ)) q.2 :=
    ((((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).indicator
      measurableSet_Ioi).comp measurable_fst).mul
      ((measurable_const.indicator (measurableSet_sqOpen a L)).comp measurable_snd))
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  have h1 : Integrable ((Ioi (0 : ℝ)).indicator fun s => K ^ 2 * Real.exp (-(2 * c) * s)) :=
    IntegrableOn.integrable_indicator ((exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul _)
      measurableSet_Ioi
  have h2 : Integrable ((sqOpen a L).indicator fun _ : ℂ => (1 : ℝ)) :=
    (integrableOn_const (volume_sqOpen_ne_top a L)).integrable_indicator (measurableSet_sqOpen a L)
  rw [Measure.volume_eq_prod]
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun q => ?_)
  have e : ∀ s : ℝ, K ^ 2 * rexp (-(2 * c * s)) = (K * rexp (-(c * s))) ^ 2 := fun s => by
    rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  simp only
  by_cases hs : q.1 ∈ Ioi (0 : ℝ) <;> by_cases hz : q.2 ∈ sqOpen a L <;>
    simp [indicator_of_mem, indicator_of_notMem, hs, hz, e q.1]

/-- the constant `M₀ = (4K + 4K²)·2(πd²)⁻¹` bounding `|p^D_s − p_s|` (`s ≤ 1`) at margin `d` -/
def smallConst (d L : ℝ) : ℝ := (4 * imgConst d L + 4 * imgConst d L ^ 2) * (2 * (π * d ^ 2)⁻¹)

lemma smallConst_nonneg (d L : ℝ) : 0 ≤ smallConst d L := by
  have := imgConst_nonneg d L; unfold smallConst; positivity

/-- `|p^D_s(x, z)| ≤ p_s(x, z) + M₀` for `0 < s ≤ 1`, `x` at margin `d`, `z ∈ D` -/
lemma abs_sqDirKernel_le_heat_add (hL : 0 < L) {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hs1 : s ≤ 1)
    {x z : ℂ} (hxre : x.re ∈ Icc (a + d) (a + L - d)) (hxim : x.im ∈ Icc (a + d) (a + L - d))
    (hz : z ∈ sqOpen a L) :
    |sqDirKernel a L s x z| ≤ heatKernel s x z + smallConst d L := by
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
  have h' := h.trans (mul_le_mul_of_nonneg_left hd' hK)
  have := abs_sub_abs_le_abs_sub (sqDirKernel a L s x z) (heatKernel s x z)
  rw [abs_of_nonneg (heatKernel_nonneg _ hs.le _ _)] at this
  unfold smallConst; linarith

/-- **Domination of the Dirichlet circle kernel**: `|F(s,z)| ≤ G(s,z) + K e^{−cs} 1_{s>0} 1_D(z)`
with `G` the circle-averaged free kernel cut at `s ≤ 2`. -/
theorem abs_dirCircFun_le (hL : 0 < L) (hδ : 0 < δ) (hB : closedBall v δ ⊆ sqOpen a L) :
    ∃ K, ∀ q : ℝ × ℂ, |dirCircFun a L δ v q| ≤ freeCircFun 2 δ v q +
      (Ioi 0).indicator (fun s => K * Real.exp (-DDDF.P29WN.rateC L * s)) q.1 *
        (sqOpen a L).indicator (fun _ => (1 : ℝ)) q.2 := by
  obtain ⟨d, hd, hmar⟩ := exists_margin (isCompact_closedBall v δ) hB
  set c := DDDF.P29WN.rateC L
  have hc : 0 < c := by unfold c DDDF.P29WN.rateC; positivity
  set M0 := smallConst d L
  have hM0 := smallConst_nonneg d L
  set K1 := decayConst L 1 ^ 2
  have hK1 : 0 ≤ K1 := sq_nonneg _
  refine ⟨M0 * Real.exp (2 * c) + K1, fun q => ?_⟩
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hG := freeCircFun_nonneg (T := 2) (δ := δ) (v := v) q
  unfold dirCircFun
  by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
  · obtain ⟨hs, hz⟩ := hq
    rw [indicator_of_mem (show q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L from ⟨hs, hz⟩), indicator_of_mem hs, indicator_of_mem hz, mul_one]
    have hs' : 0 < q.1 / 2 := half_pos hs
    have hE : 0 < Real.exp (-c * q.1) := Real.exp_pos _
    rw [abs_mul, abs_of_pos (inv_pos.2 h2π), ← Real.norm_eq_abs]
    rcases le_or_gt q.1 2 with hle | hgt
    · have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) h2π.le
        (f := fun θ => sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2)
        (g := fun θ => circHeat δ v q θ + M0)
        (Filter.Eventually.of_forall fun θ _ => by
          obtain ⟨hre, him⟩ := hmar _ (circleMap_mem_closedBall v hδ.le θ)
          rw [Real.norm_eq_abs]
          exact abs_sqDirKernel_le_heat_add hL hd hs' (by linarith) hre him hz)
        (((continuous_circHeat q).add continuous_const).intervalIntegrable _ _)
      rw [intervalIntegral.integral_add ((continuous_circHeat q).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
        intervalIntegral.integral_of_le h2π.le] at hb
      have hfree : freeCircFun 2 δ v q = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, circHeat δ v q θ := by
        unfold freeCircFun
        rw [indicator_of_mem (show q ∈ Ioc 0 2 ×ˢ univ from ⟨⟨hs, hle⟩, trivial⟩),
          intervalIntegral.integral_of_le h2π.le]
      have hM : M0 ≤ M0 * Real.exp (2 * c) * Real.exp (-c * q.1) := by
        rw [mul_assoc, ← Real.exp_add]
        exact le_mul_of_one_le_right hM0 (Real.one_le_exp (by nlinarith))
      calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2‖
          ≤ (2 * π)⁻¹ * ((∫ θ in (0 : ℝ)..2 * π, circHeat δ v q θ) + 2 * π * M0) := by
            rw [intervalIntegral.integral_of_le h2π.le
              (f := fun θ => sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2)]
            exact mul_le_mul_of_nonneg_left hb (by positivity)
        _ = freeCircFun 2 δ v q + M0 := by rw [hfree]; field_simp
        _ ≤ _ := by nlinarith
    · have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
        (C := K1 * Real.exp (-c * q.1))
        (f := fun θ => sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2) fun θ _ => by
          rw [Real.norm_eq_abs]
          have := DDDF.P29WN.abs_sqDirKernel_le_exp (a := a) hL (s := q.1 / 2) (by linarith)
            (circleMap v δ θ) q.2
          rwa [show -(2 * DDDF.P29WN.rateC L) * (q.1 / 2) = -c * q.1 by ring] at this
      rw [sub_zero, abs_of_pos h2π] at hb
      calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, sqDirKernel a L (q.1 / 2) (circleMap v δ θ) q.2‖
          ≤ (2 * π)⁻¹ * (K1 * Real.exp (-c * q.1) * (2 * π)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = K1 * Real.exp (-c * q.1) := by field_simp
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hM0 (Real.exp_pos (2 * c)).le) hE.le]
  · rw [indicator_of_notMem hq, abs_zero]
    refine add_nonneg hG (mul_nonneg (indicator_nonneg (fun s _ => ?_) _)
      (indicator_nonneg (fun _ _ => zero_le_one) _))
    have := Real.exp_pos (2 * c); positivity

/-- **R0: the Dirichlet circle kernel is in `L²(ℝ × ℂ)`** (`δ > 0`, `closedBall v δ ⊆ D`). -/
theorem memLp_dirCircFun (hL : 0 < L) (hδ : 0 < δ) (hB : closedBall v δ ⊆ sqOpen a L) :
    MemLp (dirCircFun a L δ v) 2 (volume : Measure (ℝ × ℂ)) := by
  obtain ⟨K, hK⟩ := abs_dirCircFun_le hL hδ hB
  have hc : 0 < DDDF.P29WN.rateC L := by unfold DDDF.P29WN.rateC; positivity
  refine ((memLp_freeCircFun hδ 2 v).add (memLp_expInd hc K a L)).of_le
    (measurable_dirCircFun hL).aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hK q).trans (le_abs_self _)

open scoped Classical in
/-- **DGo's kernel `dirCircKernel a L δ v ∈ L²(ℝ × ℂ)`** (DGo (3.1), DGo:491–494):
the class of `(s, z) ↦ 1_{s>0} 1_D(z) (2π)⁻¹ ∫_0^{2π} p^D_{s/2}(v + δe^{iθ}, z) dθ`;
junk `0` unless `L > 0`, `δ > 0` and `closedBall v δ ⊆ D` (as `phiKernelL2`). -/
def dirCircKernel (a L δ : ℝ) (v : ℂ) : WhiteNoise.WNSpace :=
  if h : 0 < L ∧ 0 < δ ∧ closedBall v δ ⊆ sqOpen a L then
    (memLp_dirCircFun h.1 h.2.1 h.2.2).toLp _ else 0

lemma coeFn_dirCircKernel (hL : 0 < L) (hδ : 0 < δ) (hB : closedBall v δ ⊆ sqOpen a L) :
    (dirCircKernel a L δ v : ℝ × ℂ → ℝ) =ᵐ[volume] dirCircFun a L δ v := by
  rw [dirCircKernel, dite_eq_left_of_eq_true (eq_true ⟨hL, hδ, hB⟩)]
  exact MemLp.coeFn_toLp _

end HeatDir
end DGo
end LQGMetric
