/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgBridge at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Bridge to LQGDimension and the Brownian motion `t ↦ h_{e^{−t}}(z) − h_1(z)`

* `circCov_comm`: `circCov` is symmetric (it is LQGDimension's `lPair` of the two circle measures,
  `circCov_eq_lPair`).
* `gffCircleCov_eq_incCov`: LD's `gffCircleCov ε z δ w` (the double circle average of the Green
  function of the normalized GFF) is our `incCov z ε 0 1 w δ 0 1` (= `Cov(h_ε(z) − h_1(0),
  h_δ(w) − h_1(0))`).
* `exists_isGFFCircleAverage`: for a whole-plane GFF `h`, a jointly continuous version `H` of
  `(r, z) ↦ h_r(z) − h_1(0)` satisfies `LQGDimension.IsGFFCircleAverage`; for a normalized GFF,
  `H r z = h_r(z)` a.s. (`exists_isGFFCircleAverage_normalized`).
* `isPreBrownianReal_circleAvg`: `t ↦ H(e^{−t}, z) − H(1, z)` is a pre-Brownian motion
  (DS arXiv:0808.1560 Prop. 3.3: `t ↦ h_{e^{−t}}(z) − h_1(z)` is a standard Brownian motion),
  via mathlib `IsGaussianProcess.isPreBrownianReal_of_covariance`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal

namespace LQGMetric
namespace CircleAvg

lemma circCov_eq_lPair (z : ℂ) (r : ℝ) (w : ℂ) {s : ℝ} (hs : 0 < s) :
    circCov z r w s =
      LQGDimension.Coupling.lPair (LQGDimension.Coupling.circMeas z r)
        (LQGDimension.Coupling.circMeas w s) := by
  rw [LQGDimension.Coupling.lPair_circ z w r hs, circCov,
    LQGDimension.Coupling.integral_circMeas_eq_circleAverage
      ((by fun_prop : Continuous fun x : ℂ =>
        Real.log s + Real.posLog (s⁻¹ * ‖w - x‖)).aestronglyMeasurable)]
  congr 1
  funext x
  exact circLog_eq hs.ne' w x

lemma lPair_comm (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    LQGDimension.Coupling.lPair μ ν = LQGDimension.Coupling.lPair ν μ := by
  unfold LQGDimension.Coupling.lPair
  rw [← integral_prod_swap]
  congr 1
  funext p
  simp [norm_sub_rev]

lemma circCov_comm {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    circCov z r w s = circCov w s z r := by
  rw [circCov_eq_lPair z r w hs, circCov_eq_lPair w s z hr, lPair_comm]

lemma circLog_zero_one (x : ℂ) : circLog 0 1 x = Real.log (max ‖x‖ 1) := by
  rw [circLog_eq_log_max one_pos, zero_sub, norm_neg, max_comm]

lemma gffCircleCov_eq_incCov {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z w : ℂ) :
    LQGDimension.gffCircleCov ε z δ w = incCov z ε 0 1 w δ 0 1 := by
  rw [LQGDimension.Osc37.gffCircleCov_eq_circleAverage]
  simp_rw [LQGDimension.Osc37.circleAverage_gffGreen hδ]
  have e1 : (fun x => Real.log (max ‖x‖ 1) + LQGDimension.Osc37.betaAvg δ w -
      (Real.log δ + Real.posLog (δ⁻¹ * ‖w - x‖))) =
      fun x => (circLog 0 1 x + LQGDimension.Osc37.betaAvg δ w) - circLog w δ x := by
    funext x; rw [circLog_zero_one, circLog_eq hδ.ne']
  have hci : ∀ (a : ℂ) (t : ℝ), 0 < t → CircleIntegrable (circLog a t) z ε := fun a t ht =>
    ((continuous_circLog ht.ne' a).continuousOn).circleIntegrable'
  have hA : CircleIntegrable (fun x => circLog 0 1 x + LQGDimension.Osc37.betaAvg δ w) z ε :=
    (hci 0 1 one_pos).add (circleIntegrable_const _ _ _)
  rw [e1, Real.circleAverage_fun_sub hA (hci w δ hδ),
    Real.circleAverage_fun_add (hci 0 1 one_pos) (circleIntegrable_const _ _ _),
    Real.circleAverage_const]
  have hβ : LQGDimension.Osc37.betaAvg δ w = circCov 0 1 w δ := by
    rw [circCov_comm one_pos hδ]
    simp only [LQGDimension.Osc37.betaAvg, circCov]
    congr 1
    funext x
    rw [circLog_zero_one]
  have h00 : circCov 0 1 0 1 = 0 := by
    rw [circCov_center 0 one_pos 1 one_pos]; simp [Real.posLog_apply]
  rw [hβ]
  simp only [incCov, h00]
  simp only [circCov]
  ring

lemma covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') : cov[X, Y; μ] = cov[X', Y'; μ] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma integral_cInc (hh : IsWholePlaneGFF h P) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    ∫ ω, cInc h r z s w ω ∂P = 0 := by
  have hm := (measurable_cInc hh r z s w).aemeasurable (μ := P)
  have := integral_map (μ := P) (f := fun x : ℝ => x) hm aestronglyMeasurable_id
  rw [(map_cInc hh hr hs z w).1, integral_id_gaussianReal] at this
  exact this.symm

/-- **Bridge to `LQGDimension.IsGFFCircleAverage`.** -/
theorem exists_isGFFCircleAverage (hh : IsWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGDimension.IsGFFCircleAverage H P ∧
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P]
        fun ω => circleAvg (h ω) r z - circleAvg (h ω) 1 0 := by
  have := hh.gaussian.isProbabilityMeasure
  obtain ⟨H, hHc, hHae⟩ := exists_continuous_version_circleAvg hh
  refine ⟨H, ⟨inferInstance, ?_, ?_, ?_, ?_⟩, hHc, hHae⟩
  · have hGP := (isGaussianProcess_incProc hh).comp_right
      (fun p : Ioi (0 : ℝ) × ℂ => ((p.1, p.2), ((⟨1, Set.mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)), (0 : ℂ))))
    exact hGP.congr fun p => (hHae p.1 p.1.2 p.2).symm
  · intro ε hε z
    rw [integral_congr_ae (hHae ε hε z)]
    exact integral_cInc hh hε one_pos z 0
  · intro ε hε δ hδ z w
    rw [covariance_congr_ae (hHae ε hε z) (hHae δ hδ w), gffCircleCov_eq_incCov hε hδ]
    exact covariance_cInc hh hε one_pos hδ one_pos z 0 w 0
  · intro ε hε ω
    exact (hHc ω).comp_continuous (continuous_const.prodMk continuous_id)
      fun z => ⟨hε, mem_univ _⟩

/-- For a normalized whole-plane GFF the version is a version of `h_r(z)` itself. -/
theorem exists_isGFFCircleAverage_normalized (hh : IsNormalizedWPGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGDimension.IsGFFCircleAverage H P ∧
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z := by
  obtain ⟨H, h1, h2, h3⟩ := exists_isGFFCircleAverage hh.1
  refine ⟨H, h1, h2, fun r hr z => ?_⟩
  filter_upwards [h3 r hr z, hh.2] with ω hω h0
  rw [hω, h0, sub_zero]

lemma incCov_brownian (z : ℂ) (t u : ℝ≥0) (htu : t ≤ u) :
    incCov z (Real.exp (-(t : ℝ))) z 1 z (Real.exp (-(u : ℝ))) z 1 = t := by
  have hp : ∀ x : ℝ, 0 ≤ x → Real.posLog (Real.exp x) = x := fun x hx => by
    rw [Real.posLog_eq_log (by rw [abs_of_pos (Real.exp_pos x)]; exact Real.one_le_exp hx),
      Real.log_exp]
  have hn : ∀ x : ℝ, x ≤ 0 → Real.posLog (Real.exp x) = 0 := fun x hx =>
    (Real.posLog_eq_zero_iff _).mpr (by rw [abs_of_pos (Real.exp_pos x)]; exact Real.exp_le_one_iff.mpr hx)
  have ht : (0 : ℝ) ≤ t := t.2
  have hu : (t : ℝ) ≤ u := htu
  simp only [incCov]
  rw [circCov_center z (Real.exp_pos _) _ (Real.exp_pos _), circCov_center z (Real.exp_pos _) 1
    one_pos, circCov_center z one_pos _ (Real.exp_pos _), circCov_center z one_pos 1 one_pos,
    Real.log_exp, Real.log_one, inv_one, one_mul, mul_one, ← Real.exp_neg, ← Real.exp_add,
    hp _ (by linarith), hn _ (by linarith), neg_neg, hp _ (by linarith)]
  have h1 : Real.posLog 1 = 0 := by simp [Real.posLog_apply]
  simp only [mul_one, h1]
  ring

/-- **`t ↦ h_{e^{−t}}(z) − h_1(z)` is a (pre-)Brownian motion** (DS Prop. 3.3), for the
continuous version `H` of `exists_isGFFCircleAverage`. -/
theorem isPreBrownianReal_circleAvg (hh : IsWholePlaneGFF h P) (z : ℂ) :
    ∃ B : ℝ≥0 → Ω → ℝ, IsPreBrownianReal B P ∧ (∀ ω, Continuous fun t => B t ω) ∧
      ∀ t : ℝ≥0, (fun ω => B t ω) =ᵐ[P]
        fun ω => circleAvg (h ω) (Real.exp (-(t : ℝ))) z - circleAvg (h ω) 1 z := by
  have := hh.gaussian.isProbabilityMeasure
  obtain ⟨H, -, hHc, hHae⟩ := exists_isGFFCircleAverage hh
  set B : ℝ≥0 → Ω → ℝ := fun t ω => H (Real.exp (-(t : ℝ))) z ω - H 1 z ω
  have hB : ∀ t : ℝ≥0, (fun ω => B t ω) =ᵐ[P] cInc h (Real.exp (-(t : ℝ))) z 1 z := by
    intro t
    filter_upwards [hHae (Real.exp (-(t : ℝ))) (Real.exp_pos _) z, hHae 1 one_pos z] with ω h1 h2
    simp only [B, cInc, h1, h2]
    ring
  refine ⟨B, ?_, fun ω => ?_, fun t => hB t⟩
  · have hGP : IsGaussianProcess (fun t : ℝ≥0 => cInc h (Real.exp (-(t : ℝ))) z 1 z) P :=
      (isGaussianProcess_incProc hh).comp_right fun t : ℝ≥0 =>
        (((⟨Real.exp (-(t : ℝ)), Real.exp_pos _⟩ : Ioi (0 : ℝ)), z),
          ((⟨1, Set.mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)), z))
    refine (hGP.congr fun t => (hB t).symm).isPreBrownianReal_of_covariance (fun t => ?_)
      fun s t hst => ?_
    · rw [integral_congr_ae (hB t)]
      exact integral_cInc hh (Real.exp_pos _) one_pos z z
    · rw [covariance_congr_ae (hB s) (hB t), covariance_cInc hh (Real.exp_pos _) one_pos
        (Real.exp_pos _) one_pos, incCov_brownian z s t hst]
  · have hc : Continuous fun t : ℝ≥0 => ((Real.exp (-(t : ℝ)), z) : ℝ × ℂ) := by fun_prop
    have h1 := (hHc ω).comp_continuous hc fun t => ⟨Real.exp_pos _, mem_univ _⟩
    have h2 := (hHc ω).comp_continuous (continuous_const : Continuous fun _ : ℝ≥0 =>
      ((1 : ℝ), z)) fun _ => ⟨Set.mem_Ioi.mpr one_pos, mem_univ _⟩
    exact h1.sub h2

end CircleAvg
end LQGMetric
