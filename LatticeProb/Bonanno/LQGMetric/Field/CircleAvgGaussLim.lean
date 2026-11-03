/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgGaussLim at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Almost sure limits of centered real Gaussians are centered Gaussian

`exists_gaussianReal_of_ae_tendsto`: if `Y_n ~ N(0, v_n)` and `Y_n → Z` a.s., then `v_n → V`
and `Z ~ N(0, V)`. Standard (characteristic functions: `E e^{itY_n} = e^{−v_n t²/2} → E e^{itZ}`
by dominated convergence; continuity of the characteristic function at `0` rules out
`v_n → ∞`; uniqueness, `Measure.ext_of_charFun`). Own write-up of the textbook argument
(e.g. Billingsley, *Probability and Measure*, the closure of the Gaussian family under weak
limits).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Complex

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem exists_gaussianReal_of_ae_tendsto [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    {Z : Ω → ℝ} {v : ℕ → NNReal} (hYm : ∀ n, AEMeasurable (Y n) P) (hZ : AEMeasurable Z P)
    (hY : ∀ n, P.map (Y n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    ∃ V : NNReal, Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (V : ℝ)) ∧
      P.map Z = gaussianReal 0 V := by
  set φ := charFun (P.map Z)
  have hcf : ∀ t : ℝ, Tendsto (fun n => ((Real.exp (-(v n : ℝ) * t ^ 2 / 2) : ℝ) : ℂ)) atTop
      (𝓝 (φ t)) := by
    intro t
    have h1 : ∀ n, charFun (P.map (Y n)) t = ((Real.exp (-(v n : ℝ) * t ^ 2 / 2) : ℝ) : ℂ) := by
      intro n
      rw [hY, charFun_gaussianReal, ofReal_exp]
      congr 1
      push_cast
      ring
    simp_rw [← h1]
    simp only [φ, charFun_apply_real]
    rw [integral_map hZ (by fun_prop)]
    simp_rw [fun n => integral_map (hYm n) (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => cexp (↑t * ↑x * I)) (P.map (Y n)))]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => ((by fun_prop : Continuous fun x : ℝ => cexp (↑t * ↑x * I)).comp_aestronglyMeasurable
        (hYm n).aestronglyMeasurable))
      (integrable_const 1) (fun n => Eventually.of_forall fun ω => ?_) ?_
    · rw [show (t : ℂ) * (Y n ω : ℂ) = ((t * Y n ω : ℝ) : ℂ) by push_cast; ring,
        norm_exp_ofReal_mul_I]
    · filter_upwards [hlim] with ω hω
      exact ((by fun_prop : Continuous fun x : ℝ => cexp (↑t * ↑x * I)).tendsto _).comp hω
  set a : ℕ → ℝ := fun n => Real.exp (-(v n : ℝ) / 2)
  have ha : Tendsto a atTop (𝓝 (φ 1).re) := by
    refine ((continuous_re.tendsto _).comp (hcf 1)).congr fun n => ?_
    simp only [Function.comp_apply, ofReal_re, a]
    congr 1
    ring
  have ha0 : ∀ n, 0 < a n := fun n => Real.exp_pos _
  have hA0 : 0 ≤ (φ 1).re := ge_of_tendsto' ha fun n => (ha0 n).le
  have hva : ∀ n, (v n : ℝ) = -2 * Real.log (a n) := by
    intro n; simp only [a, Real.log_exp]; ring
  rcases hA0.eq_or_lt with hA | hA
  · -- `v_n → ∞`, contradicting continuity of `φ` at `0`
    exfalso
    have ha' : Tendsto a atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hA ▸ ha)
        (Eventually.of_forall ha0)
    have hv : Tendsto (fun n => (v n : ℝ)) atTop atTop := by
      simp_rw [hva]
      exact (Real.tendsto_log_nhdsGT_zero.comp ha').const_mul_atBot_of_neg (by norm_num)
    have hzero : ∀ t : ℝ, t ≠ 0 → φ t = 0 := by
      intro t ht
      have h2 : Tendsto (fun n => Real.exp (-(v n : ℝ) * t ^ 2 / 2)) atTop (𝓝 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        have : 0 < t ^ 2 / 2 := by positivity
        have h3 := hv.atTop_mul_const this
        refine (tendsto_neg_atTop_atBot.comp h3).congr fun n => ?_
        simp only [Function.comp_apply]; ring
      have h4 := (continuous_ofReal.tendsto _).comp h2
      rw [ofReal_zero] at h4
      exact tendsto_nhds_unique (hcf t) h4
    have hc : Tendsto (fun k : ℕ => φ (1 / ((k : ℝ) + 1))) atTop (𝓝 (φ 0)) :=
      (continuous_charFun.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h0 : φ 0 = 0 := tendsto_nhds_unique hc (tendsto_const_nhds.congr fun k =>
      (hzero _ (by positivity)).symm)
    simp [φ, charFun_zero] at h0
  · set V := -2 * Real.log (φ 1).re
    have hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 V) := by
      simp_rw [hva]
      exact ((Real.continuousAt_log hA.ne').tendsto.comp ha).const_mul _
    have hV : 0 ≤ V := ge_of_tendsto' hv fun n => (v n).2
    refine ⟨Real.toNNReal V, by rwa [Real.coe_toNNReal _ hV], ?_⟩
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_gaussianReal, Real.coe_toNNReal _ hV]
    have h5 : Tendsto (fun n => ((Real.exp (-(v n : ℝ) * t ^ 2 / 2) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-V * t ^ 2 / 2) : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp
        ((Real.continuous_exp.tendsto _).comp ((hv.neg.mul_const _).div_const _))
    show φ t = _
    rw [tendsto_nhds_unique (hcf t) h5, ofReal_exp]
    congr 1
    push_cast
    ring

end LQGMetric
