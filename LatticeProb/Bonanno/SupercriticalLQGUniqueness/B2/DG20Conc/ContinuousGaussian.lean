/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.ContinuousGaussian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23CondField

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

 

private lemma disc_variance_add_le {ξ s : ℝ} (hs : 0 ≤ s)
    {Y : ℂ → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (h0 : ∀ x, ∫ ω, Y x ω ∂P = 0)
    (hvar : ∀ x ∈ L23.sq01, Var[Y x; P] ≤ s)
    (V : ℂ → ℝ) (k : ℕ) :
    MemLp (fun ω => L23.discLogLen ξ k (fun c => V c + Y c ω)) 2 P ∧
      Var[fun ω => L23.discLogLen ξ k (fun c => V c + Y c ω); P] ≤ ξ ^ 2 * s := by
  let g : (L23.grid k → ℝ) → ℝ :=
    fun y => L23.discLogLen ξ k (fun c : L23.grid k => V c + y c)
  have ht : LipschitzWith 1 (fun y : L23.grid k → ℝ =>
      (fun c : L23.grid k => V c + y c)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [NNReal.coe_one, one_mul]
    exact (dist_pi_le_iff dist_nonneg).2 (fun c => by
      simpa only [Pi.add_apply, dist_add_left] using (dist_le_pi_dist a b c))
  have hg : LipschitzWith ‖ξ‖₊ g := by
    have h := (L23.lipschitzWith_discLogLen ξ k).comp ht
    change LipschitzWith (‖ξ‖₊ * 1) g at h
    simpa only [mul_one] using h
  have h := L23.memLp_variance_le_fintype (hY.hasGaussianLaw (L23.grid k))
    (fun c => h0 c) hs (fun c => hvar c (L23.grid_subset c.2)) hg
  have heq : ∀ ω, g ((L23.grid k).restrict (fun x => Y x ω)) =
      L23.discLogLen ξ k (fun c => V c + Y c ω) := by
    intro ω
    rfl
  simpa only [heq, coe_nnnorm, Real.norm_eq_abs, sq_abs] using h

 


theorem continuous_gaussian_log_cross_variance_le {ξ s : ℝ} (hs : 0 ≤ s)
    {Y : ℂ → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x))
    (h0 : ∀ x, ∫ ω, Y x ω ∂P = 0)
    (hvar : ∀ x ∈ L23.sq01, Var[Y x; P] ≤ s)
    (V : ℂ → ℝ) (hVc : Continuous V) :
    MemLp (fun ω => L23.logLen ξ (fun x => V x + Y x ω)) 2 P ∧
      Var[fun ω => L23.logLen ξ (fun x => V x + Y x ω); P] ≤ ξ ^ 2 * s := by
  have : IsProbabilityMeasure P := (hY.hasGaussianLaw (L23.grid 0)).isProbabilityMeasure
  letI : IsProbabilityMeasure P := this
  have hm : ∀ k, Measurable fun ω =>
      L23.discLogLen ξ k (fun c => V c + Y c ω) := by
    intro k
    exact (L23.lipschitzWith_discLogLen ξ k).continuous.measurable.comp
      (measurable_pi_iff.2 fun c => measurable_const.add (hYm c))
  have ht : ∀ ω, Tendsto (fun k => L23.discLogLen ξ k
      (fun c => V c + Y c ω)) atTop
      (𝓝 (L23.logLen ξ (fun x => V x + Y x ω))) := by
    intro ω
    have h := L23.tendsto_logLen_snap (ξ := ξ) (hVc.add (hYc ω))
    have hv : (V + fun x => Y x ω) = (fun x => V x + Y x ω) := rfl
    rw [hv] at h
    simpa only [L23.discLogLen, Pi.add_apply] using h
  exact L23.memLp_variance_le_of_tendsto hm
    (fun k => (disc_variance_add_le hs hY h0 hvar V k).1)
    (fun k => (disc_variance_add_le hs hY h0 hvar V k).2) ht

end SupercriticalLQGUniqueness.B2.DG20Conc
