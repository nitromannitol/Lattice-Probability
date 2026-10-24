import LatticeProb.Prob.BrownianDirichlet.InnerLimit
import LatticeProb.Prob.BrownianDirichlet.PayoffLimit
import LatticeProb.Analysis.Elliptic.EuclideanTransport

/-!
# Brownian representation on a Euclidean ball

Finite-horizon stopping and discounted payoff convergence identify classical
zero-boundary solutions with their Brownian running payoffs.
-/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

/-- The running payoff at a finite cutoff is integrable under a Brownian law. -/
lemma integrable_truncated_running_payoff {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {B : Set (Euc d)} (hB : IsOpen B)
    (hb : Bornology.IsBounded B) {σ μd : ℝ} (hμd : 0 < μd)
    {g : Euc d → ℝ} (hg : ContinuousOn g (closure B)) (x : Euc d) (n : ℕ) :
    Integrable (fun ω ↦ ∫ t in (0 : ℝ)..
      ((min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal : ℝ),
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨M, hM⟩ := isBounded_image_closure hb hg
  let K := max M 0
  have hK : 0 ≤ K := le_max_right M 0
  let F : ℝ × BrownianPath d → ℝ := fun p ↦
    if p.1 < (n : ℝ) then
      if ENNReal.ofReal p.1 < scaledExit B σ x p.2 then
        Real.exp (-μd * p.1) * g (x + σ • p.2 p.1.toNNReal) else 0
    else 0
  have hm : Measurable F := Measurable.ite
    (measurableSet_lt measurable_fst measurable_const)
    (measurable_discounted_killed_integrand hB hg) measurable_const
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hμd) 0).const_mul K
  have hbound (t : ℝ) (ω : BrownianPath d) : ‖F (t, ω)‖ ≤ K * Real.exp (-μd * t) := by
    dsimp only [F]
    split_ifs with hn ht
    · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left
        ((hM _ (subset_closure (mem_of_lt_scaledExit ht))).trans (le_max_left M 0))
        (Real.exp_pos _).le).trans_eq (mul_comm _ _)
    all_goals simpa only [norm_zero] using mul_nonneg hK (Real.exp_pos (-μd * t)).le
  have hout : Integrable (fun ω ↦ ∫ t in Ioi (0 : ℝ), F (t, ω)) μ :=
    (integrable_const (∫ t in Ioi (0 : ℝ), K * Real.exp (-μd * t))).mono'
      hm.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
      (ae_of_all _ (fun ω ↦ norm_integral_le_of_norm_le hi
        (ae_of_all _ (fun t ↦ hbound t ω))))
  convert hout using 1
  funext ω
  rw [running_payoff_eq_killed_cutoff]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [F]
  exact ite_and _ _ _ _

/-- A classical zero-boundary solution equals its discounted Brownian payoff. -/
theorem brownian_dirichlet_representation_euc {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {c : Euc d} {R a₀ μd : ℝ} (hR : 0 < R) (ha : 0 < a₀) (hμd : 0 < μd)
    {v g : Euc d → ℝ} (hv : ContDiffOn ℝ 2 v (Metric.ball c R))
    (hvc : ContinuousOn v (closure (Metric.ball c R)))
    (hzero : ∀ y ∈ frontier (Metric.ball c R), v y = 0)
    (hgc : ContinuousOn g (closure (Metric.ball c R)))
    (hpde : ∀ y ∈ Metric.ball c R,
      μd * v y - a₀ * Laplacian.laplacian v y = g y)
    {x : Euc d} (hx : x ∈ Metric.ball c R) :
    v x = ∫ ω, (∫ t in Ioi (0 : ℝ),
      if ENNReal.ofReal t < scaledExit (Metric.ball c R) (Real.sqrt (2 * a₀)) x ω then
        Real.exp (-μd * t) * g (x + Real.sqrt (2 * a₀) • ω t.toNNReal) else 0) ∂μ := by
  have ht := tendsto_terminal_payoff hμ Metric.isOpen_ball Metric.isBounded_ball
    hx hμd hvc hzero (σ := Real.sqrt (2 * a₀))
  have hr := tendsto_running_payoff hμ Metric.isOpen_ball Metric.isBounded_ball
    hμd hgc (σ := Real.sqrt (2 * a₀)) (x := x)
  have heq (n : ℕ) := stopped_identity_ball hμ hR ha hμd hv hpde hvc hgc hx (n : ℝ≥0)
  have hs := ht.add hr
  simp only [zero_add] at hs
  have hconst := tendsto_const_nhds (x := v x) (f := atTop (α := ℕ))
  apply tendsto_nhds_unique hconst
  apply hs.congr
  intro n
  rw [← integral_add
    (integrable_terminal_payoff hμ Metric.isOpen_ball Metric.isBounded_ball hx hvc hzero n)
    (integrable_truncated_running_payoff hμ Metric.isOpen_ball Metric.isBounded_ball
      hμd hgc x n)]
  exact (heq n).symm

/-- Coordinate classical solutions have the same Euclidean Brownian representation. -/
theorem classical_dirichlet_eq_brownian_integral {d : ℕ}
    {μ : Measure (BrownianPath d)} {c : Euc d} {R μd a₀ : ℝ}
    (hR : 0 < R) (hμd : 0 < μd) (ha : 0 < a₀) (hμ : IsStandardBrownianLaw μ)
    {h u : (Fin d → ℝ) → ℝ}
    (hh : ContinuousOn h (closure ((EuclideanSpace.equiv (Fin d) ℝ) '' Metric.ball c R)))
    (hu : Elliptic.IsClassicalDirichletSolution
      ((EuclideanSpace.equiv (Fin d) ℝ) '' Metric.ball c R) μd a₀ h u)
    {x : Euc d} (hx : x ∈ Metric.ball c R) :
    u (EuclideanSpace.equiv (Fin d) ℝ x) = ∫ ω, (∫ t in Ioi (0 : ℝ),
      if ENNReal.ofReal t < scaledExit (Metric.ball c R) (Real.sqrt (2 * a₀)) x ω then
        Real.exp (-μd * t) * (h ∘ EuclideanSpace.equiv (Fin d) ℝ)
          (x + Real.sqrt (2 * a₀) • ω t.toNNReal) else 0) ∂μ := by
  obtain ⟨hv, hvc, hz, hpde⟩ := Elliptic.isClassicalDirichletSolution_transport c hR hu
  apply brownian_dirichlet_representation_euc hμ hR ha hμd hv hvc _ _ hpde hx
  · simpa only [frontier_ball c hR.ne'] using hz
  · apply hh.comp (EuclideanSpace.equiv (Fin d) ℝ).continuous.continuousOn
    intro y hy
    rw [← Elliptic.image_closure_equiv]
    exact ⟨y, hy, rfl⟩

/-- The unit-ball quadratic has payoff one at zero under an actual Brownian law. -/
theorem exists_brownian_quadratic_payoff_one :
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ ∧
      (∫ ω, (∫ t in Ioi (0 : ℝ),
        if ENNReal.ofReal t < scaledExit (Metric.ball (0 : Euc 1) 1)
            (Real.sqrt (2 * 1)) 0 ω then
          Real.exp (-1 * t) *
            (1 * (1 - ∑ i : Fin 1, (0 + Real.sqrt (2 * 1) • ω t.toNNReal) i ^ 2) +
              2 * (1 : ℝ) * 1) else 0) ∂μ) = 1 := by
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  obtain ⟨hv, hvc, hz, hpde⟩ := Elliptic.quadratic_euclidean_dirichlet (d := 1) 1 1
  refine ⟨μ, hμ, ?_⟩
  have hr := brownian_dirichlet_representation_euc hμ zero_lt_one zero_lt_one
    zero_lt_one hv hvc (by simpa only [frontier_ball _ one_ne_zero] using hz)
    (by fun_prop) hpde (x := 0) (by simp)
  simpa using hr.symm

end LatticeProb
