/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.DiscreteHarmonicMeasure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteExit
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual discrete harmonic measure

Section 4 uses the equality between discrete Dirichlet solutions and boundary
expectations of the stopped conductance walk. This module derives that equality
from the actual finite transition laws and almost-sure finite exit.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

set_option linter.unusedSectionVars false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The exit vertex, with the same duration-zero totalization as the curve law. -/
noncomputable def exitVertex (A : Set V) (ω : ℕ → V) : V :=
  ω ((exitTime A ω).untopD 0)

lemma measurable_exitVertex (A : Set V) : Measurable (exitVertex A) := by
  have hev : Measurable (fun p : (ℕ → V) × ℕ ↦ p.1 p.2) :=
    measurable_from_prod_countable_left (fun n ↦ measurable_pi_apply n)
  exact hev.comp (measurable_id.prodMk (measurable_stoppedPolygonalDuration A))

lemma exitVertex_not_mem {A : Set V} {ω : ℕ → V} (hτ : exitTime A ω ≠ ⊤) :
    exitVertex A ω ∉ A := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hτ
  have h := exitTime_mem_compl_of_ne_top hτ
  rw [← hm] at h
  rw [exitVertex, ← hm]
  exact h

lemma IsAbsorbedPath.eventually_eq_exitVertex {A : Set V} {ω : ℕ → V}
    (hω : IsAbsorbedPath A ω) (hτ : exitTime A ω ≠ ⊤) :
    ∀ᶠ n in atTop, ω n = exitVertex A ω := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hτ
  have hout : ω m ∉ A := by
    have h := exitVertex_not_mem hτ
    rw [exitVertex, ← hm] at h
    exact h
  filter_upwards [eventually_ge_atTop m] with n hn
  calc
    ω n = ω (m + (n - m)) := by rw [Nat.add_sub_of_le hn]
    _ = ω m := hω.after_exit hout (n - m)
    _ = exitVertex A ω := by rw [exitVertex, ← hm]; rfl

private lemma integral_bind_finite (p : PMF V) (κ : V → PMF V) (f : V → ℝ) :
    (∫ w, f w ∂(p.bind κ).toMeasure) =
      ∑ v, (p v).toReal * (∫ w, f w ∂(κ v).toMeasure) := by
  have hpoint (w : V) : ((p.bind κ) w).toReal =
      ∑ v, (p v).toReal * (κ v w).toReal := by
    rw [PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun v _ ↦ ENNReal.mul_ne_top (p.apply_ne_top v)
        ((κ v).apply_ne_top w))]
    simp only [ENNReal.toReal_mul]
  simp only [PMF.integral_eq_sum, smul_eq_mul, hpoint, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

variable (N : FiniteConductanceNetwork V)

/-- Interior harmonicity is exactly the mean-value property for the absorbing
conductance transition, including the absorbed rows outside the interior. -/
lemma integral_stepPMF_of_harmonic (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (f : V → ℝ)
    (hf : ∀ v ∈ A, N.laplacian f v = 0) (v : V) :
    (∫ w, f w ∂(N.stepPMF A hpos v).toMeasure) = f v := by
  have hgen : N.stoppedGenerator A f v = 0 := by
    by_cases hv : v ∈ A
    · rw [N.stoppedGenerator_eq_laplacian_div A f hv, hf v hv, zero_div]
    · exact N.stoppedGenerator_of_not_mem A f hv
  have hmean := N.integral_stepPMF_increment A hpos f v
  rw [hgen, integral_sub Integrable.of_finite Integrable.of_finite] at hmean
  simpa using sub_eq_zero.mp hmean

lemma integral_nStepPMF_of_harmonic (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (f : V → ℝ)
    (hf : ∀ v ∈ A, N.laplacian f v = 0) (v : V) (n : ℕ) :
    (∫ w, f w ∂(N.nStepPMF A hpos n v).toMeasure) = f v := by
  induction n with
  | zero => simp only [nStepPMF, PMF.toMeasure_pure, integral_dirac]
  | succ n ih =>
    rw [nStepPMF, integral_bind_finite]
    simp_rw [N.integral_stepPMF_of_harmonic A hpos f hf]
    simpa only [PMF.integral_eq_sum, smul_eq_mul] using ih

/-- The actual trajectory expectations of a harmonic function are constant. -/
lemma trajectoryLaw_integral_eval_of_harmonic (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (f : V → ℝ)
    (hf : ∀ v ∈ A, N.laplacian f v = 0) (v : V) (n : ℕ) :
    (∫ ω, f (ω n) ∂N.trajectoryLaw A hpos v) = f v := by
  calc
    (∫ ω, f (ω n) ∂N.trajectoryLaw A hpos v) =
        ∫ w, f w ∂(N.trajectoryLaw A hpos v).map (fun ω ↦ ω n) := by
      rw [integral_map (measurable_pi_apply n).aemeasurable
        (measurable_of_finite f).aestronglyMeasurable]
    _ = f v := by
      rw [N.trajectoryLaw_marginal A hpos v n]
      exact N.integral_nStepPMF_of_harmonic A hpos f hf v n

/-- Actual discrete harmonic measure is the pushforward by the first exit vertex. -/
noncomputable def discreteHarmonicMeasure (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) : Measure V :=
  (N.trajectoryLaw A hpos v).map (exitVertex A)

instance discreteHarmonicMeasure_isProbabilityMeasure (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    IsProbabilityMeasure (N.discreteHarmonicMeasure A hpos v) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_exitVertex A).aemeasurable).mpr
    inferInstance

/-- The boundary expectation of a Dirichlet solution equals its starting value.
The proof uses finite-time means and dominated convergence after the proved
almost-sure finite exit; no optional-stopping premise is assumed. -/
theorem integral_discreteHarmonicMeasure_of_solvesDirichlet (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    {g f : V → ℝ} (hf : N.SolvesDirichlet A g f) (v : V) :
    (∫ w, g w ∂N.discreteHarmonicMeasure A hpos v) = f v := by
  let μ := N.trajectoryLaw A hpos v
  have hlimit : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f (ω n)) atTop
      (𝓝 (g (exitVertex A ω))) := by
    filter_upwards [N.trajectoryLaw_ae_absorbed A hpos v,
      N.trajectoryLaw_ae_finiteExit A hpos haccess v] with ω hω hτ
    have heq : ∀ᶠ n in atTop, f (ω n) = g (exitVertex A ω) := by
      filter_upwards [hω.eventually_eq_exitVertex hτ] with n hn
      rw [hn, hf.2 _ (exitVertex_not_mem hτ)]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖f (ω n)‖ ≤ ∑ w : V, ‖f w‖ := by
    exact ae_of_all _ fun ω ↦ Finset.single_le_sum (fun w _ ↦ norm_nonneg (f w))
      (Finset.mem_univ (ω n))
  have hint := tendsto_integral_of_dominated_convergence
    (fun _ : ℕ → V ↦ ∑ w : V, ‖f w‖)
    (fun n ↦ ((measurable_of_finite f).comp (measurable_pi_apply n)).aestronglyMeasurable)
    (integrable_const _) hbound hlimit
  have hconst : Tendsto (fun n ↦ ∫ ω, f (ω n) ∂μ) atTop (𝓝 (f v)) := by
    simpa only [μ, N.trajectoryLaw_integral_eval_of_harmonic A hpos f hf.1 v] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ f v) atTop (𝓝 (f v)))
  rw [discreteHarmonicMeasure, integral_map (measurable_exitVertex A).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable]
  exact tendsto_nhds_unique hint hconst

/-- The genuine solver agrees with integration against actual exit harmonic measure. -/
theorem dirichletSolution_eq_integral_discreteHarmonicMeasure (A : Set V)
    (haccess : N.BoundaryAccessible A) (g : V → ℝ) (v : V) :
    N.dirichletSolution A haccess g v =
      ∫ w, g w ∂N.discreteHarmonicMeasure A
        (N.totalConductance_pos_of_boundaryAccessible A haccess) v :=
  (N.integral_discreteHarmonicMeasure_of_solvesDirichlet A _ haccess
    (N.dirichletSolution_spec A haccess g) v).symm

end BouRabeeGwynne.FiniteConductanceNetwork
