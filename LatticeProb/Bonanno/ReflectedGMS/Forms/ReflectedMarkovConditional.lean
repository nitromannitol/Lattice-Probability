/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ReflectedMarkovConditional at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedTrajectoryConditional

/-! Deterministic-time vertex-observable Markov identities, specialized from
the shared bounded trajectory-functional theorem. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.ReflectedMarkovConditional

open ReflectedWalk ReflectedWalk.Theorem16

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]
variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

private lemma measurable_trajectory_vertexTest (r : ℝ≥0) (f : V → ℝ) :
    Measurable (fun γ : Trajectory V => (γ r).elim 0 f) :=
  (measurable_of_countable (fun q : Option V => q.elim 0 f)).comp (measurable_pi_apply r)

private lemma norm_trajectory_vertexTest_le (r : ℝ≥0) (f : V → ℝ) (C : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ C) (γ : Trajectory V) : ‖(γ r).elim 0 f‖ ≤ C := by
  cases γ r with
  | none =>
      have hC : 0 ≤ C := (norm_nonneg (f (Classical.choice inferInstance))).trans (hf _)
      simpa using hC
  | some x => exact hf x

private lemma integral_law_vertexTest (r : ℝ≥0) (f : V → ℝ) (x : V) :
    (∫ γ, (γ r).elim 0 f ∂PF.law x) = ∫ ω, (PF.X r ω).elim 0 f ∂PF.P x := by
  have htraj : Measurable PF.trajectory := measurable_pi_iff.mpr PF.measurable_X
  rw [ProcessFamily.law, integral_map htraj.aemeasurable
    (measurable_trajectory_vertexTest r f).aestronglyMeasurable]
  rfl

theorem setIntegral_vertexFiber (h : IsReflectedWalk G w hmin PF) (z x : V)
    {s t : ℝ≥0} (hst : s ≤ t) (f : V → ℝ) (C : ℝ)
    (hf : ∀ y, ‖f y‖ ≤ C) {F : Set PF.Ω}
    (hF : MeasurableSet[PF.naturalFiltration s] F) :
    ∫ ω in F, {ω | PF.X s ω = some x}.indicator
        (fun ω => (PF.X t ω).elim 0 f) ω ∂PF.P z =
      ∫ ω in F, {ω | PF.X s ω = some x}.indicator
        (fun _ => ∫ ω', (PF.X (t - s) ω').elim 0 f ∂PF.P x) ω ∂PF.P z := by
  have hgeneric := setIntegral_trajectoryFiber h z x s (fun γ => (γ (t - s)).elim 0 f) C
    (measurable_trajectory_vertexTest (t - s) f)
    (norm_trajectory_vertexTest_le (t - s) f C hf) hF
  simpa only [shiftedPath, tsub_add_cancel_of_le hst, integral_law_vertexTest] using hgeneric

theorem condExp_vertex_test (h : IsReflectedWalk G w hmin PF) (z : V)
    {s t : ℝ≥0} (hst : s ≤ t) (f : V → ℝ) (C : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ C) :
    (PF.P z)[(fun ω => (PF.X t ω).elim 0 f) | PF.naturalFiltration s] =ᵐ[PF.P z]
      fun ω => (PF.X s ω).elim 0
        (fun x => ∫ ω', (PF.X (t - s) ω').elim 0 f ∂PF.P x) := by
  have hgeneric := condExp_trajectory_test h z s (fun γ => (γ (t - s)).elim 0 f) C
    (measurable_trajectory_vertexTest (t - s) f)
    (norm_trajectory_vertexTest_le (t - s) f C hf)
  simpa only [shiftedPath, tsub_add_cancel_of_le hst, integral_law_vertexTest] using hgeneric

end ReflectedGMS.ReflectedMarkovConditional
