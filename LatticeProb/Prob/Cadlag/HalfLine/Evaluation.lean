import LatticeProb.Prob.Cadlag.HalfLine.Metric
import LatticeProb.Prob.Cadlag.HalfLine.Convergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Sequences

/-!
# Borel measurability of half-line path evaluations

Positive right time averages of bounded continuous observables are continuous for the
Skorokhod metric. Their pointwise limits give measurable observables of each evaluation.
Truncated distances to closed sets then give Borel measurability of evaluation itself.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [MetricSpace E]

/-- Positive right time averages of bounded continuous observables are continuous. -/
theorem continuous_average {f : E → ℝ} (hf : Continuous f)
    (hb : ∃ M : ℝ, ∀ a, ‖f a‖ ≤ M) (t : Time) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : D E => (1 / ε) *
      ∫ s in (t : ℝ)..(t : ℝ) + ε, f (x.1 s.toNNReal)) := by
  apply continuous_iff_seqContinuous.mpr
  intro x y hxy
  exact tendsto_average_of_tendsto_skorohodDistance
    (tendsto_iff_dist_tendsto_zero.mp hxy) hf hb t hε

/-- A bounded continuous observable of evaluation is the measurable limit of right averages. -/
theorem measurable_comp_eval {f : E → ℝ} (hf : Continuous f)
    (hb : ∃ M : ℝ, ∀ a, ‖f a‖ ≤ M) (t : Time) :
    Measurable (fun x : D E => f (x.1 t)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n : ℕ => fun x : D E => (1 / (1 / (n + 1 : ℝ))) *
      ∫ s in (t : ℝ)..(t : ℝ) + 1 / (n + 1 : ℝ), f (x.1 s.toNNReal))
  · intro n
    exact (continuous_average hf hb t (by positivity)).measurable
  · apply tendsto_pi_nhds.mpr
    intro x
    apply (tendsto_average_eval x hf t).comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by change 0 < 1 / (n + 1 : ℝ); positivity)⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- Evaluation at any half-line time is Borel measurable. -/
theorem measurable_eval (t : Time) : Measurable (fun x : D E => x.1 t) := by
  apply measurable_of_isClosed'
  intro s hs hne _
  have hm : Measurable (fun x : D E => min (Metric.infDist (x.1 t) s) 1) := by
    apply measurable_comp_eval ((Metric.continuous_infDist_pt s).min continuous_const)
    exact ⟨1, fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min Metric.infDist_nonneg zero_le_one)]
      exact min_le_right _ _⟩
  have heq : (fun x : D E => x.1 t) ⁻¹' s =
      (fun x : D E => min (Metric.infDist (x.1 t) s) 1) ⁻¹' {0} := by
    ext x
    change x.1 t ∈ s ↔ min (Metric.infDist (x.1 t) s) 1 = 0
    rw [hs.mem_iff_infDist_zero hne]
    constructor
    · intro h
      rw [h, min_eq_left zero_le_one]
    · intro h
      rcases min_eq_iff.mp h with h | h
      · exact h.1
      · exact False.elim (one_ne_zero h.1)
  rw [heq]
  exact hm (measurableSet_singleton 0)

/-- Any family of fixed-time evaluations, in particular a finite family, is measurable. -/
theorem measurable_eval_family {ι : Type*} (t : ι → Time) :
    Measurable (fun x : D E => fun i => x.1 (t i)) :=
  measurable_pi_lambda _ (fun i => measurable_eval (t i))

/-- A measurable path-valued map has measurable evaluations. -/
theorem measurable_eval_comp {Ω : Type*} [MeasurableSpace Ω] {X : Ω → D E}
    (hX : Measurable X) (t : Time) : Measurable (fun ω => (X ω).1 t) :=
  (measurable_eval t).comp hX

omit [BorelSpace E] in
/-- Evaluation-wise measurability is preserved by measurable reparametrization of outcomes. -/
theorem measurable_evaluations_comp {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {X : Ω → D E}
    (hX : ∀ t, Measurable (fun ω => (X ω).1 t)) {g : Ω' → Ω} (hg : Measurable g)
    (t : Time) : Measurable (fun ω => (X (g ω)).1 t) :=
  (hX t).comp hg

end LatticeProb.Cadlag.HalfLine
