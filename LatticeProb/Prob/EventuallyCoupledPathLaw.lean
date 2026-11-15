import LatticeProb.Prob.EventuallyCoupledLaw
import LatticeProb.Bonanno.ReflectedGMS.Limit.PathLawFiniteDimensionalConvergence

/-!
# Continuous path laws under eventual coordinate coupling

Stationary laws on a continuous-path space coincide if each finite coordinate restriction of the
coupled paths eventually agrees almost surely.
-/

open MeasureTheory Filter

namespace LatticeProb

/-- Eventual agreement on each finite set of times identifies the two path laws. -/
theorem continuousMap_law_eq_of_ae_eventually_restrict_eq
    {Ω X E : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (U V : ℕ → Ω → C(X, E))
    (μ ν : Measure C(X, E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hU : ∀ n, Measurable (U n)) (hV : ∀ n, Measurable (V n))
    (hμ : ∀ n, P.map (U n) = μ) (hν : ∀ n, P.map (V n) = ν)
    (heq : ∀ I : Finset X, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      I.restrict (fun x => U n ω x) = I.restrict (fun x => V n ω x)) : μ = ν := by
  apply ReflectedGMS.MartingaleLimit.measure_eq_of_forall_map_finsetRestrict_eq
  intro I
  let e : C(X, E) → (I → E) := fun f => I.restrict (fun x => f x)
  have he : Measurable e := measurable_pi_iff.2 fun i =>
    (ContinuousMap.measurable_eval i.1)
  apply map_eq_of_ae_eventually_eq P (fun n => e ∘ U n) (fun n => e ∘ V n)
    (μ.map e) (ν.map e)
  · exact fun n => he.comp (hU n)
  · exact fun n => he.comp (hV n)
  · intro n
    rw [← Measure.map_map he (hU n), hμ n]
  · intro n
    rw [← Measure.map_map he (hV n), hν n]
  · exact heq I

end LatticeProb
