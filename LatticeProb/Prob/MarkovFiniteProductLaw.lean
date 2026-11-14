import LatticeProb.Prob.MarkovOrderedListLaw

/-!
# Product expectations at a finite set of times

Equal one-time transition laws determine product expectations at finite sets
of observation times for continuous Markov path-law families.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- Equal one-time transition laws determine product expectations indexed by a
finite set of observation times. -/
theorem integral_finset_prod_eq_of_markov_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x t))
    (I : Finset ℝ≥0) (f : I → E →ᵇ ℝ) (z : E) :
    ∫ x, (∏ i : I, f i (x i)) ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, (∏ i : I, f i (x i)) ∂(L z : Measure C(ℝ≥0, E)) := by
  classical
  let times : List I := (Finset.univ : Finset I).sort (· ≤ ·)
  let tests : List (ℝ≥0 × (E →ᵇ ℝ)) := times.map fun (i : I) => ((i : ℝ≥0), f i)
  have hs : tests.Pairwise (fun p q => p.1 ≤ q.1) := by
    simpa only [tests, List.pairwise_map, times, Subtype.coe_le_coe] using
      (Finset.pairwise_sort (Finset.univ : Finset I) (· ≤ ·))
  have hprod (x : C(ℝ≥0, E)) :
      (tests.map fun p => p.2 (x p.1)).prod = ∏ i : I, f i (x i) := by
    simpa only [tests, List.map_map, Function.comp_def, times, Finset.sort_toFinset] using
      (List.prod_toFinset (fun i : I => f i (x i))
        (Finset.sort_nodup (Finset.univ : Finset I) (· ≤ ·))).symm
  simpa only [hprod] using
    integral_ordered_list_prod_eq_of_markov_marginals hK hL hMK hML hmarg tests hs z

end LatticeProb
