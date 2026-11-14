import Mathlib
import LatticeProb.Prob.MarkovPathKernelDense

/-!
# Transport of the Markov property of a family of path laws along a continuous map of path spaces

Let `K : E → Prob C(ℝ≥0, E)` have the Markov property at `(z, s)` (`LatticeProb.MarkovAt`) and let
`K' : E' → Prob C(ℝ≥0, E')` be a continuous family.  If a continuous map `Φ` of path spaces carries the laws
`K y` to the laws `K' (e y)` and intertwines the stopping at `s` and the shift by `s` with the stopping at `s'`
and the shift by `s'` and the evaluation at `s` with the evaluation at `s'` through a map `e` of the state
spaces, then `K'` has the Markov property at `(e z, s')`.

* `LatticeProb.MarkovAt.map_paths`: the transport.

The typical `Φ` is `x ↦ (u ↦ e (x (c u)))` for an isometry `e` and a time scale `c > 0`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

section Map

variable {E E' : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
  [MetricSpace E'] [SecondCountableTopology E'] [MeasurableSpace E'] [BorelSpace E']
  [MeasurableSpace C(ℝ≥0, E')] [BorelSpace C(ℝ≥0, E')]

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
/-- **Transport of the Markov property along a continuous map of path spaces.** -/
theorem MarkovAt.map_paths {K : E → ProbabilityMeasure C(ℝ≥0, E)} {K' : E' → ProbabilityMeasure C(ℝ≥0, E')}
    (hK' : Continuous K') {z : E} {s s' : ℝ≥0} (h : MarkovAt K z s)
    (Φ : C(ℝ≥0, E) → C(ℝ≥0, E')) (hΦ : Continuous Φ) (e : E → E')
    (hKe : ∀ y, (K' (e y) : Measure C(ℝ≥0, E')) = (K y : Measure C(ℝ≥0, E)).map Φ)
    (hstop : ∀ x, Φ (stopPath x s) = stopPath (Φ x) s')
    (hshift : ∀ x, Φ (pathShift x s) = pathShift (Φ x) s')
    (heval : ∀ x, Φ x s' = e (x s)) : MarkovAt K' (e z) s' := by
  intro g'
  let G : (C(ℝ≥0, E) × C(ℝ≥0, E)) →ᵇ ℝ := g'.compContinuous ⟨Prod.map Φ Φ, hΦ.prodMap hΦ⟩
  have hG := h G
  have hst : Continuous fun x' : C(ℝ≥0, E') => stopPath x' s' :=
    continuous_stopPath_uncurry.comp (continuous_id.prodMk continuous_const)
  have hsh : Continuous fun x' : C(ℝ≥0, E') => pathShift x' s' :=
    continuous_pathShift_uncurry.comp (continuous_id.prodMk continuous_const)
  have hL : ∫ x', g' (stopPath x' s', pathShift x' s') ∂(K' (e z) : Measure C(ℝ≥0, E')) =
      ∫ x, G (stopPath x s, pathShift x s) ∂(K z : Measure C(ℝ≥0, E)) := by
    have hfm : Continuous fun x' : C(ℝ≥0, E') => g' (stopPath x' s', pathShift x' s') :=
      g'.continuous.comp (hst.prodMk hsh)
    rw [hKe z, integral_map hΦ.aemeasurable hfm.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [G, hstop, hshift]
  have hev : Continuous fun x' : C(ℝ≥0, E') => K' (x' s') :=
    hK'.comp (ContinuousEval.continuous_eval.comp (continuous_id.prodMk continuous_const))
  have hφ : Continuous fun x' : C(ℝ≥0, E') =>
      ∫ w, g' (stopPath x' s', w) ∂(K' (x' s') : Measure C(ℝ≥0, E')) :=
    continuous_integral_of_continuous_measure hev
      (G := fun q : C(ℝ≥0, E') × C(ℝ≥0, E') => g' (stopPath q.2 s', q.1))
      (g'.continuous.comp ((hst.comp continuous_snd).prodMk continuous_fst)) (C := ‖g'‖)
      fun q => g'.norm_coe_le_norm _
  have hR : ∫ x', ∫ w, g' (stopPath x' s', w) ∂(K' (x' s') : Measure C(ℝ≥0, E'))
        ∂(K' (e z) : Measure C(ℝ≥0, E')) =
      ∫ x, ∫ w, G (stopPath x s, w) ∂(K (x s) : Measure C(ℝ≥0, E)) ∂(K z : Measure C(ℝ≥0, E)) := by
    rw [hKe z, integral_map hΦ.aemeasurable hφ.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [heval, hKe]
    have hfm2 : Continuous fun w : C(ℝ≥0, E') => g' (stopPath (Φ x) s', w) :=
      g'.continuous.comp (continuous_const.prodMk continuous_id)
    rw [integral_map hΦ.aemeasurable hfm2.aestronglyMeasurable]
    simp [G, hstop]
  rw [hL, hR]
  exact hG

end Map

end LatticeProb
