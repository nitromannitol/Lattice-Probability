import Mathlib
import LatticeProb.Prob.StoppedPathCoupling

/-!
# Lévy–Prokhorov distance between laws of paths that stay near two points

Let `μ, ν` be probability measures on the space `C(ℝ≥0, E)` of continuous paths in a metric space `E`
with the local uniform metric `dUnif`.  Suppose that, outside a set of measure at most `p`, the paths
of `μ` stay within `r` of a point `z` for all times, and the paths of `ν` stay within `r` of a point `w`.
Then any two such paths are within `2 r + dist z w` of each other at all times, so on a horizon `T0`
their `dUnif`-distance is at most `T0 (2 r + dist z w) + exp (-T0)`.  The product coupling therefore
gives the Lévy–Prokhorov edistance bound
`levyProkhorovEDist μ ν ≤ R` whenever `T0 (2 r + dist z w) + exp (-T0) < R` and `p + p ≤ R`
(`levyProkhorovEDist_le_of_stay_near`).

This is the comparison of the laws of two stopped random paths that both remain in a small ball
until they are stopped, without any coupling between them.
-/

open MeasureTheory Set Metric

open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section StayNear

variable {E : Type*} [MetricSpace E]

attribute [local instance] dUnifMetricSpace

variable [MeasurableSpace C(ℝ≥0, E)] [OpensMeasurableSpace C(ℝ≥0, E)]

/-- **Laws of paths staying near two points.**  If `μ`-almost all paths (up to a set of measure at most
`p`) stay within `r` of `z` at all times, `ν`-almost all paths (up to a set of measure at most `p`) stay
within `r` of `w`, `T0 (2 r + dist z w) + exp (-T0) < R` and `p + p ≤ R`, then the Lévy–Prokhorov
edistance of `μ` and `ν` for the local uniform metric is at most `R`. -/
theorem levyProkhorovEDist_le_of_stay_near (μ ν : Measure C(ℝ≥0, E)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {z w : E} {r : ℝ} (T0 p R : ℝ≥0)
    (hR : T0 * (2 * r + dist z w) + Real.exp (-(T0 : ℝ)) < R)
    (hμ : μ {f | ∃ t, r < dist (f t) z} ≤ p) (hν : ν {g | ∃ t, r < dist (g t) w} ≤ p)
    (hp : p + p ≤ R) :
    levyProkhorovEDist μ ν ≤ R := by
  have hf : (μ.prod ν).map Prod.fst = μ := by rw [Measure.map_fst_prod]; simp
  have hs : (μ.prod ν).map Prod.snd = ν := by rw [Measure.map_snd_prod]; simp
  have key := levyProkhorovEDist_map_le_of_bad (μ.prod ν) (U := Prod.fst) (V := Prod.snd)
    measurable_fst measurable_snd R ?_
  · rwa [hf, hs] at key
  · have hsub : {ω : C(ℝ≥0, E) × C(ℝ≥0, E) | (R : ℝ≥0∞) ≤ edist ω.1 ω.2} ⊆
        Prod.fst ⁻¹' {f | ∃ t, r < dist (f t) z} ∪ Prod.snd ⁻¹' {g | ∃ t, r < dist (g t) w} := by
      intro ω hω
      by_contra hn
      simp only [mem_union, mem_preimage, mem_ofPred_eq, not_or, not_exists, not_lt] at hn
      have hd : dist ω.1 ω.2 < R :=
        lt_of_le_of_lt (dUnif_le_of_forall_dist_le (X := ω.1) (Y := ω.2) T0 (δ := 2 * r + dist z w)
          fun t _ => by
            have h1 := dist_triangle (ω.1 t) z (ω.2 t)
            have h2 := dist_triangle z w (ω.2 t)
            have h3 := hn.1 t
            have h4 := hn.2 t
            rw [dist_comm w (ω.2 t)] at h2
            linarith) hR
      have hlt : edist ω.1 ω.2 < (R : ℝ≥0∞) := by
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hd)).2 hd
      exact absurd hω (not_le.2 hlt)
    have h1 : (μ.prod ν) (Prod.fst ⁻¹' {f | ∃ t, r < dist (f t) z}) ≤ p := by
      have := Measure.le_map_apply (μ := μ.prod ν) (f := Prod.fst) measurable_fst.aemeasurable {f : C(ℝ≥0, E) | ∃ t, r < dist (f t) z}
      rw [hf] at this
      exact this.trans hμ
    have h2 : (μ.prod ν) (Prod.snd ⁻¹' {g | ∃ t, r < dist (g t) w}) ≤ p := by
      have := Measure.le_map_apply (μ := μ.prod ν) (f := Prod.snd) measurable_snd.aemeasurable {g : C(ℝ≥0, E) | ∃ t, r < dist (g t) w}
      rw [hs] at this
      exact this.trans hν
    calc (μ.prod ν) {ω : C(ℝ≥0, E) × C(ℝ≥0, E) | (R : ℝ≥0∞) ≤ edist ω.1 ω.2}
        ≤ (μ.prod ν) (Prod.fst ⁻¹' {f | ∃ t, r < dist (f t) z} ∪
            Prod.snd ⁻¹' {g | ∃ t, r < dist (g t) w}) := measure_mono hsub
      _ ≤ (μ.prod ν) (Prod.fst ⁻¹' {f | ∃ t, r < dist (f t) z}) +
            (μ.prod ν) (Prod.snd ⁻¹' {g | ∃ t, r < dist (g t) w}) := measure_union_le _ _
      _ ≤ p + p := add_le_add h1 h2
      _ ≤ R := by exact_mod_cast hp

end StayNear

end LatticeProb
