import LatticeProb.Prob.UpcrossGlueProductUnique
import LatticeProb.Prob.UpcrossGlueCocycle

/-!
# Comparison of upcrossing and gluing laws

A continuous-path law with prescribed first-upcrossing pieces agrees with any
zero-started probability law invariant under independent gluing at positive
integer levels.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- A law with the first-upcrossing pieces of positive-drift Brownian motion is
uniquely determined among zero-started fixed points of negative-drift gluing. -/
theorem eq_of_upcross_pieces_of_glue_fixed_points
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {d : ℝ} (hd : 0 < d) (μ ν : Measure C(ℝ≥0, ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμzero : ∀ᵐ z ∂μ, z 0 = 0) (hνzero : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))),
      (driftLaw P B hcont d).map (fun w : C(ℝ≥0, ℝ) =>
        firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
      μ.map (fun z : C(ℝ≥0, ℝ) =>
        (stopAt (hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)))
    (hν : ∀ n : ℕ, 0 < n →
      ((driftLaw P B hcont (-d)).prod ν).map
        (fun p => glueC (n : ℝ) p.1 p.2) = ν) : μ = ν := by
  let ρ := driftLaw P B hcont (-d)
  have : IsProbabilityMeasure ρ := isProbabilityMeasure_driftLaw hm hcont (-d)
  have hhit : ∀ᵐ (y : C(ℝ≥0, ℝ)) ∂ρ, ∀ n : ℕ,
      hitFrom (-(n : ℝ)) 0 (y : ℝ≥0 → ℝ) ≠ ⊤ := by
    rw [ae_all_iff]
    intro n
    filter_upwards [ae_hitFrom_neg_ne_top_driftLaw_neg hB hm hcont hd
      (Nat.cast_nonneg n)] with y hy
    exact hy.2
  apply glueC_law_unique_of_product_fixed_points ρ μ ν 0 hhit hμzero hνzero
  · intro n hn
    exact map_glueC_prod_eq hB hm hcont hd (by exact_mod_cast hn) hμzero hpiece
  · exact hν

end LatticeProb
