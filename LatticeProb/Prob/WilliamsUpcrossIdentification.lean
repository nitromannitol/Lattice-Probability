import LatticeProb.Prob.UpcrossFixedPointComparison
import LatticeProb.Prob.WilliamsProductFixedPoint

/-! # Identification of the Williams post-last-zero law -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

open QuantumZipper QuantumZipper.Williams

/-- A zero-started law with the prescribed first-upcrossing pieces is the law of
positive-drift Brownian motion viewed from its last zero. -/
theorem eq_williamsPostLastPath_law_of_upcross_pieces
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {d : ℝ} (hd : 0 < d) (hind : IndepFun (pathOf b) (pathOf b') P)
    (μ : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure μ]
    (hμzero : ∀ᵐ z ∂μ, z 0 = 0)
    (hpiece : ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))),
      (driftLaw P b hb.cont d).map (fun w : C(ℝ≥0, ℝ) =>
        firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
      μ.map (fun z : C(ℝ≥0, ℝ) =>
        (stopAt (hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) :
    μ = P.map (williamsPostLastPath hb' 1 d) := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hzero : ∀ᵐ z ∂(P.map (williamsPostLastPath hb' 1 d)), z 0 = 0 := by
    rw [ae_map_iff (measurable_williamsPostLastPath hb' 1 d).aemeasurable
      (isClosed_eq (continuous_eval_const (0 : ℝ≥0)) continuous_const).measurableSet]
    exact ae_williamsPostLastPath_zero hb' (by norm_num) hd
  apply eq_of_upcross_pieces_of_glue_fixed_points
    (⟨hb.pre, Eventually.of_forall hb.cont⟩ : IsBrownianReal b P)
    hb.meas hb.cont hd μ (P.map (williamsPostLastPath hb' 1 d)) hμzero hzero hpiece
  intro n hn
  exact driftLaw_prod_williamsPostLastPath_glueC hb hb' hd hind (by exact_mod_cast hn)

end LatticeProb
