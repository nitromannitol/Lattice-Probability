import LatticeProb.LQG.DyadicHullNeighborhoods
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S4

/-! # Mean-zero field germs on compact sets -/

set_option autoImplicit false

open Set Metric
open LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- For a fixed compact set, dyadic hull interiors and positive thickenings
induce the same mean-zero field germ. -/
theorem fieldSigmaClosed0_eq_iInf_dyadicHull {Ω : Type} (h : Ω → DistC)
    {K : Set ℂ} (hK : IsCompact K) :
    fieldSigmaClosed0 h K =
      ⨅ n : ℕ, fieldSigma0On h (interior (dyadicHull n K)) := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    obtain ⟨ε, hε, hsub⟩ := exists_thickening_subset_interior_dyadicHull hK n
    exact (iInf₂_le ε hε).trans (conf36_fieldSigma0On_mono h hsub)
  · unfold fieldSigmaClosed0
    refine le_iInf fun ε => le_iInf fun hε => ?_
    obtain ⟨n, hn⟩ := exists_dyadicHull_subset_thickening K hε
    exact (iInf_le _ n).trans
      (conf36_fieldSigma0On_mono h (interior_subset.trans hn))

end LatticeProb.LQG
