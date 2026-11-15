import LatticeProb.LQG.LQGMeasureOriginBound
import LatticeProb.LQG.LQGMeasureExistenceSingular
import LatticeProb.LQG.LQGMassFatou
import LatticeProb.LQG.LQGSingularScaledLimit

/-! # Uniform origin tightness of logarithmically singular approximations -/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG.LQGMeasureOriginBound

open LatticeProb.Gauss

/-- The origin mass bound holds uniformly over all dyadic regularization scales when the
circle-average slices are continuous. -/
theorem exists_uniform_singular_approximant_origin_bound {γ α : ℝ} (hγ : 0 < γ)
    (hαQ : α < lqgQ γ) (h : ℝ → ℂ → ℝ)
    (hcont : ∀ k : ℕ, Continuous (h (dyadicScale k)))
    (hZ : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (Real.exp (η * j))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ,
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨δ, hδ, K, hK⟩ :=
    exists_lqgApprox_fieldCircleAverage_ball_le_of_eventually hγ hαQ h hZ η hη
  have hearly : ∀ k : ℕ, ∀ᶠ j : ℕ in atTop,
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale j)) ≤
        ENNReal.ofReal η := by
    intro k
    let μ := lqgApprox γ (fieldCircleAverage α h) (dyadicScale k)
    have hc : Continuous (fieldCircleAverage α h (dyadicScale k)) :=
      LQGMeasureExistenceSingular.continuous_fieldCircleAverage_of_continuous
        (dyadicScale_pos' k) (hcont k)
    have : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_lqgApprox_of_continuous γ hc
    have hzero : μ {0} = 0 := by
      exact (withDensity_absolutelyContinuous volume _ (measure_singleton (0 : ℂ)))
    obtain ⟨U, hU, hUopen, hUη⟩ :=
      isCompact_singleton.exists_isOpen_lt_of_lt (μ := μ) (ENNReal.ofReal η) (by
        rw [hzero]; exact ENNReal.ofReal_pos.mpr hη)
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUopen 0 (hU (by simp))
    have hlim := LQGSingularScaledLimit.tendsto_dyadicScale_zero
    filter_upwards [hlim.eventually (Iio_mem_nhds hr)] with j hj
    exact (measure_mono ((ball_subset_ball hj.le).trans hrU)).trans hUη.le
  have hall : ∀ᶠ j : ℕ in atTop, ∀ k ∈ Finset.range K,
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale j)) ≤
        ENNReal.ofReal η := (eventually_all_finset _).2 fun k _ => hearly k
  have hsmall := LQGSingularScaledLimit.tendsto_dyadicScale_zero.eventually (Iio_mem_nhds hδ)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hall.and hsmall)
  refine ⟨dyadicScale J, dyadicScale_pos' J, fun k => ?_⟩
  obtain ⟨hJearly, hJδ⟩ := hJ J le_rfl
  by_cases hk : k < K
  · exact hJearly k (Finset.mem_range.mpr hk)
  · exact (measure_mono (ball_subset_ball hJδ.le)).trans (hK k (Nat.le_of_not_gt hk))

end LatticeProb.LQG.LQGMeasureOriginBound
