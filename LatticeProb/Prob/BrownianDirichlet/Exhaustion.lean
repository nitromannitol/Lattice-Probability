import LatticeProb.Prob.BrownianDirichlet.Localization
import LatticeProb.Prob.BrownianDirichlet.ScaledExit

/-!
# Exit times under exhaustion by inner balls

For every continuous path, the exit times from increasing concentric inner balls
converge to the exit time from the outer ball, including infinite exit times.
Finite truncations converge both as extended and as ordinary nonnegative reals.
-/

namespace LatticeProb

open Set Filter Metric
open scoped Topology NNReal ENNReal

variable {d : ℕ} {c : Euc d} {R : ℝ} {σ : ℝ} {x : Euc d}
    {ω : BrownianPath d}

/-- Enlarging the exit domain can only increase the first exit time. -/
theorem scaledExit_mono_set {U V : Set (Euc d)} (hUV : U ⊆ V) :
    scaledExit U σ x ω ≤ scaledExit V σ x ω := by
  change continuousExitTime U x (scalePath σ ω) ≤
    ⨅ t : {t : ℝ≥0 // x + scalePath σ ω t ∉ V}, (t.val : ℝ≥0∞)
  refine le_iInf fun t => ?_
  exact continuousExitTime_le_of_not_mem (fun h => t.property (hUV h))

/-- The exit times from the inner balls increase with the exhaustion index. -/
theorem monotone_scaledExit_innerBall (hR : 0 < R) :
    Monotone (fun k => scaledExit (ball c (innerRadius R k)) σ x ω) := by
  intro j k hjk
  exact scaledExit_mono_set (ball_subset_ball (innerRadius_monotone hR hjk))

/-- Every inner-ball exit time is bounded by the outer-ball exit time. -/
theorem scaledExit_innerBall_le (hR : 0 < R) (k : ℕ) :
    scaledExit (ball c (innerRadius R k)) σ x ω ≤ scaledExit (ball c R) σ x ω :=
  scaledExit_mono_set (ball_subset_ball (innerRadius_lt hR k).le)

/-- A compact path segment strictly before outer exit fits inside one inner ball. -/
theorem exists_lt_scaledExit_innerBall (hR : 0 < R) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < scaledExit (ball c R) σ x ω) :
    ∃ k, (t : ℝ≥0∞) < scaledExit (ball c (innerRadius R k)) σ x ω := by
  let f : ℝ≥0 → Euc d := fun s => x + σ • ω s
  have hf : Continuous f := continuous_const.add (ω.continuous.const_smul σ)
  have hcompact : IsCompact (f '' Icc 0 t) := isCompact_Icc.image hf
  have hsubset : f '' Icc 0 t ⊆ ball c R := by
    rintro y ⟨s, hs, rfl⟩
    exact mem_of_lt_scaledExit ((ENNReal.coe_le_coe.mpr hs.2).trans_lt ht)
  obtain ⟨k, hk⟩ := IsCompact.subset_innerRadius_ball hcompact hR hsubset
  refine ⟨k, lt_of_not_ge ?_⟩
  intro hle
  have hout := (continuousExitTime_le_iff_not_mapsTo isOpen_ball x
    (scalePath σ ω) t).mp hle
  apply hout
  intro s hs
  exact hk ⟨s, hs, rfl⟩

/-- Inner-ball exit times converge to outer-ball exit, even when the latter is infinite. -/
theorem tendsto_scaledExit_innerBall (hR : 0 < R) :
    Tendsto (fun k => scaledExit (ball c (innerRadius R k)) σ x ω) atTop
      (𝓝 (scaledExit (ball c R) σ x ω)) := by
  have heq : (⨆ k, scaledExit (ball c (innerRadius R k)) σ x ω) =
      scaledExit (ball c R) σ x ω := by
    apply le_antisymm
    · exact iSup_le (scaledExit_innerBall_le hR)
    · apply ENNReal.le_of_forall_nnreal_lt
      intro t ht
      obtain ⟨k, hk⟩ := exists_lt_scaledExit_innerBall hR ht
      exact hk.le.trans (le_iSup
        (fun j => scaledExit (ball c (innerRadius R j)) σ x ω) k)
  rw [← heq]
  exact tendsto_atTop_iSup (monotone_scaledExit_innerBall hR)

/-- Truncating inner-ball exit times at a finite time preserves convergence. -/
theorem tendsto_min_scaledExit_innerBall (hR : 0 < R) (N : ℝ≥0) :
    Tendsto (fun k => min (scaledExit (ball c (innerRadius R k)) σ x ω) (N : ℝ≥0∞))
      atTop (𝓝 (min (scaledExit (ball c R) σ x ω) (N : ℝ≥0∞))) :=
  (tendsto_scaledExit_innerBall hR).min tendsto_const_nhds

/-- The finite truncated exit times also converge as nonnegative real numbers. -/
theorem tendsto_toNNReal_min_scaledExit_innerBall (hR : 0 < R) (N : ℝ≥0) :
    Tendsto (fun k => (min (scaledExit (ball c (innerRadius R k)) σ x ω)
      (N : ℝ≥0∞)).toNNReal) atTop
      (𝓝 (min (scaledExit (ball c R) σ x ω) (N : ℝ≥0∞)).toNNReal) := by
  apply (ENNReal.tendsto_toNNReal ?_).comp (tendsto_min_scaledExit_innerBall hR N)
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)

end LatticeProb
