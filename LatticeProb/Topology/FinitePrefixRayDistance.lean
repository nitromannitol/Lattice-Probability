import LatticeProb.Topology.PositivePrefixRayCost
import LatticeProb.Topology.ReparamEDist

/-! # Finite prefixes and stopped-ray distance -/

set_option autoImplicit false
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

private theorem exists_prefix_clock {d : ℕ}
    (f : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T : ℝ≥0)
    (h : C(unitInterval, ℝ≥0)) (hh : Monotone h) (hh0 : h 0 = 0)
    (hh1 : T ≤ h 1) :
    ∃ c : C(unitInterval, unitInterval), Monotone c ∧ c 0 = 0 ∧ c 1 = 1 ∧
      ∀ t, normalizedPathPrefix f T (c t) = f (min (h t) T) := by
  by_cases hT : T = 0
  · subst T
    refine ⟨ContinuousMap.id unitInterval, monotone_id, rfl, rfl, ?_⟩
    intro t
    simp only [normalizedPathPrefix_apply, NNReal.coe_zero, mul_zero,
      min_eq_right zero_le]
    rfl
  · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
    refine ⟨clippedPrefixClock h T hTpos, clippedPrefixClock_monotone h T hTpos hh,
      clippedPrefixClock_zero h T hTpos hh0, clippedPrefixClock_one h T hTpos hh1, ?_⟩
    intro t
    apply congrArg f
    apply Subtype.ext
    change (clippedPrefixClock h T hTpos t : ℝ) * (T : ℝ) = (min (h t) T : ℝ)
    rw [mul_comm, mul_clippedPrefixClock]

/-- The distance of finite prefix curves is bounded by every stopped-ray clock cost,
including when either duration is zero. -/
theorem normalizedPrefixCurve_edist_le_stopped_ray_cost_all {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T U : ℝ≥0)
    (e : ℝ≥0 ≃o ℝ≥0) :
    edist (normalizedPrefixCurve f T) (normalizedPrefixCurve g U) ≤
      ⨆ s : ℝ≥0, edist (f (min s T)) (g (min (e s) U)) := by
  let K : ℝ≥0 := T + e.symm U + 1
  let h : C(unitInterval, ℝ≥0) :=
    ⟨fun t => K * ⟨(t : ℝ), t.2.1⟩, by fun_prop⟩
  let k : C(unitInterval, ℝ≥0) := ⟨fun t => e (h t), e.continuous.comp h.continuous⟩
  have hh : Monotone h := by
    intro a b hab
    change K * ⟨(a : ℝ), a.2.1⟩ ≤ K * ⟨(b : ℝ), b.2.1⟩
    exact mul_le_mul_of_nonneg_left hab zero_le
  have hh0 : h 0 = 0 := by
    change K * (0 : ℝ≥0) = 0
    exact mul_zero K
  have h1 : h 1 = K := by
    change K * (1 : ℝ≥0) = K
    exact mul_one K
  have hh1 : T ≤ h 1 := by
    rw [h1]
    dsimp [K]
    exact le_trans le_self_add le_self_add
  have he0 : e 0 = 0 := e.map_bot
  have hk : Monotone k := e.monotone.comp hh
  have hk0 : k 0 = 0 := by simp [k, hh0, he0]
  have hk1 : U ≤ k 1 := by
    change U ≤ e (h 1)
    rw [← e.apply_symm_apply U]
    apply e.monotone
    rw [h1]
    dsimp [K]
    exact le_trans (le_add_left le_rfl) le_self_add
  obtain ⟨c, hc, hc0, hc1, hcf⟩ := exists_prefix_clock f T h hh hh0 hh1
  obtain ⟨b, hb, hb0, hb1, hbg⟩ := exists_prefix_clock g U k hk hk0 hk1
  have H := curveSpace_edist_le_iSup_of_monotone_clocks
    (normalizedPathPrefix f T) (normalizedPathPrefix g U) c b hc hc0 hc1 hb hb0 hb1
  refine H.trans (iSup_le fun t => ?_)
  rw [hcf t, hbg t]
  exact le_iSup_of_le (h t) (by rfl)

/-- The distance of finite prefix curves is bounded by the distance of their
constant-tail extensions. -/
theorem normalizedPrefixCurve_edist_le_reparamEDist_stopped_all {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T U : ℝ≥0) :
    edist (normalizedPrefixCurve f T) (normalizedPrefixCurve g U) ≤
      ReparamEDist.reparamEDist (fun t => f (min t T)) (fun t => g (min t U)) := by
  refine le_iInf fun e => ?_
  exact normalizedPrefixCurve_edist_le_stopped_ray_cost_all f g T U e

end LatticeProb
