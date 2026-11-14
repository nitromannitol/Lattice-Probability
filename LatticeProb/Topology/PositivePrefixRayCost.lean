import LatticeProb.Topology.ClippedPrefixCost

/-! # Finite prefixes and stopped rays -/

set_option autoImplicit false
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- The distance between two positive finite prefixes is bounded by the cost of any
increasing reparametrization of their constant-tail extensions. -/
theorem normalizedPrefixCurve_edist_le_stopped_ray_cost {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T U : ℝ≥0)
    (hT : 0 < T) (hU : 0 < U) (e : ℝ≥0 ≃o ℝ≥0) :
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
  refine (normalizedPrefixCurve_edist_le_iSup_clipped f g T U hT hU h k
    hh hh0 hh1 hk hk0 hk1).trans ?_
  apply iSup_le
  intro t
  exact le_iSup_of_le (h t) (by rfl)

end LatticeProb
