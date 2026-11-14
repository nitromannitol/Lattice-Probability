/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LipschitzUniformExteriorBalls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.LipschitzLocalExteriorBalls
import Mathlib.Data.Finset.Lattice.Fold

/-! Compactness makes the exterior-ball scale and relative radius uniform
over the entire boundary of a bounded Lipschitz domain. -/

open Set

namespace BouRabeeGwynne

theorem HasLipschitzBoundary.exists_uniform_exterior_balls {d : ℕ} {U : Set (Euc d)}
    (hL : HasLipschitzBoundary U) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ s > 0, ∃ κ > 0, κ ≤ 1 ∧
      ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r → r < s →
        ∃ c : Euc d, dist c p = r ∧ Metric.closedBall c (κ * r) ⊆ Uᶜ := by
  classical
  choose s hs κ hκ hκone hlocal using
    fun p : frontier U => hL.exists_local_exterior_balls hU p.property
  have hcompact : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcover : frontier U ⊆ ⋃ p : frontier U, Metric.ball p.1 (s p) := by
    intro p hp
    apply mem_iUnion.mpr
    refine ⟨⟨p, hp⟩, ?_⟩
    simpa only [Metric.mem_ball, dist_self] using hs ⟨p, hp⟩
  obtain ⟨I, hIcover⟩ := hcompact.elim_finite_subcover
    (fun p : frontier U => Metric.ball p.1 (s p)) (fun _ => Metric.isOpen_ball) hcover
  by_cases hIne : I.Nonempty
  · let s₀ : ℝ := I.inf' hIne s
    have hs₀ : 0 < s₀ := (Finset.lt_inf'_iff hIne).mpr (fun p _ => hs p)
    let κ₀ : ℝ := min 1 (I.inf' hIne κ)
    have hκinf : 0 < I.inf' hIne κ :=
      (Finset.lt_inf'_iff hIne).mpr (fun p _ => hκ p)
    have hκ₀ : 0 < κ₀ := lt_min zero_lt_one hκinf
    refine ⟨s₀, hs₀, κ₀, hκ₀, min_le_left _ _, ?_⟩
    intro p hp r hr hrs
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hIcover hp)
    have hsi : s₀ ≤ s i := Finset.inf'_le s hi
    have hκi : κ₀ ≤ κ i := (min_le_right _ _).trans (Finset.inf'_le κ hi)
    obtain ⟨c, hc, hext⟩ := hlocal i p hp hpi r hr (hrs.trans_le hsi)
    exact ⟨c, hc, (Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right hκi hr.le)).trans hext⟩
  · refine ⟨1, by norm_num, 1, by norm_num, le_rfl, ?_⟩
    intro p hp r hr hrs
    have h := hIcover hp
    have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIne
    simp [hIempty] at h

end BouRabeeGwynne
