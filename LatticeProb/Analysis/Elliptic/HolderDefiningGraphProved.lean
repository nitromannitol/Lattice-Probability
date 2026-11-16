import LatticeProb.Analysis.Elliptic.HolderDefiningGraphHessian
import LatticeProb.Analysis.Elliptic.HolderDefiningGraphGlobal

/-!
# Hölder regularity of defining graphs

A defining function yields a globally controlled Hölder graph near each boundary point.
-/

open scoped Topology ENNReal

namespace LatticeProb.Elliptic.HolderExtension

/-- A regular boundary point admits a globally Hölder controlled local graph. -/
theorem definingFunction_local_graph {d : ℕ} {σ : ℝ}
    (hσ : 0 < σ) (hσ' : σ < 1) {U : Set (Fin d → ℝ)}
    (hU : IsC2HolderDomain σ U) {p : Fin d → ℝ} (hp : p ∈ frontier U) :
    ∃ (i : Fin d) (g : (Fin d → ℝ) → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ 2 g ∧ c2HolderNorm σ Set.univ g < ⊤ ∧
      (∀ x t, g (Function.update x i t) = g x) ∧ g p = p i ∧
      ((∀ x ∈ Metric.ball p r, x ∈ U ↔ x i < g x) ∨
       (∀ x ∈ Metric.ball p r, x ∈ U ↔ g x < x i)) := by
  obtain ⟨ρ, i, g, a, ha, hρ, hnorm, _, _, hi, hg, _, hinv, hgp, hzero, hside⟩ :=
    definingFunction_global_C2_graph_with_level hU hp
  have hzero' : ∀ᶠ x in 𝓝 p, ρ (Function.update x i (g x)) = 0 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds p ha) hzero
  obtain ⟨H, b, _, hb, hH⟩ :=
    exists_holder_increment_secondPartial_graph hσ.le hσ'.le ρ g hρ hnorm hg p i hgp hzero' hi
  have hab : 0 < min a b := lt_min ha hb
  have hH' : ∀ j k, ∀ x ∈ Metric.ball p (min a b), ∀ y ∈ Metric.ball p (min a b),
      |secondPartial j k g x - secondPartial j k g y| ≤
        H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
    intro j k x hx y hy
    exact hH j k x (Metric.ball_subset_ball (min_le_right _ _) hx)
      y (Metric.ball_subset_ball (min_le_right _ _) hy)
  obtain ⟨G, r, hr, hra, hG, hGn, hGi, heq⟩ :=
    exists_global_graph_of_local_holder hσ hσ' g hg p i hinv hab hH'
  have hsub : Metric.ball p r ⊆ Metric.ball p a :=
    Metric.ball_subset_ball (hra.trans (min_le_left _ _))
  have hGp : G p = p i := (heq p (Metric.mem_ball_self hr)).trans hgp
  refine ⟨i, G, r, hr, hG, hGn, hGi, hGp, ?_⟩
  rcases hside with hleft | hright
  · left
    intro x hx
    rw [heq x hx]
    exact hleft x (hsub hx)
  · right
    intro x hx
    rw [heq x hx]
    exact hright x (hsub hx)

end LatticeProb.Elliptic.HolderExtension
