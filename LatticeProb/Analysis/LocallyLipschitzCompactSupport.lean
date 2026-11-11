import Mathlib

/-!
# Locally Lipschitz functions with compact support are Lipschitz

A locally Lipschitz map `g` from a pseudometric space to a normed group whose support is compact is globally Lipschitz:
finitely many neighbourhoods on which `g` is Lipschitz cover the support, a Lebesgue number `δ` of this cover handles
pairs of points at distance less than `δ`, and pairs at distance at least `δ` are handled by the bound `2 sup ‖g‖ / δ`.

* `LatticeProb.exists_lipschitzWith_of_locallyLipschitz_of_hasCompactSupport`.
-/

namespace LatticeProb

open Metric Set
open scoped NNReal Topology

/-- A locally Lipschitz function with compact support is Lipschitz. -/
theorem exists_lipschitzWith_of_locallyLipschitz_of_hasCompactSupport {α E : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup E] {g : α → E} (hg : LocallyLipschitz g) (hc : HasCompactSupport g) :
    ∃ C : ℝ≥0, LipschitzWith C g := by
  classical
  have hcont : Continuous g := hg.continuous
  choose K t ht hKt using hg
  obtain ⟨I, -, hI⟩ := hc.isCompact.elim_nhds_subcover (fun x => interior (t x))
    (fun x _ => interior_mem_nhds.2 (ht x))
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun i : I => interior (t i)) hc.isCompact
    (fun _ => isOpen_interior) (by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hI hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hcont
  refine ⟨max (I.sup K) (Real.toNNReal (2 * M / δ)), LipschitzWith.of_dist_le_mul ?_⟩
  have key : ∀ x y, x ∈ tsupport g → dist x y < δ →
      dist (g x) (g y) ≤ (max (I.sup K) (Real.toNNReal (2 * M / δ)) : ℝ≥0) * dist x y := by
    intro x y hx hxy
    obtain ⟨i, hi⟩ := hleb x hx
    have hxi : x ∈ t i := interior_subset (hi (mem_ball_self hδ))
    have hyi : y ∈ t i := interior_subset (hi (mem_ball'.2 hxy))
    refine ((hKt i).dist_le_mul x hxi y hyi).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
    exact_mod_cast (Finset.le_sup (f := K) i.2).trans (le_max_left _ _)
  intro x y
  rcases lt_or_ge (dist x y) δ with hxy | hxy
  · by_cases hx : x ∈ tsupport g
    · exact key x y hx hxy
    · by_cases hy : y ∈ tsupport g
      · rw [dist_comm (g x), dist_comm x]
        exact key y x hy (by rwa [dist_comm])
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy, dist_self]
        positivity
  · have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
    have h1 : dist (g x) (g y) ≤ 2 * M := by
      refine (dist_le_norm_add_norm _ _).trans ?_
      linarith [hM x, hM y]
    have h2 : 2 * M ≤ 2 * M / δ * dist x y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left hxy (by linarith)
    refine h1.trans (h2.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg))
    rw [NNReal.coe_max]
    exact (Real.le_coe_toNNReal _).trans (le_max_right _ _)

end LatticeProb
