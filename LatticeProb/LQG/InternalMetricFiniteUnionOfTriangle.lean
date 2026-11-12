import Mathlib
import LatticeProb.LQG.InternalMetricFiniteUnion
import LatticeProb.LQG.InternalMetricOfTriangle

/-!
# Internal diameters of finite connected unions, triangle inequality only

The finite-union bound of `LatticeProb.LQG.IsEuclideanLengthMetric.internalMetric_biUnion_le_sum` uses
the Euclidean length property of `D` only through the triangle inequality of the internal metric.  Here
the same bound is proved for a function `E : ℂ → ℂ → ℝ` that satisfies the triangle inequality in the form
`ofReal (E x z) ≤ ofReal (E x y) + ofReal (E y z)`, with no other assumption (for instance `E` may be a
Weyl scaling `e^{ξ f} D` of a Euclidean length metric by a function `f` that is unbounded near a point).

* `internalMetric_biUnion_le_sum_of_ofReal_triangle`: if `E(u, v; R_i) ≤ A_i` for all `u, v ∈ R_i`,
  `i ∈ F`, and `⋃_{i ∈ F} R_i` is preconnected with closed pieces, then
  `E(u, v; ⋃ R_i) ≤ ∑_{i ∈ F} A_i` for all `u, v` in the union;
* `exists_internalMetric_biUnion_le_ofReal_of_ofReal_triangle`: the same with real bounds.
-/

open Set
open scoped ENNReal

namespace LatticeProb.LQG

/-- Internal diameter of a preconnected finite union of closed sets for a function with the triangle
inequality `ofReal (E x z) ≤ ofReal (E x y) + ofReal (E y z)`: if `E(u, v; R_i) ≤ A_i` for all `u, v ∈ R_i`
and all `i ∈ F`, then `E(u, v; K) ≤ ∑_{i ∈ F} A_i` for all `u, v ∈ K = ⋃_{i ∈ F} R_i`. -/
theorem internalMetric_biUnion_le_sum_of_ofReal_triangle {E : ℂ → ℂ → ℝ}
    (htri : ∀ x y z, ENNReal.ofReal (E x z) ≤ ENNReal.ofReal (E x y) + ENNReal.ofReal (E y z))
    {ι : Type*} {F : Finset ι} {R : ι → Set ℂ} (hK : IsPreconnected (⋃ i ∈ F, R i))
    (hR : ∀ i ∈ F, IsClosed (R i)) {A : ι → ℝ≥0∞}
    (hA : ∀ i ∈ F, ∀ u ∈ R i, ∀ v ∈ R i, internalMetric E (R i) u v ≤ A i) :
    ∀ u ∈ ⋃ i ∈ F, R i, ∀ v ∈ ⋃ i ∈ F, R i, internalMetric E (⋃ i ∈ F, R i) u v ≤ ∑ i ∈ F, A i := by
  classical
  set K := ⋃ i ∈ F, R i with hKdef
  have hsub : ∀ i ∈ F, R i ⊆ K := fun i hi => subset_biUnion_of_mem (u := R) hi
  intro u hu
  suffices H : ∀ n : ℕ, ∀ G ⊆ F, (F \ G).card ≤ n → (⋃ i ∈ G, R i).Nonempty →
      (∀ v ∈ ⋃ i ∈ G, R i, internalMetric E K u v ≤ ∑ i ∈ G, A i) →
      ∀ v ∈ K, internalMetric E K u v ≤ ∑ i ∈ F, A i by
    obtain ⟨i₀, hi₀, hui₀⟩ := mem_iUnion₂.1 hu
    refine H _ {i₀} (Finset.singleton_subset_iff.2 hi₀) le_rfl
      ⟨u, mem_iUnion₂.2 ⟨i₀, Finset.mem_singleton_self _, hui₀⟩⟩ fun v hv => ?_
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 hv
    rw [Finset.mem_singleton.1 hi] at hvi
    rw [Finset.sum_singleton]
    exact (internalMetric_anti E (hsub i₀ hi₀) u v).trans (hA i₀ hi₀ u hui₀ v hvi)
  intro n
  induction n with
  | zero =>
    intro G hGF hcard _ hb v hv
    have hFG : F ⊆ G := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 (Nat.le_zero.1 hcard))
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 hv
    exact (hb v (mem_iUnion₂.2 ⟨i, hFG hi, hvi⟩)).trans (Finset.sum_le_sum_of_subset hGF)
  | succ n ih =>
    intro G hGF hcard hne hb
    by_cases hstep : ∃ j ∈ F, j ∉ G ∧ (R j ∩ ⋃ i ∈ G, R i).Nonempty
    · obtain ⟨j, hjF, hjG, x, hxj, hxG⟩ := hstep
      have hGF' : insert j G ⊆ F := Finset.insert_subset hjF hGF
      have hcard' : (F \ insert j G).card ≤ n := by
        have h1 : F \ insert j G = (F \ G).erase j := by
          ext i; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
        rw [h1, Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hjF, hjG⟩)]
        omega
      refine ih (insert j G) hGF' hcard' (hne.mono (biUnion_subset_biUnion_left fun i hi =>
        Finset.mem_insert_of_mem hi)) fun v hv => ?_
      rw [Finset.sum_insert hjG]
      obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 hv
      rcases Finset.mem_insert.1 hi with hij | hiG
      · rw [hij] at hvi
        calc internalMetric E K u v ≤ internalMetric E K u x + internalMetric E K x v :=
              internalMetric_triangle_of_ofReal_triangle htri K u x v
          _ ≤ ∑ i ∈ G, A i + A j := add_le_add (hb x hxG)
              ((internalMetric_anti E (hsub j hjF) x v).trans (hA j hjF x hxj v hvi))
          _ = A j + ∑ i ∈ G, A i := add_comm _ _
      · exact (hb v (mem_iUnion₂.2 ⟨i, hiG, hvi⟩)).trans le_add_self
    · intro v hv
      have hall := IsPreconnected.biUnion_subset_of_forall_inter_eq_empty hK hR hGF hne fun j hj hjG =>
        Set.not_nonempty_iff_eq_empty.1 fun h => hstep ⟨j, hj, hjG, h⟩
      exact (hb v (hall hv)).trans (Finset.sum_le_sum_of_subset hGF)

/-- Finite internal diameter of a preconnected finite union of closed sets, with real bounds, for a
function with the triangle inequality `ofReal (E x z) ≤ ofReal (E x y) + ofReal (E y z)`: if every piece
has internal diameter at most some real number, so has the union. -/
theorem exists_internalMetric_biUnion_le_ofReal_of_ofReal_triangle {E : ℂ → ℂ → ℝ}
    (htri : ∀ x y z, ENNReal.ofReal (E x z) ≤ ENNReal.ofReal (E x y) + ENNReal.ofReal (E y z))
    {ι : Type*} {F : Finset ι} {R : ι → Set ℂ}
    (hK : IsPreconnected (⋃ i ∈ F, R i)) (hR : ∀ i ∈ F, IsClosed (R i))
    (hA : ∀ i ∈ F, ∃ a : ℝ, ∀ u ∈ R i, ∀ v ∈ R i, internalMetric E (R i) u v ≤ ENNReal.ofReal a) :
    ∃ A : ℝ, ∀ u ∈ ⋃ i ∈ F, R i, ∀ v ∈ ⋃ i ∈ F, R i,
      internalMetric E (⋃ i ∈ F, R i) u v ≤ ENNReal.ofReal A := by
  choose! a ha using hA
  have hfin : ∑ i ∈ F, ENNReal.ofReal (a i) ≠ ∞ := ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  refine ⟨(∑ i ∈ F, ENNReal.ofReal (a i)).toReal, fun u hu v hv => ?_⟩
  rw [ENNReal.ofReal_toReal hfin]
  exact internalMetric_biUnion_le_sum_of_ofReal_triangle htri hK hR ha u hu v hv

end LatticeProb.LQG
