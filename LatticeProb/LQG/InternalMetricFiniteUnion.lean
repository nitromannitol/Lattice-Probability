import Mathlib
import LatticeProb.LQG.LQGMetricMeasurable

/-!
# Internal diameters of finite connected unions

Let `K = ⋃_{i ∈ F} R_i` be a preconnected finite union of closed sets. If every piece `R_i` has internal diameter at
most `A_i` for a Euclidean length metric `D` (that is, `D(u, v; R_i) ≤ A_i` for all `u, v ∈ R_i`), then `K` has internal
diameter at most `∑_{i ∈ F} A_i`. This is the reduction of the finiteness of the internal diameter of a connected
finite union of closed rectangles to that of single rectangles.

* `IsPreconnected.biUnion_subset_of_forall_inter_eq_empty`: if a subfamily `G ⊆ F` with nonempty union meets no piece
  outside `G`, then its union is all of `K` (the intersection graph of a preconnected finite union of closed sets is
  connected);
* `IsEuclideanLengthMetric.internalMetric_biUnion_le_sum`: the internal-diameter bound, by growing a subfamily `G`
  containing the starting point one piece at a time, each new piece meeting the union of the previous ones, and using
  the triangle inequality of the internal metric at a common point;
* `IsEuclideanLengthMetric.exists_internalMetric_biUnion_le_ofReal`: the same with real bounds.
-/

namespace LatticeProb.LQG

open Set
open scoped ENNReal

/-- The intersection graph of a preconnected finite union of closed sets is connected: if the union of a subfamily
`G ⊆ F` is nonempty and meets no piece `R_j` with `j ∈ F \ G`, then it contains the whole union over `F`. -/
theorem IsPreconnected.biUnion_subset_of_forall_inter_eq_empty {α ι : Type*} [TopologicalSpace α]
    {F G : Finset ι} {R : ι → Set α} (hK : IsPreconnected (⋃ i ∈ F, R i)) (hR : ∀ i ∈ F, IsClosed (R i))
    (hGF : G ⊆ F) (hne : (⋃ i ∈ G, R i).Nonempty)
    (hdisj : ∀ j ∈ F, j ∉ G → R j ∩ ⋃ i ∈ G, R i = ∅) :
    ⋃ i ∈ F, R i ⊆ ⋃ i ∈ G, R i := by
  classical
  set X := ⋃ i ∈ G, R i
  set Y := ⋃ i ∈ F.filter (· ∉ G), R i
  have hX : IsClosed X := isClosed_biUnion_finset fun i hi => hR i (hGF hi)
  have hY : IsClosed Y := isClosed_biUnion_finset fun i hi => hR i (Finset.mem_filter.1 hi).1
  have hcov : ⋃ i ∈ F, R i ⊆ X ∪ Y := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 hv
    by_cases hiG : i ∈ G
    · exact Or.inl (mem_iUnion₂.2 ⟨i, hiG, hvi⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨hi, hiG⟩, hvi⟩)
  have hXK : X ⊆ ⋃ i ∈ F, R i := iUnion₂_subset fun i hi => subset_biUnion_of_mem (u := R) (hGF hi)
  intro v hv
  by_contra hvX
  have hvY : v ∈ Y := (hcov hv).resolve_left hvX
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z, -, hzX, hzY⟩ := isPreconnected_closed_iff.1 hK X Y hX hY hcov ⟨x, hXK hx, hx⟩ ⟨v, hv, hvY⟩
  obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 hzY
  obtain ⟨hjF, hjG⟩ := Finset.mem_filter.1 hj
  have h := hdisj j hjF hjG
  exact (Set.eq_empty_iff_forall_notMem.1 h) z ⟨hzj, hzX⟩

/-- Internal diameter of a preconnected finite union of closed sets: if `D(u, v; R_i) ≤ A_i` for all `u, v ∈ R_i` and
all `i ∈ F`, then `D(u, v; K) ≤ ∑_{i ∈ F} A_i` for all `u, v ∈ K = ⋃_{i ∈ F} R_i`. -/
theorem IsEuclideanLengthMetric.internalMetric_biUnion_le_sum {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ι : Type*} {F : Finset ι} {R : ι → Set ℂ} (hK : IsPreconnected (⋃ i ∈ F, R i))
    (hR : ∀ i ∈ F, IsClosed (R i)) {A : ι → ℝ≥0∞}
    (hA : ∀ i ∈ F, ∀ u ∈ R i, ∀ v ∈ R i, internalMetric D (R i) u v ≤ A i) :
    ∀ u ∈ ⋃ i ∈ F, R i, ∀ v ∈ ⋃ i ∈ F, R i, internalMetric D (⋃ i ∈ F, R i) u v ≤ ∑ i ∈ F, A i := by
  classical
  set K := ⋃ i ∈ F, R i with hKdef
  have hsub : ∀ i ∈ F, R i ⊆ K := fun i hi => subset_biUnion_of_mem (u := R) hi
  intro u hu
  -- Grow a subfamily `G ∋ i₀` whose union is reached from `u` within `∑_{G} A`.
  suffices H : ∀ n : ℕ, ∀ G ⊆ F, (F \ G).card ≤ n → (⋃ i ∈ G, R i).Nonempty →
      (∀ v ∈ ⋃ i ∈ G, R i, internalMetric D K u v ≤ ∑ i ∈ G, A i) →
      ∀ v ∈ K, internalMetric D K u v ≤ ∑ i ∈ F, A i by
    obtain ⟨i₀, hi₀, hui₀⟩ := mem_iUnion₂.1 hu
    refine H _ {i₀} (Finset.singleton_subset_iff.2 hi₀) le_rfl
      ⟨u, mem_iUnion₂.2 ⟨i₀, Finset.mem_singleton_self _, hui₀⟩⟩ fun v hv => ?_
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 hv
    rw [Finset.mem_singleton.1 hi] at hvi
    rw [Finset.sum_singleton]
    exact (internalMetric_anti D (hsub i₀ hi₀) u v).trans (hA i₀ hi₀ u hui₀ v hvi)
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
        calc internalMetric D K u v ≤ internalMetric D K u x + internalMetric D K x v :=
              hD.internalMetric_triangle K u x v
          _ ≤ ∑ i ∈ G, A i + A j := add_le_add (hb x hxG)
              ((internalMetric_anti D (hsub j hjF) x v).trans (hA j hjF x hxj v hvi))
          _ = A j + ∑ i ∈ G, A i := add_comm _ _
      · exact (hb v (mem_iUnion₂.2 ⟨i, hiG, hvi⟩)).trans le_add_self
    · intro v hv
      have hall := IsPreconnected.biUnion_subset_of_forall_inter_eq_empty hK hR hGF hne fun j hj hjG =>
        Set.not_nonempty_iff_eq_empty.1 fun h => hstep ⟨j, hj, hjG, h⟩
      exact (hb v (hall hv)).trans (Finset.sum_le_sum_of_subset hGF)

/-- Finite internal diameter of a preconnected finite union of closed sets, with real bounds: if every piece has
internal diameter at most some real number, so has the union. -/
theorem IsEuclideanLengthMetric.exists_internalMetric_biUnion_le_ofReal {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ι : Type*} {F : Finset ι} {R : ι → Set ℂ}
    (hK : IsPreconnected (⋃ i ∈ F, R i)) (hR : ∀ i ∈ F, IsClosed (R i))
    (hA : ∀ i ∈ F, ∃ a : ℝ, ∀ u ∈ R i, ∀ v ∈ R i, internalMetric D (R i) u v ≤ ENNReal.ofReal a) :
    ∃ A : ℝ, ∀ u ∈ ⋃ i ∈ F, R i, ∀ v ∈ ⋃ i ∈ F, R i,
      internalMetric D (⋃ i ∈ F, R i) u v ≤ ENNReal.ofReal A := by
  choose! a ha using hA
  have hfin : ∑ i ∈ F, ENNReal.ofReal (a i) ≠ ∞ := ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  refine ⟨(∑ i ∈ F, ENNReal.ofReal (a i)).toReal, fun u hu v hv => ?_⟩
  rw [ENNReal.ofReal_toReal hfin]
  exact hD.internalMetric_biUnion_le_sum hK hR ha u hu v hv

end LatticeProb.LQG
