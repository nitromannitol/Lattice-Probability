import LatticeProb.Prob.Percolation.LSS.Basic

/-!
# Cylinder hulls of sets of configurations

The cylinder hull of a set of configurations over a finite set of coordinates: the
configurations that agree on the coordinates with some member of the set. The hull
contains the set, shrinks as the coordinate set grows, is increasing when the set is,
depends only on the coordinates in the finite set, and, for a closed set, the hulls
over all finite coordinate sets intersect to the set itself.

Ported from the Exploding-Sandpiles formalization, `Support/ExtLSSCyl.lean`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace LatticeProb.Percolation.LSS

variable {S : Type}

/-- The cylinder hull of `F` over the finite coordinate set `T`: the configurations that
agree on `T` with some configuration of `F`. -/
def xlsb_cylHull (T : Finset S) (F : Set (S → Bool)) : Set (S → Bool) :=
  {x | ∃ y ∈ F, ∀ s ∈ T, y s = x s}

/-- A set is contained in its cylinder hull over any finite coordinate set. -/
theorem xlsb_subset_cylHull (T : Finset S) (F : Set (S → Bool)) : F ⊆ xlsb_cylHull T F :=
  fun x hx => ⟨x, hx, fun _ _ => rfl⟩

/-- Cylinder hulls shrink as the finite coordinate set grows. -/
theorem xlsb_cylHull_antitone {T T' : Finset S} (h : T ⊆ T') (F : Set (S → Bool)) :
    xlsb_cylHull T' F ⊆ xlsb_cylHull T F := by
  rintro x ⟨y, hy, hyx⟩
  exact ⟨y, hy, fun s hs => hyx s (h hs)⟩

/-- The cylinder hull of an increasing set is increasing. -/
theorem xlsb_cylHull_increasing (T : Finset S) {F : Set (S → Bool)} (hF : IsIncreasingSet F) :
    IsIncreasingSet (xlsb_cylHull T F) := by
  classical
  intro x x' hx hxx'
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨fun s => if s ∈ T then x' s else y s, ?_, ?_⟩
  · refine hF y _ hy ?_
    intro s hs
    by_cases h : s ∈ T
    · rw [ite_eq_left h]
      exact hxx' s (by rw [← hyx s h]; exact hs)
    · rw [ite_eq_right h]
      exact hs
  · intro s hs
    simp [hs]

/-- Membership in the cylinder hull over `T` depends only on the coordinates in `T`. -/
theorem xlsb_cylHull_det (T : Finset S) (F : Set (S → Bool)) (x y : S → Bool)
    (hxy : ∀ t ∈ T, x t = y t) : x ∈ xlsb_cylHull T F ↔ y ∈ xlsb_cylHull T F := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, fun s hs => (hzx s hs).trans (hxy s hs)⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, hz, fun s hs => (hzy s hs).trans (hxy s hs).symm⟩

/-- The cylinder hull over a finite coordinate set is the preimage of a set of restrictions. -/
theorem xlsb_cylHull_eq_preimage (T : Finset S) (F : Set (S → Bool)) :
    xlsb_cylHull T F = (fun x : S → Bool => fun t : T => x t) ⁻¹'
      ((fun x : S → Bool => fun t : T => x t) '' F) := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, funext fun t => hyx t t.2⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, fun s hs => congrFun hyx ⟨s, hs⟩⟩

/-- Cylinder hulls over a finite coordinate set are measurable. -/
theorem xlsb_measurableSet_cylHull (T : Finset S) (F : Set (S → Bool)) :
    MeasurableSet (xlsb_cylHull T F) := by
  rw [xlsb_cylHull_eq_preimage]
  have hmeas : Measurable (fun x : S → Bool => fun t : T => x t) :=
    Measurable.of_eval fun t => measurable_pi_apply (t : S)
  exact hmeas (Set.toFinite _).measurableSet

/-- The intersection of the cylinder hulls over all subsets of `T` is the hull over `T`. -/
theorem xlsb_biInter_le_eq (T : Finset S) (F : Set (S → Bool)) :
    ⋂ (T' : Finset S) (_ : T' ≤ T), xlsb_cylHull T' F = xlsb_cylHull T F := by
  refine Set.Subset.antisymm ?_ ?_
  · exact Set.iInter₂_subset
      (s := fun (T' : Finset S) (_ : T' ≤ T) => xlsb_cylHull T' F) T le_rfl
  · exact Set.subset_iInter₂ fun T' hT' => xlsb_cylHull_antitone hT' F

/-- For a closed set, the cylinder hulls over all finite coordinate sets intersect to the
set itself. -/
theorem xlsb_iInter_cylHull {F : Set (S → Bool)} (hF : IsClosed F) :
    ⋂ T : Finset S, xlsb_cylHull T F = F := by
  refine Set.Subset.antisymm ?_ (Set.subset_iInter fun T => xlsb_subset_cylHull T F)
  intro x hx
  rw [← hF.closure_eq, mem_closure_iff_nhds]
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hIU⟩ := hU
  have hxt : ∀ i, x i ∈ t i := fun i => by
    have := ht i
    rwa [nhds_discrete, Filter.mem_pure] at this
  obtain ⟨y, hy, hyx⟩ := Set.mem_iInter.1 hx hI.toFinset
  refine ⟨y, hIU ?_, hy⟩
  intro i hi
  rw [hyx i (hI.mem_toFinset.2 hi)]
  exact hxt i

end LatticeProb.Percolation.LSS
