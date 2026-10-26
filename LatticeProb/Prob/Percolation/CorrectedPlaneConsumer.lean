import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization

/-!
# Coordinate corrected planes on the fully open lattice

Reflection of neighbors about a vertex cancels the actual component Laplacian of a
coordinate. The coordinate is an A₁ function with identically zero error from its slope.
The actual unique infinite all-open component also supplies the zero-slope constant check.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

/-- On the actual all-open infinite component every coordinate is harmonic, by pairing
opposite neighbors in the literal component neighbor sum. -/
theorem allOpen_component_coordinate_harmonic (d : ℕ) [NeZero d] (i : Fin d)
    (x : uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d)) :
    componentLaplacian (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d))
      (fun y => (y.val i : ℝ)) x = 0 := by
  classical
  let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d)
  let reflect (y : C) : C := ⟨x.val + x.val - y.val, by
    change x.val + x.val - y.val ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d)).supp
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial⟩
  have hmem (y : C) (hy : y ∈ (componentGraph C).neighborFinset x) :
      reflect y ∈ (componentGraph C).neighborFinset x := by
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    change (openGraph (allOpen d)).Adj x.val y.val at hy
    change (openGraph (allOpen d)).Adj x.val (x.val + x.val - y.val)
    have hy' := Graph.Zd.adj_iff.mp (openGraph_le (allOpen d) hy)
    apply (openGraph_adj_iff _ _ _).mpr
    refine ⟨Graph.Zd.adj_iff.mpr ?_, rfl⟩
    obtain ⟨j, hj | hj⟩ := hy'
    · refine ⟨j, Or.inr ?_⟩
      rw [hj]
      abel
    · refine ⟨j, Or.inl ?_⟩
      rw [hj]
      abel
  unfold componentLaplacian
  apply Finset.sum_involution (fun y _ => reflect y)
  · intro y _
    change ((y.val i : ℝ) - (x.val i : ℝ)) +
      (((x.val + x.val - y.val) i : ℝ) - (x.val i : ℝ)) = 0
    simp only [Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]
    ring
  · intro y _ hne he
    have hv := congrArg (fun z : C => (z.val i : ℝ)) he
    change (((x.val + x.val - y.val) i : ℤ) : ℝ) = (y.val i : ℝ) at hv
    simp only [Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub] at hv
    exact hne (by linarith)
  · exact hmem
  · intro y _
    apply Subtype.ext
    change x.val + x.val - (x.val + x.val - y.val) = y.val
    abel

/-- A nonzero coordinate slope gives a real corrected plane on the actual infinite
all-open component in every positive dimension. -/
theorem allOpen_isCorrectedPlane_coordinate (d : ℕ) [NeZero d] (i : Fin d) :
    IsCorrectedPlane (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d))
      (Pi.single i 1) (fun x => (x.val i : ℝ)) := by
  let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d)
  constructor
  · apply mem_harmonicGrowthSpace_one_of_global_l1_bound C _
      (allOpen_component_coordinate_harmonic d i) (M := 1) zero_le_one
    intro x
    have hi := Finset.single_le_sum (fun j _ => abs_nonneg (x.val j : ℝ))
      (Finset.mem_univ i)
    linarith
  · intro ε hε
    refine ⟨1, zero_lt_one, fun R hR x _ => ?_⟩
    have hs : componentSlope C (Pi.single i 1) x = (x.val i : ℝ) := by
      simp only [componentSlope, Pi.single_apply, ite_mul, one_mul, zero_mul]
      exact Finset.sum_ite_eq' Finset.univ i (fun j => (x.val j : ℝ)) |>.trans
        (if_pos (Finset.mem_univ i))
    rw [hs, sub_self, abs_zero]
    exact mul_nonneg hε.le (zero_lt_one.trans_le hR).le

/-- The two-dimensional coordinate corrected plane is nonconstant on its actual component. -/
theorem allOpen_two_nonconstant_correctedPlane :
    let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
    ∃ u : C → ℝ, IsCorrectedPlane C (Pi.single 0 1) u ∧
      ∃ x y : C, u x ≠ u y := by
  dsimp only
  let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
  have hzero : (0 : Vertex 2) ∈ C.supp := by
    change (0 : Vertex 2) ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  have hunit : unit (0 : Fin 2) ∈ C.supp := by
    change unit (0 : Fin 2) ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  refine ⟨(fun x => (x.val 0 : ℝ)), allOpen_isCorrectedPlane_coordinate 2 0,
    ⟨0, hzero⟩, ⟨unit 0, hunit⟩, ?_⟩
  norm_num [unit, Pi.single_apply]

/-- The constant one on the same actual infinite component has zero slope. -/
theorem allOpen_two_isCorrectedPlane_const :
    IsCorrectedPlane (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2))
      0 (fun _ => 1) := isCorrectedPlane_const _ 1

end

end LatticeProb.Percolation
