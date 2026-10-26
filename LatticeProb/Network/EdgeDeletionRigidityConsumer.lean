import LatticeProb.Network.EdgeDeletionRigidity

/-!
# An infinite-ray consumer of single-edge cancellation

The ray has vertex set `ℕ` and consecutive vertices adjacent. Two distinct constant
functions witness every premise of the cancellation theorem at its actual edge `{0,1}`.
-/

namespace LatticeProb.Network

/-- The infinite ray, with its actual consecutive-vertex edges. -/
def edgeCancellationRay : SimpleGraph ℕ where
  Adj x y := x + 1 = y ∨ y + 1 = x
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro x h; omega⟩

/-- Each ray neighbor lies among the predecessor and successor. -/
noncomputable instance edgeCancellationRayLocallyFinite : edgeCancellationRay.LocallyFinite :=
  fun n => Set.Finite.fintype (Set.Finite.subset
    ({n - 1, n + 1} : Finset ℕ).finite_toSet (by
      intro m hm
      change n + 1 = m ∨ m + 1 = n at hm
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      omega))

/-- Distinct constants on an infinite graph inhabit all cancellation hypotheses, including
harmonicity after deleting the actual edge `{0,1}`, and the theorem gives its old zero drop. -/
theorem exists_ray_edge_cancellation_consumer :
    ∃ (u v : ℕ → ℝ), u 0 ≠ v 0 ∧ edgeCancellationRay.Adj 0 1 ∧
      (∀ x, netLaplacian edgeCancellationRay (unitCond edgeCancellationRay) u x = 0) ∧
      (∀ x, netLaplacian (edgeCancellationRay.deleteEdges
        (({s(0, 1)} : Finset (Sym2 ℕ)) : Set (Sym2 ℕ)))
        (unitCond (edgeCancellationRay.deleteEdges
          (({s(0, 1)} : Finset (Sym2 ℕ)) : Set (Sym2 ℕ)))) v x = 0) ∧
      (∃ (K : Finset ℕ) (c : ℝ), ∀ x, x ∉ K → v x - u x = c) ∧ u 0 = u 1 := by
  let u : ℕ → ℝ := fun _ => 2
  let v : ℕ → ℝ := fun _ => 5
  have hadj : edgeCancellationRay.Adj 0 1 := Or.inl rfl
  have hu : ∀ x, netLaplacian edgeCancellationRay (unitCond edgeCancellationRay) u x = 0 :=
    netLaplacian_const _ 2
  have hv : ∀ x,
      netLaplacian (edgeCancellationRay.deleteEdges
        (({s(0, 1)} : Finset (Sym2 ℕ)) : Set (Sym2 ℕ)))
        (unitCond (edgeCancellationRay.deleteEdges
          (({s(0, 1)} : Finset (Sym2 ℕ)) : Set (Sym2 ℕ)))) v x = 0 :=
    netLaplacian_const _ 5
  have hcof : ∃ (K : Finset ℕ) (c : ℝ), ∀ x, x ∉ K → v x - u x = c :=
    ⟨∅, 3, fun _ _ => by norm_num [u, v]⟩
  exact ⟨u, v, by norm_num [u, v], hadj, hu, hv, hcof,
    edge_drop_eq_zero_of_harmonic_cofinite_difference edgeCancellationRay hadj u v hu hv hcof⟩

end LatticeProb.Network
