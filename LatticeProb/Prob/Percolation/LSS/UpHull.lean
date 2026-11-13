import LatticeProb.Prob.Percolation.LSS.Basic

/-!
# Increasing hulls of sets of configurations

The increasing hull of a set of configurations: the configurations that dominate some
member of the set coordinatewise. The hull contains the set, is increasing, lies inside
every increasing superset of the set, and is closed when the set is closed, because the
domination relation is closed and the configuration space is compact.

Ported from the Exploding-Sandpiles formalization, `Support/ExtLSSUpHull.lean`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace LatticeProb.Percolation.LSS

variable {S : Type}

/-- The increasing hull of `F`: the configurations dominating some configuration of `F`. -/
def xlsc_upHull (F : Set (S → Bool)) : Set (S → Bool) :=
  {x | ∃ y ∈ F, ∀ s, y s = true → x s = true}

/-- A set of configurations is contained in its increasing hull. -/
theorem xlsc_subset_upHull (F : Set (S → Bool)) : F ⊆ xlsc_upHull F := by
  intro x hx
  exact ⟨x, hx, fun _ h => h⟩

/-- The increasing hull of a set of configurations is an increasing set. -/
theorem xlsc_upHull_increasing (F : Set (S → Bool)) : IsIncreasingSet (xlsc_upHull F) := by
  intro ω ω' hω hle
  obtain ⟨y, hy, hyω⟩ := hω
  exact ⟨y, hy, fun s hs => hle s (hyω s hs)⟩

/-- The increasing hull of `F` lies inside every increasing set containing `F`. -/
theorem xlsc_upHull_subset {A F : Set (S → Bool)} (hA : IsIncreasingSet A) (hFA : F ⊆ A) :
    xlsc_upHull F ⊆ A := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact hA y x (hFA hy) hyx

/-- The coordinatewise domination relation on configurations is closed in the product
space. -/
theorem xlsc_isClosed_le :
    IsClosed {p : (S → Bool) × (S → Bool) | ∀ s, p.1 s = true → p.2 s = true} := by
  have hset : {p : (S → Bool) × (S → Bool) | ∀ s, p.1 s = true → p.2 s = true} =
      ⋂ s : S, ((fun p : (S → Bool) × (S → Bool) => p.1 s) ⁻¹' {false} ∪
        (fun p : (S → Bool) × (S → Bool) => p.2 s) ⁻¹' {true}) := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_preimage, mem_singleton_iff]
    refine forall_congr' fun s => ?_
    cases p.1 s <;> cases p.2 s <;> simp
  rw [hset]
  refine isClosed_iInter fun s => IsClosed.union ?_ ?_
  · exact IsClosed.preimage ((continuous_apply s).comp continuous_fst) (isClosed_discrete _)
  · exact IsClosed.preimage ((continuous_apply s).comp continuous_snd) (isClosed_discrete _)

/-- The increasing hull of a closed set of configurations is closed. -/
theorem xlsc_isClosed_upHull {F : Set (S → Bool)} (hF : IsClosed F) :
    IsClosed (xlsc_upHull F) := by
  have hset : xlsc_upHull F = Prod.snd '' ((F ×ˢ (univ : Set (S → Bool))) ∩
      {p : (S → Bool) × (S → Bool) | ∀ s, p.1 s = true → p.2 s = true}) := by
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨(y, x), ⟨⟨hy, mem_univ _⟩, h⟩, rfl⟩
    · rintro ⟨⟨y, z⟩, ⟨⟨hy, -⟩, h⟩, rfl⟩
      exact ⟨y, hy, h⟩
  rw [hset]
  have hcomp : IsCompact ((F ×ˢ (univ : Set (S → Bool))) ∩
      {p : (S → Bool) × (S → Bool) | ∀ s, p.1 s = true → p.2 s = true}) :=
    (hF.isCompact.prod isCompact_univ).inter_right xlsc_isClosed_le
  exact (hcomp.image continuous_snd).isClosed

end LatticeProb.Percolation.LSS
