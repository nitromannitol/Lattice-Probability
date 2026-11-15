import LatticeProb.Walk.AdjacentPrefixExtension
import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-! # Holding clocks of finite-prefix extensions -/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb

/-- Positive holding times on a finite prefix make the clock of its alternating
last-edge extension unbounded. -/
theorem jumpTimesUnbounded_alternateLastEdge (H : CellConfig) (x : ℕ → H.cells)
    (k : ℕ) (hpos : ∀ j ≤ k + 1, 0 < H.holding (x j)) :
    H.JumpTimesUnbounded (alternateLastEdge x k) := by
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.range (k + 2))
    (fun i => H.holding (x i)) ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hc : 0 < H.holding (x j) := hpos j (by
    have := Finset.mem_range.mp hj
    omega)
  have hbound : ∀ n, H.holding (x j) ≤ H.holding (alternateLastEdge x k n) := by
    intro n
    rcases alternateLastEdge_edges x k n with ⟨i, hi, heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
      exact hmin i (Finset.mem_range.mpr (by omega))
    · rw [heq]
      exact hmin (k + 1) (Finset.mem_range.mpr (by omega))
  intro N
  obtain ⟨n, hn⟩ := exists_nat_gt ((N : ℝ) / H.holding (x j))
  refine ⟨n, ?_⟩
  have hsum : (n : ℝ) * H.holding (x j) ≤ H.jumpTime (alternateLastEdge x k) n := by
    unfold CellConfig.jumpTime
    calc
      (n : ℝ) * H.holding (x j) = ∑ _i ∈ Finset.range n, H.holding (x j) := by simp
      _ ≤ ∑ i ∈ Finset.range n, H.holding (alternateLastEdge x k i) :=
        Finset.sum_le_sum (fun i _ => hbound i)
  have hn' : (N : ℝ) < (n : ℝ) * H.holding (x j) := (div_lt_iff₀ hc).mp hn
  exact hn'.trans_le hsum

end LatticeProb
end
