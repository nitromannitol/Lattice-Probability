/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UEnd at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UMeet

/-!
# DZZ P3.2 upper bound, ball crossing: the rings and the ends (P2-DZZ32U)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1058–1077) with balls (l. 1098–1101):

* `isPathConnected_frontier_chain`: the boundaries of a chain of neighbouring boxes of one level
  (an enclosure `ℂ_i`) form a path-connected set `Γ_i`;
* `preconn_meets_frontier`: a preconnected set meeting a closed set `B` and a point outside
  `int B` meets `∂B`;
* **`ball_end`**: the end `A` (`ℂ_start`, l. 1058–1066, 1076) reaches the boundary of a box of the
  first enclosing ring along a set covered by at most `R` balls of mass `≤ δ²`.

Own arguments on the level-`N` grid (decision D84), following DZZ's sketch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

lemma preconn_meets_frontier {K B : Set ℂ} (hK : IsPreconnected K) (hB : IsClosed B) {a w : ℂ}
    (ha : a ∈ K) (haB : a ∈ B) (hw : w ∈ K) (hwB : w ∉ interior B) :
    (K ∩ frontier B).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hsub : K ⊆ interior B ∪ Bᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · left
      by_contra hzi
      have : z ∈ frontier B := ⟨subset_closure hzB, hzi⟩
      exact (eq_empty_iff_forall_notMem.1 h) z ⟨hz, this⟩
    · exact Or.inr hzB
  have hai : a ∈ interior B := by
    rcases hsub ha with h' | h'
    · exact h'
    · exact absurd haB h'
  have := hK.subset_left_of_subset_union isOpen_interior hB.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hsub ⟨a, ha, hai⟩
  exact hwB (this hw)

/-- A square reached from `boxAt N u` along squares meeting `K` (with `u ∈ K`) meets `K`. -/
lemma meets_of_reach {K : Set ℂ} {u : ℂ} (hu : u ∈ K) (huV : u ∈ dzzV) {N : ℕ} {x : DyBox}
    (h : Relation.ReflTransGen (fun a b => SqAdj a b ∧ (b.closedBox ∩ K).Nonempty)
      (boxAt N u) x) : (x.closedBox ∩ K).Nonempty := by
  induction h with
  | refl => exact ⟨u, mem_closedBox_boxAt huV, hu⟩
  | tail _ h _ => exact h.2

end DZZ
end LQGMetric
