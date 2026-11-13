/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonTraceLast at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonFamilyImage




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Convex

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

theorem polygonPath_trace_edges_last (v : ℕ → ℂ) (n : ℕ) :
    Exponent.PolygonCofinality.polygonPath v n '' Icc (0:ℝ) 1 =
      {v n} ∪ ⋃ j ∈ Finset.range n, [v j -[ℝ] v (j+1)] := by
  rw [Exponent.PaidDuality.polygonPath_trace]
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  ext z
  constructor
  · rintro (h | h)
    · have hz : z = v 0 := by simpa using h
      right
      rw [hz]
      exact Set.mem_iUnion_of_mem 0
        (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hn0)
          (left_mem_segment ℝ (v 0) (v (0+1))))
    · exact Or.inr h
  · rintro (h | h)
    · have hz : z = v n := by simpa using h
      right
      rw [hz]
      have hlast : n-1 < n := Nat.sub_lt hn0 (Nat.succ_pos 0)
      have heq : n-1+1=n := Nat.sub_add_cancel hn0
      refine Set.mem_iUnion_of_mem (n-1) ?_
      refine Set.mem_iUnion_of_mem (Finset.mem_range.mpr hlast) ?_
      simpa [heq] using
        (right_mem_segment ℝ (v (n-1)) (v (n-1+1)))
    · exact Or.inr h


end SupercriticalLQGUniqueness.Exponent.InwardMap
