/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.AppendFamilies at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.BandCarrier




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

private theorem appendFamily_card (A B : Exponent.PolygonalCost.RatPolygonFamily) :
    A.last+B.last+1+1 = (A.last+1)+(B.last+1) := by omega

def appendFamilies (A B : Exponent.PolygonalCost.RatPolygonFamily) : Exponent.PolygonalCost.RatPolygonFamily where
  last := A.last+B.last+1
  paths i := Fin.append A.paths B.paths
    (Fin.cast (appendFamily_card A B) i)

def appendFamilyLeft (A B : Exponent.PolygonalCost.RatPolygonFamily)
    (i : Fin (A.last+1)) : Fin ((appendFamilies A B).last+1) :=
  ⟨i.val, by simp [appendFamilies]; omega⟩

def appendFamilyRight (A B : Exponent.PolygonalCost.RatPolygonFamily)
    (i : Fin (B.last+1)) : Fin ((appendFamilies A B).last+1) :=
  ⟨A.last+1+i.val, by simp [appendFamilies]; omega⟩

theorem appendFamilies_left (A B : Exponent.PolygonalCost.RatPolygonFamily)
    (i : Fin (A.last+1)) :
    (appendFamilies A B).paths (appendFamilyLeft A B i) = A.paths i := by
  have hidx : Fin.cast (appendFamily_card A B) (appendFamilyLeft A B i) =
      Fin.castAdd (B.last+1) i := Fin.ext rfl
  change Fin.append A.paths B.paths
    (Fin.cast (appendFamily_card A B) (appendFamilyLeft A B i)) = A.paths i
  rw [hidx, Fin.append_left]

theorem appendFamilies_right (A B : Exponent.PolygonalCost.RatPolygonFamily)
    (i : Fin (B.last+1)) :
    (appendFamilies A B).paths (appendFamilyRight A B i) = B.paths i := by
  have hidx : Fin.cast (appendFamily_card A B) (appendFamilyRight A B i) =
      Fin.natAdd (A.last+1) i := Fin.ext rfl
  change Fin.append A.paths B.paths
    (Fin.cast (appendFamily_card A B) (appendFamilyRight A B i)) = B.paths i
  rw [hidx, Fin.append_right]

theorem appendFamilies_cost (A B : Exponent.PolygonalCost.RatPolygonFamily)
    (ξ : ℝ) (f : ℂ → ℝ) :
    (appendFamilies A B).cost ξ f = A.cost ξ f + B.cost ξ f := by
  let g : Fin ((A.last+1)+(B.last+1)) → ℝ≥0∞ :=
    fun i => LQGMetric.lfppLen ξ f (Fin.append A.paths B.paths i).path
  change (∑ i : Fin (A.last+B.last+1+1),
    g (Fin.cast (appendFamily_card A B) i)) =
    (∑ i : Fin (A.last+1), LQGMetric.lfppLen ξ f (A.paths i).path) +
    (∑ i : Fin (B.last+1), LQGMetric.lfppLen ξ f (B.paths i).path)
  rw [show (∑ i : Fin (A.last+B.last+1+1),
      g (Fin.cast (appendFamily_card A B) i)) =
      ∑ i : Fin ((A.last+1)+(B.last+1)), g i from
    Equiv.sum_comp (finCongr (appendFamily_card A B)) g]
  rw [Fin.sum_univ_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    simp [g]

theorem ratFamily_trace_iUnion (F : Exponent.PolygonalCost.RatPolygonFamily) :
    F.trace = ⋃ i : Fin (F.last+1), (F.paths i).path '' Set.Icc (0:ℝ) 1 := by
  ext z
  simp only [Exponent.PolygonalCost.RatPolygonFamily.trace, Exponent.PaidDuality.polygonPathsTrace,
    Finset.mem_univ, Set.iUnion_true]
  rfl

theorem appendFamilies_trace (A B : Exponent.PolygonalCost.RatPolygonFamily) :
    (appendFamilies A B).trace = A.trace ∪ B.trace := by
  rw [ratFamily_trace_iUnion, ratFamily_trace_iUnion, ratFamily_trace_iUnion]
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    by_cases hleft : i.val < A.last+1
    · let j : Fin (A.last+1) := ⟨i.val, hleft⟩
      have hij : i = appendFamilyLeft A B j := Fin.ext rfl
      rw [hij, appendFamilies_left] at hi
      exact Or.inl (Set.mem_iUnion.mpr ⟨j, hi⟩)
    · let j : Fin (B.last+1) := ⟨i.val-(A.last+1), by
          have hi0 := i.isLt
          simp [appendFamilies] at hi0
          omega⟩
      have hij : i = appendFamilyRight A B j := Fin.ext (by
        change i.val = A.last+1+(i.val-(A.last+1))
        omega)
      rw [hij, appendFamilies_right] at hi
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, hi⟩)
  · intro hz
    rcases hz with hA | hB
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
      exact Set.mem_iUnion.mpr ⟨appendFamilyLeft A B i,
        by rw [appendFamilies_left]; exact hi⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hB
      exact Set.mem_iUnion.mpr ⟨appendFamilyRight A B i,
        by rw [appendFamilies_right]; exact hi⟩


end SupercriticalLQGUniqueness.Exponent.InwardMap
