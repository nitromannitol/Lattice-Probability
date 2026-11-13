/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.FourBandCarrier at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.AppendFamilies




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

variable {ξ : ℝ} {f : ℂ → ℝ}

def fourBandRatFamily (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    Exponent.PolygonalCost.RatPolygonFamily where
  last := 3
  paths i := if i.val = 0 then bandPolygon F.nB F.vB F.ratB
    else if i.val = 1 then bandPolygon F.nT F.vT F.ratT
    else if i.val = 2 then bandPolygon F.nL F.vL F.ratL
    else bandPolygon F.nR F.vR F.ratR

private theorem fourBand_path_0 (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    ((fourBandRatFamily F).paths (0:Fin 4)).path = Exponent.PolygonCofinality.polygonPath F.vB F.nB := by
  simp [fourBandRatFamily, bandPolygon_path]

private theorem fourBand_path_1 (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    ((fourBandRatFamily F).paths (1:Fin 4)).path = Exponent.PolygonCofinality.polygonPath F.vT F.nT := by
  simp [fourBandRatFamily, bandPolygon_path]

private theorem fourBand_path_2 (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    ((fourBandRatFamily F).paths (2:Fin 4)).path = Exponent.PolygonCofinality.polygonPath F.vL F.nL := by
  simp [fourBandRatFamily, bandPolygon_path]

private theorem fourBand_path_3 (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    ((fourBandRatFamily F).paths (3:Fin 4)).path = Exponent.PolygonCofinality.polygonPath F.vR F.nR := by
  simp [fourBandRatFamily, bandPolygon_path]

theorem fourBandRatFamily_trace (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    (fourBandRatFamily F).trace = F.trace := by
  rw [ratFamily_trace_iUnion]
  ext z
  change z ∈ (⋃ i : Fin 4,
      ((fourBandRatFamily F).paths i).path '' Icc (0:ℝ) 1) ↔
    z ∈ F.trace
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    fin_cases i
    · have hB : z ∈ Exponent.PolygonCofinality.polygonPath F.vB F.nB '' Icc (0:ℝ) 1 := by
        simpa [fourBandRatFamily, bandPolygon_path] using hi
      exact Or.inl (Or.inl (Or.inl hB))
    · have hT : z ∈ Exponent.PolygonCofinality.polygonPath F.vT F.nT '' Icc (0:ℝ) 1 := by
        simpa [fourBandRatFamily, bandPolygon_path] using hi
      exact Or.inl (Or.inl (Or.inr hT))
    · have hL : z ∈ Exponent.PolygonCofinality.polygonPath F.vL F.nL '' Icc (0:ℝ) 1 := by
        simpa [fourBandRatFamily, bandPolygon_path] using hi
      exact Or.inl (Or.inr hL)
    · have hR : z ∈ Exponent.PolygonCofinality.polygonPath F.vR F.nR '' Icc (0:ℝ) 1 := by
        simpa [fourBandRatFamily, bandPolygon_path] using hi
      exact Or.inr hR
  · intro hz
    change z ∈ _ ∪ _ ∪ _ ∪ _ at hz
    rcases hz with (((hB | hT) | hL) | hR)
    · exact Set.mem_iUnion.mpr ⟨0, by rw [fourBand_path_0]; exact hB⟩
    · exact Set.mem_iUnion.mpr ⟨1, by rw [fourBand_path_1]; exact hT⟩
    · exact Set.mem_iUnion.mpr ⟨2, by rw [fourBand_path_2]; exact hL⟩
    · exact Set.mem_iUnion.mpr ⟨3, by rw [fourBand_path_3]; exact hR⟩

theorem fourBandRatFamily_cost (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    (fourBandRatFamily F).cost ξ f = F.cost := by
  change (∑ i : Fin 4, lfppLen ξ f ((fourBandRatFamily F).paths i).path) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp [fourBand_path_0, fourBand_path_1, fourBand_path_2,
    fourBand_path_3, Exponent.PolygonalCost.RationalFourBand.cost, add_assoc]


end SupercriticalLQGUniqueness.Exponent.InwardMap
