/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.CellArea at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs

/-!
# Unit mass, null overlaps and counting cells by area (deterministic)

Paper : "Distinct cells overlap only on sets of zero quantum area, so `A^γ_h(U^H_A) = |A|` for
finite `A ⊂ ℤ`." The area-overlap argument proves the
overlap claim from the area parameterization alone: if `μ(η([s, t])) = t − s` for all `s ≤ t`, then for
`s ≤ t ≤ s' ≤ t'`, `μ(η([s,t]) ∩ η([s',t'])) = 0` (inclusion–exclusion on `η([s,t']) = a ∪ c ∪ d`).

The counting lemma `finite_card_le_of_area` is the deterministic core of the cell-counting argument: if every cell meeting `D`
lies in `E`, then every finite family of such cells has cardinality `μ(⋃) ≤ μ(E)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- The image of a compact interval under a continuous curve is measurable. -/
theorem measurableSet_image_Icc (η : C(ℝ, ℂ)) (s t : ℝ) : MeasurableSet (η '' Icc s t) :=
  (isCompact_Icc.image η.continuous).measurableSet

/-- **Null overlaps of the area-parameterized curve** (the area-overlap argument): if `μ(η([s,t])) = t − s` for all
`s ≤ t`, then the images of two consecutive-or-separated intervals overlap in a `μ`-null set. -/
theorem measure_image_inter_eq_zero {μ : Measure ℂ} {η : C(ℝ, ℂ)}
    (hpar : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) {s t s' t' : ℝ}
    (hst : s ≤ t) (hts' : t ≤ s') (hs't' : s' ≤ t') :
    μ (η '' Icc s t ∩ η '' Icc s' t') = 0 := by
  set a := η '' Icc s t
  set c := η '' Icc t s'
  set d := η '' Icc s' t'
  have hunion : η '' Icc s t' = a ∪ c ∪ d := by
    have hI : Icc s t' = Icc s t ∪ Icc t s' ∪ Icc s' t' := by
      rw [Icc_union_Icc_eq_Icc hst hts', Icc_union_Icc_eq_Icc (le_trans hst hts') hs't']
    rw [hI, image_union, image_union]
  have hall : μ (a ∪ c ∪ d) = ENNReal.ofReal (t - s) + ENNReal.ofReal (s' - t) +
      ENNReal.ofReal (t' - s') := by
    rw [← hunion, hpar s t' (le_trans (le_trans hst hts') hs't'),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  have hle : μ (a ∪ c ∪ d) ≤ μ (a ∪ d) + μ c := by
    calc μ (a ∪ c ∪ d) = μ ((a ∪ d) ∪ c) := by
          congr 1
          ext z
          simp only [mem_union]
          tauto
      _ ≤ μ (a ∪ d) + μ c := measure_union_le _ _
  have hc : μ c = ENNReal.ofReal (s' - t) := hpar t s' hts'
  have had : μ (a ∪ d) + μ (a ∩ d) = ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') := by
    rw [measure_union_add_inter a (measurableSet_image_Icc η s' t'), hpar s t hst, hpar s' t' hs't']
  have hfin : μ (a ∪ d) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_union_le a d)
    rw [hpar s t hst, hpar s' t' hs't']
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have h1 : ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') ≤ μ (a ∪ d) := by
    have h2 : ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') + ENNReal.ofReal (s' - t) ≤
        μ (a ∪ d) + ENNReal.ofReal (s' - t) := by
      calc ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') + ENNReal.ofReal (s' - t)
          = μ (a ∪ c ∪ d) := by rw [hall]; ring
        _ ≤ μ (a ∪ d) + μ c := hle
        _ = μ (a ∪ d) + ENNReal.ofReal (s' - t) := by rw [hc]
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h2
  have h3 : μ (a ∪ d) + μ (a ∩ d) ≤ μ (a ∪ d) + 0 := by
    rw [had, add_zero]
    exact h1
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 h3) zero_le

end MatedCRTHarmonic.CellScaling
