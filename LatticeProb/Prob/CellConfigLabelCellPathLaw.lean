import LatticeProb.Prob.CellConfigLabelCellKernel
import LatticeProb.Prob.CellConfigLabelSupport

/-! # Cell walk and its labelled trajectory -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- The label of a cell in a fixed valid configuration. -/
def cellLabel (H : GMSSpace) (K : H.1.cells) : ℕ :=
  ((H.1.cellEquiv H.2).symm K).val

/-- Relabelling the cell transition gives the labelled transition. -/
theorem cellKernel_map_label (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) :
    (CellConfigSRW.kernel H.1 (H.1.cellEquiv H.2 v)).map (cellLabel H) =
      fixedKernel H v.val := by
  classical
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton n)]
  by_cases hn : H.1.slot n = none
  · have hp : cellLabel H ⁻¹' {n} = ∅ := by
      ext K
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro he
      have hv := H.1.slot_val ((H.1.cellEquiv H.2).symm K)
      rw [← he] at hn
      change H.1.slot (cellLabel H K) = some _ at hv
      rw [hn] at hv
      cases hv
    rw [hp, measure_empty, fixedKernel, Kernel.comap_apply, kernel_singleton,
      step_eq_zero_of_occupied_of_absent H (by rw [H.1.slot_val v]; simp) hn, ENNReal.ofReal_zero]
  · let w : Code.Vertex H.1.code := ⟨n, by
      change (H.1.slot n).isSome = true
      cases hs : H.1.slot n <;> simp_all⟩
    have hp : cellLabel H ⁻¹' {n} = {H.1.cellEquiv H.2 w} := by
      ext K
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro he
        apply (H.1.cellEquiv H.2).symm.injective
        apply Subtype.ext
        simpa [cellLabel, w] using he
      · intro he
        subst K
        simp [cellLabel, w]
    rw [hp]
    exact (fixedKernel_singleton_eq_cellKernel H v w).symm

/-- The entire labelled trajectory is the image of the cell walk. -/
theorem cellWalk_map_label (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) :
    (CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v)).map
      (fun p j => cellLabel H (p j)) = pathKernel (H, v.val) := by
  let : IsMarkovKernel (CellConfigSRW.kernel H.1) :=
    CellConfigSRW.isMarkovKernel_kernel H.1 H.2
  have hf : Measurable (cellLabel H) := measurable_of_countable _
  have hstep : ∀ (i : ℕ) (h : Finset.Iic i → H.1.cells),
      ((MatedCRTHarmonic.Markov.histKernel (CellConfigSRW.kernel H.1) i) h).map
          (cellLabel H) =
        (ReflectedWalk.MarkovChain.histKernel (fixedKernel H) i)
          (BouRabeeGwynne.TrajectoryCoupling.prefixMap (cellLabel H) i h) := by
    intro i h
    change (CellConfigSRW.kernel H.1 (h ⟨i, Finset.mem_Iic.mpr le_rfl⟩)).map _ = _
    let w := (H.1.cellEquiv H.2).symm (h ⟨i, Finset.mem_Iic.mpr le_rfl⟩)
    simpa [w, cellLabel, ReflectedWalk.MarkovChain.histKernel,
      ReflectedWalk.MarkovChain.lastCoord, BouRabeeGwynne.TrajectoryCoupling.prefixMap] using
      cellKernel_map_label H w
  have hinit : (Measure.dirac (H.1.cellEquiv H.2 v)).map (cellLabel H) =
      Measure.dirac v.val := by
    rw [Measure.map_dirac' hf]
    simp [cellLabel]
  have h := BouRabeeGwynne.TrajectoryCoupling.map_trajectory_law
    (Measure.dirac (H.1.cellEquiv H.2 v))
    (MatedCRTHarmonic.Markov.histKernel (CellConfigSRW.kernel H.1))
    (Measure.dirac v.val) (ReflectedWalk.MarkovChain.histKernel (fixedKernel H))
    (cellLabel H) hf hinit hstep
  rw [pathKernel_eq_fixedChain]
  exact h

end LatticeProb.CellConfigLabelTransition
