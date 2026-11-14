import LatticeProb.Prob.DrivenHistoryIndependence
import LatticeProb.Prob.DependentKernelMap

/-!
# Transition laws of driven paths

The law of a finite history and its next state is the composition of the
history law with the transition kernel evaluated at the last state.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {Ω X U : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace U] [Nonempty U]

/-- An independently driven path has the prescribed next-state kernel given its history. -/
theorem map_drivenPath_history_next (P : Measure Ω)
    (F : X → U → X) (hF : Measurable (Function.uncurry F)) (x : X)
    (Z : ℕ → Ω → U) (hZ : ∀ j, Measurable (Z j)) (hI : iIndepFun Z P)
    (κ : Kernel X X) [IsMarkovKernel κ] (n : ℕ)
    (hκ : ∀ y, (P.map (Z n)).map (F y) = κ y) :
    P.map (fun ω : Ω =>
      ((fun i : Finset.Iic n => drivenPath F x (fun j => Z j ω) i),
        drivenPath F x (fun j => Z j ω) (n + 1))) =
      (P.map (fun ω (i : Finset.Iic n) => drivenPath F x (fun j => Z j ω) i) ⊗ₘ
        κ.comap (fun h : Finset.Iic n → X => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)) := by
  let : IsProbabilityMeasure P := hI.isProbabilityMeasure
  let H : Ω → (Finset.Iic n → X) :=
    fun ω i => drivenPath F x (fun j => Z j ω) i
  let last : (Finset.Iic n → X) → X := fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hH : Measurable H := by
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i.val).comp
      ((measurable_drivenPath F hF).comp (measurable_const.prodMk (Measurable.of_eval hZ)))
  have hlast : Measurable last := measurable_pi_apply _
  have hg : Measurable (fun p : (Finset.Iic n → X) × U => F (last p.1) p.2) :=
    hF.comp ((hlast.comp measurable_fst).prodMk measurable_snd)
  have hprod := compProd_map_dependent_of_kernel_map (P.map H)
    (Kernel.const _ (P.map (Z n))) (κ.comap last hlast)
    id (fun h u => F (last h) u) measurable_id hg (fun h => hκ (last h))
  rw [Measure.map_id] at hprod
  calc
    _ = (P.map (fun ω => (H ω, Z n ω))).map
        (fun p => (p.1, F (last p.1) p.2)) := by
          rw [Measure.map_map (measurable_fst.prodMk hg) (hH.prodMk (hZ n))]
          rfl
    _ = _ := by
      rw [map_drivenPath_history_instruction_compProd P F hF x Z hZ hI n]
      exact hprod

end LatticeProb
