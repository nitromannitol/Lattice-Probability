import LatticeProb.Prob.DrivenHistoryTransition
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryIdentification

/-!
# Trajectory law of an independently driven path

Independent instructions whose update laws represent a Markov kernel generate
its full Ionescu–Tulcea trajectory law from a deterministic initial state.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder

namespace LatticeProb

variable {Ω X U : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace U] [Nonempty U]

/-- The entire driven path has the trajectory law of its transition kernel. -/
theorem map_drivenPath_eq_trajMeasure (P : Measure Ω)
    (F : X → U → X) (hF : Measurable (Function.uncurry F)) (x : X)
    (Z : ℕ → Ω → U) (hZ : ∀ j, Measurable (Z j)) (hI : iIndepFun Z P)
    (κ : Kernel X X) [IsMarkovKernel κ]
    (hκ : ∀ n y, (P.map (Z n)).map (F y) = κ y) :
    P.map (fun ω => drivenPath F x (fun j => Z j ω)) =
      Kernel.trajMeasure (X := fun _ => X) (Measure.dirac x)
        (fun n => κ.comap
          (fun h : Finset.Iic n → X => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)) := by
  let : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hpath : Measurable (fun ω => drivenPath F x (fun j => Z j ω)) :=
    (measurable_drivenPath F hF).comp
      (measurable_const.prodMk (Measurable.of_eval hZ))
  apply BouRabeeGwynne.TrajectoryCoupling.map_eq_trajMeasure_of_history_next P _ hpath
  · simp only [drivenPath_zero, Measure.map_const, measure_univ, one_smul]
  · intro n
    exact map_drivenPath_history_next P F hF x Z hZ hI κ n (hκ n)

end LatticeProb
