import LatticeProb.Prob.CellConfigLabelKernel
import LatticeProb.Bonanno.ReflectedWalk.ApproximatingChain
import Mathlib.Probability.Kernel.Composition.Prod

/-! # Path kernel for labelled cell walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- A labelled transition that retains its cell configuration. -/
def environmentStep : Kernel (GMSSpace × ℕ) (GMSSpace × ℕ) :=
  (Kernel.deterministic Prod.fst measurable_fst).prod kernel

instance : IsMarkovKernel environmentStep := by
  unfold environmentStep
  infer_instance

/-- Jointly measurable law of the sequence of labels, indexed from time zero. -/
def pathKernel : Kernel (GMSSpace × ℕ) (ℕ → ℕ) :=
  (ReflectedWalk.MarkovChain.pathKernel environmentStep).map (fun p n => (p n).2)

instance : IsMarkovKernel pathKernel := by
  exact Kernel.IsMarkovKernel.map _ (Measurable.of_eval fun i =>
    measurable_snd.comp (measurable_pi_apply i))

/-- The initial label has the prescribed starting value. -/
theorem pathKernel_initial (H : GMSSpace) (n : ℕ) :
    (pathKernel (H, n)).map (fun p => p 0) = Measure.dirac n := by
  have hm : Measurable (fun p : ℕ → GMSSpace × ℕ => fun i => (p i).2) :=
    Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i)
  rw [pathKernel, Kernel.map_apply _ hm, Measure.map_map (measurable_pi_apply 0) hm,
    ReflectedWalk.MarkovChain.pathKernel_apply]
  change Measure.map (Prod.snd ∘ (fun p : ℕ → GMSSpace × ℕ => p 0)) _ = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply 0),
    ReflectedWalk.MarkovChain.chainLaw_marginal_zero,
    Measure.map_dirac' measurable_snd]

/-- The first step has the original conductance transition law. -/
theorem pathKernel_first (H : GMSSpace) (n : ℕ) :
    (pathKernel (H, n)).map (fun p => p 1) = kernel (H, n) := by
  have hm : Measurable (fun p : ℕ → GMSSpace × ℕ => fun i => (p i).2) :=
    Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i)
  rw [pathKernel, Kernel.map_apply _ hm, Measure.map_map (measurable_pi_apply 1) hm,
    ReflectedWalk.MarkovChain.pathKernel_apply]
  change Measure.map (Prod.snd ∘ (fun p : ℕ → GMSSpace × ℕ => p 1)) _ = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply 1),
    ReflectedWalk.MarkovChain.chainLaw_marginal_one]
  change environmentStep.snd (H, n) = kernel (H, n)
  rw [environmentStep, Kernel.snd_prod]

end LatticeProb.CellConfigLabelTransition
