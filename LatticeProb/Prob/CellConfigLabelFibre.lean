import LatticeProb.Prob.CellConfigLabelPathKernel
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryCoupling

/-! # Fixed-configuration labelled walk law -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- The transition on labels when the cell configuration is fixed. -/
def fixedKernel (H : GMSSpace) : Kernel ℕ ℕ :=
  kernel.comap (fun n => (H, n)) (measurable_const.prodMk measurable_id)

instance (H : GMSSpace) : IsMarkovKernel (fixedKernel H) := by
  unfold fixedKernel
  infer_instance

/-- The jointly measurable path kernel has the fixed-configuration chain law
at every configuration, including absorbing rows. -/
theorem pathKernel_eq_fixedChain (H : GMSSpace) (n : ℕ) :
    pathKernel (H, n) = ReflectedWalk.MarkovChain.chainLaw (fixedKernel H) n := by
  let f : ℕ → GMSSpace × ℕ := fun j => (H, j)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  have hstep : ∀ (i : ℕ) (h : Finset.Iic i → ℕ),
      ((ReflectedWalk.MarkovChain.histKernel (fixedKernel H) i) h).map f =
        (ReflectedWalk.MarkovChain.histKernel environmentStep i)
          (BouRabeeGwynne.TrajectoryCoupling.prefixMap f i h) := by
    intro i h
    ext s hs
    rw [Measure.map_apply hf hs]
    change kernel (H, _) (f ⁻¹' s) = environmentStep (H, _) s
    rw [environmentStep, Kernel.deterministic_prod_apply' measurable_fst kernel _ hs]
  have hinit : (Measure.dirac n).map f = Measure.dirac (H, n) :=
    Measure.map_dirac' hf n
  have hlaw := BouRabeeGwynne.TrajectoryCoupling.map_trajectory_law
    (Measure.dirac n) (ReflectedWalk.MarkovChain.histKernel (fixedKernel H))
    (Measure.dirac (H, n)) (ReflectedWalk.MarkovChain.histKernel environmentStep)
    f hf hinit hstep
  change (ReflectedWalk.MarkovChain.chainLaw (fixedKernel H) n).map
      (fun p j => f (p j)) =
    ReflectedWalk.MarkovChain.chainLaw environmentStep (H, n) at hlaw
  have hproj : Measurable (fun p : ℕ → GMSSpace × ℕ => fun j => (p j).2) :=
    Measurable.of_eval fun j => measurable_snd.comp (measurable_pi_apply j)
  have hemb : Measurable (fun p : ℕ → ℕ => fun j => f (p j)) :=
    Measurable.of_eval fun j => hf.comp (measurable_pi_apply j)
  rw [pathKernel, Kernel.map_apply _ hproj, ReflectedWalk.MarkovChain.pathKernel_apply,
    ← hlaw, Measure.map_map hproj hemb]
  change Measure.map id _ = _
  exact Measure.map_id

end LatticeProb.CellConfigLabelTransition
