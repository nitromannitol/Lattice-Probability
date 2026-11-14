import LatticeProb.Prob.SharedNoiseTrajectory
import Mathlib.Probability.Independence.InfinitePi

/-!
# Product-noise coupling of Markov trajectories

A countable product of uniform measures supplies the independent instructions
for a coupling of Markov trajectories through their first hit of a set.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder unitInterval
open MatedCRTHarmonic.Markov

namespace LatticeProb

/-- Two Markov trajectories can be coupled on the product uniform space so that
    they agree through their first hit of a set outside which their kernels agree. -/
theorem exists_productNoise_trajectories {X : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (κ η : Kernel X X) [IsMarkovKernel κ] [IsMarkovKernel η]
    (B : Set X) (hB : MeasurableSet B) (hκ : ∀ x ∉ B, κ x = η x) (x : X) :
    ∃ A C : (ℕ → I) → (ℕ → X), Measurable A ∧ Measurable C ∧
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map A =
        Kernel.trajMeasure (X := fun _ => X) (Measure.dirac x)
          (fun n => κ.comap
            (fun h : Finset.Iic n → X => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
            (measurable_pi_apply _)) ∧
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map C =
        Kernel.trajMeasure (X := fun _ => X) (Measure.dirac x)
          (fun n => η.comap
            (fun h : Finset.Iic n → X => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
            (measurable_pi_apply _)) ∧
      ∀ ω, hitTime B (A ω) = hitTime B (C ω) ∧
        ∀ n : ℕ, (n : ℕ∞) ≤ hitTime B (A ω) → A ω n = C ω n := by
  apply exists_sharedNoise_trajectories
    (Measure.infinitePi fun _ : ℕ => (volume : Measure I))
    (fun n ω => ω n) (fun n => measurable_pi_apply n)
  · exact iIndepFun_infinitePi (X := fun _ (u : I) => u) fun _ => measurable_id
  · intro n
    exact Measure.infinitePi_map_eval _ n
  · exact hB
  · exact hκ

end LatticeProb
