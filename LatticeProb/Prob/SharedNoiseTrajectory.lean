import LatticeProb.Prob.SharedKernelUpdates
import LatticeProb.Prob.DrivenTrajectoryLaw
import LatticeProb.Walk.CoupledPrefixHit

/-!
# Shared-noise coupling of Markov trajectories

Two kernels that agree outside a measurable set admit trajectories driven by
common uniform instructions that agree through their first hit of the set.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder unitInterval
open MatedCRTHarmonic.Markov

namespace LatticeProb

/-- Couple two Markov trajectories using common independent uniform instructions. -/
theorem exists_sharedNoise_trajectories {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) (Z : ℕ → Ω → I) (hZ : ∀ n, Measurable (Z n))
    (hI : iIndepFun Z P) (hU : ∀ n, P.map (Z n) = volume)
    (κ η : Kernel X X) [IsMarkovKernel κ] [IsMarkovKernel η]
    (B : Set X) (hB : MeasurableSet B) (hκ : ∀ x ∉ B, κ x = η x) (x : X) :
    ∃ A C : Ω → (ℕ → X), Measurable A ∧ Measurable C ∧
      P.map A = Kernel.trajMeasure (X := fun _ => X) (Measure.dirac x)
        (fun n => κ.comap
          (fun h : Finset.Iic n → X => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)) ∧
      P.map C = Kernel.trajMeasure (X := fun _ => X) (Measure.dirac x)
        (fun n => η.comap
          (fun h : Finset.Iic n → X => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)) ∧
      ∀ ω, hitTime B (A ω) = hitTime B (C ω) ∧
        ∀ n : ℕ, (n : ℕ∞) ≤ hitTime B (A ω) → A ω n = C ω n := by
  obtain ⟨F, G, hF, hG, hFκ, hGη, hFG⟩ :=
    exists_shared_kernel_updates κ η Bᶜ hB.compl hκ
  let A : Ω → (ℕ → X) := fun ω => drivenPath F x (fun j => Z j ω)
  let C : Ω → (ℕ → X) := fun ω => drivenPath G x (fun j => Z j ω)
  have hA : Measurable A := (measurable_drivenPath F hF).comp
    (measurable_const.prodMk (Measurable.of_eval hZ))
  have hC : Measurable C := (measurable_drivenPath G hG).comp
    (measurable_const.prodMk (Measurable.of_eval hZ))
  refine ⟨A, C, hA, hC, ?_, ?_, ?_⟩
  · apply map_drivenPath_eq_trajMeasure P F hF x Z hZ hI κ
    intro n y
    rw [hU n, hFκ y]
  · apply map_drivenPath_eq_trajMeasure P G hG x Z hZ hI η
    intro n y
    rw [hU n, hGη y]
  · intro ω
    have h0 : A ω 0 = C ω 0 := rfl
    have hx : ∀ n, A ω (n + 1) = F (A ω n) (Z n ω) := fun _ => rfl
    have hy : ∀ n, C ω (n + 1) = G (C ω n) (Z n ω) := fun _ => rfl
    exact ⟨coupled_hitTime_eq B F G (fun j => Z j ω) (A ω) (C ω) h0 hx hy hFG,
      coupled_eq_of_le_hitTime B F G (fun j => Z j ω) (A ω) (C ω) h0 hx hy hFG⟩

end LatticeProb
