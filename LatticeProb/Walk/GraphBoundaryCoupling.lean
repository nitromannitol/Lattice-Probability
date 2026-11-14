import LatticeProb.Prob.ProductNoiseTrajectory
import LatticeProb.Walk.BoundaryUnionHit
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Coupling graph walks through a boundary hit

Markov trajectories whose transitions agree in the interior can be coupled
through their first visit to the inner boundary.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder unitInterval Set
open MatedCRTHarmonic.Markov

namespace LatticeProb

/-- Two almost surely legal graph walks with identical interior kernels admit a
    coupling agreeing through their common first inner-boundary hit. -/
theorem exists_productNoise_graphBoundary_trajectories {V : Type*}
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    (G : SimpleGraph V) (A : Set V)
    (κ η : Kernel V V) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hB : MeasurableSet (Aᶜ ∪ Graph.innerBoundary G A))
    (hκ : ∀ x ∉ Aᶜ ∪ Graph.innerBoundary G A, κ x = η x) (x : V)
    (hlegal : ∀ (k : Kernel V V) [IsMarkovKernel k], k = κ ∨ k = η →
      ∀ᵐ p ∂Kernel.trajMeasure (X := fun _ => V) (Measure.dirac x)
        (fun n => k.comap
          (fun h : Finset.Iic n → V => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)),
        p 0 ∈ A ∧ ∀ n, p (n + 1) = p n ∨ G.Adj (p n) (p (n + 1))) :
    ∃ P Q : (ℕ → I) → (ℕ → V), Measurable P ∧ Measurable Q ∧
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map P =
        Kernel.trajMeasure (X := fun _ => V) (Measure.dirac x)
          (fun n => κ.comap
            (fun h : Finset.Iic n → V => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
            (measurable_pi_apply _)) ∧
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map Q =
        Kernel.trajMeasure (X := fun _ => V) (Measure.dirac x)
          (fun n => η.comap
            (fun h : Finset.Iic n → V => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
            (measurable_pi_apply _)) ∧
      ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure I)),
        hitTime (Graph.innerBoundary G A) (P ω) =
            hitTime (Graph.innerBoundary G A) (Q ω) ∧
        ∀ n : ℕ, (n : ℕ∞) ≤ hitTime (Graph.innerBoundary G A) (P ω) →
          P ω n = Q ω n := by
  obtain ⟨P, Q, hP, hQ, hPlaw, hQlaw, hcouple⟩ :=
    exists_productNoise_trajectories κ η _ hB hκ x
  refine ⟨P, Q, hP, hQ, hPlaw, hQlaw, ?_⟩
  have hPae := (hP.quasiMeasurePreserving _).ae (by
    rw [hPlaw]
    exact hlegal κ (Or.inl rfl))
  have hQae := (hQ.quasiMeasurePreserving _).ae (by
    rw [hQlaw]
    exact hlegal η (Or.inr rfl))
  filter_upwards [hPae, hQae] with ω hp hq
  have hp' := hitTime_compl_union_innerBoundary G A (P ω) hp.1 hp.2
  have hq' := hitTime_compl_union_innerBoundary G A (Q ω) hq.1 hq.2
  have hc := hcouple ω
  rw [hp', hq'] at hc
  exact hc

end LatticeProb
