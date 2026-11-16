import LatticeProb.Prob.AELeSigma
import LatticeProb.Prob.ExitObservationCondExp

/-! # Almost-sure containment of decreasing observation tails -/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace LatticeProb

/-- Countable decreasing target histories preserve containment up to null sets
at their infimum. The source histories need not be decreasing. -/
theorem AELeSigma.iInf_of_antitone {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure[m] Ω} {F G : ℕ → MeasurableSpace Ω}
    (hG : Antitone G) (hFG : ∀ n, AELeSigma (F n) (G n) μ) :
    AELeSigma (⨅ n, F n) (⨅ n, G n) μ := by
  classical
  intro s hs
  have hsF : ∀ n, MeasurableSet[F n] s := fun n => (iInf_le F n) _ hs
  choose t ht hst using fun n => hFG n s (hsF n)
  refine ⟨Filter.liminf t atTop, ?_, ?_⟩
  · refine (MeasurableSpace.measurableSet_iInf).2 fun k => ?_
    rw [← Filter.liminf_nat_add t k]
    let : MeasurableSpace Ω := G k
    apply MeasurableSet.measurableSet_liminf
    intro n
    exact hG (Nat.le_add_left k n) _ (ht (n + k))
  · exact (MeasureTheory.liminf_ae_eq_of_forall_ae_eq t (fun n => (hst n).symm)).symm

/-- Mutually almost-surely contained decreasing histories have the same
conditional expectations at their tails. -/
theorem condExp_iInf_ae_eq_of_mutual_aeLeSigma {Ω : Type*}
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    {F G : ℕ → MeasurableSpace Ω} (hF : Antitone F) (hG : Antitone G)
    (hFm : (⨅ n, F n) ≤ m) (hGm : (⨅ n, G n) ≤ m)
    (hFG : ∀ n, AELeSigma (F n) (G n) μ)
    (hGF : ∀ n, AELeSigma (G n) (F n) μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | ⨅ n, F n] =ᵐ[μ] μ[f | ⨅ n, G n] :=
  condExp_ae_eq_of_mutual_aeLeSigma hFm hGm
    (AELeSigma.iInf_of_antitone hG hFG) (AELeSigma.iInf_of_antitone hF hGF) hf

end LatticeProb
