import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionOscillation

/-! # Pasted excursion paths under a joint measure -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- Marginal compatibility, starting points and excursion oscillation bounds
control two pasted paths on every pair of good excursions. -/
theorem ae_pasted_excursion_dist_le_of_marginal_support
    {d K : ℕ} {V : Type*} (pos : V → Euc d)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (P : TimePartition K) {R a S : ℝ}
    (hdiam : ∀ i ≤ K, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (ρ : Measure ((ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d))))
    (x y : Euc d) (hnear : dist x y ≤ a)
    (hw : ∀ᵐ w ∂ρ.fst,
      (fun i => ClockedWalkExcursion.curve (w i).2) ∈
        ExcursionTrajectory.compatiblePaths K d ∧
      ClockedWalkExcursion.start (w 0).2 = x ∧
      ∀ i ≤ K, ClockedWalkExcursion.curve (w i).2 ∈ curveOscillationLe R)
    (hb : ∀ᵐ b ∂ρ.snd,
      (fun i => (b i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
      (b 0).2 0 = y ∧ ∀ i ≤ K, (b i).2 ∈ curveOscillationLe S) :
    ∀ᵐ p ∂ρ, (∀ i ≤ K, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) →
      ∀ t, dist (P.concatenate (ExcursionTrajectory.prefixChain K d
          (fun i => ClockedWalkExcursion.curve (p.1 i).2)) t)
        (P.concatenate (ExcursionTrajectory.prefixChain K d (fun i => (p.2 i).2)) t) ≤
          R + a + S := by
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hw,
    ae_of_ae_map measurable_snd.aemeasurable hb] with p hpw hpb
  intro hgood t
  apply goodExcursionPair_pasted_pointwise_dist_le pos P m E hdiam p.1 p.2
    hpw.1 hpb.1 hgood _ hpw.2.2 hpb.2.2 t
  simpa only [hpw.2.1, hpb.2.1] using hnear

end LatticeProb
