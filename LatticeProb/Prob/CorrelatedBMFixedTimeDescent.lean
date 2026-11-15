import LatticeProb.Prob.CorrelatedBMRationalDescent

/-!
# Immediate descent at a fixed time

At each fixed real time, both coordinates of a two-sided correlated Brownian pair descend
immediately on either side, almost surely. The exceptional set may depend on the time.
-/

open MeasureTheory Set

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Either coordinate descends immediately on both sides of a fixed real time, almost surely. -/
theorem ae_real_descends {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) (a : ℝ) :
    ∀ᵐ ω ∂μ, (∀ u < a, ∃ w ∈ Ioo u a, lrCoord i w ω < lrCoord i a ω) ∧
      ∀ u, a < u → ∃ w ∈ Ioo a u, lrCoord i w ω < lrCoord i a ω := by
  have hL := ae_forall_pos_exists_lt_zero (reversedCoordinate_isBrownianReal hμ i a)
    (fun t => (measurable_lrCoord (i, a - (t : ℝ))).sub (measurable_lrCoord (i, a)))
  have hR := ae_forall_pos_exists_lt_zero (shiftedCoordinate_isBrownianReal hμ i a)
    (fun t => (measurable_lrCoord (i, a + (t : ℝ))).sub (measurable_lrCoord (i, a)))
  filter_upwards [hL, hR] with ω hωL hωR
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨t, ht0, htε, hneg⟩ := hωL (a - u) (sub_pos.2 hu)
    refine ⟨a - t, ⟨by linarith, by linarith⟩, ?_⟩
    have h' : lrCoord i (a - t) ω - lrCoord i a ω < 0 := hneg
    linarith
  · obtain ⟨t, ht0, htε, hneg⟩ := hωR (u - a) (sub_pos.2 hu)
    refine ⟨a + t, ⟨by linarith, by linarith⟩, ?_⟩
    have h' : lrCoord i (a + t) ω - lrCoord i a ω < 0 := hneg
    linarith

/-- At a fixed real time, both coordinates descend immediately on both sides, almost surely. -/
theorem ae_forall_coord_real_descends {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (a : ℝ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2,
      (∀ u < a, ∃ w ∈ Ioo u a, lrCoord i w ω < lrCoord i a ω) ∧
        ∀ u, a < u → ∃ w ∈ Ioo a u, lrCoord i w ω < lrCoord i a ω :=
  ae_all_iff.2 fun i => ae_real_descends hμ i a

end LatticeProb.CorrelatedBM
