import LatticeProb.Prob.BrownianSkeletonUnboundedPath
import LatticeProb.Prob.BrownianOpenExitFinite

/-!
# Almost-sure finiteness of Brownian skeleton clocks

Brownian motion in positive dimension has unbounded range almost surely. Thus
successive exit clocks from bounded domains are almost surely finite.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A translated positive-dimensional Brownian path has unbounded range almost surely. -/
theorem ae_brownian_translated_range_unbounded {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {x : Euc d} {B : ℝ≥0 → Ω → Euc d} {P : Measure Ω}
    (hd : 1 ≤ d) (hB : LatticeProb.IsBrownianSpace d x B P) (z : Euc d) :
    ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range fun t => z + B t ω) := by
  have hexits : ∀ᵐ ω ∂P, ∀ n : ℕ,
      LatticeProb.openExitTime B (Metric.ball (0 : Euc d) (n : ℝ)) ω ≠ ∞ :=
    ae_all_iff.mpr (fun n => LatticeProb.ae_openExitTime_ne_top hd hB Metric.isBounded_ball)
  filter_upwards [hexits, hB.cont] with ω hω hcont hbounded
  obtain ⟨R, hRpos, hR⟩ := hbounded.exists_pos_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt (R + ‖z‖)
  have hout := LatticeProb.openExitTime_not_mem Metric.isOpen_ball hcont (hω n)
  apply hout
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖B (LatticeProb.openExitTime B (Metric.ball (0 : Euc d) (n : ℝ)) ω).toNNReal ω‖
        ≤ ‖z + B (LatticeProb.openExitTime B (Metric.ball (0 : Euc d) (n : ℝ)) ω).toNNReal ω‖ + ‖z‖ := by
          simpa only [add_sub_cancel_left] using
            norm_sub_le (z + B (LatticeProb.openExitTime B (Metric.ball (0 : Euc d) (n : ℝ)) ω).toNNReal ω) z
    _ ≤ R + ‖z‖ := add_le_add (hR _ ⟨_, rfl⟩) le_rfl
    _ < (n : ℝ) := hn

/-- All successive bounded-domain skeleton clocks are finite almost surely. -/
theorem ae_brownianSkeletonClock_finite {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {x : Euc d} {B : ℝ≥0 → Ω → Euc d} {P : Measure Ω}
    (hd : 1 ≤ d) (hB : LatticeProb.IsBrownianSpace d x B P)
    (path : Ω → BrownianPath d) (hpath : ∀ t ω, path ω t = B t ω)
    {J : Type*} [Countable J] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)] (U : J → Set (Euc d))
    (hU : ∀ j, Bornology.IsBounded (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, (brownianSkeletonClock U z j₀ selector n (path ω)).2 ≠ ∞ := by
  filter_upwards [ae_brownian_translated_range_unbounded hd hB z] with ω hω n
  apply brownianSkeletonClock_finite_of_unbounded_range U hU z j₀ selector (path ω) _ n
  simpa only [hpath] using hω

end BouRabeeGwynne
