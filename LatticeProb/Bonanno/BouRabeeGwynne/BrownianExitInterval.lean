/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExitInterval at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNextExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionRange

/-! Every time between an actual stopping time and its next exit occurs in
the normalized restarted excursion. Thus a range bound controls the whole
original time interval, including its endpoints. -/

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

lemma mem_range_stoppedBrownianNextRepresentative {d : ℕ}
    (U : Set (Euc d)) (z : Euc d) (τ : BrownianPath d → ℝ≥0∞)
    (ω : BrownianPath d) (hfinite : brownianNextExitTime U z τ ω ≠ ∞)
    {t : ℝ≥0} (ht : t ∈ Icc (τ ω).toNNReal (brownianNextExitTime U z τ ω).toNNReal) :
    z + ω t ∈ range (stoppedBrownianRepresentative U (z + ω (τ ω).toNNReal)
      (shiftedBrownianPath (τ ω).toNNReal ω)) := by
  have hparts := ENNReal.add_ne_top.mp hfinite
  have htime : t - (τ ω).toNNReal ≤
      (continuousExitTime U (z + ω (τ ω).toNNReal)
        (shiftedBrownianPath (τ ω).toNNReal ω)).toNNReal := by
    apply tsub_le_iff_right.mpr
    have ht' := ht.2
    rw [brownianNextExitTime, ENNReal.toNNReal_add hparts.1 hparts.2] at ht'
    simpa only [add_comm] using ht'
  obtain ⟨u, hu⟩ := mem_range_stoppedBrownianRepresentative U
    (z + ω (τ ω).toNNReal) (shiftedBrownianPath (τ ω).toNNReal ω) htime
  refine ⟨u, hu.trans ?_⟩
  change (z + ω (τ ω).toNNReal) +
    (ω ((τ ω).toNNReal + (t - (τ ω).toNNReal)) - ω (τ ω).toNNReal) = z + ω t
  rw [add_tsub_cancel_of_le ht.1]
  abel

theorem dist_le_of_stoppedBrownianNextRepresentative_range {d : ℕ}
    (U : Set (Euc d)) (z : Euc d) (τ : BrownianPath d → ℝ≥0∞)
    (ω : BrownianPath d) (hfinite : brownianNextExitTime U z τ ω ≠ ∞)
    (η : ℝ)
    (hbound : ∀ u : unitInterval,
      dist (stoppedBrownianRepresentative U (z + ω (τ ω).toNNReal)
        (shiftedBrownianPath (τ ω).toNNReal ω) u) (z + ω (τ ω).toNNReal) ≤ η)
    {s t : ℝ≥0}
    (hs : s ∈ Icc (τ ω).toNNReal (brownianNextExitTime U z τ ω).toNNReal)
    (ht : t ∈ Icc (τ ω).toNNReal (brownianNextExitTime U z τ ω).toNNReal) :
    dist (z + ω s) (z + ω t) ≤ 2 * η := by
  obtain ⟨u, hu⟩ := mem_range_stoppedBrownianNextRepresentative U z τ ω hfinite hs
  obtain ⟨v, hv⟩ := mem_range_stoppedBrownianNextRepresentative U z τ ω hfinite ht
  have hsu := hbound u
  have htv := hbound v
  rw [hu] at hsu
  rw [hv] at htv
  calc
    dist (z + ω s) (z + ω t) ≤
      dist (z + ω s) (z + ω (τ ω).toNNReal) +
        dist (z + ω (τ ω).toNNReal) (z + ω t) := dist_triangle _ _ _
    _ ≤ η + η := add_le_add hsu (by simpa only [dist_comm] using htv)
    _ = 2 * η := by ring

end BouRabeeGwynne
