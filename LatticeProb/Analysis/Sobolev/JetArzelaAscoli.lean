/-
# Arzelà–Ascoli with a general normed codomain (the jet-net input)

The low-frequency net route (`RellichCmNetSupply.lean`, `rkBandLimitedJetNet`) needs
Arzelà–Ascoli applied not to scalar functions but to the **iterated-derivative jet**
`x ↦ (f x, f' x, …)`, which lands in a finite-dimensional normed space.  The landed scalar form
`exists_finite_supNet_of_uniformLip` (`RellichCmNetReduction.lean`) is stated for
`BoundedContinuousFunction α ℝ`; this module generalizes it to a normed codomain `β` with
`ProperSpace β` (the jet space is finite-dimensional, hence proper).

The proof is the same: `BoundedContinuousFunction.arzela_ascoli` with the compact range
`Metric.closedBall 0 C` (compact by `ProperSpace`), equicontinuity from the Lipschitz bound, and
`EMetric.totallyBounded_iff'` for the centres-in-`S` net form.
-/
import Mathlib

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb.Sobolev

/-- **Arzelà–Ascoli, net form, general normed codomain.**  A uniformly bounded, uniformly
`C`-Lipschitz family of bounded continuous functions on a compact space into a proper normed
space has, for every `ε > 0`, a finite subset `T ⊆ S` that is an `ε`-net for `S` in the sup
metric.  The centres are elements of `S`. -/
theorem exists_finite_supNet_of_uniformLip_of_proper {α β : Type*} [PseudoMetricSpace α]
    [CompactSpace α] [NormedAddCommGroup β] [ProperSpace β]
    (S : Set (BoundedContinuousFunction α β)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ C)
    (hlip : ∀ f ∈ S, ∀ x y, dist (f x) (f y) ≤ C * dist x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set (BoundedContinuousFunction α β), T ⊆ S ∧ T.Finite ∧
      ∀ f ∈ S, ∃ g ∈ T, dist f g ≤ ε := by
  have hcomp : IsCompact (closure S) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 C) (isCompact_closedBall 0 C) S
      (fun f x hf => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hb f hf x)
      (by
        intro x
        refine Metric.equicontinuousAt_iff.mpr ?_
        intro η hη
        refine ⟨η / (C + 1), by positivity, fun y hy i => ?_⟩
        have h1 : dist ((i : BoundedContinuousFunction α β) x)
            ((i : BoundedContinuousFunction α β) y) ≤ C * dist x y :=
          hlip i i.2 x y
        have hden : (0 : ℝ) < C + 1 := by linarith
        have h2 : dist x y < η / (C + 1) := by rwa [dist_comm] at hy
        have h3 : C * (η / (C + 1)) < η := by
          rw [← mul_div_assoc, div_lt_iff₀ hden]
          nlinarith [hη]
        have h4 : C * dist x y ≤ C * (η / (C + 1)) :=
          mul_le_mul_of_nonneg_left (le_of_lt h2) hC
        linarith [h1, h4, h3])
  have htb : TotallyBounded S := hcomp.totallyBounded.subset subset_closure
  rw [EMetric.totallyBounded_iff'] at htb
  obtain ⟨T, hTS, hTfin, hTcov⟩ :=
    htb (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨T, hTS, hTfin, ?_⟩
  intro f hf
  rcases Set.mem_iUnion₂.1 (hTcov hf) with ⟨g, hgT, hfg⟩
  refine ⟨g, hgT, ?_⟩
  rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at hfg
  exact le_of_lt hfg

end LatticeProb.Sobolev
