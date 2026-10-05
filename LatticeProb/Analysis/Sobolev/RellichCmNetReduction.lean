/-
# The `C^m` net ⟹ low-frequency net reduction (Arzelà–Ascoli glue)

`rkLowFreqNet` (`RellichLowFreqNet.lean`) is the residual of the Rellich–Kondrachov external:
once a cutoff makes the high-frequency part of the `H^{s₀}` norm small, the remaining
low-frequency part of the `H^s` unit ball of test functions is totally bounded in `H^{s₀}`.

The classical proof obtains that total boundedness from a *uniform `C^m` bound* on the
low-frequency family: Arzelà–Ascoli turns the uniform derivative bounds into a finite net for
the sup norm, and the quantitative Fourier-decay residual `rkResidual_diff_bound`
(`RellichNet.lean`) converts `C^m`-closeness into `H^{s₀}`-closeness.

This module proves the Arzelà–Ascoli step
`exists_finite_supNet_of_uniformLip`: a uniformly bounded, uniformly Lipschitz family of
continuous functions on a compact space has a finite sup-net with centres in the family (so the
centres stay inside the family of test functions).

The former reduction `rkLowFreqNet_of_uniformCmNet`, which carried the `C^m`-net hypothesis
`rkUniformCmNet` and converted it to `rkLowFreqNet`, has been **removed**: `rkUniformCmNet` is
**false** once `s < m` (the `H^s` unit ball is not `C^m`-bounded; see the refutation recorded in
`RellichLowFreqNet.lean`), and its only consumer `RellichAssembly.lean` is quarantined.  The sound
route to `rkLowFreqNet` is `RellichLowFreqGlue.lean`.
-/
import Mathlib
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.RellichEstimate
import LatticeProb.Analysis.Sobolev.RellichNet

open MeasureTheory Set Metric
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-! ### Arzelà–Ascoli: a finite sup-net with centres in the family -/

/-- **Arzelà–Ascoli, net form.**  A set `S` of bounded continuous functions on a compact space
that is uniformly bounded by `C` and uniformly `C`-Lipschitz has, for every `ε > 0`, a finite
subset `T ⊆ S` that is an `ε`-net for `S` in the sup metric.  The centres are elements of `S`,
which is what keeps them inside the family of test functions in the reduction. -/
theorem exists_finite_supNet_of_uniformLip {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    (S : Set (BoundedContinuousFunction α ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ C)
    (hlip : ∀ f ∈ S, ∀ x y, dist (f x) (f y) ≤ C * dist x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set (BoundedContinuousFunction α ℝ), T ⊆ S ∧ T.Finite ∧
      ∀ f ∈ S, ∃ g ∈ T, dist f g ≤ ε := by
  have hcomp : IsCompact (closure S) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-C) C) isCompact_Icc S
      (fun f x hf => by
        rw [Set.mem_Icc]
        have h := hb f hf x
        rw [Real.norm_eq_abs] at h
        exact abs_le.mp h)
      (by
        intro x
        refine Metric.equicontinuousAt_iff.mpr ?_
        intro η hη
        refine ⟨η / (C + 1), by positivity, fun y hy i => ?_⟩
        have h1 : dist ((i : BoundedContinuousFunction α ℝ) x)
            ((i : BoundedContinuousFunction α ℝ) y) ≤ C * dist x y :=
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

/-! ### Quarantine: the refuted `C^m`-net input `rkUniformCmNet`

The declarations `rkUniformCmNet` and `rkLowFreqNet_of_uniformCmNet` that stood here have been
**removed**.  `rkUniformCmNet` asserted that the low-frequency family of test functions on `D`
admits a finite `C^m`-net; it is **false** for every `s < m`, because the `H^s` unit ball is
not `C^m`-bounded (the oscillating family `N^{-M} sin (N x_1) rho(x)` with `s < M < m`; the
refutation is recorded in `RellichLowFreqNet.lean`).  Its only consumer, `RellichAssembly.lean`, is
quarantined.  The sound route to `rkLowFreqNet` is `RellichLowFreqGlue.lean`.

What remains here is the genuine Arzela-Ascoli step `exists_finite_supNet_of_uniformLip` above.
-/

end LatticeProb.Sobolev
