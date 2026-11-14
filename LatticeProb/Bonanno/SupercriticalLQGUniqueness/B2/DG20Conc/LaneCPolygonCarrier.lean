/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPolygonCarrier at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPolygonApprox
import Mathlib.Topology.MetricSpace.Thickening

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP
open SupercriticalLQGUniqueness.Exponent.PolygonCofinality

 


theorem laneC_polygon_mem_of_segments
    {A : Set ℂ} {v : ℕ → ℂ} {N : ℕ} (hv0 : v 0 ∈ A)
    (hseg : ∀ i < N, ∀ u ∈ Icc (0 : ℝ) 1,
      segPath (v i) (v (i + 1)) u ∈ A) :
    ∀ u ∈ Icc (0 : ℝ) 1, polygonPath v N u ∈ A := by
  induction N with
  | zero =>
    intro u hu
    simpa [polygonPath] using hv0
  | succ N ih =>
    have hsegN : ∀ i < N, ∀ u ∈ Icc (0 : ℝ) 1,
        segPath (v i) (v (i + 1)) u ∈ A := by
      intro i hi
      exact hseg i (hi.trans (Nat.lt_succ_self N))
    have hsegLast := hseg N (Nat.lt_succ_self N)
    intro u hu
    change concatPath (polygonPath v N) (segPath (v N) (v (N + 1))) u ∈ A
    unfold concatPath
    split_ifs with h
    · simpa only [add_zero] using
        ih hsegN (2 * u) ⟨by linarith [hu.1], by linarith⟩
    · exact hsegLast (2 * u - 1)
        ⟨by linarith [not_le.mp h], by linarith [hu.2]⟩

 


end SupercriticalLQGUniqueness.B2.DG20Conc
