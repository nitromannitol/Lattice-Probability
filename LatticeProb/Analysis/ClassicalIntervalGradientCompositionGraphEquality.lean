import LatticeProb.Analysis.ClassicalIntervalGradientCompositionGraph
import LatticeProb.Analysis.ClassicalIntervalGradientFiniteSines
import LatticeProb.Analysis.PartialAdjointCompositionClosed

/-! # Closed interval gradient composition and the sine graph -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace LatticeProb

open LQGMetric.HeatSq

/-- The graph of the closed interval gradient followed by its adjoint is the
closure of the finite diagonal graph of normalized sine modes. -/
theorem classicalIntervalGradient_sineGraph_closure_iff {a b : ℝ}
    (hab : a < b) (x y : Lp ℂ 2 (volume.restrict (Ioo a b))) :
    (x, y) ∈ (show (Lp ℂ 2 (volume.restrict (Ioo a b))) →ₗ.[ℂ]
      (Lp ℂ 2 (volume.restrict (Ioo a b))) from
      ⟨_, orthonormalDiagonalCore (intervalSineHilbertBasis hab).orthonormal
        (fun n => (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2)⟩).graph.topologicalClosure ↔
    ∃ u : (classicalIntervalGradient a b).closure.domain,
      ∃ hu : (classicalIntervalGradient a b).closure u ∈
          (classicalIntervalGradient a b).closure.adjoint.domain,
        ((u : Lp ℂ 2 (volume.restrict (Ioo a b))),
          (classicalIntervalGradient a b).closure.adjoint ⟨_, hu⟩) = (x, y) := by
  classical
  constructor
  · intro h
    let B := intervalSineHilbertBasis hab
    let eig : ℕ → ℝ := fun n => (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2
    have hc : ∀ n, inner ℂ (B n) y = (eig n : ℂ) * inner ℂ (B n) x :=
      (hilbertBasis_diagonal_graph_closure_iff B eig x y).1 h
    have hx : Tendsto (fun s : Finset ℕ => ∑ n ∈ s, B.repr x n • B n) atTop (𝓝 x) :=
      B.hasSum_repr x
    have hy : Tendsto (fun s : Finset ℕ => ∑ n ∈ s, B.repr y n • B n) atTop (𝓝 y) :=
      B.hasSum_repr y
    have hclosed := isClosed_adjoint_composition_graph
      (classicalIntervalGradient a b).closure
      (classicalIntervalGradient_closure_dense hab)
      (classicalIntervalGradient_isClosable hab).closure_isClosed
    apply hclosed.mem_of_tendsto (hx.prodMk_nhds hy)
    apply Filter.Eventually.of_forall
    intro s
    let c : ℕ → ℂ := fun n => B.repr x n * (Real.sqrt (2 / (b - a)) : ℂ)
    obtain ⟨hs, hd, hv⟩ := classicalIntervalGradient_closure_adjoint_gradient_finite_sines hab s c
    have hfirst : (∑ n ∈ s, c n • (intervalSineMode_memLp a b n).toLp
        (intervalSineMode a (b - a) n)) = ∑ n ∈ s, B.repr x n • B n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [c, B, intervalSineHilbertBasis_apply, intervalNormalizedSineLp, mul_smul]
    have hsecond : (∑ n ∈ s, c n • (intervalSineEigenvalueMode_memLp a b n).toLp
        (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
          intervalSineMode a (b - a) n x)) = ∑ n ∈ s, B.repr y n • B n := by
      apply Finset.sum_congr rfl
      intro n hn
      have heig : (intervalSineEigenvalueMode_memLp a b n).toLp
          (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
            intervalSineMode a (b - a) n x) =
          (((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) : ℂ) •
            (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n) := by
        rw [← MemLp.toLp_const_smul]
        congr 1
      rw [heig, B.repr_apply_apply, hc n, ← B.repr_apply_apply]
      simp only [c, B, eig, intervalSineHilbertBasis_apply, intervalNormalizedSineLp,
        smul_smul]
      congr 1
      ring
    refine ⟨⟨_, hs⟩, hd, ?_⟩
    exact Prod.ext hfirst (hv.trans hsecond)
  · rintro ⟨u, hu, he⟩
    rw [← he]
    exact classicalIntervalGradient_composition_mem_sineGraph_closure hab u hu

end LatticeProb
