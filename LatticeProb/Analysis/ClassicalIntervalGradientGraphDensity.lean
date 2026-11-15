import LatticeProb.Analysis.ClassicalIntervalGradientGraphOrthogonality
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Density of sine modes in the interval gradient graph -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- The complex span of the sine modes and their derivatives is dense in the
closed interval gradient graph, with its Hilbert product topology. -/
theorem classicalIntervalGradient_closure_sine_graph_dense {a b : ℝ} (hab : a < b) :
    let E := Lp ℂ 2 (volume.restrict (Ioo a b))
    let f : ℕ → WithLp 2 (E × E) := fun n => WithLp.toLp 2
      ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n),
       (intervalSineDerivative_memLp a b n).toLp (intervalSineDerivative a (b - a) n))
    (Submodule.span ℂ (Set.range f)).topologicalClosure =
      ((classicalIntervalGradient a b).closure.graph.comap
        (WithLp.prodContinuousLinearEquiv 2 ℂ E E).toLinearMap) := by
  classical
  dsimp only
  let E := Lp ℂ 2 (volume.restrict (Ioo a b))
  let U := WithLp 2 (E × E)
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ E E
  let f : ℕ → U := fun n => WithLp.toLp 2
    ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n),
     (intervalSineDerivative_memLp a b n).toLp (intervalSineDerivative a (b - a) n))
  let S : Submodule ℂ U := Submodule.span ℂ (Set.range f)
  let G : Submodule ℂ U := (classicalIntervalGradient a b).closure.graph.comap e.toLinearMap
  change S.topologicalClosure = G
  have hclosed : IsClosed (G : Set U) := by
    have hg := (classicalIntervalGradient_isClosable hab).closure_isClosed
    exact hg.preimage e.continuous
  have hle : S.topologicalClosure ≤ G := by
    apply S.topologicalClosure_minimal ?_ hclosed
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    obtain ⟨hs, hv⟩ := classicalIntervalGradient_closure_sine hab n
    have h := (classicalIntervalGradient a b).closure.mem_graph ⟨_, hs⟩
    rw [hv] at h
    exact h
  have horth : S.topologicalClosureᗮ ⊓ G = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro p hp
    have hg : e p ∈ (classicalIntervalGradient a b).closure.graph := hp.2
    have ho : ∀ n : ℕ,
        inner ℂ ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n))
          (e p).1 +
        inner ℂ ((intervalSineDerivative_memLp a b n).toLp
          (intervalSineDerivative a (b - a) n)) (e p).2 = 0 := by
      intro n
      have hn : f n ∈ S.topologicalClosure := S.le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self n))
      have hz := (Submodule.mem_orthogonal _ _).mp hp.1 (f n) hn
      change inner ℂ (WithLp.toLp 2
        ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n),
         (intervalSineDerivative_memLp a b n).toLp (intervalSineDerivative a (b - a) n))) p = 0 at hz
      rw [WithLp.prod_inner_apply] at hz
      exact hz
    have hz := classicalIntervalGradient_closure_sine_graph_orthogonal_eq_zero hab (e p) hg ho
    have : p = 0 := e.injective (by simpa using hz)
    simp [this]
  have hsum := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
  rw [horth, sup_bot_eq] at hsum
  exact hsum

end LatticeProb
