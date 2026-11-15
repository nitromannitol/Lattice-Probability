import LatticeProb.Analysis.ClassicalIntervalGradientGraphDensity

/-! # Sequential sine approximation in the interval gradient graph -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace LatticeProb

open LQGMetric.HeatSq

/-- Every element of the closed interval gradient graph admits finite sine
approximations converging simultaneously with their gradients in L². -/
theorem classicalIntervalGradient_closure_sine_approximation {a b : ℝ} (hab : a < b)
    (p : Lp ℂ 2 (volume.restrict (Ioo a b)) × Lp ℂ 2 (volume.restrict (Ioo a b)))
    (hp : p ∈ (classicalIntervalGradient a b).closure.graph) :
    ∃ c : ℕ → (ℕ →₀ ℂ),
      Tendsto (fun k => ∑ n ∈ (c k).support, (c k) n •
        (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n)) atTop (𝓝 p.1) ∧
      Tendsto (fun k => ∑ n ∈ (c k).support, (c k) n •
        (intervalSineDerivative_memLp a b n).toLp
          (intervalSineDerivative a (b - a) n)) atTop (𝓝 p.2) := by
  classical
  let E := Lp ℂ 2 (volume.restrict (Ioo a b))
  let U := WithLp 2 (E × E)
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ E E
  let f : ℕ → U := fun n => WithLp.toLp 2
    ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n),
     (intervalSineDerivative_memLp a b n).toLp (intervalSineDerivative a (b - a) n))
  let S : Submodule ℂ U := Submodule.span ℂ (Set.range f)
  have hmem : e.symm p ∈ S.topologicalClosure := by
    rw [classicalIntervalGradient_closure_sine_graph_dense hab]
    simpa [e] using hp
  have hc : e.symm p ∈ closure (S : Set U) := by
    change e.symm p ∈ (S.topologicalClosure : Set U) at hmem
    rw [Submodule.topologicalClosure_coe] at hmem
    exact hmem
  obtain ⟨u, hu, hulim⟩ := mem_closure_iff_seq_limit.mp hc
  have hex : ∀ k, ∃ c : ℕ →₀ ℂ, (c.sum fun n z => z • f n) = u k := by
    intro k
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp (hu k)
  choose c hc using hex
  have hpair : Tendsto (fun k => e (u k)) atTop (𝓝 p) := by
    simpa only [Function.comp_def, e.apply_symm_apply] using
      e.continuous.continuousAt.tendsto.comp hulim
  refine ⟨c, ?_, ?_⟩
  · have h := continuous_fst.continuousAt.tendsto.comp hpair
    simpa only [Function.comp_def, ← hc, Finsupp.sum, map_sum, map_smul, e, f,
      WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_toLp, Prod.fst_sum,
      Prod.smul_fst] using h
  · have h := continuous_snd.continuousAt.tendsto.comp hpair
    simpa only [Function.comp_def, ← hc, Finsupp.sum, map_sum, map_smul, e, f,
      WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_toLp, Prod.snd_sum,
      Prod.smul_snd] using h

end LatticeProb
