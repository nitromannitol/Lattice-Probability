import LatticeProb.Bonanno.ReflectedGMS.GMS.WeakConvergenceTransfer

/-! # Compact-window containment under weak convergence -/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Metric ReflectedGMS
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- Weak convergence of continuous-path laws gives eventual boundedness in probability
on any compact time window. The exceptional event is bounded as an outer measure. -/
theorem eventually_measure_path_window_norm_gt_lt
    {ι : Type*} {L : Filter ι}
    {μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    {μs : ι → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    (hlim : Tendsto μs L (𝓝 μ)) (T : ℝ≥0) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ, ∀ᶠ i in L, (μs i : Measure (BouRabeeGwynne.BrownianPath 2))
      {f | ∃ t ≤ T, R < ‖f t‖} < η := by
  let A : ℕ → Set (BouRabeeGwynne.BrownianPath 2) := fun n =>
    {f | ∀ t ≤ T, ‖f t‖ < (n : ℝ)}
  have hA : Monotone A := by
    intro n m hnm f hf t ht
    exact lt_of_lt_of_le (hf t ht) (by exact_mod_cast hnm)
  have hcover : ∀ f, ∃ n, A n ∈ 𝓝 f := by
    intro f
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).bddAbove_image
      f.continuous.norm.continuousOn
    obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
    refine ⟨n, Filter.mem_of_superset
      (ReflectedGMS.GMS.WeakConvergenceTransfer.setOf_forall_dist_lt_mem_nhds f T zero_lt_one) ?_⟩
    intro g hg t ht
    have hft : ‖f t‖ ≤ M := hM ⟨t, ⟨zero_le, ht⟩, rfl⟩
    have hdist := hg t ht
    have htri := norm_le_norm_sub_add (g t) (f t)
    rw [dist_eq_norm, norm_sub_rev] at hdist
    linarith
  obtain ⟨n, hn⟩ :=
    ReflectedGMS.GMS.WeakConvergenceTransfer.exists_eventually_measure_compl_interior_lt
      hlim A hA hcover hη
  refine ⟨n, hn.mono fun i hi => lt_of_le_of_lt ?_ hi⟩
  apply measure_mono
  intro f hf hfint
  obtain ⟨t, ht, hgt⟩ := hf
  have hbound := interior_subset hfint t ht
  exact (not_lt_of_ge hgt.le) hbound

end LatticeProb
end
