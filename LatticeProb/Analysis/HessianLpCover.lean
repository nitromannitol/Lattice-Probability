import LatticeProb.Analysis.HessianLpReduction

/-! # Covering step for interior Hessian estimates

A local bound for the Hessian on `B(x, ρ/2)`, with data on `B(x, 4ρ/3)`, gives the bound on
`B(a, r/2)` with data on `B(a, r)`. Take `ρ = 3r/8`, cover `B(a, r/2)` by finitely many balls
`B(xₖ, 3r/16)` with `xₖ` in the closed ball `B̄(a, r/2)`, and note `B(xₖ, r/2) ⊆ B(a, r)`.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace HessianAdapter

/-- The `L^p` seminorm over a finite union of measurable sets is at most the sum of the `L^p`
seminorms over the sets. -/
theorem eLpNorm_restrict_biUnion_le {α ι F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p) {f : α → F} (hf : AEStronglyMeasurable f μ)
    (t : Finset ι) {s : ι → Set α} (hs : ∀ i ∈ t, MeasurableSet (s i)) :
    eLpNorm f p (μ.restrict (⋃ i ∈ t, s i)) ≤ ∑ i ∈ t, eLpNorm f p (μ.restrict (s i)) := by
  have hU : MeasurableSet (⋃ i ∈ t, s i) := Finset.measurableSet_biUnion t hs
  have hnn : ∀ (j : ι) (y : α), 0 ≤ (s j).indicator (fun z => ‖f z‖) y :=
    fun j y => Set.indicator_nonneg (fun _ _ => norm_nonneg _) y
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hU]
  calc eLpNorm ((⋃ i ∈ t, s i).indicator f) p μ
      ≤ eLpNorm (∑ i ∈ t, (s i).indicator fun z => ‖f z‖) p μ := by
        refine eLpNorm_mono_real (hf.indicator hU) fun y => ?_
        rw [Finset.sum_apply]
        by_cases hy : y ∈ ⋃ i ∈ t, s i
        · obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
          rw [Set.indicator_of_mem hy]
          calc ‖f y‖ = (s i).indicator (fun z => ‖f z‖) y :=
                (Set.indicator_of_mem hyi (fun z => ‖f z‖)).symm
            _ ≤ ∑ j ∈ t, (s j).indicator (fun z => ‖f z‖) y :=
              Finset.single_le_sum (fun j _ => hnn j y) hi
        · rw [Set.indicator_of_notMem hy, norm_zero]
          exact Finset.sum_nonneg fun j _ => hnn j y
    _ ≤ ∑ i ∈ t, eLpNorm ((s i).indicator fun z => ‖f z‖) p μ := eLpNorm_sum_le hp
    _ = ∑ i ∈ t, eLpNorm f p (μ.restrict (s i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (hs i hi), eLpNorm_norm f hf.restrict]

/-- The local estimate at the scale `ρ = 3r/8` gives the estimate on `B(a, r/2)` with data on
`B(a, r)`, for functions with finite right-hand side. -/
theorem L4_cover (d : ℕ) (h : LocalBallStmt d) : Q2FinAt (Euc d) volume := by
  intro p hp hpt a r hr
  obtain ⟨K, hK, hloc⟩ := h p hp hpt (3 * r / 8) (by positivity)
  obtain ⟨t, hta, hcov⟩ := (isCompact_closedBall a (r / 2)).elim_nhds_subcover
    (fun x => ball x (3 * r / 16)) fun x _ => ball_mem_nhds x (by positivity)
  refine ⟨t.card * K, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hK, ?_⟩
  intro w hw hfin
  set R := eLpNorm (Δ w) p (volume.restrict (ball a r)) +
    eLpNorm w ⊤ (volume.restrict (ball a r)) with hR
  have h43 : 4 * (3 * r / 8) / 3 = r / 2 := by ring
  have h12 : 3 * r / 8 / 2 = 3 * r / 16 := by ring
  have hsub : ∀ x ∈ t, ball x (r / 2) ⊆ ball a r := fun x hx =>
    ball_subset_ball' (by have := mem_closedBall.mp (hta x hx); linarith)
  have hRk : ∀ x ∈ t, eLpNorm (Δ w) p (volume.restrict (ball x (r / 2))) +
      eLpNorm w ⊤ (volume.restrict (ball x (r / 2))) ≤ R := fun x hx =>
    add_le_add (eLpNorm_mono_measure _ (Measure.restrict_mono (hsub x hx) le_rfl))
      (eLpNorm_mono_measure _ (Measure.restrict_mono (hsub x hx) le_rfl))
  have hk : ∀ x ∈ t, eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p
      (volume.restrict (ball x (3 * r / 16))) ≤ K * R := by
    intro x hx
    have hx' := hloc x w (by rw [h43]; exact hw.mono (hsub x hx))
      (by rw [h43]; exact ne_top_of_le_ne_top hfin (hRk x hx))
    rw [h43, h12] at hx'
    exact hx'.trans (by gcongr; exact hRk x hx)
  have hmeas : AEStronglyMeasurable (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) volume :=
    (measurable_fderiv ℝ (fderiv ℝ w)).norm.aestronglyMeasurable
  calc eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p (volume.restrict (ball a (r / 2)))
      ≤ eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p
          (volume.restrict (⋃ x ∈ t, ball x (3 * r / 16))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_closedBall.trans hcov) le_rfl)
    _ ≤ ∑ x ∈ t, eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p
          (volume.restrict (ball x (3 * r / 16))) :=
        eLpNorm_restrict_biUnion_le (one_le_two.trans hp) hmeas t fun _ _ => measurableSet_ball
    _ ≤ ∑ x ∈ t, K * R := Finset.sum_le_sum hk
    _ = t.card * K * R := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end HessianAdapter
